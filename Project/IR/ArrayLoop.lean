import Project.IR.Live
import Project.IR.Loop
import Project.IR.Build

/-!
The rule lemma for the compiler's loop over an array state.  The compiler
translates `LeanExe.loop n init f`, where `init` is an `Array Float` variable and
`f l x` is one call of a compiled function, to a copy of `init` into the state
local and `Stmt.loop`, whose body calls the function, releases the previous
state, and moves the call's result into the state local.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

theorem Expr.evalResults_frame (writes : List Nat) {mem : Mem} {scratch : Nat} :
    ∀ {args : List ((type : ScalarType) × Expr type)} {state after : State} {vals : List Value},
      Expr.evalResults mem scratch args state = some (vals, after) →
        State.Frame scratch writes state after
  | [], _, _, _, h => by
      simp only [Expr.evalResults, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact State.Frame.refl _ _ _
  | ⟨_, e⟩ :: rest, state, _, _, h => by
      unfold Expr.evalResults at h
      cases hE : e.eval mem scratch state with
      | none => simp [hE] at h
      | some r =>
          obtain ⟨value, next⟩ := r
          cases hR : Expr.evalResults mem scratch rest next with
          | none => simp [hE, hR] at h
          | some r' =>
              obtain ⟨_, _⟩ := r'
              simp only [hE, hR, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact (Expr.eval_frame writes e mem scratch state next value hE).trans
                (Expr.evalResults_frame writes hR)

/-- A new array joins the live temporaries. -/
theorem Live.push {heap0 heap heap' : Heap} {initial store store' : Store Unit}
    {temps : List (UInt64 × Array UInt64)} {ptr : UInt64} {ws : Array UInt64}
    (hLive : Live heap0 initial heap store temps)
    (hNew : heap.NewArray store heap' store' ptr ws) :
    Live heap0 initial heap' store' ((ptr, ws) :: temps) := by
  have hKeepT : ∀ t ∈ temps, heap'.Owned store' t.1 t.2 ∧ block store' t.1 = block store t.1 :=
    fun t ht => ⟨(hNew.ownedKeep t.1 t.2 (hLive.tempsOwned t ht)).1,
      block_eq (hNew.ownedKeep t.1 t.2 (hLive.tempsOwned t ht)).2⟩
  refine ⟨hNew.at_, hNew.caps.trans hLive.caps, fun p ws h => hNew.borrowed p ws (hLive.borrowed p ws h),
    fun p ws h => ⟨(hNew.ownedKeep p ws (hLive.owned p ws h).1).1,
      (hNew.ownedKeep p ws (hLive.owned p ws h).1).2.trans (hLive.owned p ws h).2⟩,
    fun t ht => ?_, fun t ht p ws h => ?_, fun t ht p ws h => ?_, ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hNew.owned
    · exact (hKeepT t ht).1
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hNew.borrowedApart p ws (hLive.borrowed p ws h)
    · rw [(hKeepT t ht).2]; exact hLive.apartB t ht p ws h
  · rcases List.mem_cons.mp ht with rfl | ht
    · have hDisjoint := hNew.ownedApart p ws (hLive.owned p ws h).1
      rw [(hLive.owned p ws h).2] at hDisjoint
      exact hDisjoint
    · rw [(hKeepT t ht).2]; exact hLive.apartO t ht p ws h
  · refine List.pairwise_cons.mpr ⟨fun t ht => ?_, ?_⟩
    · rw [(hKeepT t ht).2]
      exact regionsDisjoint_symm (hNew.ownedApart t.1 t.2 (hLive.tempsOwned t ht))
    · refine List.Pairwise.imp_of_mem (fun {t u} ht hu h => ?_) hLive.pairwise
      rw [(hKeepT t ht).2, (hKeepT u hu).2]
      exact h

/-- A copy of an array adds the copy to the live temporaries. -/
theorem Live.copy {typeIdx scratch src size dst limit index : Nat} (hMemory32 : m.memIs64 = false)
    (hImports : m.imports = []) (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [size, dst, limit, index].Nodup)
    (hBelow : ∀ j ∈ [size, dst, limit, index], j < scratch)
    (hSrc : src ∉ [size, dst, limit, index]) (hSrcBelow : src < scratch) {before : State}
    (hRoom : scratch < before.params.length + before.locals.length) {heap0 heap : Heap}
    {initial store : Store Unit} {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {ptr : UInt64} {xs : Array UInt64}
    (hPtr : before.get src = some (.i64 ptr)) (hArray : heap.Borrowed store ptr xs) :
    Triple m (.copy dst limit index size src) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' p, Live heap0 initial heap' s
        ((p, xs) :: temps) ∧ State.Frame scratch [size, dst, limit, index] before st ∧
        st.get dst = some (.i64 p)) :=
  (Stmt.copy_spec hMemory32 hImports hFunc hLocals hBelow hSrc hSrcBelow hRoom hLive.at_
    (hLive.cap hCap) hPtr hArray).mono (fun _ _ h => h)
    fun _ _ ⟨p, hFrame, hDst, hNew⟩ => ⟨_, p, hLive.push hNew, hFrame, hDst⟩

/-- The compiler's loop over an array state: local `state` receives a copy of the
array at local `src`; for each index below `count`, a call of function `idx`
leaves the next state in local `next`, the previous state is released, and
`state` takes the next. -/
def Stmt.arrayLoop (state size limit index next src idx : Nat) (count : Expr .u64)
    (args : List ((type : ScalarType) × Expr type)) : Stmt :=
  .seq (.copy state limit index size src) <|
    .loop limit index count <|
      .seq (.call idx args [next]) (.seq (.release state) (.assign state (.get next)))

/-- The loop leaves `LeanExe.loop n init (fun l x => g (F l x))` in a new array at
the head of the live temporaries, whose pointer local `state` holds, or aborts,
provided the call of `idx`, which implements `g`, receives arguments that represent
`F l x` at each index `l` and state `x`. -/
theorem Live.arrayLoop [Represent α] {idx : Nat} {g : α → Array Float}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams)
    {allocType releaseType : Nat} (hMemory32 : m.memIs64 = false) (hImports : m.imports = [])
    (hAlloc : m.funcs[0]? = some (allocFunction allocType))
    (hRelease : m.funcs[1]? = some (releaseFunction releaseType))
    {scratch state size limit index next src : Nat}
    (hLocals : [state, size, limit, index, next].Nodup)
    (hBelow : ∀ j ∈ [state, size, limit, index, next], j < scratch)
    (hSrc : src ∉ [state, size, limit, index, next]) (hSrcBelow : src < scratch)
    {before : State} (hRoom : scratch < before.params.length + before.locals.length)
    {heap0 heap : Heap} {initial store : Store Unit}
    {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {ptr : UInt64} {init : Array Float} (hPtr : before.get src = some (.i64 ptr))
    (hInit : heap.Borrowed store ptr (init.map Float.toBits))
    {count : Expr .u64} {n : UInt64}
    (hCount : ∀ mem st, State.Frame scratch [state, size, limit, index, next] before st →
      ∃ after, count.eval mem scratch st = some (n, after))
    (F : UInt64 → Array Float → α)
    (hArgs : ∀ (k : Nat) (p : UInt64) (heap' : Heap) (store' : Store Unit) (st : State),
      k < n.toNat → State.Frame scratch [state, size, limit, index, next] before st →
      st.get index = some (.i64 (UInt64.ofNat k)) → st.get state = some (.i64 p) →
      Live heap0 initial heap' store'
        ((p, (loopPrefix (fun l x => g (F l x)) init k).map Float.toBits) :: temps) →
      ∃ vals after, Expr.evalResults store'.mem scratch args st = some (vals, after) ∧
        Represent.borrowed heap' store' vals
          (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) init k)))
    {rest : Stmt} {Q : Store Unit → State → Prop}
    (hRest : ∀ heap' p s st,
      Live heap0 initial heap' s
        ((p, (LeanExe.loop n init fun l x => g (F l x)).map Float.toBits) :: temps) →
      State.Frame scratch [state, size, limit, index, next] before st →
      st.get state = some (.i64 p) →
      Triple m rest scratch (fun s' st' => s' = s ∧ st' = st) Q) :
    Triple m (.seq (Stmt.arrayLoop state size limit index next src idx count args) rest) scratch
      (fun s st => s = store ∧ st = before) Q := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨hStateB, hSizeB, hLimitB, hIndexB, hNextB⟩ := hBelow
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  obtain ⟨⟨hSS, hSL, hSI, hSN⟩, ⟨hZL, hZI, hZN⟩, ⟨hLI, hLN⟩, hIN⟩ := hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hSrc
  have hn := n.toNat_lt
  have hSize : (init.map Float.toBits).size = init.size := Array.size_map ..
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have hFrameLen : ∀ {w : List Nat} {st : State}, State.Frame scratch w before st →
      scratch < st.params.length + st.locals.length := fun h => by
    rw [h.params, h.locals]; exact hRoom
  let Inv : Store Unit → State → Prop := fun s st =>
    State.Frame scratch [state, size, limit, index, next] before st ∧
      ∃ k, k ≤ n.toNat ∧ st.get index = some (.i64 (UInt64.ofNat k)) ∧
        st.get limit = some (.i64 n) ∧
        ∃ heap' p, Live heap0 initial heap' s
          ((p, (loopPrefix (fun l x => g (F l x)) init k).map Float.toBits) :: temps) ∧
          st.get state = some (.i64 p)
  let measure : Store Unit → State → Nat := fun _ st =>
    match st.get index with
    | some (.i64 k) => n.toNat - k.toNat
    | _ => 0
  refine Stmt.seq_spec (M := fun s st => ∃ heap' p,
      Live heap0 initial heap' s
        ((p, (LeanExe.loop n init fun l x => g (F l x)).map Float.toBits) :: temps) ∧
      State.Frame scratch [state, size, limit, index, next] before st ∧
      st.get state = some (.i64 p)) (Stmt.seq_spec (Live.copy hMemory32 hImports hAlloc
      (by simp; omega) (by simp; omega) (by simp; omega) hSrcBelow hRoom hLive hCap hPtr hInit)
      ?_) ?_
  · apply Triple.of_forall
    rintro s1 st1 ⟨heap1, p1, hLive1, hFrame1, hState1⟩
    have hFrame1W : State.Frame scratch [state, size, limit, index, next] before st1 :=
      hFrame1.weaken (by simp)
    obtain ⟨c1, hCountEval⟩ := hCount s1.mem st1 hFrame1W
    have hFrameC := Expr.eval_frame [] count s1.mem scratch st1 c1 _ hCountEval
    have hLenC : scratch < c1.params.length + c1.locals.length := by
      rw [hFrameC.params, hFrameC.locals]; exact hFrameLen hFrame1W
    obtain ⟨t1, hSet1⟩ := State.exists_set? (state := c1) (index := limit) (.i64 n) (by omega)
    obtain ⟨t2, hSet2⟩ := State.exists_set? (state := t1) (index := index) (.i64 0) (by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hSet1
      subst hSet1; rw [hLen]; omega)
    refine Stmt.seq_spec (M := fun s st => s = s1 ∧ st = t1) ?_ <|
      Stmt.seq_spec (M := fun s st => s = s1 ∧ st = t2) ?_ <|
      (Stmt.while_spec Inv measure ?_ fun bound' => ?_).mono ?_ ?_
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      exact ⟨n, c1, t1, hCountEval, hSet1, rfl, rfl⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      exact ⟨0, _, _, rfl, hSet2, rfl, rfl⟩
    · rintro s st ⟨-, k, -, hIndexGet, hLimitGet, -⟩
      exact ⟨decide (UInt64.ofNat k < n), st, by simp [Expr.eval, hIndexGet, hLimitGet]⟩
    · apply Triple.of_forall
      rintro s cur ⟨current, ⟨hFrameCur, k, hk, hIndexGet, hLimitGet, heapK, p, hLiveK, hStateGet⟩,
        rfl, hCondition⟩
      simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
      obtain ⟨hLess, rfl⟩ := hCondition
      rw [ofNat_lt_iff hk] at hLess
      obtain ⟨vals, after, hEval, hRep⟩ :=
        hArgs k p heapK s current hLess hFrameCur hIndexGet hStateGet hLiveK
      have hFrameA := Expr.evalResults_frame [] hEval
      have hLenA : scratch < after.params.length + after.locals.length := by
        rw [hFrameA.params, hFrameA.locals]; exact hFrameLen hFrameCur
      refine Stmt.seq_spec (M := fun s' st' => ∃ heap' q, Live heap0 initial heap' s'
          ((q, (g (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) init k))).map
            Float.toBits) :: temps) ∧
          st' = (after.update next (.i64 q)).update state (.i64 q)) ?_ ?_
      · refine Live.call_seq hImpl hImport hFunc hParams hLiveK hCap hEval hRep
          (by omega) fun heap2 q s2 hLive2 => ?_
        have hPtr2 : (after.update next (.i64 q)).get state = some (.i64 p) := by
          rw [State.get_update_ne hSN, hFrameA.get state hStateB (by simp), hStateGet]
        refine hLive2.releaseSecond_seq hImports hRelease hPtr2 fun s3 hLive3 => ?_
        refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s' st' ⟨rfl, rfl⟩
        refine ⟨q, _, _, Expr.eval_get (State.get_update_same (by omega)),
          State.set?_eq_update _ (by rw [hLen]; omega), _, q, hLive3, rfl⟩
      · apply Triple.of_forall
        rintro s' st' ⟨heap3, q, hLive3, rfl⟩
        refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s'' st ⟨rfl, hst⟩
        have hLen4 : index < st.params.length + st.locals.length := by
          rw [hst, hLen, hLen]; omega
        have hIndex4 : st.get index = some (.i64 (UInt64.ofNat k)) := by
          rw [hst, State.get_update_ne (Ne.symm hSI), State.get_update_ne hIN,
            hFrameA.get index hIndexB (by simp), hIndexGet]
        have hW : ∀ j ∈ [next, state, index], j ∈ [state, size, limit, index, next] := by simp
        have hFrame4 : State.Frame scratch [state, size, limit, index, next] before st := by
          rw [hst]
          exact ((hFrameCur.trans (hFrameA.weaken (by simp))).set?
            (State.set?_eq_update _ (by omega)) (Or.inl (hW next (by simp)))).set?
            (State.set?_eq_update _ (by rw [hLen]; omega)) (Or.inl (hW state (by simp)))
        refine ⟨UInt64.ofNat k + 1, st, st.update index (.i64 (UInt64.ofNat k + 1)),
          by simp [Expr.eval, hIndex4, U64Op.apply], State.set?_eq_update _ hLen4,
          ⟨hFrame4.set? (State.set?_eq_update _ hLen4) (Or.inl (hW index (by simp))),
            k + 1, hLess, ?_, ?_, heap3, q, ?_, ?_⟩, ?_⟩
        · rw [State.get_update_same hLen4]
          congr 2
          apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
          omega
        · rw [State.get_update_ne hLI, hst, State.get_update_ne (Ne.symm hSL),
            State.get_update_ne hLN, hFrameA.get limit hLimitB (by simp), hLimitGet]
        · rw [loopPrefix_succ]
          exact hLive3
        · rw [State.get_update_ne hSI, hst, State.get_update_same (by rw [hLen]; omega)]
        · simp only [measure, State.get_update_same hLen4, hIndexGet, UInt64.toNat_add,
            UInt64.toNat_ofNat', UInt64.reduceToNat]
          rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
    · rintro s st ⟨rfl, rfl⟩
      have hLimit1 : t1.get limit = some (.i64 n) := State.get_set?_same hSet1
      refine ⟨((hFrame1W.trans (hFrameC.weaken (by simp))).set? hSet1
          (Or.inl (by simp))).set? hSet2 (Or.inl (by simp)),
        0, Nat.zero_le _, State.get_set?_same hSet2, ?_, heap1, p1, ?_, ?_⟩
      · rw [State.get_set?_ne hLI hSet2, hLimit1]
      · simpa [loopPrefix, hSize] using hLive1
      · rw [State.get_set?_ne hSI hSet2, State.get_set?_ne hSL hSet1,
          hFrameC.get state hStateB (by simp), hState1]
    · rintro s st ⟨current, ⟨hFrame, k, hk, hIndexGet, hLimitGet, heapK, p, hLiveK, hStateGet⟩,
        hCondition⟩
      simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
      obtain ⟨hNotLess, rfl⟩ := hCondition
      rw [ofNat_lt_iff hk] at hNotLess
      obtain rfl : k = n.toNat := by omega
      exact ⟨heapK, p, hLiveK, hFrame, hStateGet⟩
  · apply Triple.of_forall
    rintro s st ⟨heap', p, hLive', hFrame, hState⟩
    exact hRest heap' p s st hLive' hFrame hState

end Project.IR
