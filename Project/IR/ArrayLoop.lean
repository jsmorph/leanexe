import Project.IR.Tuple
import Project.IR.Loop
import Project.IR.Build

/-!
The rule lemmas for the compiler's loops over array states.  The compiler translates
`LeanExe.loop n init f`, where `init` is an `Array Float` variable and `f l x` is one call
of a compiled function, to a copy of `init` into the state local and `Stmt.loop`, whose
body calls the function, releases the previous state, and moves the call's result into the
state local.  It translates a loop over a nest of arrays that the called function consumes,
started from owned arrays, to `Stmt.tupleLoop`, whose body is the call alone.
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
    (hLive : Live heap0 initial moved heap store temps)
    (hNew : heap.NewArray store heap' store' ptr ws) :
    Live heap0 initial moved heap' store' ((ptr, ws) :: temps) :=
  Live.step (consumed := []) (news := [(ptr, ws)]) hLive hNew.at_ hNew.caps
    (hNew.keeps.mono (fun _ hb => nomatch hb) fun _ hb => hb)
    (fun t ht => by rw [List.mem_singleton.mp ht]; exact hNew.owned) (List.pairwise_singleton _ _)

/-- A copy of an array adds the copy to the live temporaries. -/
theorem Live.copy {typeIdx scratch src size dst limit index : Nat} (hMemory32 : m.memIs64 = false)
    (hImports : m.imports = []) (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (hLocals : [size, dst, limit, index].Nodup)
    (hBelow : ∀ j ∈ [size, dst, limit, index], j < scratch)
    (hSrc : src ∉ [size, dst, limit, index]) (hSrcBelow : src < scratch) {before : State}
    (hRoom : scratch < before.params.length + before.locals.length) {heap0 heap : Heap}
    {initial store : Store Unit} {temps : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {ptr : UInt64} {xs : Array UInt64}
    (hPtr : before.get src = some (.i64 ptr)) (hArray : heap.Borrowed store ptr xs) :
    Triple m (.copy dst limit index size src) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' p, Live heap0 initial moved heap' s
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
    (hLive : Live heap0 initial moved heap store temps) (hCap : initial.memoryCap m 0 ≤ 65535)
    {ptr : UInt64} {init : Array Float} (hPtr : before.get src = some (.i64 ptr))
    (hInit : heap.Borrowed store ptr (init.map Float.toBits))
    {count : Expr .u64} {n : UInt64}
    (hCount : ∀ mem st, State.Frame scratch [state, size, limit, index, next] before st →
      ∃ after, count.eval mem scratch st = some (n, after))
    (F : UInt64 → Array Float → α)
    (hArgs : ∀ (k : Nat) (p : UInt64) (heap' : Heap) (store' : Store Unit) (st : State),
      k < n.toNat → State.Frame scratch [state, size, limit, index, next] before st →
      st.get index = some (.i64 (UInt64.ofNat k)) → st.get state = some (.i64 p) →
      Live heap0 initial moved heap' store'
        ((p, (loopPrefix (fun l x => g (F l x)) init k).map Float.toBits) :: temps) →
      ∃ vals after, Expr.evalResults store'.mem scratch args st = some (vals, after) ∧
        Represent.borrowed heap' store' vals
          (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) init k)))
    {rest : Stmt} {Q : Store Unit → State → Prop}
    (hRest : ∀ heap' p s st,
      Live heap0 initial moved heap' s
        ((p, (LeanExe.loop n init fun l x => g (F l x)).map Float.toBits) :: temps) →
      State.Frame scratch [state, size, limit, index, next] before st →
      st.get state = some (.i64 p) →
      Triple m rest scratch (fun s' st' => s' = s ∧ st' = st) Q)
    (hNoMoves : ∀ (s : Store Unit) (vs : List Value) (y : α), Represent.moves s vs y = [] := by
      intro _ _ _; rfl) :
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
        ∃ heap' p, Live heap0 initial moved heap' s
          ((p, (loopPrefix (fun l x => g (F l x)) init k).map Float.toBits) :: temps) ∧
          st.get state = some (.i64 p)
  let measure : Store Unit → State → Nat := fun _ st =>
    match st.get index with
    | some (.i64 k) => n.toNat - k.toNat
    | _ => 0
  refine Stmt.seq_spec (M := fun s st => ∃ heap' p,
      Live heap0 initial moved heap' s
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
      refine Stmt.seq_spec (M := fun s' st' => ∃ heap' q, Live heap0 initial moved heap' s'
          ((q, (g (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) init k))).map
            Float.toBits) :: temps) ∧
          st' = (after.update next (.i64 q)).update state (.i64 q)) ?_ ?_
      · refine Live.call_seq hImpl hImport hFunc hParams hLiveK hCap hEval hRep
          (by omega) (hNoMoves := hNoMoves) fun heap2 q s2 hLive2 => ?_
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

/-- The assignments of the locals `srcs` to the locals `states`, in order, before `next`. -/
def Stmt.copies (states srcs : List Nat) (next : Stmt) : Stmt :=
  (states.zip srcs).foldr (fun c rest => .seq (.assign c.1 (.get c.2)) rest) next

/-- The loop over a nest of arrays that the callee consumes: the locals `states` receive the
arrays at the locals `srcs`, and for each index below `count` a call of function `idx`
consumes the arrays and leaves the next ones in `states`. -/
def Stmt.tupleLoop (states : List Nat) (limit index : Nat) (srcs : List Nat) (idx : Nat)
    (count : Expr .u64) (args : List ((type : ScalarType) × Expr type)) : Stmt :=
  Stmt.copies states srcs (.loop limit index count (.call idx args states))

/-- The copies leave the words at `srcs` in the distinct locals `states`, which `srcs`
avoids, and `next` runs from there. -/
theorem Stmt.copies_spec {scratch : Nat} {next : Stmt} {initial : Store Unit}
    {Q : Store Unit → State → Prop} :
    ∀ {states srcs : List Nat} {ps : List UInt64} {before : State},
      states.Nodup → (∀ j ∈ srcs, j ∉ states) → (∀ j ∈ states, j < scratch) →
      scratch ≤ before.params.length + before.locals.length →
      before.Holds srcs (ps.map .i64) → states.length = srcs.length →
      (∀ b, State.Frame scratch states before b → b.Holds states (ps.map .i64) →
        Triple m next scratch (fun s st => s = initial ∧ st = b) Q) →
      Triple m (Stmt.copies states srcs next) scratch (fun s st => s = initial ∧ st = before) Q
  | [], [], [], before, _, _, _, _, _, _, hNext => hNext before (.refl _ _ _) .nil
  | s :: states, src :: srcs, p :: ps, before, hNodup, hFresh, hBelow, hRoom, hHolds, hLength,
      hNext => by
      have hSrc : before.get src = some (.i64 p) := (List.forall₂_cons.mp hHolds).1
      have hS : s < before.params.length + before.locals.length := by
        have := hBelow s List.mem_cons_self; omega
      have hSrcs : s ∉ srcs := fun h => hFresh s (List.mem_cons_of_mem _ h) List.mem_cons_self
      have hOut : s ∉ states := (List.nodup_cons.mp hNodup).1
      have hRoom1 : scratch ≤ (before.update s (.i64 p)).params.length +
          (before.update s (.i64 p)).locals.length := by
        simp only [State.update_params_length, State.update_locals_length]; exact hRoom
      refine Stmt.seq_spec (Stmt.run_spec (final := before.update s (.i64 p))
        (by simp [Stmt.run, Expr.eval, hSrc, State.set?_eq_update _ hS])) ?_
      refine Stmt.copies_spec (List.nodup_cons.mp hNodup).2
        (fun j hj hjs => hFresh j (List.mem_cons_of_mem _ hj) (List.mem_cons_of_mem _ hjs))
        (fun j hj => hBelow j (List.mem_cons_of_mem _ hj)) hRoom1
        (State.Holds.set? (State.set?_eq_update _ hS) hSrcs (List.forall₂_cons.mp hHolds).2)
        (by simpa using hLength) fun b hFrame hHoldsB => hNext b ?_ (.cons ?_ hHoldsB)
      · exact ((State.Frame.refl _ _ _).update (Or.inl List.mem_cons_self)).trans
          (hFrame.weaken fun j hj => List.mem_cons_of_mem _ hj)
      · rw [hFrame.get s (hBelow s List.mem_cons_self) hOut]
        exact State.get_update_same hS
  | [], _ :: _, _, _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, _, h, _ => by simp at h
  | _, [], _ :: _, _, _, _, _, _, h, _, _ => nomatch h
  | _, _ :: _, [], _, _, _, _, _, h, _, _ => nomatch h

/-- The tuple loop leaves `LeanExe.loop n x0 fun l x => g (F l x)` in new temporaries at the
head of the list, in place of the arrays of `x0`, or aborts.  The call of `idx`, which
implements `g`, must receive arguments that represent `F l x` at index `l` and state `x`,
consume exactly the state's arrays, and read only arrays apart from them. -/
theorem Live.tupleLoop [Represent α] [Represent β] [Arrays β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams)
    {moved : List UInt64} {scratch limit index : Nat} {states srcs : List Nat}
    (hLocals : (limit :: index :: states).Nodup)
    (hBelow : ∀ j ∈ limit :: index :: states, j < scratch)
    (hSrcs : ∀ j ∈ srcs, j ∉ states) (hLength : states.length = srcs.length)
    {before : State} (hRoom : scratch ≤ before.params.length + before.locals.length)
    {heap0 heap : Heap} {initial store : Store Unit} {ts rest : List (UInt64 × Array UInt64)}
    {x0 : β} (hTs : ts.map (·.2) = Arrays.arrays x0)
    (hLive : Live heap0 initial moved heap store (ts ++ rest))
    (hCap : initial.memoryCap m 0 ≤ 65535) (hSrcValues : before.Holds srcs (pointers ts))
    {count : Expr .u64} {n : UInt64}
    (hCount : ∀ mem st, State.Frame scratch states before st →
      ∃ after, count.eval mem scratch st = some (n, after))
    (F : UInt64 → β → α)
    (hArgs : ∀ (k : Nat) (us : List (UInt64 × Array UInt64)) (heap' : Heap)
        (store' : Store Unit) (st : State),
      k < n.toNat → State.Frame scratch (limit :: index :: states) before st →
      st.get index = some (.i64 (UInt64.ofNat k)) → st.Holds states (pointers us) →
      us.map (·.2) = Arrays.arrays (loopPrefix (fun l x => g (F l x)) x0 k) →
      Live heap0 initial moved heap' store' (us ++ rest) →
      ∃ vals after, Expr.evalResults store'.mem scratch args st = some (vals, after) ∧
        Represent.borrowed heap' store' vals
          (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) x0 k)) ∧
        Represent.moves store' vals (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) x0 k)) =
          us.map (·.1) ∧
        ∀ q ∈ Represent.reads vals (F (UInt64.ofNat k) (loopPrefix (fun l x => g (F l x)) x0 k)),
          ∀ t ∈ us, regionsDisjoint q (block store' t.1)) :
    Triple m (.tupleLoop states limit index srcs idx count args) scratch
      (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' us,
        us.map (·.2) = Arrays.arrays (LeanExe.loop n x0 fun l x => g (F l x)) ∧
        Live heap0 initial moved heap' s (us ++ rest) ∧
        State.Frame scratch (limit :: index :: states) before st ∧
        st.Holds states (pointers us)) := by
  obtain ⟨hL, hI, hNodup⟩ : limit ∉ index :: states ∧ index ∉ states ∧ states.Nodup := by
    simp only [List.nodup_cons] at hLocals
    exact ⟨hLocals.1, hLocals.2.1, hLocals.2.2⟩
  have hBL := hBelow limit List.mem_cons_self
  have hBI := hBelow index (List.mem_cons_of_mem _ List.mem_cons_self)
  have hBS : ∀ j ∈ states, j < scratch := fun j hj =>
    hBelow j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj))
  have hSize : states.length = Arrays.size β := by
    rw [hLength, hSrcValues.length_eq, List.length_map, ← Arrays.length_arrays x0, ← hTs,
      List.length_map]
  have hSrcWords : before.Holds srcs ((ts.map (·.1)).map .i64) := by
    rw [List.map_map]; exact hSrcValues
  refine Stmt.copies_spec hNodup hSrcs hBS hRoom hSrcWords hLength fun b hFrameB hHoldsB => ?_
  rw [List.map_map] at hHoldsB
  have hRoomB : scratch ≤ b.params.length + b.locals.length := by
    rw [hFrameB.params, hFrameB.locals]; exact hRoom
  have hFrameAll : ∀ st, State.Frame scratch (limit :: index :: states) b st →
      State.Frame scratch (limit :: index :: states) before st := fun st h =>
    (hFrameB.weaken fun j hj => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)).trans h
  refine (Stmt.loop_inv (vars := states) (writes := states) (vals0 := pointers ts)
    (fun k s vals => ∃ heap' us, vals = pointers us ∧
      us.map (·.2) = Arrays.arrays (loopPrefix (fun l x => g (F l x)) x0 k) ∧
      Live heap0 initial moved heap' s (us ++ rest))
    (fun h => hL (List.mem_cons.mpr (.inl h))) hBL hBI
    ⟨fun h => hL (List.mem_cons_of_mem _ h), hI⟩ (fun j hj => ⟨hj, hBS j hj⟩) hRoomB
    (hCount store.mem b hFrameB) hHoldsB ⟨heap, ts, rfl, hTs, hLive⟩ ?_).mono
      (fun _ _ h => h) ?_
  · rintro k s vals st hk ⟨heap', us, rfl, hUs, hLiveK⟩ hFrame hHolds hIndexGet -
    obtain ⟨vals, after, hEval, hBorrowed, hMoves, hReads⟩ :=
      hArgs k us heap' s st hk (hFrameAll st hFrame) hIndexGet hHolds hUs hLiveK
    have hFrameAfter := Expr.evalResults_frame states hEval
    have hLen : scratch ≤ after.params.length + after.locals.length := by
      rw [hFrameAfter.params, hFrameAfter.locals, hFrame.params, hFrame.locals]; exact hRoomB
    refine (Live.callTuple hImpl hImport hFunc (results := states) hParams hLiveK hCap hEval
      hBorrowed hMoves hReads hSize fun r hr => by have := hBS r hr; omega).mono
        (fun _ _ h => h) ?_
    rintro s' st' ⟨heap'', us', hUs', hLive', hSet⟩
    refine ⟨hFrameAfter.setAll (fun j hj => .inl (List.mem_reverse.mp hj)) hSet, pointers us',
      State.Holds.reverse (State.setAll_holds (List.nodup_reverse.mpr hNodup) hSet), heap'', us',
      rfl, ?_, hLive'⟩
    rw [loopPrefix_succ]
    exact hUs'
  · rintro s st ⟨hFrame, vals, hHolds, heap', us, rfl, hUs, hLiveN⟩
    exact ⟨heap', us, hUs, hLiveN, hFrameAll st hFrame, hHolds⟩

end Project.IR
