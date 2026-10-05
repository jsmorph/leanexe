import Project.IR.ArrayLoop
import LeanExe.RepeatWhile

/-!
The template of `LeanExe.repeatWhile fuel init cond step`.  The state lives in the locals
`states`, one per component, with an array as its pointer.  While the counter is below the
fuel and `cond` holds, one call of the step function writes the next state into `states`; when
`cond` fails, the counter jumps to the fuel and the loop ends.  The call consumes every array of
the state, so the template itself allocates and releases nothing.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module}

/-- The loop of `LeanExe.repeatWhile`, with the fuel in `limit` and the number of steps in
`counter`. -/
def Stmt.repeatWhile (states : List Nat) (limit counter : Nat) (fuel : Expr .u64)
    (cond : Expr .bool) (idx : Nat) (args : List ((type : ScalarType) × Expr type)) : Stmt :=
  .seq (.assign limit fuel) <|
  .seq (.assign counter (.const 0)) <|
  .while (.ltU (.get counter) (.get limit)) <|
    .ite cond
      (.seq (.call idx args states) (.assign counter (.bin .add (.get counter) (.const 1))))
      (.assign counter (.get limit))

theorem repeatWhile_go_continue {cond : β → Bool} {step : β → β} {k : Nat} {x : β}
    (h : cond x = true) :
    LeanExe.repeatWhile.go cond step (k + 1) x = LeanExe.repeatWhile.go cond step k (step x) := by
  simp [LeanExe.repeatWhile.go, h]

theorem repeatWhile_go_stop {cond : β → Bool} {step : β → β} {x : β} (h : cond x = false) :
    ∀ k, LeanExe.repeatWhile.go cond step k x = x
  | 0 => rfl
  | _ + 1 => by simp [LeanExe.repeatWhile.go, h]

/-- The loop leaves `LeanExe.repeatWhile n x0 cond step` in the state locals, or aborts.  It
starts with the fuel `n` at `fuel`, and with the locals `states` holding `x0`, owned, in a heap
that keeps every region of `heap0` apart from the blocks `gone`.  While `cond` holds, the call of
`idx`, which implements `g`, receives arguments that represent `F x` and consumes only blocks of
the state `x`, and `g (F x)` is `step x`.  The postcondition gives the final state the same
facts. -/
theorem Stmt.repeatWhile_spec [Represent α] [Represent β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams)
    {scratch limit counter : Nat} {states : List Nat}
    (hLocals : (limit :: counter :: states).Nodup)
    (hBelow : ∀ j ∈ limit :: counter :: states, j < scratch)
    {before : State} (hRoom : scratch ≤ before.params.length + before.locals.length)
    {heap0 : Heap} {initial start : Store Unit} {gone : List (Nat × Nat)}
    {fuel : Expr .u64} {n : UInt64}
    (hFuel : ∃ after, fuel.eval start.mem scratch before = some (n, after))
    {condition : Expr .bool} (cond : β → Bool) (step : β → β) (F : β → α)
    (hStep : ∀ x, g (F x) = step x)
    (hWidth : ∀ (heap : Heap) store vals (y : β), Represent.owned heap store vals y →
      vals.length = states.length)
    {x0 : β} {vals0 : List Value}
    (hStart : ∃ heap1 : Heap, heap1.At start ∧ start.memoryCaps = initial.memoryCaps ∧
      Represent.owned heap1 start vals0 x0 ∧
      heap0.Keeps initial gone heap1 start (Represent.blocks start vals0 x0))
    (hHolds0 : before.Holds states vals0) (hCap : initial.memoryCap m 0 ≤ 65535)
    (hCond : ∀ (s : Store Unit) (st : State) (x : β) (vals : List Value) (heap : Heap),
      st.Holds states vals → Represent.owned heap s vals x →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ after, condition.eval s.mem scratch st = some (cond x, after))
    (hArgs : ∀ (s : Store Unit) (st : State) (x : β) (vals : List Value) (heap : Heap),
      st.Holds states vals → heap.At s → s.memoryCaps = initial.memoryCaps →
      Represent.owned heap s vals x →
      heap0.Keeps initial gone heap s (Represent.blocks s vals x) →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ avals after, Expr.evalResults s.mem scratch args st = some (avals, after) ∧
        Represent.borrowed heap s avals (F x) ∧
        Separate s (Represent.moves s avals (F x)) (Represent.reads s avals (F x)) ∧
        ∀ b ∈ (Represent.moves s avals (F x)).map (block s), b ∈ Represent.blocks s vals x) :
    Triple m (.repeatWhile states limit counter fuel condition idx args) scratch
      (fun s st => s = start ∧ st = before)
      (fun s st => ∃ (heap : Heap) (vals : List Value), heap.At s ∧
        s.memoryCaps = initial.memoryCaps ∧
        Represent.owned heap s vals (LeanExe.repeatWhile n x0 cond step) ∧
        heap0.Keeps initial gone heap s
          (Represent.blocks s vals (LeanExe.repeatWhile n x0 cond step)) ∧
        st.Holds states vals ∧ State.Frame scratch (limit :: counter :: states) before st) := by
  obtain ⟨hL, hC, hNodup⟩ : limit ∉ counter :: states ∧ counter ∉ states ∧ states.Nodup := by
    simp only [List.nodup_cons] at hLocals
    exact ⟨hLocals.1, hLocals.2.1, hLocals.2.2⟩
  have hLC : limit ≠ counter := fun h => hL (List.mem_cons.mpr (.inl h))
  have hLS : limit ∉ states := fun h => hL (List.mem_cons_of_mem _ h)
  have hBL := hBelow limit List.mem_cons_self
  have hBC := hBelow counter (List.mem_cons_of_mem _ List.mem_cons_self)
  have hBS : ∀ j ∈ states, j < scratch := fun j hj =>
    hBelow j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj))
  have hIn : ∀ j, j = limit ∨ j = counter ∨ j ∈ states → j ∈ limit :: counter :: states := by
    intro j hj; simp only [List.mem_cons]; tauto
  obtain ⟨a0, hFuelEval⟩ := hFuel
  have hFrameA0 := Expr.eval_frame (limit :: counter :: states) fuel start.mem scratch before a0 _
    hFuelEval
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := a0) (index := limit) (.i64 n)
    (by have := hFrameA0.params; have := hFrameA0.locals; omega)
  have hFrame1 := hFrameA0.set? hSet1 (.inl List.mem_cons_self)
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := counter) (.i64 0)
    (by have := hFrame1.params; have := hFrame1.locals; omega)
  have hFrame2 := hFrame1.set? hSet2 (.inl (List.mem_cons_of_mem _ List.mem_cons_self))
  have hLimit2 : s2.get limit = some (.i64 n) := by
    rw [State.get_set?_ne hLC hSet2, State.get_set?_same hSet1]
  have hCounter2 : s2.get counter = some (.i64 0) := State.get_set?_same hSet2
  have hHolds2 : s2.Holds states vals0 := by
    have hF0 := Expr.eval_frame [limit, counter] fuel start.mem scratch before a0 _ hFuelEval
    have hF2 := (hF0.set? hSet1 (.inl (by simp))).set? hSet2 (.inl (by simp))
    exact hHolds0.frame hF2 fun j hj => ⟨hBS j hj, by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hLS (h ▸ hj), fun h => hC (h ▸ hj)⟩⟩
  refine Stmt.seq_spec (M := fun s st => s = start ∧ st = s1) ?_ <|
    Stmt.seq_spec (M := fun s st => s = start ∧ st = s2) ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    exact ⟨n, a0, s1, hFuelEval, hSet1, rfl, rfl⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    exact ⟨0, s1, s2, rfl, hSet2, rfl, rfl⟩
  have hN : ∀ j, j ≤ n.toNat → (UInt64.ofNat j).toNat = j := fun j hj =>
    UInt64.toNat_ofNat_of_lt' (by have := n.toNat_lt; simp [UInt64.size] at this ⊢; omega)
  let final := LeanExe.repeatWhile n x0 cond step
  let Inv : Store Unit → State → Prop := fun s st =>
    ∃ (j : Nat) (x : β) (vals : List Value) (heap : Heap), j ≤ n.toNat ∧
      LeanExe.repeatWhile.go cond step (n.toNat - j) x = final ∧
      heap.At s ∧ s.memoryCaps = initial.memoryCaps ∧ Represent.owned heap s vals x ∧
      heap0.Keeps initial gone heap s (Represent.blocks s vals x) ∧
      st.Holds states vals ∧ State.Frame scratch (limit :: counter :: states) before st ∧
      st.get limit = some (.i64 n) ∧ st.get counter = some (.i64 (UInt64.ofNat j))
  let measure : Store Unit → State → Nat := fun _ st =>
    match st.get counter with
    | some (.i64 c) => n.toNat - c.toNat
    | _ => 0
  refine (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · rintro s st ⟨j, -, -, -, -, -, -, -, -, -, -, -, hLimitGet, hCounterGet⟩
    exact ⟨decide (UInt64.ofNat j < n), st, by simp [Expr.eval, hLimitGet, hCounterGet]⟩
  · apply Triple.of_forall
    rintro s st ⟨cur, ⟨j, x, vals, heap, hj, hGo, hAt, hCaps, hOwned, hKeeps, hHolds, hFrame,
      hLimitGet, hCounterGet⟩, hMeasure, hCondition⟩
    simp only [Expr.eval, hLimitGet, hCounterGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hj] at hLess
    have hBound : bound = n.toNat - j := by
      rw [← hMeasure]; simp only [measure, hCounterGet, hN j hj]
    obtain ⟨c1, hCondEval⟩ := hCond s cur x vals heap hHolds hOwned hFrame
    have hFrameC := Expr.eval_frame [] condition s.mem scratch cur c1 _ hCondEval
    have hKeepC : ∀ i, i < scratch → c1.get i = cur.get i := fun i hi => hFrameC.get i hi (by simp)
    have hFrameBC : State.Frame scratch (limit :: counter :: states) before c1 :=
      hFrame.trans (hFrameC.weaken fun _ h => nomatch h)
    have hHoldsC : c1.Holds states vals := hHolds.frame hFrameC fun j hj => ⟨hBS j hj, by simp⟩
    refine (Stmt.ite_spec
      (PThen := fun s' st' => s' = s ∧ st' = c1 ∧ cond x = true)
      (PElse := fun s' st' => s' = s ∧ st' = c1 ∧ cond x = false) ?_ ?_).mono ?_
        fun _ _ h => h
    · apply Triple.of_forall
      rintro s' st' ⟨hs', hst', hTrue⟩
      subst s' st'
      obtain ⟨avals, after, hEval, hBorrowed, hSep, hMovesIn⟩ :=
        hArgs s c1 x vals heap hHoldsC hAt hCaps hOwned hKeeps hFrameBC
      have hFrameE := Expr.evalResults_frame [] hEval
      refine Stmt.seq_spec (Stmt.callImplements_spec (results := states) hImpl hImport hFunc
        hParams hEval hAt hBorrowed hSep (memoryCap_le_of_caps hCaps hCap)
        fun heap' store values hOwned' => ?_) ?_
      · refine State.setAll_exists (by simp [hWidth _ _ _ _ hOwned']) fun r hr => ?_
        have := hBS r (List.mem_reverse.mp hr)
        rw [hFrameE.params, hFrameE.locals, hFrameC.params, hFrameC.locals, hFrameBC.params.symm,
          hFrameBC.locals.symm] at *
        rw [← hFrameC.params, ← hFrameC.locals]
        omega
      apply Triple.of_forall
      rintro s'' st'' ⟨heap', values, hAt', hOwned', hCaps', hKeeps', hSetAll⟩
      have hFrameS := (hFrameE.weaken (writes' := states) fun _ h => nomatch h).setAll
        (fun r hr => .inl (List.mem_reverse.mp hr)) hSetAll
      have hHoldsS : st''.Holds states values :=
        State.Holds.reverse (State.setAll_holds (List.nodup_reverse.mpr hNodup) hSetAll)
      have hCounterS : st''.get counter = some (.i64 (UInt64.ofNat j)) := by
        rw [hFrameS.get counter hBC hC, hKeepC counter hBC, hCounterGet]
      have hLimitS : st''.get limit = some (.i64 n) := by
        rw [hFrameS.get limit hBL hLS, hKeepC limit hBL, hLimitGet]
      obtain ⟨st3, hSet3⟩ := State.exists_set? (state := st'') (index := counter)
        (.i64 (UInt64.ofNat j + 1))
        (by have := hFrameS.params; have := hFrameS.locals; have := hFrameE.params;
            have := hFrameE.locals; have := hFrameBC.params; have := hFrameBC.locals; omega)
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s3 st ⟨hs3, hst⟩
      subst s3 st
      refine ⟨UInt64.ofNat j + 1, st'', st3,
        by simp [Expr.eval, hCounterS, U64Op.apply], hSet3,
        ⟨j + 1, step x, values, heap', by omega, ?_, hAt', hCaps'.trans hCaps,
          by rw [← hStep]; exact hOwned', ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [← hGo, show n.toNat - j = (n.toNat - (j + 1)) + 1 by omega,
          repeatWhile_go_continue hTrue]
      · rw [← hStep]
        refine hKeeps.trans hKeeps' fun r _ hFresh b hb => ?_
        exact hFresh b (hMovesIn b hb)
      · exact hHoldsS.frame (((State.Frame.refl _ _ _).set? hSet3
          (.inl List.mem_cons_self)).weaken (writes' := [counter]) fun _ h => h)
          fun r hr => ⟨hBS r hr, by simp only [List.mem_singleton]; exact fun h => hC (h ▸ hr)⟩
      · exact ((hFrameBC.trans (hFrameE.weaken fun _ h => nomatch h)).trans
          ((State.Frame.refl _ _ _).setAll (fun r hr => .inl (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_reverse.mp hr)))) hSetAll)).set? hSet3
            (.inl (List.mem_cons_of_mem _ List.mem_cons_self))
      · rw [State.get_set?_ne hLC hSet3, hLimitS]
      · rw [State.get_set?_same hSet3]
        congr 2
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        have := n.toNat_lt
        omega
      · simp only [measure, State.get_set?_same hSet3, UInt64.toNat_add, UInt64.toNat_ofNat',
          UInt64.reduceToNat]
        have := n.toNat_lt
        rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    · apply Triple.of_forall
      rintro s' st' ⟨hs', hst', hFalse⟩
      subst s' st'
      obtain ⟨st3, hSet3⟩ := State.exists_set? (state := c1) (index := counter) (.i64 n)
        (by have := hFrameBC.params; have := hFrameBC.locals; omega)
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s3 st ⟨hs3, hst⟩
      subst s3 st
      have hStop := repeatWhile_go_stop (step := step) hFalse
      rw [hStop] at hGo
      refine ⟨n, c1, st3, by simp [Expr.eval, hKeepC limit hBL, hLimitGet], hSet3,
        ⟨n.toNat, x, vals, heap, le_rfl, by rw [hStop]; exact hGo, hAt, hCaps, hOwned, hKeeps,
          ?_, hFrameBC.set? hSet3 (.inl (List.mem_cons_of_mem _ List.mem_cons_self)),
          by rw [State.get_set?_ne hLC hSet3, hKeepC limit hBL, hLimitGet],
          by rw [State.get_set?_same hSet3, UInt64.ofNat_toNat]⟩, ?_⟩
      · exact hHoldsC.frame (((State.Frame.refl _ _ _).set? hSet3
          (.inl List.mem_cons_self)).weaken (writes' := [counter]) fun _ h => h)
          fun r hr => ⟨hBS r hr, by simp only [List.mem_singleton]; exact fun h => hC (h ▸ hr)⟩
      · simp only [measure, State.get_set?_same hSet3]
        omega
    · rintro s' st' ⟨rfl, rfl⟩
      exact ⟨cond x, c1, hCondEval, by cases cond x <;> simp⟩
  · rintro s st ⟨rfl, rfl⟩
    obtain ⟨heap1, hAt1, hCaps1, hOwned1, hKeeps1⟩ := hStart
    exact ⟨0, x0, vals0, heap1, Nat.zero_le _, by simp [final, LeanExe.repeatWhile], hAt1,
      hCaps1, hOwned1, hKeeps1, hHolds2, hFrame2, hLimit2, hCounter2⟩
  · rintro s st ⟨cur, ⟨j, x, vals, heap, hj, hGo, hAt, hCaps, hOwned, hKeeps, hHolds, hFrame,
      hLimitGet, hCounterGet⟩, hCondition⟩
    simp only [Expr.eval, hLimitGet, hCounterGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hj] at hNotLess
    obtain rfl : j = n.toNat := by omega
    rw [Nat.sub_self] at hGo
    simp only [LeanExe.repeatWhile.go] at hGo
    subst hGo
    exact ⟨heap, vals, hAt, hCaps, hOwned, hKeeps, hHolds, hFrame⟩

/-- The loop of `LeanExe.repeatWhile` over a state of scalars, with a pure step: it keeps the
store and leaves `LeanExe.repeatWhile n x0 cond step` in the state locals.  While `cond` holds,
the call of `idx`, which computes `g` on scalars, receives the values of `F x`, and `g (F x)` is
`step x`. -/
theorem Stmt.repeatWhile_pure_spec [Scalar α] [Scalar β] {idx : Nat} {g : α → β}
    (hImpl : ImplementsPure m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams)
    {scratch limit counter : Nat} {states : List Nat}
    (hLocals : (limit :: counter :: states).Nodup)
    (hBelow : ∀ j ∈ limit :: counter :: states, j < scratch)
    {before : State} (hRoom : scratch ≤ before.params.length + before.locals.length)
    {initial : Store Unit} {fuel : Expr .u64} {n : UInt64}
    (hFuel : ∃ after, fuel.eval initial.mem scratch before = some (n, after))
    {condition : Expr .bool} (cond : β → Bool) (step : β → β) (F : β → α)
    (hStep : ∀ x, g (F x) = step x)
    (hWidth : ∀ y : β, (Scalar.values y).length = states.length)
    {x0 : β} (hHolds0 : before.Holds states (Scalar.values x0))
    (hCond : ∀ (st : State) (x : β), st.Holds states (Scalar.values x) →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ after, condition.eval initial.mem scratch st = some (cond x, after))
    (hArgs : ∀ (st : State) (x : β), st.Holds states (Scalar.values x) →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ after, Expr.evalResults initial.mem scratch args st = some (Scalar.values (F x), after)) :
    Triple m (.repeatWhile states limit counter fuel condition idx args) scratch
      (fun s st => s = initial ∧ st = before)
      (fun s st => s = initial ∧
        st.Holds states (Scalar.values (LeanExe.repeatWhile n x0 cond step)) ∧
        State.Frame scratch (limit :: counter :: states) before st) := by
  obtain ⟨hL, hC, hNodup⟩ : limit ∉ counter :: states ∧ counter ∉ states ∧ states.Nodup := by
    simp only [List.nodup_cons] at hLocals
    exact ⟨hLocals.1, hLocals.2.1, hLocals.2.2⟩
  have hLC : limit ≠ counter := fun h => hL (List.mem_cons.mpr (.inl h))
  have hLS : limit ∉ states := fun h => hL (List.mem_cons_of_mem _ h)
  have hBL := hBelow limit List.mem_cons_self
  have hBC := hBelow counter (List.mem_cons_of_mem _ List.mem_cons_self)
  have hBS : ∀ j ∈ states, j < scratch := fun j hj =>
    hBelow j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj))
  obtain ⟨a0, hFuelEval⟩ := hFuel
  have hFrameA0 := Expr.eval_frame (limit :: counter :: states) fuel initial.mem scratch before a0 _
    hFuelEval
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := a0) (index := limit) (.i64 n)
    (by have := hFrameA0.params; have := hFrameA0.locals; omega)
  have hFrame1 := hFrameA0.set? hSet1 (.inl List.mem_cons_self)
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := counter) (.i64 0)
    (by have := hFrame1.params; have := hFrame1.locals; omega)
  have hFrame2 := hFrame1.set? hSet2 (.inl (List.mem_cons_of_mem _ List.mem_cons_self))
  have hLimit2 : s2.get limit = some (.i64 n) := by
    rw [State.get_set?_ne hLC hSet2, State.get_set?_same hSet1]
  have hCounter2 : s2.get counter = some (.i64 0) := State.get_set?_same hSet2
  have hHolds2 : s2.Holds states (Scalar.values x0) := by
    have hF0 := Expr.eval_frame [limit, counter] fuel initial.mem scratch before a0 _ hFuelEval
    have hF2 := (hF0.set? hSet1 (.inl (by simp))).set? hSet2 (.inl (by simp))
    exact hHolds0.frame hF2 fun j hj => ⟨hBS j hj, by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hLS (h ▸ hj), fun h => hC (h ▸ hj)⟩⟩
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
    Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    exact ⟨n, a0, s1, hFuelEval, hSet1, rfl, rfl⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, hst⟩
    subst s st
    exact ⟨0, s1, s2, rfl, hSet2, rfl, rfl⟩
  have hN : ∀ j, j ≤ n.toNat → (UInt64.ofNat j).toNat = j := fun j hj =>
    UInt64.toNat_ofNat_of_lt' (by have := n.toNat_lt; simp [UInt64.size] at this ⊢; omega)
  let final := LeanExe.repeatWhile n x0 cond step
  let Inv : Store Unit → State → Prop := fun s st =>
    ∃ (j : Nat) (x : β), j ≤ n.toNat ∧
      LeanExe.repeatWhile.go cond step (n.toNat - j) x = final ∧ s = initial ∧
      st.Holds states (Scalar.values x) ∧ State.Frame scratch (limit :: counter :: states) before st ∧
      st.get limit = some (.i64 n) ∧ st.get counter = some (.i64 (UInt64.ofNat j))
  let measure : Store Unit → State → Nat := fun _ st =>
    match st.get counter with
    | some (.i64 c) => n.toNat - c.toNat
    | _ => 0
  refine (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · rintro s st ⟨j, -, -, -, -, -, -, hLimitGet, hCounterGet⟩
    exact ⟨decide (UInt64.ofNat j < n), st, by simp [Expr.eval, hLimitGet, hCounterGet]⟩
  · apply Triple.of_forall
    rintro s st ⟨cur, ⟨j, x, hj, hGo, hs, hHolds, hFrame, hLimitGet, hCounterGet⟩, hMeasure,
      hCondition⟩
    simp only [Expr.eval, hLimitGet, hCounterGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hj] at hLess
    have hBound : bound = n.toNat - j := by
      rw [← hMeasure]; simp only [measure, hCounterGet, hN j hj]
    obtain ⟨c1, hCondEval⟩ := hCond cur x hHolds hFrame
    have hFrameC := Expr.eval_frame [] condition initial.mem scratch cur c1 _ hCondEval
    have hKeepC : ∀ i, i < scratch → c1.get i = cur.get i := fun i hi => hFrameC.get i hi (by simp)
    have hFrameBC : State.Frame scratch (limit :: counter :: states) before c1 :=
      hFrame.trans (hFrameC.weaken fun _ h => nomatch h)
    have hHoldsC : c1.Holds states (Scalar.values x) :=
      hHolds.frame hFrameC fun j hj => ⟨hBS j hj, by simp⟩
    refine (Stmt.ite_spec
      (PThen := fun s' st' => s' = initial ∧ st' = c1 ∧ cond x = true)
      (PElse := fun s' st' => s' = initial ∧ st' = c1 ∧ cond x = false) ?_ ?_).mono ?_
        fun _ _ h => h
    · apply Triple.of_forall
      rintro s' st' ⟨hs', hst', hTrue⟩
      subst s' st'
      obtain ⟨after, hEval⟩ := hArgs c1 x hHoldsC hFrameBC
      have hFrameE := Expr.evalResults_frame [] hEval
      obtain ⟨next, hSetAll⟩ := State.setAll_exists (state := after) (indices := states.reverse)
        (values := (Scalar.values (g (F x))).reverse) (by simp [hWidth]) fun r hr => by
          have := hBS r (List.mem_reverse.mp hr)
          rw [hFrameE.params, hFrameE.locals, hFrameC.params, hFrameC.locals,
            hFrameBC.params.symm, hFrameBC.locals.symm] at *
          rw [← hFrameC.params, ← hFrameC.locals]
          omega
      refine Stmt.seq_spec (Stmt.callPure_spec hImpl hImport hFunc hParams hEval hSetAll) ?_
      apply Triple.of_forall
      rintro s'' st'' ⟨hs'', hst''⟩
      subst s'' st''
      have hFrameS := (hFrameE.weaken (writes' := states) fun _ h => nomatch h).setAll
        (fun r hr => .inl (List.mem_reverse.mp hr)) hSetAll
      have hHoldsS : next.Holds states (Scalar.values (g (F x))) :=
        State.Holds.reverse (State.setAll_holds (List.nodup_reverse.mpr hNodup) hSetAll)
      have hCounterS : next.get counter = some (.i64 (UInt64.ofNat j)) := by
        rw [hFrameS.get counter hBC hC, hKeepC counter hBC, hCounterGet]
      have hLimitS : next.get limit = some (.i64 n) := by
        rw [hFrameS.get limit hBL hLS, hKeepC limit hBL, hLimitGet]
      obtain ⟨st3, hSet3⟩ := State.exists_set? (state := next) (index := counter)
        (.i64 (UInt64.ofNat j + 1))
        (by have := hFrameS.params; have := hFrameS.locals; have := hFrameE.params;
            have := hFrameE.locals; have := hFrameBC.params; have := hFrameBC.locals; omega)
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s3 st ⟨hs3, hst⟩
      subst s3 st
      refine ⟨UInt64.ofNat j + 1, next, st3,
        by simp [Expr.eval, hCounterS, U64Op.apply], hSet3,
        ⟨j + 1, step x, by omega, ?_, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [← hGo, show n.toNat - j = (n.toNat - (j + 1)) + 1 by omega,
          repeatWhile_go_continue hTrue]
      · rw [← hStep]
        exact hHoldsS.frame (((State.Frame.refl _ _ _).set? hSet3
          (.inl List.mem_cons_self)).weaken (writes' := [counter]) fun _ h => h)
          fun r hr => ⟨hBS r hr, by simp only [List.mem_singleton]; exact fun h => hC (h ▸ hr)⟩
      · exact ((hFrameBC.trans (hFrameE.weaken fun _ h => nomatch h)).trans
          ((State.Frame.refl _ _ _).setAll (fun r hr => .inl (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_reverse.mp hr)))) hSetAll)).set? hSet3
            (.inl (List.mem_cons_of_mem _ List.mem_cons_self))
      · rw [State.get_set?_ne hLC hSet3, hLimitS]
      · rw [State.get_set?_same hSet3]
        congr 2
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        have := n.toNat_lt
        omega
      · simp only [measure, State.get_set?_same hSet3, UInt64.toNat_add, UInt64.toNat_ofNat',
          UInt64.reduceToNat]
        have := n.toNat_lt
        rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    · apply Triple.of_forall
      rintro s' st' ⟨hs', hst', hFalse⟩
      subst s' st'
      obtain ⟨st3, hSet3⟩ := State.exists_set? (state := c1) (index := counter) (.i64 n)
        (by have := hFrameBC.params; have := hFrameBC.locals; omega)
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s3 st ⟨hs3, hst⟩
      subst s3 st
      have hStop := repeatWhile_go_stop (step := step) hFalse
      rw [hStop] at hGo
      refine ⟨n, c1, st3, by simp [Expr.eval, hKeepC limit hBL, hLimitGet], hSet3,
        ⟨n.toNat, x, le_rfl, by rw [hStop]; exact hGo, rfl, ?_,
          hFrameBC.set? hSet3 (.inl (List.mem_cons_of_mem _ List.mem_cons_self)),
          by rw [State.get_set?_ne hLC hSet3, hKeepC limit hBL, hLimitGet],
          by rw [State.get_set?_same hSet3, UInt64.ofNat_toNat]⟩, ?_⟩
      · exact hHoldsC.frame (((State.Frame.refl _ _ _).set? hSet3
          (.inl List.mem_cons_self)).weaken (writes' := [counter]) fun _ h => h)
          fun r hr => ⟨hBS r hr, by simp only [List.mem_singleton]; exact fun h => hC (h ▸ hr)⟩
      · simp only [measure, State.get_set?_same hSet3]
        omega
    · rintro s' st' ⟨rfl, rfl⟩
      exact ⟨cond x, c1, hs ▸ hCondEval, by cases cond x <;> simp [hs]⟩
  · rintro s st ⟨rfl, rfl⟩
    exact ⟨0, x0, Nat.zero_le _, by simp [final, LeanExe.repeatWhile], rfl, hHolds2, hFrame2,
      hLimit2, hCounter2⟩
  · rintro s st ⟨cur, ⟨j, x, hj, hGo, hs, hHolds, hFrame, hLimitGet, hCounterGet⟩, hCondition⟩
    simp only [Expr.eval, hLimitGet, hCounterGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hj] at hNotLess
    obtain rfl : j = n.toNat := by omega
    rw [Nat.sub_self] at hGo
    simp only [LeanExe.repeatWhile.go] at hGo
    subst hGo
    exact ⟨hs, hHolds, hFrame⟩

end Project.IR
