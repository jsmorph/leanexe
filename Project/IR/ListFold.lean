import Project.IR.Stmt
import Project.Pipeline.Records

/-!
The rule lemma for the compiler's list fold template.  The compiler translates
`xs.foldl g init`, for a `List UInt64` in local `list`, to an assignment of `init` to an
accumulator followed by `Stmt.listFold`, which follows the tail pointers from the head and,
for each element, assigns the value of `g`'s body to the accumulator.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline

variable {m : Module}

/-- Local `cursor` starts at the list at local `list`.  While it is not null, local
`element` receives the word in its first slot, local `acc` the value of `body`, and `cursor`
the pointer in its second slot. -/
def Stmt.listFold (list acc cursor element : Nat) {accType : ScalarType} (body : Expr accType) :
    Stmt :=
  .seq (.assign cursor (.get list)) <|
  .while (.ne (.get cursor) (.const 0)) <|
    .seq (.load .u64 element (.get cursor)) <|
    .seq (.assign acc body) <|
    .load .u64 cursor (.bin .add (.get cursor) (.const 8))

theorem Stmt.listFold_spec {accType : ScalarType} {scratch list acc cursor element : Nat}
    {body : Expr accType} {initial : Store Unit} {before : State} {ptr : UInt64}
    {start : accType.denote} {xs : List UInt64} (g : accType.denote → UInt64 → accType.denote)
    (hLocals : [list, acc, cursor, element].Nodup)
    (hBelow : ∀ j ∈ [list, acc, cursor, element], j < scratch)
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hList : ListAt initial.mem ptr xs)
    (hPtr : before.get list = some (.i64 ptr))
    (hStart : before.get acc = some (accType.value start))
    (hBody : ∀ state a e, State.Frame scratch [acc, cursor, element] before state →
      state.get acc = some (accType.value a) → state.get element = some (.i64 e) →
      ∃ next, body.eval initial.mem scratch state = some (g a e, next)) :
    Triple m (.listFold list acc cursor element body) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧
        State.Frame scratch [acc, cursor, element] before state ∧
        state.get acc = some (accType.value (xs.foldl g start))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hListAcc, hListCursor, hListElement⟩, ⟨hAccCursor, hAccElement⟩, hCursorElement⟩ :=
    hLocals
  obtain ⟨hListBelow, hAccBelow, hCursorBelow, hElementBelow⟩ := hBelow
  have hWrites : ∀ j ∈ [acc, cursor, element], j ∈ [acc, cursor, element] ∨ scratch ≤ j :=
    fun _ h => Or.inl h
  let Inv : Store Unit → State → Prop := fun store state =>
    store = initial ∧ State.Frame scratch [acc, cursor, element] before state ∧
      ∃ ys zs q, xs = ys ++ zs ∧ state.get cursor = some (.i64 q) ∧ ListAt initial.mem q zs ∧
        state.get acc = some (accType.value (ys.foldl g start))
  let measure : Store Unit → State → Nat := fun store state =>
    match state.get cursor with
    | some (.i64 q) => listLength store.mem q
    | _ => 0
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := cursor) (.i64 ptr)
    (by omega)
  have hFrame1 := (State.Frame.refl scratch [acc, cursor, element] before).set? hSet1
    (hWrites _ (by simp))
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1) ?_ <|
    (Stmt.while_spec Inv measure ?_ fun n => ?_).mono ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨ptr, before, s1, by simp [Expr.eval, hPtr], hSet1, rfl, rfl⟩
  · rintro store state ⟨-, -, ys, zs, q, -, hCursor, -, -⟩
    exact ⟨q != 0, state, by simp [Expr.eval, hCursor]⟩
  · apply Triple.of_forall
    rintro store state ⟨current, ⟨hStore, hFrame, ys, zs, q, hSplit, hCursor, hZs, hAcc⟩,
      hMeasure, hCondition⟩
    subst store
    simp only [Expr.eval, hCursor, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq, bne_iff_ne, ne_eq] at hCondition
    obtain ⟨hNonzero, rfl⟩ := hCondition
    cases zs with
    | nil => exact absurd hZs hNonzero
    | cons z rest =>
    have hLength := hZs.listLength
    obtain ⟨-, hAddress, hPages, hz, hRest⟩ := hZs
    have hListHere : current.get list = some (.i64 ptr) :=
      (hFrame.get list hListBelow (by simp; omega)).trans hPtr
    obtain ⟨t1, hSetT1⟩ := State.exists_set? (state := current) (index := element) (.i64 z)
      (by have := hFrame.params; have := hFrame.locals; omega)
    have hFrameT1 := hFrame.set? hSetT1 (hWrites _ (by simp))
    have hAccT1 : t1.get acc = some (accType.value (ys.foldl g start)) := by
      rw [State.get_set?_ne (by omega) hSetT1, hAcc]
    obtain ⟨t2, hBodyEval⟩ := hBody t1 _ _ hFrameT1 hAccT1 (State.get_set?_same hSetT1)
    have hFrameT2 := hFrameT1.trans (Expr.eval_frame _ body initial.mem scratch t1 t2 _ hBodyEval)
    obtain ⟨t3, hSetT3⟩ := State.exists_set? (state := t2) (index := acc)
      (accType.value (g (ys.foldl g start) z))
      (by have := hFrameT2.params; have := hFrameT2.locals; omega)
    have hFrameT3 := hFrameT2.set? hSetT3 (hWrites _ (by simp))
    have hBodyKeeps : ∀ j, j < scratch → t2.get j = t1.get j := fun j hj =>
      (Expr.eval_frame [] body initial.mem scratch t1 t2 _ hBodyEval).get j hj (by simp)
    have hCursorT3 : t3.get cursor = some (.i64 q) := by
      rw [State.get_set?_ne (by omega) hSetT3, hBodyKeeps cursor hCursorBelow,
        State.get_set?_ne (by omega) hSetT1, hCursor]
    obtain ⟨t4, hSetT4⟩ := State.exists_set? (state := t3) (index := cursor)
      (.i64 (initial.mem.read64 (slotAddress q 1)))
      (by have := hFrameT3.params; have := hFrameT3.locals; omega)
    have hSlot : ∀ i, i < 2 → (slotAddress q i).toNat = q.toNat + 8 * i := fun i hi =>
      slotAddress_toNat (by omega)
    refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = t1) ?_ <|
      Stmt.seq_spec (M := fun store state => store = initial ∧ state = t3) ?_ ?_
    · refine Stmt.load_spec.mono ?_ fun _ _ h => h
      rintro store state ⟨hStore, hState⟩
      subst store state
      refine ⟨q, current, t1, by simp [Expr.eval, hCursor], ?_, ?_, rfl, rfl⟩
      · rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : slotAddress q 0 = q.toUInt32 := by simp [slotAddress]
        rw [← this, hz]
        exact hSetT1
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro store state ⟨hStore, hState⟩
      subst store state
      exact ⟨_, t2, t3, hBodyEval, hSetT3, rfl, rfl⟩
    · refine Stmt.load_spec.mono ?_ fun _ _ h => h
      rintro store state ⟨hStore, hState⟩
      subst store state
      have hAddress1 : (q + 8).toUInt32 = slotAddress q 1 := rfl
      refine ⟨q + 8, t3, t4, by simp [Expr.eval, hCursorT3, U64Op.apply], ?_, ?_, ?_⟩
      · rw [hAddress1, hSlot 1 (by omega)]
        omega
      · rw [hAddress1]
        exact hSetT4
      refine ⟨⟨rfl, hFrameT3.set? hSetT4 (hWrites _ (by simp)), ys ++ [z], rest, _,
        by rw [hSplit]; simp, State.get_set?_same hSetT4, hRest, ?_⟩, ?_⟩
      · rw [State.get_set?_ne (by omega) hSetT4, State.get_set?_same hSetT3, List.foldl_append]
        rfl
      · simp only [measure, State.get_set?_same hSetT4, hRest.listLength] at hMeasure ⊢
        simp only [hCursor, hLength, List.length_cons] at hMeasure
        omega
  · rintro store state ⟨rfl, rfl⟩
    refine ⟨rfl, hFrame1, [], xs, ptr, rfl, State.get_set?_same hSet1, hList, ?_⟩
    rw [State.get_set?_ne (by omega) hSet1, hStart]
    rfl
  · rintro store state ⟨current, ⟨hStore, hFrame, ys, zs, q, hSplit, hCursor, hZs, hAcc⟩,
      hCondition⟩
    subst store
    simp only [Expr.eval, hCursor, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq, bne_eq_false_iff_eq] at hCondition
    obtain ⟨rfl, rfl⟩ := hCondition
    cases zs with
    | nil => exact ⟨rfl, hFrame, by rw [hAcc, hSplit, List.append_nil]⟩
    | cons z rest => exact absurd rfl hZs.1

end Project.IR
