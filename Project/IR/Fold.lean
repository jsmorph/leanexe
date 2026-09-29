import Project.IR.Stmt
import Project.ProofKit.Array

/-!
The rule lemma for the compiler's array fold template.  The compiler translates
`xs.foldl g init`, for an `Array UInt64` in local `array`, to an assignment of
`init` to an accumulator followed by `Stmt.fold`, which walks the elements in
order and assigns the value of `g`'s body to the accumulator.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.ProofKit.ScalarTransition

/-- Local `length` receives the length of the array at local `array`.  For each
index from 0, held in local `index`, local `element` receives the element and
local `acc` receives the value of `body`. -/
def Stmt.fold (array acc index length element : Nat) (body : Expr .u64) : Stmt :=
  .seq (.load length (.get array)) <|
  .seq (.assign index (.const 0)) <|
  .while (.ltU (.get index) (.get length)) <|
    .seq (.load element (.bin .add (.get array)
      (.bin .mul (.bin .add (.get index) (.const 1)) (.const 8)))) <|
    .seq (.assign acc body) <|
    .assign index (.bin .add (.get index) (.const 1))

theorem elementAddress (ptr : UInt64) (k : Nat) :
    ptr + (UInt64.ofNat k + 1) * 8 = ptr + UInt64.ofNat (8 * (k + 1)) := by
  congr 1
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
  omega

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The fold leaves `xs.foldl g start` in `acc`, where `start` is the value of
`acc` on entry, provided `body` evaluates to `g a e` whenever `acc` holds `a` and
`element` holds `e`.  It keeps the store and changes only its four locals and
scratch locals. -/
theorem Stmt.fold_spec {scratch array acc index length element : Nat} {body : Expr .u64}
    {initial : Store Unit} {before : State} {ptr start : UInt64} {xs : Array UInt64}
    (g : UInt64 → UInt64 → UInt64)
    (hLocals : [array, acc, index, length, element].Nodup)
    (hBelow : ∀ j ∈ [array, acc, index, length, element], j < scratch)
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hArray : UInt64Array.At initial ptr xs)
    (hPtr : before.get array = some (.i64 ptr))
    (hStart : before.get acc = some (.i64 start))
    (hBody : ∀ state a e, State.Frame scratch [acc, index, length, element] before state →
      state.get acc = some (.i64 a) → state.get element = some (.i64 e) →
      ∃ next, body.eval scratch state = some (g a e, next)) :
    Triple (.fold array acc index length element body) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧
        State.Frame scratch [acc, index, length, element] before state ∧
        state.get acc = some (.i64 (xs.foldl g start))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hLocals
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hBelow
  obtain ⟨⟨hArrayAcc, hArrayIndex, hArrayLength, hArrayElement⟩,
    ⟨hAccIndex, hAccLength, hAccElement⟩, ⟨hIndexLength, hIndexElement⟩, hLengthElement⟩ :=
    hLocals
  obtain ⟨hArrayBelow, hAccBelow, hIndexBelow, hLengthBelow, hElementBelow⟩ := hBelow
  have ⟨hFit, hPages, hSize, hElements⟩ := hArray
  have hArrayOut : array ∉ [acc, index, length, element] := by simp; omega
  have hWrites : ∀ j ∈ [acc, index, length, element], j ∈ [acc, index, length, element] ∨
      scratch ≤ j := fun _ h => Or.inl h
  let Inv : Store Unit → State → Prop := fun store state =>
    store = initial ∧ State.Frame scratch [acc, index, length, element] before state ∧
      ∃ k, k ≤ xs.size ∧ state.get index = some (.i64 (UInt64.ofNat k)) ∧
        state.get length = some (.i64 (UInt64.ofNat xs.size)) ∧
        state.get acc = some (.i64 (ArrayFold.foldPrefix xs g start k))
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 k) => xs.size - k.toNat
    | _ => 0
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := before) (index := length)
    (.i64 (UInt64.ofNat xs.size)) (by omega)
  have hFrame1 := (State.Frame.refl scratch [acc, index, length, element] before).set? hSet1
    (hWrites _ (by simp))
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := index) (.i64 0)
    (by have := hFrame1.params; have := hFrame1.locals; omega)
  have hFrame2 := hFrame1.set? hSet2 (hWrites _ (by simp))
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1) ?_ <|
    Stmt.seq_spec (M := fun store state => store = initial ∧ state = s2) ?_ <|
    (Stmt.while_spec Inv measure ?_ fun n => ?_).mono ?_ ?_
  · refine Stmt.load_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    refine ⟨ptr, before, s1, by simp [Expr.eval, hPtr], ?_, by rw [hSize]; exact hSet1, rfl, rfl⟩
    rw [UInt64Array.At.pointerAddress_toNat hArray]
    omega
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, s1, s2, rfl, hSet2, rfl, rfl⟩
  · rintro store state ⟨-, -, k, -, hIndex, hLength, -⟩
    exact ⟨decide (UInt64.ofNat k < UInt64.ofNat xs.size), state,
      by simp [Expr.eval, hIndex, hLength]⟩
  · apply Triple.of_forall
    rintro store state ⟨current, ⟨hStore, hFrame, k, hk, hIndex, hLength, hAcc⟩, rfl,
      hCondition⟩
    subst store
    simp only [Expr.eval, hIndex, hLength, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_ofNat (by omega) (by omega)] at hLess
    have hPtrHere : current.get array = some (.i64 ptr) :=
      (hFrame.get array hArrayBelow hArrayOut).trans hPtr
    obtain ⟨t1, hSetT1⟩ := State.exists_set? (state := current) (index := element)
      (.i64 xs[k]) (by have := hFrame.params; have := hFrame.locals; omega)
    have hFrameT1 := hFrame.set? hSetT1 (hWrites _ (by simp))
    have hAccT1 : t1.get acc = some (.i64 (ArrayFold.foldPrefix xs g start k)) := by
      rw [State.get_set?_ne (by omega) hSetT1, hAcc]
    obtain ⟨t2, hBodyEval⟩ := hBody t1 _ _ hFrameT1 hAccT1 (State.get_set?_same hSetT1)
    have hFrameT2 := hFrameT1.trans (Expr.eval_frame _ body scratch t1 t2 _ hBodyEval)
    obtain ⟨t3, hSetT3⟩ := State.exists_set? (state := t2) (index := acc)
      (.i64 (g (ArrayFold.foldPrefix xs g start k) xs[k]))
      (by have := hFrameT2.params; have := hFrameT2.locals; omega)
    have hFrameT3 := hFrameT2.set? hSetT3 (hWrites _ (by simp))
    have hBodyKeeps : ∀ j, j < scratch → t2.get j = t1.get j := fun j hj =>
      (Expr.eval_frame [] body scratch t1 t2 _ hBodyEval).get j hj (by simp)
    have hIndexT3 : t3.get index = some (.i64 (UInt64.ofNat k)) := by
      rw [State.get_set?_ne (by omega) hSetT3, hBodyKeeps index hIndexBelow,
        State.get_set?_ne (by omega) hSetT1, hIndex]
    obtain ⟨t4, hSetT4⟩ := State.exists_set? (state := t3) (index := index)
      (.i64 (UInt64.ofNat k + 1))
      (by have := hFrameT3.params; have := hFrameT3.locals; omega)
    refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = t1) ?_ <|
      Stmt.seq_spec (M := fun store state => store = initial ∧ state = t3) ?_ ?_
    · refine Stmt.load_spec.mono ?_ fun _ _ h => h
      rintro store state ⟨hStore, hState⟩
      subst store state
      refine ⟨ptr + UInt64.ofNat (8 * (k + 1)), current, t1, ?_, ?_, ?_, rfl, rfl⟩
      · simp [Expr.eval, hPtrHere, hIndex, U64Op.apply, elementAddress ptr k]
      · rw [UInt64Array.At.elementAddress_toNat hArray k hLess]
        omega
      · rw [hElements k hLess]
        exact hSetT1
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro store state ⟨hStore, hState⟩
      subst store state
      exact ⟨_, t2, t3, hBodyEval, hSetT3, rfl, rfl⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro store state ⟨hStore, hState⟩
      subst store state
      refine ⟨UInt64.ofNat k + 1, t3, t4, by simp [Expr.eval, hIndexT3, U64Op.apply], hSetT4,
        ⟨rfl, hFrameT3.set? hSetT4 (hWrites _ (by simp)), k + 1, hLess, ?_, ?_, ?_⟩, ?_⟩
      · rw [State.get_set?_same hSetT4]
        simp
      · rw [State.get_set?_ne (by omega) hSetT4, State.get_set?_ne (by omega) hSetT3,
          hBodyKeeps length hLengthBelow, State.get_set?_ne (by omega) hSetT1, hLength]
      · rw [State.get_set?_ne (by omega) hSetT4, State.get_set?_same hSetT3,
          ArrayFold.foldPrefix_succ xs g start k hLess]
      · have hkFit : k + 1 < 2 ^ 64 := by omega
        simp only [measure, State.get_set?_same hSetT4, hIndex, UInt64.toNat_add,
          UInt64.toNat_ofNat', UInt64.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · rintro store state ⟨rfl, rfl⟩
    refine ⟨rfl, hFrame2, 0, Nat.zero_le _, State.get_set?_same hSet2, ?_, ?_⟩
    · rw [State.get_set?_ne (by omega) hSet2, State.get_set?_same hSet1]
    · rw [State.get_set?_ne (by omega) hSet2, State.get_set?_ne (by omega) hSet1, hStart]
      simp [ArrayFold.foldPrefix]
  · rintro store state ⟨current, ⟨hStore, hFrame, k, hk, hIndex, hLength, hAcc⟩, hCondition⟩
    subst store
    simp only [Expr.eval, hIndex, hLength, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_ofNat (by omega) (by omega)] at hNotLess
    obtain rfl : k = xs.size := by omega
    exact ⟨rfl, hFrame, by rw [hAcc, ArrayFold.foldPrefix_size]⟩

end Project.IR
