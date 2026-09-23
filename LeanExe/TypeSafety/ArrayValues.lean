import LeanExe.TypeSafety.Core

/-!
# Persistent abstract array operations

The operations consume raw finite lists. Their proofs separately establish
homogeneous element types and the exclusive `nat64Limit` length bound. Failure
is `inl unit`; success is `inr` of the result. No operation mutates its input,
models allocation, or depends on a typing derivation to execute.
-/

namespace LeanExe.TypeSafety

namespace ArrayValues

def replace? : List Value → Nat → Value → Option (List Value)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value => (replace? rest index value).map (head :: ·)

def get? (elements : List Value) (index : Nat) : Value :=
  match lookup elements index with
  | none => .inl .unit
  | some value => .inr value

def set? (elements : List Value) (index : Nat) (value : Value) : Value :=
  match replace? elements index value with
  | none => .inl .unit
  | some result => .inr (.array result)

def push? (elements : List Value) (value : Value) : Value :=
  if elements.length + 1 < nat64Limit then
    .inr (.array (elements ++ [value]))
  else .inl .unit

def append? (left right : List Value) : Value :=
  if left.length + right.length < nat64Limit then
    .inr (.array (left ++ right))
  else .inl .unit

theorem lookup_none_iff {α : Type} {elements : List α} :
    lookup elements index = none ↔ elements.length ≤ index := by
  induction elements generalizing index with
  | nil => simp [lookup]
  | cons head rest ih =>
      cases index with
      | zero => simp [lookup]
      | succ index =>
          simpa only [lookup, List.length_cons, Nat.succ_le_succ_iff] using ih

theorem lookup_append_left {α : Type} {left right : List α}
    (bounded : index < left.length) : lookup (left ++ right) index = lookup left index := by
  induction left generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero index bounded)
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih (Nat.lt_of_succ_lt_succ bounded)

theorem lookup_append_right {α : Type} (left right : List α) (index : Nat) :
    lookup (left ++ right) (left.length + index) = lookup right index := by
  induction left with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons head rest ih =>
      simpa only [List.cons_append, List.length_cons, Nat.succ_add, lookup] using ih

theorem replace_none_iff : replace? elements index value = none ↔
    elements.length ≤ index := by
  induction elements generalizing index with
  | nil => simp [replace?]
  | cons head rest ih =>
      cases index with
      | zero => simp [replace?]
      | succ index =>
          cases found : replace? rest index value with
          | none =>
              have bounded := ih.mp found
              constructor
              · intro _
                exact Nat.succ_le_succ bounded
              · intro _
                simp [replace?, found]
          | some result =>
              constructor
              · intro impossible
                simp [replace?, found] at impossible
              · intro bounded
                have missing := ih.mpr (Nat.le_of_succ_le_succ bounded)
                rw [found] at missing
                cases missing

theorem replace_length (changed : replace? elements index value = some result) :
    result.length = elements.length := by
  induction elements generalizing index result with
  | nil => simp [replace?] at changed
  | cons head rest ih =>
      cases index with
      | zero =>
          simp only [replace?, Option.some.injEq] at changed
          cases changed
          rfl
      | succ index =>
          cases found : replace? rest index value with
          | none => simp [replace?, found] at changed
          | some tail =>
              simp only [replace?, found, Option.map_some, Option.some.injEq] at changed
              cases changed
              exact congrArg Nat.succ (ih found)

theorem replace_lookup_same (changed : replace? elements index value = some result) :
    lookup result index = some value := by
  induction elements generalizing index result with
  | nil => simp [replace?] at changed
  | cons head rest ih =>
      cases index with
      | zero =>
          simp only [replace?, Option.some.injEq] at changed
          cases changed
          rfl
      | succ index =>
          cases found : replace? rest index value with
          | none => simp [replace?, found] at changed
          | some tail =>
              simp only [replace?, found, Option.map_some, Option.some.injEq] at changed
              cases changed
              exact ih (index := index) (result := tail) found

theorem replace_lookup_other (changed : replace? elements index value = some result)
    (different : other ≠ index) : lookup result other = lookup elements other := by
  induction elements generalizing index result other with
  | nil => simp [replace?] at changed
  | cons head rest ih =>
      cases index with
      | zero =>
          simp only [replace?, Option.some.injEq] at changed
          cases changed
          cases other with
          | zero => exact False.elim (different rfl)
          | succ other => rfl
      | succ index =>
          cases found : replace? rest index value with
          | none => simp [replace?, found] at changed
          | some tail =>
              simp only [replace?, found, Option.map_some, Option.some.injEq] at changed
              cases changed
              cases other with
              | zero => rfl
              | succ other =>
                  exact ih found (fun same => different (congrArg Nat.succ same))

theorem get_failure_iff : get? elements index = .inl .unit ↔
    elements.length ≤ index := by
  cases found : lookup elements index with
  | none =>
      constructor
      · intro _
        exact lookup_none_iff.mp found
      · intro _
        simp [get?, found]
  | some value =>
      constructor
      · intro impossible
        simp [get?, found] at impossible
      · intro bounded
        have missing := lookup_none_iff.mpr bounded
        rw [found] at missing
        cases missing

theorem set_failure_iff : set? elements index value = .inl .unit ↔
    elements.length ≤ index := by
  cases found : replace? elements index value with
  | none =>
      constructor
      · intro _
        exact replace_none_iff.mp found
      · intro _
        simp [set?, found]
  | some result =>
      constructor
      · intro impossible
        simp [set?, found] at impossible
      · intro bounded
        have missing := (replace_none_iff (value := value)).mpr bounded
        rw [found] at missing
        cases missing

theorem push_failure_iff : push? elements value = .inl .unit ↔
    nat64Limit ≤ elements.length + 1 := by
  by_cases bounded : elements.length + 1 < nat64Limit
  · simp [push?, bounded, Nat.not_le_of_gt bounded]
  · simp [push?, bounded, Nat.le_of_not_lt bounded]

theorem append_failure_iff : append? left right = .inl .unit ↔
    nat64Limit ≤ left.length + right.length := by
  by_cases bounded : left.length + right.length < nat64Limit
  · simp [append?, bounded, Nat.not_le_of_gt bounded]
  · simp [append?, bounded, Nat.le_of_not_lt bounded]

theorem set_success_iff : set? elements index value = .inr (.array result) ↔
    replace? elements index value = some result := by
  cases found : replace? elements index value with
  | none => simp [set?, found]
  | some changed => simp [set?, found]

theorem set_success_length (success : set? elements index value = .inr (.array result)) :
    result.length = elements.length :=
  replace_length (set_success_iff.mp success)

theorem get_after_set_same (success : set? elements index value = .inr (.array result)) :
    get? result index = .inr value := by
  have found := replace_lookup_same (set_success_iff.mp success)
  simp [get?, found]

theorem get_after_set_other (success : set? elements index value = .inr (.array result))
    (different : other ≠ index) : get? result other = get? elements other := by
  unfold get?
  rw [replace_lookup_other (set_success_iff.mp success) different]

theorem push_success (bounded : elements.length + 1 < nat64Limit) :
    push? elements value = .inr (.array (elements ++ [value])) := by
  simp [push?, bounded]

theorem append_success (bounded : left.length + right.length < nat64Limit) :
    append? left right = .inr (.array (left ++ right)) := by
  simp [append?, bounded]

theorem push_success_iff : push? elements value = .inr (.array result) ↔
    elements.length + 1 < nat64Limit ∧ result = elements ++ [value] := by
  by_cases bounded : elements.length + 1 < nat64Limit
  · simp [push?, bounded, eq_comm]
  · simp [push?, bounded]

theorem append_success_iff : append? left right = .inr (.array result) ↔
    left.length + right.length < nat64Limit ∧ result = left ++ right := by
  by_cases bounded : left.length + right.length < nat64Limit
  · simp [append?, bounded, eq_comm]
  · simp [append?, bounded]

theorem push_success_length (success : push? elements value = .inr (.array result)) :
    result.length = elements.length + 1 := by
  obtain ⟨_, rfl⟩ := push_success_iff.mp success
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem append_success_length (success : append? left right = .inr (.array result)) :
    result.length = left.length + right.length := by
  obtain ⟨_, rfl⟩ := append_success_iff.mp success
  exact List.length_append

theorem get_after_push_last : get? (elements ++ [value]) elements.length = .inr value := by
  have found := lookup_append_right elements [value] 0
  simpa only [Nat.add_zero, lookup, get?] using congrArg
    (fun result => match result with | none => Value.inl .unit | some item => .inr item) found

theorem get_after_append_left (bounded : index < left.length) :
    get? (left ++ right) index = get? left index := by
  unfold get?
  rw [lookup_append_left bounded]

theorem get_after_append_right :
    get? (left ++ right) (left.length + index) = get? right index := by
  unfold get?
  rw [lookup_append_right]

end ArrayValues

theorem ValuesTyped.append (left : ValuesTyped declarations values α)
    (right : ValuesTyped declarations values' α) :
    ValuesTyped declarations (values ++ values') α := by
  induction values with
  | nil => exact right
  | cons value rest ih =>
      cases left with
      | cons hvalue hrest => exact .cons hvalue (ih hrest)

theorem ValuesTyped.lookup (typed : ValuesTyped declarations elements α)
    (found : lookup elements index = some value) : ValueTyped declarations value α := by
  induction elements generalizing index with
  | nil => simp [LeanExe.TypeSafety.lookup] at found
  | cons head rest ih =>
      cases typed with
      | cons hvalue hrest =>
          cases index with
          | zero =>
              simp only [LeanExe.TypeSafety.lookup, Option.some.injEq] at found
              cases found
              exact hvalue
          | succ index => exact ih hrest found

theorem ValuesTyped.replace (typed : ValuesTyped declarations elements α)
    (hvalue : ValueTyped declarations value α)
    (changed : ArrayValues.replace? elements index value = some result) :
    ValuesTyped declarations result α := by
  induction elements generalizing index result with
  | nil => simp [ArrayValues.replace?] at changed
  | cons head rest ih =>
      cases typed with
      | cons hhead hrest =>
          cases index with
          | zero =>
              simp only [ArrayValues.replace?, Option.some.injEq] at changed
              cases changed
              exact .cons hvalue hrest
          | succ index =>
              cases found : ArrayValues.replace? rest index value with
              | none => simp [ArrayValues.replace?, found] at changed
              | some tail =>
                  simp only [ArrayValues.replace?, found, Option.map_some,
                    Option.some.injEq] at changed
                  cases changed
                  exact .cons hhead (ih hrest found)

namespace ArrayValues

theorem empty_typed (item : Ty) (formed : TyWF declarations item) :
    ValueTyped declarations (.array []) (.array item) :=
  .array (.nil formed) (by decide)

theorem get_typed (typed : ValuesTyped declarations elements α) :
    ValueTyped declarations (get? elements index) (.sum .unit α) := by
  cases found : lookup elements index with
  | none => simpa only [get?, found] using
      (ValueTyped.inl ValueTyped.unit typed.wellFormed :
        ValueTyped declarations (.inl .unit) (.sum .unit α))
  | some value =>
      simpa only [get?, found] using ValueTyped.inr (typed.lookup found) TyWF.unit

theorem set_typed (typed : ValuesTyped declarations elements α)
    (bounded : elements.length < nat64Limit) (hvalue : ValueTyped declarations value α) :
    ValueTyped declarations (set? elements index value) (.sum .unit (.array α)) := by
  cases found : replace? elements index value with
  | none => simpa only [set?, found] using
      (ValueTyped.inl ValueTyped.unit (.array typed.wellFormed) :
        ValueTyped declarations (.inl .unit) (.sum .unit (.array α)))
  | some result =>
      have resultBound : result.length < nat64Limit := by
        rw [replace_length found]
        exact bounded
      simpa only [set?, found] using ValueTyped.inr
        (ValueTyped.array (typed.replace hvalue found) resultBound) TyWF.unit

theorem push_typed (typed : ValuesTyped declarations elements α)
    (hvalue : ValueTyped declarations value α) :
    ValueTyped declarations (push? elements value) (.sum .unit (.array α)) := by
  by_cases bounded : elements.length + 1 < nat64Limit
  · have resultBound : (elements ++ [value]).length < nat64Limit := by
      simpa only [List.length_append, List.length_cons, List.length_nil] using bounded
    simpa [push?, bounded] using ValueTyped.inr
      (ValueTyped.array (typed.append (.cons hvalue (.nil typed.wellFormed))) resultBound) TyWF.unit
  · simpa [push?, bounded] using
      (ValueTyped.inl ValueTyped.unit (.array typed.wellFormed) :
        ValueTyped declarations (.inl .unit) (.sum .unit (.array α)))

theorem append_typed (leftTyped : ValuesTyped declarations left α)
    (rightTyped : ValuesTyped declarations right α) :
    ValueTyped declarations (append? left right) (.sum .unit (.array α)) := by
  by_cases bounded : left.length + right.length < nat64Limit
  · have resultBound : (left ++ right).length < nat64Limit := by
      simpa only [List.length_append] using bounded
    simpa [append?, bounded] using ValueTyped.inr
      (ValueTyped.array (leftTyped.append rightTyped) resultBound) TyWF.unit
  · simpa [append?, bounded] using
      (ValueTyped.inl ValueTyped.unit (.array leftTyped.wellFormed) :
        ValueTyped declarations (.inl .unit) (.sum .unit (.array α)))

end ArrayValues

end LeanExe.TypeSafety
