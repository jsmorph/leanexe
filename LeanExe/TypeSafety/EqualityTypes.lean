import LeanExe.TypeSafety.EqualityFlags

/-!
# Independent structural-equality admission

`EqTy` is a least inductive judgment, independent of the checker. A nominal type
requires equality support for every field of every constructor. Recursive
reference cycles therefore cannot supply a finite derivation, including cycles
under arrays or otherwise unused constructor alternatives.

The executable checker monotonically saturates a finite declaration table from
false. `EqualityFlags` proves that the declaration-table length is a sufficient
number of rounds. Exact checker correspondence does not assume global declaration
formation: unrelated malformed declarations do not affect a scalar query. A
public source checker must still check global formation separately.

This module adds no expression primitive or source execution rule.
-/

namespace LeanExe.TypeSafety

mutual
inductive EqTy (declarations : DataDecls) : Ty → Prop where
  | unit : EqTy declarations .unit
  | bool : EqTy declarations .bool
  | nat64 : EqTy declarations .nat64
  | word : EqTy declarations (.word width)
  | prod : EqTy declarations α → EqTy declarations β → EqTy declarations (.prod α β)
  | sum : EqTy declarations α → EqTy declarations β → EqTy declarations (.sum α β)
  | array : EqTy declarations α → EqTy declarations (.array α)
  | data (found : lookup declarations index = some constructors) :
      EqConstructors declarations constructors → EqTy declarations (.data index)

inductive EqTypes (declarations : DataDecls) : List Ty → Prop where
  | nil : EqTypes declarations []
  | cons : EqTy declarations head → EqTypes declarations tail →
      EqTypes declarations (head :: tail)

inductive EqConstructors (declarations : DataDecls) : DataDecl → Prop where
  | nil : EqConstructors declarations []
  | cons : EqTypes declarations fields → EqConstructors declarations rest →
      EqConstructors declarations (fields :: rest)
end

mutual
theorem EqTy.wellFormed (admitted : EqTy declarations τ) : TyWF declarations τ := by
  cases admitted with
  | unit => exact .unit
  | bool => exact .bool
  | nat64 => exact .nat64
  | word => exact .word
  | prod left right => exact .prod left.wellFormed right.wellFormed
  | sum left right => exact .sum left.wellFormed right.wellFormed
  | array item => exact .array item.wellFormed
  | data found _ => exact .data (lookup_lt found)

theorem EqTypes.wellFormed (admitted : EqTypes declarations types) : TypesWF declarations types := by
  cases admitted with
  | nil => exact .nil
  | cons head tail => exact .cons head.wellFormed tail.wellFormed

theorem EqConstructors.wellFormed (admitted : EqConstructors declarations constructors) :
    ConstructorsWF declarations constructors := by
  cases admitted with
  | nil => exact .nil
  | cons head tail => exact .cons head.wellFormed tail.wellFormed
end

namespace EqualityCheck

/-- Check type structure against the currently accepted nominal entries. -/
def typeAccepted (flags : List Bool) : Ty → Bool
  | .unit | .bool | .nat64 | .word _ => true
  | .prod left right | .sum left right => typeAccepted flags left && typeAccepted flags right
  | .array item => typeAccepted flags item
  | .data index => decide (lookup flags index = some true)

def typesAccepted (flags : List Bool) : List Ty → Bool
  | [] => true
  | head :: tail => typeAccepted flags head && typesAccepted flags tail

def constructorsAccepted (flags : List Bool) : DataDecl → Bool
  | [] => true
  | fields :: rest => typesAccepted flags fields && constructorsAccepted flags rest

/-- Every entry is recomputed from the preceding table, checking every constructor and field. -/
def next (declarations : DataDecls) (flags : List Bool) : List Bool :=
  match declarations with
  | [] => []
  | constructors :: rest => constructorsAccepted flags constructors :: next rest flags

def stage (declarations : DataDecls) (round : Nat) : List Bool :=
  saturate (next declarations) declarations.length round

theorem typeAccepted_mono (ordered : FlagsLE left right)
    (accepted : typeAccepted left τ = true) : typeAccepted right τ = true := by
  induction τ with
  | unit | bool | nat64 | word _ => rfl
  | prod α β ihα ihβ | sum α β ihα ihβ =>
      obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp accepted
      exact Bool.and_eq_true_iff.mpr ⟨ihα first, ihβ second⟩
  | array item ih => exact ih accepted
  | data index => exact decide_eq_true (ordered.lookup (of_decide_eq_true accepted))

theorem typesAccepted_mono (ordered : FlagsLE left right)
    (accepted : typesAccepted left types = true) : typesAccepted right types = true := by
  induction types with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp accepted
      exact Bool.and_eq_true_iff.mpr ⟨typeAccepted_mono ordered first, ih rest⟩

theorem constructorsAccepted_mono (ordered : FlagsLE left right)
    (accepted : constructorsAccepted left constructors = true) :
    constructorsAccepted right constructors = true := by
  induction constructors with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp accepted
      exact Bool.and_eq_true_iff.mpr ⟨typesAccepted_mono ordered first, ih rest⟩

theorem next_length (declarations : DataDecls) (flags : List Bool) :
    (next declarations flags).length = declarations.length := by
  induction declarations with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem next_monotone (declarations : DataDecls) : Monotone (next declarations) := by
  intro left right ordered
  induction declarations with
  | nil => exact .nil
  | cons head tail ih => exact .cons (constructorsAccepted_mono ordered) ih

theorem next_keepsLength (declarations : DataDecls) :
    KeepsLength (next declarations) declarations.length := by
  intro flags _
  exact next_length declarations flags

theorem stage_length (declarations : DataDecls) (round : Nat) :
    (stage declarations round).length = declarations.length :=
  saturate_length (next_keepsLength declarations) round

/-- After exactly N rounds, the table is a fixed point. -/
theorem stage_stable (declarations : DataDecls) :
    stage declarations declarations.length =
      next declarations (stage declarations declarations.length) :=
  saturate_stable (next_keepsLength declarations) (next_monotone declarations)

/-- A marked output entry corresponds exactly to the complete selected declaration. -/
theorem lookup_next_iff : lookup (next declarations flags) index = some true ↔
    ∃ constructors, lookup declarations index = some constructors ∧
      constructorsAccepted flags constructors = true := by
  induction declarations generalizing index with
  | nil =>
      constructor
      · intro impossible; cases impossible
      · intro witness; obtain ⟨_, impossible, _⟩ := witness; cases impossible
  | cons head tail ih =>
      cases index with
      | zero =>
          constructor
          · intro found
            exact ⟨head, rfl, Option.some.inj found⟩
          · intro witness
            obtain ⟨constructors, found, checked⟩ := witness
            have same := Option.some.inj found
            cases same
            exact congrArg some checked
      | succ index => exact ih

/-- An invariant of intermediate tables, expressed through the independent judgment. -/
def Sound (declarations : DataDecls) (flags : List Bool) : Prop :=
  ∀ {index}, lookup flags index = some true → EqTy declarations (.data index)

theorem typeAccepted_sound (sound : Sound declarations flags)
    (accepted : typeAccepted flags τ = true) : EqTy declarations τ := by
  induction τ with
  | unit => exact .unit
  | bool => exact .bool
  | nat64 => exact .nat64
  | word _ => exact .word
  | prod α β ihα ihβ =>
      obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp accepted
      exact .prod (ihα first) (ihβ second)
  | sum α β ihα ihβ =>
      obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp accepted
      exact .sum (ihα first) (ihβ second)
  | array item ih => exact .array (ih accepted)
  | data index => exact sound (of_decide_eq_true accepted)

theorem typesAccepted_sound (sound : Sound declarations flags)
    (accepted : typesAccepted flags types = true) : EqTypes declarations types := by
  induction types with
  | nil => exact .nil
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp accepted
      exact .cons (typeAccepted_sound sound first) (ih rest)

theorem constructorsAccepted_sound (sound : Sound declarations flags)
    (accepted : constructorsAccepted flags constructors = true) :
    EqConstructors declarations constructors := by
  induction constructors with
  | nil => exact .nil
  | cons head tail ih =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp accepted
      exact .cons (typesAccepted_sound sound first) (ih rest)

theorem lookup_bottom_ne_true (width index : Nat) :
    lookup (List.replicate width false) index ≠ some true := by
  induction width generalizing index with
  | zero => intro impossible; cases impossible
  | succ width ih =>
      cases index with
      | zero => intro impossible; cases impossible
      | succ index => exact ih index

theorem next_sound (sound : Sound declarations flags) :
    Sound declarations (next declarations flags) := by
  intro index found
  obtain ⟨constructors, declared, checked⟩ := lookup_next_iff.mp found
  exact .data declared (constructorsAccepted_sound sound checked)

theorem stage_sound (declarations : DataDecls) (round : Nat) :
    Sound declarations (stage declarations round) := by
  induction round with
  | zero =>
      intro index found
      exact False.elim (lookup_bottom_ne_true declarations.length index found)
  | succ round ih => exact next_sound ih

/-- Completeness uses mutual induction on domain derivations and the proved fixed point. -/
theorem typeAccepted_complete (stable : flags = next declarations flags)
    (admitted : EqTy declarations τ) : typeAccepted flags τ = true := by
  exact EqTy.rec
    (motive_1 := fun τ _ => typeAccepted flags τ = true)
    (motive_2 := fun types _ => typesAccepted flags types = true)
    (motive_3 := fun constructors _ => constructorsAccepted flags constructors = true)
    rfl rfl rfl (fun {_} => rfl)
    (fun _ _ first second => Bool.and_eq_true_iff.mpr ⟨first, second⟩)
    (fun _ _ first second => Bool.and_eq_true_iff.mpr ⟨first, second⟩)
    (fun _ item => item)
    (fun found _ checked => by
      apply decide_eq_true
      rw [stable]
      exact lookup_next_iff.mpr ⟨_, found, checked⟩)
    rfl (fun _ _ head tail => Bool.and_eq_true_iff.mpr ⟨head, tail⟩)
    rfl (fun _ _ head tail => Bool.and_eq_true_iff.mpr ⟨head, tail⟩)
    admitted

theorem typesAccepted_complete (stable : flags = next declarations flags)
    (admitted : EqTypes declarations types) : typesAccepted flags types = true := by
  induction types with
  | nil => rfl
  | cons head tail ih =>
      cases admitted with
      | cons first rest =>
          exact Bool.and_eq_true_iff.mpr ⟨typeAccepted_complete stable first, ih rest⟩

theorem constructorsAccepted_complete (stable : flags = next declarations flags)
    (admitted : EqConstructors declarations constructors) :
    constructorsAccepted flags constructors = true := by
  induction constructors with
  | nil => rfl
  | cons head tail ih =>
      cases admitted with
      | cons first rest =>
          exact Bool.and_eq_true_iff.mpr ⟨typesAccepted_complete stable first, ih rest⟩

end EqualityCheck

/-- Equality admission for a queried type; global formation is checked separately. -/
def equalitySupported (declarations : DataDecls) (τ : Ty) : Bool :=
  EqualityCheck.typeAccepted (EqualityCheck.stage declarations declarations.length) τ

theorem equalitySupported_iff : equalitySupported declarations τ = true ↔ EqTy declarations τ := by
  constructor
  · exact EqualityCheck.typeAccepted_sound (EqualityCheck.stage_sound declarations declarations.length)
  · exact EqualityCheck.typeAccepted_complete (EqualityCheck.stage_stable declarations)

end LeanExe.TypeSafety
