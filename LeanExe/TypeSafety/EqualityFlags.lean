import LeanExe.TypeSafety.Formation

/-!
# Constructive saturation of finite Boolean tables

A monotone, length-preserving table transformer reaches a fixed point from the
all-false table within as many rounds as there are entries. The proof counts true
entries directly, without finite-set machinery or an assumed iteration bound.
-/

namespace LeanExe.TypeSafety.EqualityCheck

/-- Pointwise implication together with exact table-length alignment. -/
inductive FlagsLE : List Bool → List Bool → Prop where
  | nil : FlagsLE [] []
  | cons : (left = true → right = true) → FlagsLE leftRest rightRest →
      FlagsLE (left :: leftRest) (right :: rightRest)

def trueCount : List Bool → Nat
  | [] => 0
  | head :: tail => if head then trueCount tail + 1 else trueCount tail

theorem FlagsLE.refl (flags : List Bool) : FlagsLE flags flags := by
  induction flags with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (fun same => same) ih

theorem FlagsLE.trans (first : FlagsLE left middle) (second : FlagsLE middle right) :
    FlagsLE left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head _ ih =>
      cases second with
      | cons next tail => exact .cons (fun same => next (head same)) (ih tail)

theorem FlagsLE.length (ordered : FlagsLE left right) : left.length = right.length := by
  induction ordered with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem FlagsLE.lookup (ordered : FlagsLE left right)
    (found : lookup left index = some true) : lookup right index = some true := by
  induction ordered generalizing index with
  | nil => cases found
  | cons head _ ih =>
      cases index with
      | zero => exact congrArg some (head (Option.some.inj found))
      | succ index => exact ih found

theorem FlagsLE.bottom (flags : List Bool) : FlagsLE (List.replicate flags.length false) flags := by
  induction flags with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (fun impossible => by cases impossible) ih

theorem trueCount_le_length (flags : List Bool) : trueCount flags ≤ flags.length := by
  induction flags with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      cases head with
      | false => exact Nat.le_succ_of_le ih
      | true => exact Nat.succ_le_succ ih

theorem FlagsLE.count_le (ordered : FlagsLE left right) : trueCount left ≤ trueCount right := by
  induction ordered with
  | nil => exact Nat.le_refl _
  | @cons left right _ _ head _ ih =>
      cases left <;> cases right
      · exact ih
      · exact Nat.le_succ_of_le ih
      · cases head rfl
      · exact Nat.succ_le_succ ih

theorem FlagsLE.eq_of_count_eq (ordered : FlagsLE left right)
    (same : trueCount left = trueCount right) : left = right := by
  induction ordered with
  | nil => rfl
  | @cons left right leftRest rightRest head tail ih =>
      cases left <;> cases right
      · exact congrArg (false :: ·) (ih same)
      · change trueCount leftRest = trueCount rightRest + 1 at same
        have impossible : trueCount leftRest < trueCount rightRest + 1 :=
          Nat.lt_succ_of_le tail.count_le
        rw [same] at impossible
        exact False.elim (Nat.lt_irrefl _ impossible)
      · cases head rfl
      · exact congrArg (true :: ·) (ih (Nat.succ.inj same))

theorem FlagsLE.count_lt_of_ne (ordered : FlagsLE left right) (different : left ≠ right) :
    trueCount left < trueCount right := by
  rcases Nat.eq_or_lt_of_le ordered.count_le with same | strict
  · exact False.elim (different (ordered.eq_of_count_eq same))
  · exact strict

/-- Synchronous iteration from the least table; `width` fixes the finite domain. -/
def saturate (next : List Bool → List Bool) (width : Nat) : Nat → List Bool
  | 0 => List.replicate width false
  | round + 1 => next (saturate next width round)

variable {next : List Bool → List Bool} {width : Nat}

/-- Only tables of the chosen width are required to preserve their length. -/
def KeepsLength (next : List Bool → List Bool) (width : Nat) : Prop :=
  ∀ flags, flags.length = width → (next flags).length = width

def Monotone (next : List Bool → List Bool) : Prop :=
  ∀ {left right}, FlagsLE left right → FlagsLE (next left) (next right)

theorem saturate_length (keepsLength : KeepsLength next width) (round : Nat) :
    (saturate next width round).length = width := by
  induction round with
  | zero => exact List.length_replicate
  | succ round ih => exact keepsLength _ ih

theorem saturate_le_next (keepsLength : KeepsLength next width) (monotone : Monotone next)
    (round : Nat) : FlagsLE (saturate next width round) (saturate next width (round + 1)) := by
  induction round with
  | zero =>
      have ordered := FlagsLE.bottom (saturate next width 1)
      rw [saturate_length keepsLength 1] at ordered
      exact ordered
  | succ round ih => exact monotone ih

/-- Every nonstationary round has accumulated at least one new true entry per round. -/
theorem saturate_stable_or_count (keepsLength : KeepsLength next width) (monotone : Monotone next)
    (round : Nat) :
    saturate next width round = saturate next width (round + 1) ∨
      round ≤ trueCount (saturate next width round) := by
  induction round with
  | zero => exact .inr (Nat.zero_le _)
  | succ round ih =>
      rcases ih with stable | count
      · exact .inl (congrArg next stable)
      · by_cases stable : saturate next width round = saturate next width (round + 1)
        · exact .inl (congrArg next stable)
        · exact .inr (Nat.lt_of_le_of_lt count
            ((saturate_le_next keepsLength monotone round).count_lt_of_ne stable))

/-- The iteration bound is proved: no more than `width` rounds are necessary. -/
theorem saturate_stable (keepsLength : KeepsLength next width) (monotone : Monotone next) :
    saturate next width width = next (saturate next width width) := by
  rcases saturate_stable_or_count keepsLength monotone width with stable | count
  · exact stable
  · have ordered := saturate_le_next keepsLength monotone width
    apply ordered.eq_of_count_eq
    apply Nat.le_antisymm ordered.count_le
    have bounded := trueCount_le_length (saturate next width (width + 1))
    rw [saturate_length keepsLength (width + 1)] at bounded
    exact Nat.le_trans bounded count

end LeanExe.TypeSafety.EqualityCheck
