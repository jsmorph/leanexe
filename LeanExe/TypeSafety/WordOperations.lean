import LeanExe.TypeSafety.NatOperations

/-!
# Mathematical unsigned word operations

Canonical words are naturals below the width's modulus. Arithmetic uses exact
mathematical intermediates; modular subtraction normalizes both operands before
subtracting, so natural-number saturation cannot replace modular underflow.
Conversions share one normalization function and carry source-width obligations
only in their typing and algebraic laws. Comparisons reuse `NatCmpOp` on the
represented unsigned naturals. No word operation introduces a failure outcome.
-/

namespace LeanExe.TypeSafety

inductive WordBinOp where
  | add | sub | mul | div | mod | min | max
  deriving DecidableEq, Repr

def normalizeWord (width : WordWidth) (value : Nat) : Nat := value % width.modulus

def evalWordBin (width : WordWidth) : WordBinOp → Nat → Nat → Nat
  | .add, left, right => (left + right) % width.modulus
  | .sub, left, right =>
      (left % width.modulus + width.modulus - right % width.modulus) % width.modulus
  | .mul, left, right => (left * right) % width.modulus
  | .div, left, right => left / right
  | .mod, left, right => left % right
  | .min, left, right => Nat.min left right
  | .max, left, right => Nat.max left right

variable {source target width : WordWidth} {left right value : Nat} {operation : WordBinOp}

theorem WordWidth.modulus_le_nat64 (width : WordWidth) : width.modulus ≤ nat64Limit := by
  cases width <;> decide

theorem normalizeWord_eq : normalizeWord width value = value % width.modulus := rfl

theorem normalizeWord_bounded : normalizeWord width value < width.modulus :=
  Nat.mod_lt _ width.modulus_pos

theorem normalizeWord_eq_self_iff : normalizeWord width value = value ↔ value < width.modulus := by
  constructor
  · intro same
    have bounded := normalizeWord_bounded (width := width) (value := value)
    rw [same] at bounded
    exact bounded
  · exact Nat.mod_eq_of_lt

theorem normalizeWord_idempotent : normalizeWord width (normalizeWord width value) =
    normalizeWord width value :=
  normalizeWord_eq_self_iff.mpr normalizeWord_bounded

theorem normalizeWord_widen (bounded : value < source.modulus)
    (ordered : source.bits ≤ target.bits) : normalizeWord target value = value :=
  normalizeWord_eq_self_iff.mpr (Nat.lt_of_lt_of_le bounded (WordWidth.modulus_mono ordered))

theorem normalizeWord_roundtrip (bounded : value < source.modulus)
    (ordered : source.bits ≤ target.bits) :
    normalizeWord source (normalizeWord target value) = value := by
  rw [normalizeWord_widen bounded ordered]
  exact normalizeWord_eq_self_iff.mpr bounded

theorem wordToNat_bounded (bounded : value < width.modulus) : value < nat64Limit :=
  Nat.lt_of_lt_of_le bounded width.modulus_le_nat64

theorem evalWordBin_bounded (leftBound : left < width.modulus)
    (rightBound : right < width.modulus) : evalWordBin width operation left right < width.modulus := by
  cases operation with
  | add | sub | mul => exact Nat.mod_lt _ width.modulus_pos
  | div => exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound
  | mod =>
      cases right with
      | zero => simpa [evalWordBin] using leftBound
      | succ right => exact Nat.lt_trans (Nat.mod_lt _ (Nat.zero_lt_succ _)) rightBound
  | min => exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) leftBound
  | max => exact Nat.max_lt.mpr ⟨leftBound, rightBound⟩

theorem evalWordBin_add_eq : evalWordBin width .add left right =
    (left + right) % width.modulus := rfl

theorem evalWordBin_add_no_wrap (bounded : left + right < width.modulus) :
    evalWordBin width .add left right = left + right := Nat.mod_eq_of_lt bounded

theorem evalWordBin_add_wrap (leftBound : left < width.modulus)
    (rightBound : right < width.modulus) (wrapped : width.modulus ≤ left + right) :
    evalWordBin width .add left right = left + right - width.modulus := by
  change (left + right) % width.modulus = left + right - width.modulus
  rw [Nat.mod_eq_sub_mod wrapped]
  exact Nat.mod_eq_of_lt
    (Nat.sub_lt_left_of_lt_add wrapped (Nat.add_lt_add leftBound rightBound))

theorem evalWordBin_sub_eq : evalWordBin width .sub left right =
    (left % width.modulus + width.modulus - right % width.modulus) % width.modulus := rfl

theorem evalWordBin_sub_no_underflow (leftBound : left < width.modulus)
    (rightBound : right < width.modulus) (ordered : right ≤ left) :
    evalWordBin width .sub left right = left - right := by
  simp only [evalWordBin, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]
  have same : left + width.modulus - right = (left - right) + width.modulus :=
    Nat.sub_add_comm ordered
  rw [same, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) leftBound)

theorem evalWordBin_sub_underflow (leftBound : left < width.modulus)
    (rightBound : right < width.modulus) (ordered : left < right) :
    evalWordBin width .sub left right = width.modulus - (right - left) := by
  simp only [evalWordBin, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]
  have rightLe : right ≤ width.modulus := Nat.le_of_lt rightBound
  have belowSum : right ≤ left + width.modulus :=
    Nat.le_trans rightLe (Nat.le_add_left _ _)
  have belowModulus : left + width.modulus - right < width.modulus :=
    Nat.sub_lt_left_of_lt_add belowSum (Nat.add_lt_add_right ordered _)
  rw [Nat.mod_eq_of_lt belowModulus, Nat.add_sub_assoc rightLe]
  apply Eq.symm
  apply (Nat.sub_eq_iff_eq_add (Nat.le_trans (Nat.sub_le right left) rightLe)).mpr
  calc
    width.modulus = (width.modulus - right) + right := (Nat.sub_add_cancel rightLe).symm
    _ = (width.modulus - right) + (left + (right - left)) := by
      rw [Nat.add_sub_cancel' (Nat.le_of_lt ordered)]
    _ = (left + (width.modulus - right)) + (right - left) := by
      rw [← Nat.add_assoc, Nat.add_comm (width.modulus - right) left]

theorem evalWordBin_mul_eq : evalWordBin width .mul left right =
    (left * right) % width.modulus := rfl

theorem evalWordBin_mul_no_wrap (bounded : left * right < width.modulus) :
    evalWordBin width .mul left right = left * right := Nat.mod_eq_of_lt bounded

theorem evalWordBin_div_eq : evalWordBin width .div left right = left / right := rfl

theorem evalWordBin_mod_eq : evalWordBin width .mod left right = left % right := rfl

theorem evalWordBin_div_zero : evalWordBin width .div left 0 = 0 := by simp [evalWordBin]

theorem evalWordBin_mod_zero : evalWordBin width .mod left 0 = left := by simp [evalWordBin]

/-- Reconstruction also holds at zero under the explicitly total division convention. -/
theorem evalWordBin_div_mod :
    right * evalWordBin width .div left right + evalWordBin width .mod left right = left :=
  Nat.div_add_mod _ _

theorem evalWordBin_min_left (ordered : left ≤ right) :
    evalWordBin width .min left right = left := Nat.min_eq_left ordered

theorem evalWordBin_min_right (ordered : right ≤ left) :
    evalWordBin width .min left right = right := Nat.min_eq_right ordered

theorem evalWordBin_max_left (ordered : right ≤ left) :
    evalWordBin width .max left right = left := Nat.max_eq_left ordered

theorem evalWordBin_max_right (ordered : left ≤ right) :
    evalWordBin width .max left right = right := Nat.max_eq_right ordered

end LeanExe.TypeSafety
