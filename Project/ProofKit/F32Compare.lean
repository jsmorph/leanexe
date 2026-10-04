import Project.ProofKit.F32Add

/-!
Lean's comparisons of binary32 values agree with Talos's `IEEE32.lt`, `le`, and
`eq`, which compare values in units of `2^-149`.  Decoding a non-NaN bit
pattern gives a canonical unpacked float, and Lean's `UnpackedFloat.compare` on
canonical floats orders them by value.
-/

namespace Project.ProofKit.F32Compare
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32AddFinite F32Decoded
  FloatCommon

/-- The value of an unpacked float in units of `2^-149`, with the infinities
at `±2^277`, beyond every finite binary32 magnitude. -/
def value : UnpackedFloat → Int
  | .notANumber => 0
  | .infinity s => s.apply ((2 ^ 277 : Nat) : Int)
  | .zero _ => 0
  | .finite s m e _ => s.apply ((m * 2 ^ (e + 149).toNat : Nat) : Int)

/-- A finite binary32 mantissa and exponent: subnormal at the least exponent,
or normal. -/
def CanonicalFinite (m : Nat) (e : Int) : Prop :=
  -149 ≤ e ∧ e ≤ 104 ∧ m < 2 ^ 24 ∧ (e = -149 ∨ 2 ^ 23 ≤ m)

def Canonical : UnpackedFloat → Prop
  | .notANumber => False
  | .infinity _ => True
  | .zero _ => True
  | .finite _ m e _ => CanonicalFinite m e

theorem finite_lt_top {m : Nat} {e : Int} (h : CanonicalFinite m e) :
    m * 2 ^ (e + 149).toNat < 2 ^ 277 := by
  obtain ⟨hlo, hhi, hm, -⟩ := h
  calc m * 2 ^ (e + 149).toNat < 2 ^ 24 * 2 ^ (e + 149).toNat :=
        Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    _ ≤ 2 ^ 24 * 2 ^ 253 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 2 ^ 277 := by rw [← pow_add]

theorem decode_canonical (x : UInt32) (hx : Wasm.IEEE32.isNaN x = false) :
    Canonical (decode x) ∧ value (decode x) = Wasm.IEEE32.scaledValue x := by
  by_cases hi : Wasm.IEEE32.isInfinite x = true
  · rw [F32Add.decode_infinite x hi]
    refine ⟨trivial, ?_⟩
    simp only [Wasm.IEEE32.isInfinite, Bool.and_eq_true, beq_iff_eq] at hi
    have hm : Wasm.IEEE32.scaledMagnitude x = 2 ^ 277 := by
      unfold Wasm.IEEE32.scaledMagnitude
      simp only [hi.1, hi.2]
      rw [show (2 : Nat) ^ 277 = 2 ^ 23 * 2 ^ 254 by rw [← pow_add]]
      norm_num
    simp only [value, Wasm.IEEE32.scaledValue, hm, sourceSign]
    cases Wasm.IEEE32.sign x <;> rfl
  · have hi' : Wasm.IEEE32.isInfinite x = false := Bool.eq_false_iff.mpr hi
    have he := F32Add.exponent_ne x hx hi'
    by_cases hz : Wasm.IEEE32.scaledMagnitude x = 0
    · rw [F32Add.decode_zero x hz, F32Add.zero_value x hz]
      exact ⟨trivial, rfl⟩
    · rw [decode_finite x he hz]
      refine ⟨?_, scaled_value x⟩
      have hf := CodeLib.IEEE32.fraction_lt x
      have hel := CodeLib.IEEE32.exponent_lt x
      show CanonicalFinite (mantissa x) (exponent x)
      unfold CanonicalFinite mantissa exponent
      split <;> omega

theorem compare_ext {α β : Type} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (hlt : a < b ↔ c < d) (heq : a = b ↔ c = d) : compare a b = compare c d := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (hlt.mp h)]
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (heq.mp h)]
  · have h1 : ¬ c < d := fun h' => lt_asymm h (hlt.mpr h')
    have h2 : c ≠ d := fun h' => ne_of_gt h (heq.mpr h')
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))]

/-- Ordering canonical finite values lexicographically by exponent and then
mantissa orders them by magnitude. -/
theorem lex_compare {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₁ : CanonicalFinite m₁ e₁)
    (h₂ : CanonicalFinite m₂ e₂) :
    (compare e₁ e₂).then (compare m₁ m₂) =
      compare (m₁ * 2 ^ (e₁ + 149).toNat) (m₂ * 2 ^ (e₂ + 149).toNat) := by
  have below : ∀ {m m' : Nat} {e e' : Int}, CanonicalFinite m e → CanonicalFinite m' e' →
      e < e' → m * 2 ^ (e + 149).toNat < m' * 2 ^ (e' + 149).toNat := by
    intro m m' e e' h h' hlt
    obtain ⟨hlo, -, hm, -⟩ := h
    obtain ⟨-, -, -, hnorm⟩ := h'
    have hm' : 2 ^ 23 ≤ m' := by rcases hnorm with h | h <;> omega
    obtain ⟨d, hd⟩ : ∃ d, (e' + 149).toNat = (e + 149).toNat + 1 + d := ⟨(e' - e - 1).toNat, by omega⟩
    rw [hd, pow_add, pow_add]
    calc m * 2 ^ (e + 149).toNat < 2 ^ 24 * 2 ^ (e + 149).toNat :=
          Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
      _ = 2 ^ 23 * (2 ^ (e + 149).toNat * 2 ^ 1) := by ring
      _ ≤ m' * (2 ^ (e + 149).toNat * 2 ^ 1) := Nat.mul_le_mul_right _ hm'
      _ ≤ m' * (2 ^ (e + 149).toNat * 2 ^ 1 * 2 ^ d) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos d))
  rcases lt_trichotomy e₁ e₂ with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (below h₁ h₂ h)]
    rfl
  · rw [compare_eq_iff_eq.mpr rfl]
    exact compare_ext (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).symm
      (Nat.mul_left_inj (Nat.two_pow_pos _).ne').symm
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (below h₂ h₁ h)]
    rfl

theorem compare_natCast (a b : Nat) : compare (a : Int) (b : Int) = compare a b :=
  compare_ext Int.ofNat_lt (Int.ofNat_inj)

theorem compare_neg (a b : Int) : compare (-a) (-b) = (compare a b).swap := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (by omega)]
    rfl
  · rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
    rfl
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (by omega)]
    rfl

/-- Lean's comparison of canonical unpacked floats is the comparison of their
values. -/
theorem compare_canonical (a b : UnpackedFloat) (ha : Canonical a) (hb : Canonical b) :
    a.compare b = some (compare (value a) (value b)) := by
  have hTop : (0 : Int) < ((2 ^ 277 : Nat) : Int) := by positivity
  cases a with
  | notANumber => exact ha.elim
  | infinity s =>
      cases b with
      | notANumber => exact hb.elim
      | infinity t =>
          cases s <;> cases t <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_eq_iff_eq.mpr rfl).symm
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
      | zero t =>
          cases s <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
      | finite t m e hm =>
          have htop := finite_lt_top hb
          have hpos : 0 < m * 2 ^ (e + 149).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
          cases s <;> cases t <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
  | zero s =>
      cases b with
      | notANumber => exact hb.elim
      | infinity t =>
          cases t <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
      | zero t => exact congrArg some (compare_eq_iff_eq.mpr rfl).symm
      | finite t m e hm =>
          have hpos : 0 < m * 2 ^ (e + 149).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
          cases t <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
  | finite s m e hm =>
      have htop := finite_lt_top ha
      have hpos : 0 < m * 2 ^ (e + 149).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
      cases b with
      | notANumber => exact hb.elim
      | infinity t =>
          cases s <;> cases t <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
      | zero t =>
          cases s <;> simp only [UnpackedFloat.compare, value, Sign.apply] <;>
            first
            | exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
            | exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
      | finite t m' e' hm' =>
          have hpos' : 0 < m' * 2 ^ (e' + 149).toNat := Nat.mul_pos hm' (Nat.two_pow_pos _)
          cases s <;> cases t <;> simp only [UnpackedFloat.compare, value, Sign.apply]
          · rw [lex_compare ha hb, compare_neg, compare_natCast]
          · exact congrArg some (compare_lt_iff_lt.mpr (by omega)).symm
          · exact congrArg some (compare_gt_iff_gt.mpr (by omega)).symm
          · rw [lex_compare ha hb, compare_natCast]

theorem compare_bits (x y : UInt32) :
    (decode x).compare (decode y) =
      if Wasm.IEEE32.isNaN x || Wasm.IEEE32.isNaN y then none
      else some (compare (Wasm.IEEE32.scaledValue x) (Wasm.IEEE32.scaledValue y)) := by
  by_cases hx : Wasm.IEEE32.isNaN x = true
  · rw [decode_nan x hx]
    simp [hx, UnpackedFloat.compare]
  by_cases hy : Wasm.IEEE32.isNaN y = true
  · rw [decode_nan y hy]
    cases decode x <;> simp [hy, UnpackedFloat.compare]
  have hx' := Bool.eq_false_iff.mpr hx
  have hy' := Bool.eq_false_iff.mpr hy
  obtain ⟨hcx, hvx⟩ := decode_canonical x hx'
  obtain ⟨hcy, hvy⟩ := decode_canonical y hy'
  rw [compare_canonical _ _ hcx hcy, hvx, hvy]
  simp [hx', hy']

theorem lt_bits (x y : UInt32) :
    (Float32.Model.ofBits x).lt (Float32.Model.ofBits y) = Wasm.IEEE32.lt x y := by
  simp only [Float32.Model.lt, unpack_ofBits, UnpackedFloat.lt, compare_bits, Wasm.IEEE32.lt]
  split
  · rfl
  · rcases lt_trichotomy (Wasm.IEEE32.scaledValue x) (Wasm.IEEE32.scaledValue y) with h | h | h
    · simp [compare_lt_iff_lt.mpr h, h]
    · simp [h]
    · simp [compare_gt_iff_gt.mpr h, not_lt.mpr h.le]

theorem le_bits (x y : UInt32) :
    (Float32.Model.ofBits x).le (Float32.Model.ofBits y) = Wasm.IEEE32.le x y := by
  simp only [Float32.Model.le, unpack_ofBits, UnpackedFloat.le, compare_bits, Wasm.IEEE32.le]
  split
  · rfl
  · simp only [Option.any_some]
    rcases lt_trichotomy (Wasm.IEEE32.scaledValue x) (Wasm.IEEE32.scaledValue y) with h | h | h
    · simp [compare_lt_iff_lt.mpr h, h.le]
    · simp [h]
    · simp [compare_gt_iff_gt.mpr h, not_le.mpr h]

theorem beq_bits (x y : UInt32) :
    (Float32.Model.ofBits x).beq (Float32.Model.ofBits y) = Wasm.IEEE32.eq x y := by
  simp only [Float32.Model.beq, unpack_ofBits, UnpackedFloat.beq, compare_bits, Wasm.IEEE32.eq]
  split <;> simp

end Project.ProofKit.F32Compare
