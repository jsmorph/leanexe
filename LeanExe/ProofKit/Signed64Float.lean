import LeanExe.ProofKit.Signed64
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64NegateOps
import LeanExe.ProofKit.F32Convert
import LeanExe.ProofKit.F32Negate
import LeanExe.ProofKit.F32TruncSat

/-!
The word forms of Lean's conversions between `Int64` and the floats, over the unsigned conversions,
and their equations.

`Int64.toFloat a` rounds the integer `a.toInt` to binary64 in Lean's model: `Float.Model.ofInt`
calls `UnpackedFloat.normalize`, which rounds the magnitude to nearest with ties to even and
attaches the sign afterwards.  Rounding therefore commutes with negation, and the word form
`toFloat` converts the magnitude with `UInt64.toFloat` and negates the result when the sign bit is
set.  The magnitude is the word `0 - w`, which for `minValue` is `2 ^ 63` read unsigned.  The proof
does not assume the symmetry: `F64Convert.ofInt_eq` equates the model with Talos's `fromInt`, which
rounds the magnitude and packs it with the sign, and `fromInt_neg` proves from
`F64NegateOps.negate_roundScaledMagnitude` that the rounding of `-n` is the negation of the rounding
of `n` for every positive `n`.  `toFloat32` and `fromInt32_neg` do the same at binary32, where
`UInt64.toFloat32` rounds the 64-bit magnitude once.

`Float.toInt64 x` truncates toward zero and saturates: it is `Int64.ofIntClamp` of the model's
truncated integer, with `minValue` for negative infinity, `maxValue` for positive infinity, and 0
for NaN.  The word form `ofFloat` uses `Float.toUInt64`, which truncates and saturates at
`[0, 2 ^ 64 - 1]`: for `x < 0` it negates the truncation of `-x` saturated at `2 ^ 63`, and
otherwise it saturates the truncation of `x` at `2 ^ 63 - 1`.  NaN and both zeros take the second
branch, where `Float.toUInt64` gives 0.  `toInt64_unpacked` proves the equation once over Lean's
unpacked floats, for both formats, and `ofFloat_eq` and `ofFloat32_eq` apply it.

The last section states the equations in the forms that the reflector takes.
-/

namespace LeanExe.ProofKit.Signed64

open Float.Model Float.Model.UnpackedFloat

/-! ## Signed integers to floats -/

/-- `Int64.toFloat` on the word: the unsigned conversion of the magnitude, negated when the sign
bit is set.  The form is the one that the ports of optimized-routines write by hand, such as
`Library.Numerics.Float64.Log`. -/
@[inline] def toFloat (w : UInt64) : Float :=
  if w >>> 63 == 1 then -((0 - w).toFloat) else w.toFloat

/-- `Int64.toFloat32` on the word, as `toFloat`. -/
@[inline] def toFloat32 (w : UInt64) : Float32 :=
  if w >>> 63 == 1 then -((0 - w).toFloat32) else w.toFloat32

/-- The integer of an `Int64` whose sign bit is clear is the natural number of its word. -/
theorem toInt_of_msb_false (a : Int64) (h : a.toUInt64.toBitVec.msb = false) :
    a.toInt = (a.toUInt64.toNat : Int) := by
  have hb := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  have hn : a.toUInt64.toBitVec.toNat = a.toUInt64.toNat := rfl
  rw [toInt_cond, ite_eq_left (by omega)]

/-- The integer of an `Int64` whose sign bit is set is the negation of the positive natural number
of `0 - w`. -/
theorem toInt_of_msb_true (a : Int64) (h : a.toUInt64.toBitVec.msb = true) :
    a.toInt = -((0 - a.toUInt64).toNat : Int) ∧ 0 < (0 - a.toUInt64).toNat := by
  have hb := BitVec.msb_eq_true_iff_two_mul_ge.mp h
  have hn : a.toUInt64.toBitVec.toNat = a.toUInt64.toNat := rfl
  have hlt := a.toUInt64.toNat_lt
  have hs : (0 - a.toUInt64).toNat = 18446744073709551616 - a.toUInt64.toNat := by
    rw [UInt64.toNat_sub]
    simp only [UInt64.toNat_zero, Nat.reducePow, Nat.add_zero]
    omega
  rw [toInt_cond, ite_eq_right (by omega), hs]
  omega

theorem float_ext {x y : Float} (h : x.toBits = y.toBits) : x = y := by
  rw [← F64Bits.ofBits_toBits x, ← F64Bits.ofBits_toBits y, h]

theorem float32_ext {x y : Float32} (h : x.toBits = y.toBits) : x = y := by
  rw [← F32Bits.ofBits_toBits x, ← F32Bits.ofBits_toBits y, h]

/-- Talos's `fromInt` rounds the magnitude and packs it with the sign, so the rounding of `-n` is
the negation of the rounding of `n` for every positive `n`. -/
theorem fromInt_neg (n : Nat) (hn : 0 < n) :
    Wasm.IEEE64.fromInt (-(n : Int)) = Wasm.IEEE64.negate (Wasm.IEEE64.fromInt n) := by
  unfold Wasm.IEEE64.fromInt
  have h1 : decide (-(n : Int) < 0) = true := by simp only [decide_eq_true_eq]; omega
  have h2 : decide ((n : Int) < 0) = false := by simp only [decide_eq_false_iff_not]; omega
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_natCast, F64NegateOps.negate_roundScaledMagnitude]
  rfl

theorem fromInt32_neg (n : Nat) (hn : 0 < n) :
    Wasm.IEEE32.fromInt (-(n : Int)) = Wasm.IEEE32.negate (Wasm.IEEE32.fromInt n) := by
  unfold Wasm.IEEE32.fromInt
  have h1 : decide (-(n : Int) < 0) = true := by simp only [decide_eq_true_eq]; omega
  have h2 : decide ((n : Int) < 0) = false := by simp only [decide_eq_false_iff_not]; omega
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_natCast, F32Negate.negate_roundScaledMagnitude]
  rfl

/-- Lean's `Int64.toFloat` is Talos's `fromInt` of the integer. -/
theorem toBits_int64ToFloat (a : Int64) : a.toFloat.toBits = Wasm.IEEE64.fromInt a.toInt := by
  change (Float.Model.ofInt a.toInt).toBits = _
  exact F64Convert.ofInt_eq _

theorem toBits_int64ToFloat32 (a : Int64) :
    a.toFloat32.toBits = Wasm.IEEE32.fromInt a.toInt := by
  change (Float32.Model.ofInt a.toInt).toBits = _
  exact F32Convert.ofInt_eq _

theorem toBits_uint64ToFloat32 (w : UInt64) :
    w.toFloat32.toBits = Wasm.IEEE32.fromInt (w.toNat : Int) := by
  change (Float32.Model.ofInt (w.toNat : Int)).toBits = _
  exact F32Convert.ofInt_eq _

theorem toFloat_eq (a : Int64) : a.toFloat = toFloat a.toUInt64 := by
  apply float_ext
  unfold toFloat
  rw [shr63]
  cases h : a.toUInt64.toBitVec.msb
  · have h01 : ((0 : UInt64) == 1) = false := by decide
    simp only [Bool.false_eq_true, ite_false, h01]
    rw [toBits_int64ToFloat, F64Convert.toBits_toFloat, toInt_of_msb_false a h]
    rfl
  · simp only [ite_true, beq_self_eq_true]
    obtain ⟨hv, hpos⟩ := toInt_of_msb_true a h
    have hn : Wasm.IEEE64.negate (Wasm.IEEE64.convertI64U (0 - a.toUInt64)) = a.toFloat.toBits := by
      rw [toBits_int64ToFloat, hv, fromInt_neg _ hpos]
      rfl
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, F64Convert.toBits_toFloat,
      ← F64Sign.isNaN_negate (Wasm.IEEE64.convertI64U (0 - a.toUInt64)), hn,
      F64Bits.toBits_canonical]

theorem toFloat32_eq (a : Int64) : a.toFloat32 = toFloat32 a.toUInt64 := by
  apply float32_ext
  unfold toFloat32
  rw [shr63]
  cases h : a.toUInt64.toBitVec.msb
  · have h01 : ((0 : UInt64) == 1) = false := by decide
    simp only [Bool.false_eq_true, ite_false, h01]
    rw [toBits_int64ToFloat32, toBits_uint64ToFloat32, toInt_of_msb_false a h]
  · simp only [ite_true, beq_self_eq_true]
    obtain ⟨hv, hpos⟩ := toInt_of_msb_true a h
    have hn : Wasm.IEEE32.negate (Wasm.IEEE32.fromInt ((0 - a.toUInt64).toNat : Int)) =
        a.toFloat32.toBits := by
      rw [toBits_int64ToFloat32, hv, fromInt32_neg _ hpos]
    rw [F32Bits.toBits_neg, F32Sign.sub_negZero, toBits_uint64ToFloat32,
      ← F32Sign.isNaN_negate (Wasm.IEEE32.fromInt ((0 - a.toUInt64).toNat : Int)), hn,
      F32Bits.toBits_canonical]

/-! ## Floats to signed integers -/

/-- `Float.toInt64` on words: the truncation of `-x` saturated at `2 ^ 63` and negated for
`x < 0`, and otherwise the truncation of `x` saturated at `2 ^ 63 - 1`. -/
@[inline] def ofFloat (x : Float) : UInt64 :=
  if x < 0 then 0 - min (-x).toUInt64 M else min x.toUInt64 (M - 1)

/-- `Float32.toInt64` on words, as `ofFloat`. -/
@[inline] def ofFloat32 (x : Float32) : UInt64 :=
  if x < 0 then 0 - min (-x).toUInt64 M else min x.toUInt64 (M - 1)

theorem toNat_min (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    omega
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    omega

theorem ofNatClamp_toNat (q : Nat) :
    (UInt64.ofNatClamp q).toNat = min q 18446744073709551615 := by
  have hs : UInt64.size = 18446744073709551616 := rfl
  unfold UInt64.ofNatClamp
  split
  · rw [UInt64.toNat_ofNatLT]
    omega
  · rw [UInt64.toNat_ofNatLT]
    omega

/-- Lean's clamp of a natural number into `Int64`, on words: the clamp into `UInt64` saturated at
`2 ^ 63 - 1`. -/
theorem ofIntClamp_nat (q : Nat) :
    (Int64.ofIntClamp (q : Int)).toUInt64 = min (UInt64.ofNatClamp q) (M - 1) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_min, ofNatClamp_toNat]
  have hM : (M - 1).toNat = 9223372036854775807 := rfl
  have hmin : Int64.minValue.toInt = -9223372036854775808 := by decide
  have hmax : Int64.maxValue.toInt = 9223372036854775807 := by decide
  rw [hM]
  unfold Int64.ofIntClamp
  split
  · split
    · rename_i h1 h2
      rw [hmax] at h2
      show (BitVec.ofInt 64 (q : Int)).toNat = _
      rw [BitVec.toNat_ofInt]
      have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by norm_num
      rw [h64, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
      omega
    · rename_i h1 h2
      rw [hmax] at h2
      show (9223372036854775807 : Nat) = _
      omega
  · rename_i h1
    rw [hmin] at h1
    omega

/-- Lean's clamp of the negation of a natural number into `Int64`, on words: the negation of the
clamp into `UInt64` saturated at `2 ^ 63`. -/
theorem ofIntClamp_neg (q : Nat) :
    (Int64.ofIntClamp (-(q : Int))).toUInt64 = 0 - min (UInt64.ofNatClamp q) M := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub, toNat_min, ofNatClamp_toNat]
  have hM : M.toNat = 9223372036854775808 := rfl
  have hmin : Int64.minValue.toInt = -9223372036854775808 := by decide
  have hmax : Int64.maxValue.toInt = 9223372036854775807 := by decide
  rw [hM]
  simp only [UInt64.toNat_zero, Nat.reducePow, Nat.add_zero]
  unfold Int64.ofIntClamp
  split
  · split
    · rename_i h1 h2
      rw [hmin] at h1
      show (BitVec.ofInt 64 (-(q : Int))).toNat = _
      rw [BitVec.toNat_ofInt]
      have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by norm_num
      rw [h64]
      omega
    · rename_i h1 h2
      rw [hmax] at h2
      omega
  · rename_i h1
    rw [hmin] at h1
    show (9223372036854775808 : Nat) = _
    omega

/-- The equation of the word form over Lean's unpacked floats, for both formats: Lean's
`toInt64` of `u` is the word that the unsigned truncations of `u` and of its negation give. -/
theorem toInt64_unpacked (u : UnpackedFloat) :
    u.toInt64.toUInt64 =
      if u.lt (.zero .positive) then 0 - min u.neg.toUInt64 M else min u.toUInt64 (M - 1) := by
  cases u with
  | notANumber => decide +kernel
  | infinity s => cases s <;> decide +kernel
  | zero s => cases s <;> decide +kernel
  | finite s m e hm =>
    cases s
    · have hl : (UnpackedFloat.finite .negative m e hm).lt (.zero .positive) = true := rfl
      rw [ite_eq_left hl]
      show (Int64.ofIntClamp (roundToInt .negative m e)).toUInt64 =
        0 - min (UInt64.ofNatClamp (roundToInt .positive m e).toNat) M
      rw [F32TruncSat.roundToInt_eq, F32TruncSat.roundToInt_eq]
      exact ofIntClamp_neg _
    · have hl : (UnpackedFloat.finite .positive m e hm).lt (.zero .positive) = false := rfl
      rw [ite_eq_right (by rw [hl]; decide)]
      show (Int64.ofIntClamp (roundToInt .positive m e)).toUInt64 =
        min (UInt64.ofNatClamp (roundToInt .positive m e).toNat) (M - 1)
      rw [F32TruncSat.roundToInt_eq]
      exact ofIntClamp_nat _

theorem unpack_neg (x : Float) : (-x).toModel.unpack = x.toModel.unpack.neg := by
  show (Float.Model.pack x.toModel.unpack.neg).unpack = _
  rw [F64Bits.toModel_eq, F64Packing.unpack_ofBits, ← F64Sub.decode_negate]
  have h : Float.Model.pack (F64Encoding.decode (Wasm.IEEE64.negate x.toBits)) =
      Float.Model.ofBits (Wasm.IEEE64.negate x.toBits) := by
    unfold Float.Model.ofBits
    rw [F64Encoding.unpack_eq]
  rw [h, F64Packing.unpack_ofBits]

theorem unpack_neg32 (x : Float32) : (-x).toModel.unpack = x.toModel.unpack.neg := by
  show (Float32.Model.pack x.toModel.unpack.neg).unpack = _
  rw [F32Bits.toModel_eq, F32Packing.unpack_ofBits, ← F32Sub.decode_negate]
  have h : Float32.Model.pack (F32Encoding.decode (Wasm.IEEE32.negate x.toBits)) =
      Float32.Model.ofBits (Wasm.IEEE32.negate x.toBits) := by
    unfold Float32.Model.ofBits
    rw [F32Encoding.unpack_eq]
  rw [h, F32Packing.unpack_ofBits]

theorem decide_lt_zero (x : Float) :
    decide (x < 0) = x.toModel.unpack.lt (.zero .positive) := by
  have h0 : (0 : Float).toModel.unpack = .zero .positive := by
    rw [F64Bits.toModel_eq, F64Packing.unpack_ofBits]
    have hb : (0 : Float).toBits = 0 := by decide +kernel
    rw [hb]
    rfl
  show decide (x.lt 0 = true) = _
  simp only [Float.lt, decide_eq_true_eq]
  show decide (x.toModel.unpack.lt (0 : Float).toModel.unpack = true) = _
  rw [h0]
  cases x.toModel.unpack.lt (.zero .positive) <;> rfl

theorem decide_lt_zero32 (x : Float32) :
    decide (x < 0) = x.toModel.unpack.lt (.zero .positive) := by
  have h0 : (0 : Float32).toModel.unpack = .zero .positive := by
    rw [F32Bits.toModel_eq, F32Packing.unpack_ofBits]
    have hb : (0 : Float32).toBits = 0 := by decide +kernel
    rw [hb]
    rfl
  show decide (x.lt 0 = true) = _
  simp only [Float32.lt, decide_eq_true_eq]
  show decide (x.toModel.unpack.lt (0 : Float32).toModel.unpack = true) = _
  rw [h0]
  cases x.toModel.unpack.lt (.zero .positive) <;> rfl

theorem ofFloat_eq (x : Float) : x.toInt64.toUInt64 = ofFloat x := by
  show x.toModel.unpack.toInt64.toUInt64 = _
  rw [toInt64_unpacked]
  unfold ofFloat
  have hd := decide_lt_zero x
  by_cases h : x < 0
  · rw [ite_eq_left h, ite_eq_left (by rw [← hd]; simpa using h)]
    show _ = 0 - min (-x).toModel.unpack.toUInt64 M
    rw [unpack_neg]
  · rw [ite_eq_right h, ite_eq_right (by rw [← hd]; simpa using h)]
    rfl

theorem ofFloat32_eq (x : Float32) : x.toInt64.toUInt64 = ofFloat32 x := by
  show x.toModel.unpack.toInt64.toUInt64 = _
  rw [toInt64_unpacked]
  unfold ofFloat32
  have hd := decide_lt_zero32 x
  by_cases h : x < 0
  · rw [ite_eq_left h, ite_eq_left (by rw [← hd]; simpa using h)]
    show _ = 0 - min (-x).toModel.unpack.toUInt64 M
    rw [unpack_neg32]
  · rw [ite_eq_right h, ite_eq_right (by rw [← hd]; simpa using h)]
    rfl

/-! ## The reflector's forms -/

theorem toFloat_word (a : Int64) : toFloat a.toUInt64 = a.toFloat := (toFloat_eq a).symm

theorem toFloat32_word (a : Int64) : toFloat32 a.toUInt64 = a.toFloat32 := (toFloat32_eq a).symm

theorem ofFloat_word (x : Float) : Int64.ofUInt64 (ofFloat x) = x.toInt64 :=
  congrArg Int64.ofUInt64 (ofFloat_eq x).symm

theorem ofFloat32_word (x : Float32) : Int64.ofUInt64 (ofFloat32 x) = x.toInt64 :=
  congrArg Int64.ofUInt64 (ofFloat32_eq x).symm

#print axioms toFloat_eq
#print axioms toFloat32_eq
#print axioms ofFloat_eq
#print axioms ofFloat32_eq

end LeanExe.ProofKit.Signed64
