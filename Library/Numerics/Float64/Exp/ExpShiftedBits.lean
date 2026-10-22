import Library.Numerics.Float64.Exp.ExpIntegerSelection
import LeanExe.ProofKit.F64Packing

namespace Library.Numerics.Float64.Exp.ExpShiftedBits
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem integer_binade_word (w : UInt64) (q : Nat)
    (hs : Wasm.IEEE64.sign w = false)
    (hv : Wasm.IEEE64.scaledValue w = (q : Int) * 2 ^ 1074)
    (hql : 2 ^ 52 ≤ q) (hqu : q < 2 ^ 53) :
    w = Wasm.IEEE64.encodeFinite false 1075 (q - 2 ^ 52) := by
  have hq0 : q ≠ 0 := by omega
  have hmagI : (Wasm.IEEE64.scaledMagnitude w : Int) = (q : Int) * 2 ^ 1074 := by
    simpa only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false] using hv
  have hm : Wasm.IEEE64.scaledMagnitude w = q * 2 ^ 1074 := by exact_mod_cast hmagI
  have hqlog : Nat.log2 q = 52 := (Nat.log2_eq_iff hq0).mpr ⟨hql, hqu⟩
  have hmlog : Nat.log2 (Wasm.IEEE64.scaledMagnitude w) = 1126 := by
    rw [hm, F64DyadicBounds.log2_mul_two_pow q 1074 hq0, hqlog]
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have h0 : Wasm.IEEE64.exponent w ≠ 0 := by
    intro he
    have hmf : Wasm.IEEE64.scaledMagnitude w = Wasm.IEEE64.fraction w := by
      simp [Wasm.IEEE64.scaledMagnitude, he]
    have hm0 : Wasm.IEEE64.scaledMagnitude w ≠ 0 := by rw [hm]; positivity
    have hflog : Nat.log2 (Wasm.IEEE64.fraction w) < 52 :=
      (Nat.log2_lt (by rwa [← hmf])).mpr hf
    rw [hmf] at hmlog
    omega
  have hsig : 2 ^ 52 + Wasm.IEEE64.fraction w ≠ 0 := by positivity
  have hsiglog : Nat.log2 (2 ^ 52 + Wasm.IEEE64.fraction w) = 52 :=
    (Nat.log2_eq_iff hsig).mpr ⟨by omega, by omega⟩
  have hmlog' : Nat.log2 (Wasm.IEEE64.scaledMagnitude w) =
      52 + (Wasm.IEEE64.exponent w - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, h0, ite_false]
    rw [F64DyadicBounds.log2_mul_two_pow _ _ hsig, hsiglog]
  have he : Wasm.IEEE64.exponent w = 1075 := by omega
  have hmag' : Wasm.IEEE64.scaledMagnitude w =
      (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ 1074 := by
    simp [Wasm.IEEE64.scaledMagnitude, he]
  rw [hmag'] at hm
  have hfrac : Wasm.IEEE64.fraction w = q - 2 ^ 52 := by
    have hsum := (Nat.mul_left_inj (by positivity : (2 : Nat) ^ 1074 ≠ 0)).mp hm
    omega
  simpa only [hs, he, hfrac] using (F64Packing.encode_fields w).symm

#print axioms integer_binade_word

private theorem integer_encoding_toNat (q : Nat) (hql : 2 ^ 52 ≤ q) (hqu : q < 2 ^ 53) :
    (Wasm.IEEE64.encodeFinite false 1075 (q - 2 ^ 52)).toNat =
      1075 * 2 ^ 52 + (q - 2 ^ 52) := by
  simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add,
    UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

private theorem magic_bits_identity (q : Nat) (hql : 2 ^ 52 ≤ q) :
    ((1075 * 2 ^ 52 + (q - 2 ^ 52) : Nat) : Int) =
      (0x4338000000000000 : Int) + ((q : Int) - 3 * 2 ^ 51) := by
  omega

theorem shifted_encoding (z : UInt64) (hzf : Finite z) (hz : |value z| ≤ (2 : ℝ) ^ 18) :
    ∃ k : Int, Finite (ExpIntegerSelection.selected z) ∧
      Wasm.IEEE64.scaledValue (ExpIntegerSelection.selected z) = k * 2 ^ 1074 ∧
      k.natAbs ≤ 2 ^ 18 ∧
      ((ExpIntegerSelection.shifted z).toNat : Int) = (0x4338000000000000 : Int) + k := by
  obtain ⟨hf, hs, q, hv, he⟩ := ExpIntegerSelection.shifted_integer z hzf hz
  have hqR : (2 : ℝ) ^ 52 ≤ (q : ℝ) ∧ (q : ℝ) < (2 : ℝ) ^ 53 := by
    have hzb := abs_le.mp hz
    have hqb := abs_le.mp he
    rw [ExpIntegerSelection.magic_values.2.2.2] at hqb
    norm_num at hzb hqb
    constructor
    · have h : (4503599627370496 : ℝ) ≤ (q : ℝ) := by
        linarith only [hzb.1, hqb.1]
      convert h using 1
      norm_num
    · have h : (q : ℝ) < (9007199254740992 : ℝ) := by
        linarith only [hzb.2, hqb.2]
      convert h using 1
      norm_num
  have hql : 2 ^ 52 ≤ q := by exact_mod_cast hqR.1
  have hqu : q < 2 ^ 53 := by exact_mod_cast hqR.2
  let k := (q : Int) - 3 * 2 ^ 51
  have hp := ExpIntegerSelection.selected_integer_of_shifted z q hf hs hv he hz
  change Finite (ExpIntegerSelection.selected z) ∧
    Wasm.IEEE64.scaledValue (ExpIntegerSelection.selected z) = k * 2 ^ 1074 ∧
    k.natAbs ≤ 2 ^ 18 ∧ |(k : ℝ) - value z| ≤ 1 / 2 at hp
  have hw : (ExpIntegerSelection.shifted z).toNat = 1075 * 2 ^ 52 + (q - 2 ^ 52) := by
    rw [integer_binade_word _ q hs hv hql hqu]
    exact integer_encoding_toNat q hql hqu
  refine ⟨k, hp.1, hp.2.1, hp.2.2.1, ?_⟩
  rw [hw]
  exact magic_bits_identity q hql

#print axioms shifted_encoding

theorem table_remainder (ki : UInt64) (k : Int)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k) :
    (ki % 128).toNat = (k % 128).toNat := by
  have hI : (ki.toNat : Int) % 128 = k % 128 := by
    rw [hki, Int.add_emod]
    norm_num
  have hI' : ((ki.toNat % 128 : Nat) : Int) = k % 128 := by
    simpa only [Int.natCast_mod, Nat.cast_ofNat] using hI
  have hN := congrArg Int.toNat hI'
  rw [UInt64.toNat_mod]
  change ki.toNat % 128 = (k % 128).toNat
  simpa only [Int.toNat_natCast] using hN

theorem quotient_bounds (k : Int) (hk : k.natAbs ≤ 98305) :
    -769 ≤ k / 128 ∧ k / 128 ≤ 768 := by
  have h : (k.natAbs : Int) ≤ 98305 := by exact_mod_cast hk
  rw [← Int.abs_eq_natAbs] at h
  have hb := abs_le.mp h
  omega

theorem euclidean_index (k : Int) :
    (k % 128).toNat < 128 ∧ k = 128 * (k / 128) + ((k % 128).toNat : Int) := by
  have hlo : 0 ≤ k % 128 := Int.emod_nonneg _ (by decide)
  have hhi : k % 128 < 128 := Int.emod_lt_of_pos _ (by decide)
  have hc : ((k % 128).toNat : Int) = k % 128 := Int.toNat_of_nonneg hlo
  constructor
  · omega
  · rw [hc]
    omega

#print axioms table_remainder
#print axioms quotient_bounds
#print axioms euclidean_index

end Library.Numerics.Float64.Exp.ExpShiftedBits
