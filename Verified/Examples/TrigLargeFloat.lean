import Verified.Examples.TrigLargeInt
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64Bits

/-!
The floating-point stage of `Trig.remLarge`.  The 53-bit words `hi` and `lo` convert exactly,
their products with powers of two are exact, and `y0 = a + c` with `y1 = c - (y0 - a)` is an
exact two-sum, since `a` is a multiple of `2 ^ g` above `2 ^ 52` such multiples and `c` is below
one of them.  So `y0 + y1` equals `(hi · 2 ^ 53 + lo) · 2 ^ (ea - 2)` scaled units, and `y1` is at
most `y0 / 2 ^ 53` in magnitude.
-/

namespace Verified.Examples.TrigLargeFloat

open CodeLib.IEEE64 LeanExe.ProofKit TrigLargeInt TrigWords

set_option exponentiation.threshold 4096

/-- An integer below `2 ^ 53` converts exactly. -/
theorem convert_exact (n : UInt64) (hn : n.toNat < 2 ^ 53) :
    Finite (Wasm.IEEE64.convertI64U n) ∧ Wasm.IEEE64.sign (Wasm.IEEE64.convertI64U n) = false ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.convertI64U n) = n.toNat * 2 ^ 1074 := by
  have hc : Wasm.IEEE64.convertI64U n =
      Wasm.IEEE64.roundScaledMagnitude false (n.toNat * 2 ^ 1074) := rfl
  have hmax : n.toNat * 2 ^ 1074 < 2 ^ 2097 := by
    calc n.toNat * 2 ^ 1074 < 2 ^ 53 * 2 ^ 1074 := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ ≤ 2 ^ 2097 := by norm_num
  have h := F64GridExact.signed_grid_packing_exact (n.toNat : Int) 1074 (by simp; omega)
    (by norm_num)
  have hneg : decide ((n.toNat : Int) < 0) = false := by simp
  rw [hneg, Int.natAbs_natCast] at h
  have hs := (F64Packing.pack_spec false _ hmax).2.2
  rw [hc]
  refine ⟨h.1, hs, ?_⟩
  have hv := h.2
  simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false] at hv
  exact_mod_cast hv

/-- The word `e <<< 52` is the power `2 ^ (e - 1023)`. -/
theorem pow_word (e : UInt64) (E : Nat) (he : e.toNat = E) (h1 : 1 ≤ E) (h2 : E < 2047) :
    Finite (e <<< 52) ∧ Wasm.IEEE64.sign (e <<< 52) = false ∧
      Wasm.IEEE64.scaledMagnitude (e <<< 52) = 2 ^ 52 * 2 ^ (E - 1) := by
  have ht : (e <<< 52).toNat = E * 2 ^ 52 := by
    rw [shl_toNat, he]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  have hexp : Wasm.IEEE64.exponent (e <<< 52) = E := by
    unfold Wasm.IEEE64.exponent
    rw [ht]
    omega
  have hfr : Wasm.IEEE64.fraction (e <<< 52) = 0 := by
    unfold Wasm.IEEE64.fraction
    rw [ht]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexp, bne_iff_ne, ne_eq]
    omega
  · simp only [Wasm.IEEE64.sign, ht, decide_eq_false_iff_not]
    omega
  · simp only [Wasm.IEEE64.scaledMagnitude, hexp, hfr, Nat.add_zero,
      show (E == 0) = false by simp; omega, Bool.false_eq_true, ite_false]

/-- The product of an integer below `2 ^ 53` and a power of two is exact. -/
theorem mul_int_pow (n e : UInt64) (E : Nat) (hn : n.toNat < 2 ^ 53) (he : e.toNat = E)
    (h1 : 1 ≤ E) (h2 : E + 51 ≤ 2043) :
    Finite (Wasm.IEEE64.mul (Wasm.IEEE64.convertI64U n) (e <<< 52)) ∧
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul (Wasm.IEEE64.convertI64U n) (e <<< 52)) =
        (n.toNat : Int) * 2 ^ (E + 51) := by
  obtain ⟨hcf, hcs, hcm⟩ := convert_exact n hn
  obtain ⟨hpf, hps, hpm⟩ := pow_word e E he h1 (by omega)
  rw [mul_finite_rounder _ _ hcf hpf, hcs, hps, hcm, hpm]
  have hprod : n.toNat * 2 ^ 1074 * (2 ^ 52 * 2 ^ (E - 1)) = n.toNat * 2 ^ (1074 + (E + 51)) := by
    rw [show 1074 + (E + 51) = 1074 + 52 + (E - 1) by omega, pow_add, pow_add]
    ring
  rw [hprod, show (false != false) = false from rfl,
    F64PowerScale.dyadic_shifted_exact false _ _ hn]
  have h := F64GridExact.signed_grid_packing_exact (n.toNat : Int) (E + 51) (by simp; omega) h2
  have hneg : decide ((n.toNat : Int) < 0) = false := by simp
  rw [hneg, Int.natAbs_natCast] at h
  exact h

/-- `stage5` is an exact two-sum of the exact products `a = hi · 2 ^ (ea - 1023)` and
`c = lo · 2 ^ (ea - 1076)`, in scaled units. -/
theorem stage5_spec (k hi lo lz : UInt64) (ea : Nat) (hea : (k + 910 - lz).toNat = ea)
    (hec : (k + 857 - lz).toNat = ea - 53) (hea1 : 54 ≤ ea) (hea2 : ea + 51 ≤ 1023)
    (hhi1 : 2 ^ 52 ≤ hi.toNat) (hhi2 : hi.toNat < 2 ^ 53) (hlo : lo.toNat < 2 ^ 53) :
    Finite (stage5 k hi lo lz).1.toBits ∧ Finite (stage5 k hi lo lz).2.toBits ∧
      Wasm.IEEE64.scaledValue (stage5 k hi lo lz).1.toBits +
          Wasm.IEEE64.scaledValue (stage5 k hi lo lz).2.toBits =
        ((hi.toNat : Int) * 2 ^ 53 + lo.toNat) * 2 ^ (ea - 2) ∧
      0 < Wasm.IEEE64.scaledValue (stage5 k hi lo lz).1.toBits ∧
      |Wasm.IEEE64.scaledValue (stage5 k hi lo lz).2.toBits| * 2 ^ 53 ≤
        Wasm.IEEE64.scaledValue (stage5 k hi lo lz).1.toBits := by
  unfold stage5
  dsimp only
  simp only [F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Convert.toBits_toFloat,
    F64Bits.toBits_ofBits, F64Bits.shiftLeft_52_not_nan, Bool.false_eq_true, ite_false]
  obtain ⟨haf, hav⟩ := mul_int_pow hi (k + 910 - lz) ea hhi2 hea (by omega) (by omega)
  obtain ⟨hcf, hcv⟩ := mul_int_pow lo (k + 857 - lz) (ea - 53) hlo hec (by omega) (by omega)
  generalize Wasm.IEEE64.mul (Wasm.IEEE64.convertI64U hi) ((k + 910 - lz) <<< 52) = A
    at haf hav ⊢
  generalize Wasm.IEEE64.mul (Wasm.IEEE64.convertI64U lo) ((k + 857 - lz) <<< 52) = C
    at hcf hcv ⊢
  generalize hPdef : (2 : Int) ^ (ea - 2) = P
  have hP : 0 < P := by rw [← hPdef]; positivity
  have e1 : (2 : Int) ^ (ea + 51) = 2 ^ 53 * P := by
    rw [← hPdef, ← pow_add, show 53 + (ea - 2) = ea + 51 by omega]
  have e2 : (2 : Int) ^ (ea - 53 + 51) = P := by
    rw [← hPdef, show ea - 53 + 51 = ea - 2 by omega]
  rw [e1] at hav
  rw [e2] at hcv
  have hH : (2 : Int) ^ 52 ≤ hi.toNat := by exact_mod_cast hhi1
  have hH2 : (hi.toNat : Int) < 2 ^ 53 := by exact_mod_cast hhi2
  have hL : (lo.toNat : Int) < 2 ^ 53 := by exact_mod_cast hlo
  have hL0 : (0 : Int) ≤ lo.toNat := Int.natCast_nonneg _
  have hsum : Wasm.IEEE64.scaledValue A + Wasm.IEEE64.scaledValue C =
      ((hi.toNat : Int) * 2 ^ 53 + lo.toNat) * P := by
    rw [hav, hcv]
    ring
  have hlow : (2 : Int) ^ 105 ≤ (hi.toNat : Int) * 2 ^ 53 + lo.toNat := by
    have h1 : (2 : Int) ^ 105 = 2 ^ 52 * 2 ^ 53 := by norm_num
    rw [h1]
    nlinarith
  have hhigh : (hi.toNat : Int) * 2 ^ 53 + lo.toNat < 2 ^ 106 := by
    have h1 : (2 : Int) ^ 106 = 2 ^ 53 * 2 ^ 53 := by norm_num
    have h2 : (hi.toNat : Int) ≤ 2 ^ 53 - 1 := by linarith
    nlinarith
  have hl : (2 : Int) ^ (52 + (ea + 51)) ≤
      Wasm.IEEE64.scaledValue A + Wasm.IEEE64.scaledValue C := by
    rw [hsum, show (2 : Int) ^ (52 + (ea + 51)) = 2 ^ 105 * P by
      rw [← hPdef, ← pow_add, show 105 + (ea - 2) = 52 + (ea + 51) by omega]]
    exact Int.mul_le_mul_of_nonneg_right hlow hP.le
  have hu : Wasm.IEEE64.scaledValue A + Wasm.IEEE64.scaledValue C <
      (2 : Int) ^ (53 + (ea + 51)) := by
    rw [hsum, show (2 : Int) ^ (53 + (ea + 51)) = 2 ^ 106 * P by
      rw [← hPdef, ← pow_add, show 106 + (ea - 2) = 53 + (ea + 51) by omega]]
    exact Int.mul_lt_mul_of_pos_right hhigh hP
  obtain ⟨hyf, ⟨R, hR, hR1, hR2⟩, herr⟩ :=
    F64GridExact.add_binade A C haf hcf (ea + 51) (by omega) (by omega) hl hu
  generalize Wasm.IEEE64.add A C = Y0 at hyf hR herr ⊢
  rw [e1] at hR
  have herrInt : |Wasm.IEEE64.scaledValue Y0 -
      (Wasm.IEEE64.scaledValue A + Wasm.IEEE64.scaledValue C)| ≤ 2 ^ 52 * P := by
    have hv : value Y0 - (value A + value C) =
        ((Wasm.IEEE64.scaledValue Y0 - (Wasm.IEEE64.scaledValue A +
          Wasm.IEEE64.scaledValue C) : Int) : ℝ) / 2 ^ 1074 := by
      simp only [value]
      push_cast
      ring
    rw [hv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      div_le_div_iff_of_pos_right (by positivity)] at herr
    have hg : (2 : ℝ) ^ (ea + 51) / 2 = ((2 ^ 52 * P : Int) : ℝ) := by
      have h := congrArg (fun z : Int => (z : ℝ)) e1
      simp only [Int.cast_pow, Int.cast_ofNat, Int.cast_mul] at h
      rw [h]
      push_cast
      ring
    rw [hg] at herr
    exact_mod_cast herr
  rw [hR, hsum] at herrInt
  have hX : |(R : Int) * 2 ^ 53 - ((hi.toNat : Int) * 2 ^ 53 + lo.toNat)| ≤ 2 ^ 52 := by
    have h : |(R : Int) * 2 ^ 53 - ((hi.toNat : Int) * 2 ^ 53 + lo.toNat)| * P ≤ 2 ^ 52 * P := by
      rw [← abs_of_pos hP, ← abs_mul, abs_of_pos hP]
      calc _ = |(R : Int) * (2 ^ 53 * P) - ((hi.toNat : Int) * 2 ^ 53 + lo.toNat) * P| := by
            ring_nf
        _ ≤ 2 ^ 52 * P := herrInt
    exact le_of_mul_le_mul_right h hP
  rw [abs_le] at hX
  have hRH : (R : Int) - hi.toNat ≤ 1 ∧ -1 ≤ (R : Int) - hi.toNat := by
    constructor <;> nlinarith
  obtain ⟨hDf, hDv⟩ := F64GridExact.sub_grid_exact Y0 A hyf haf ((R : Int) - hi.toNat) (ea + 51)
    (by rw [hR, hav, e1]; ring) (by omega) (by omega)
  generalize Wasm.IEEE64.sub Y0 A = D at hDf hDv ⊢
  obtain ⟨hYf, hYv⟩ := F64GridExact.sub_grid_exact C D hcf hDf
    ((lo.toNat : Int) - ((R : Int) - hi.toNat) * 2 ^ 53) (ea - 2)
    (by rw [hcv, hDv, hR, hav, hPdef]; ring) (by omega) (by omega)
  refine ⟨hyf, hYf, ?_, ?_, ?_⟩
  · rw [hYv, hDv, hR, hav, hcv]
    ring
  · rw [hR]
    have hR0 : (0 : Int) < R := by omega
    exact mul_pos hR0 (mul_pos (by norm_num) hP)
  · rw [hYv, hDv, hR, hav, hcv]
    have hY : Wasm.IEEE64.scaledValue C - (Wasm.IEEE64.scaledValue Y0 - Wasm.IEEE64.scaledValue A) =
        ((lo.toNat : Int) - ((R : Int) - hi.toNat) * 2 ^ 53) * P := by
      rw [hcv, hR, hav]
      ring
    rw [show (lo.toNat : Int) * P - ((R : Int) * (2 ^ 53 * P) - (hi.toNat : Int) * (2 ^ 53 * P)) =
      ((lo.toNat : Int) - ((R : Int) - hi.toNat) * 2 ^ 53) * P by ring, abs_mul, abs_of_pos hP]
    have hz : |(lo.toNat : Int) - ((R : Int) - hi.toNat) * 2 ^ 53| ≤ 2 ^ 52 := by
      rw [abs_le]
      constructor <;> linarith
    have hR1' : (2 : Int) ^ 52 ≤ R := by exact_mod_cast hR1
    nlinarith

#print axioms convert_exact
#print axioms pow_word
#print axioms mul_int_pow
#print axioms stage5_spec

end Verified.Examples.TrigLargeFloat
