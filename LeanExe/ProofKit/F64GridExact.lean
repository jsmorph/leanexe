import LeanExe.ProofKit.F64DyadicBounds
import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64RoundingScale
import CodeLib.IEEE64.Operations

/-!
Exact and binade-local rounding of binary64 sums.  A sum on the grid of `2 ^ shift` with at most
54 significant bits is exact.  A positive sum in the binade `[2 ^ (52 + g), 2 ^ (53 + g))` of
scaled units rounds to a multiple of `2 ^ g` within half of `2 ^ g`.
-/

namespace LeanExe.ProofKit.F64GridExact
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem roundedMagnitude_shifted_small (n shift : Nat) (hn : n ≤ 2 ^ 53) :
    roundedMagnitude (n * 2 ^ shift) = n * 2 ^ shift := by
  by_cases hz : n = 0
  · subst n
    simp [roundedMagnitude]
  by_cases hl : 2 ^ 52 ≤ n
  · exact F64DyadicBounds.roundedMagnitude_shifted n shift hl hn
  have hlog : Nat.log2 n < 52 := (Nat.log2_lt hz).mpr (by omega)
  let gap := 52 - Nat.log2 n
  by_cases hs : gap ≤ shift
  · have hlo : 2 ^ 52 ≤ n * 2 ^ gap := by
      calc
        _ = 2 ^ Nat.log2 n * 2 ^ gap := by
          rw [← pow_add]
          congr 1
          dsimp [gap]
          omega
        _ ≤ n * 2 ^ gap := Nat.mul_le_mul_right _ (Nat.log2_self_le hz)
    have hhi : n * 2 ^ gap ≤ 2 ^ 53 := by
      have hp : n * 2 ^ gap < 2 ^ (Nat.log2 n + 1) * 2 ^ gap :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (by positivity)
      have hid : 2 ^ (Nat.log2 n + 1) * 2 ^ gap = 2 ^ 53 := by
        rw [← pow_add]
        congr 1
        dsimp [gap]
        omega
      rw [hid] at hp
      exact hp.le
    have hid : n * 2 ^ shift = (n * 2 ^ gap) * 2 ^ (shift - gap) := by
      rw [Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hs]
    rw [hid]
    exact F64DyadicBounds.roundedMagnitude_shifted _ _ hlo hhi
  · have hp : n * 2 ^ shift ≠ 0 := Nat.mul_ne_zero hz (by positivity)
    have ht : n * 2 ^ shift < 2 ^ 52 := (Nat.log2_lt hp).mp (by
      rw [F64DyadicBounds.log2_mul_two_pow n shift hz]
      dsimp [gap] at hs
      omega)
    exact roundedMagnitude_eq_self (ht.le.trans (by norm_num))

theorem signed_grid_packing_exact (z : Int) (shift : Nat)
    (hz : z.natAbs ≤ 2 ^ 53) (hshift : shift ≤ 2043) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift)) ∧
    Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift)) =
      z * 2 ^ shift := by
  have hmax : z.natAbs * 2 ^ shift < 2 ^ 2097 := by
    calc
      _ ≤ 2 ^ 53 * 2 ^ 2043 :=
        Nat.mul_le_mul hz (Nat.pow_le_pow_right (by omega) hshift)
      _ = 2 ^ 2096 := by rw [← pow_add]
      _ < 2 ^ 2097 := by norm_num
  have hp := F64Packing.pack_spec (z < 0) _ hmax
  have hv := F64Packing.scaledValue_pack (z < 0) _ hmax
  rw [roundedMagnitude_shifted_small _ _ hz] at hv
  refine ⟨hp.1, ?_⟩
  rw [hv]
  by_cases hn : z < 0
  · rw [ite_eq_left (by simpa using hn)]
    have habs := Int.eq_neg_natAbs_of_nonpos hn.le
    simp only [Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
    calc
      _ = (-(z.natAbs : Int)) * (2 : Int) ^ shift := by ring
      _ = z * (2 : Int) ^ shift := congrArg (fun x : Int => x * 2 ^ shift) habs.symm
  · rw [ite_eq_right (by simpa using hn)]
    have habs := Int.eq_natAbs_of_nonneg (le_of_not_gt hn)
    simp only [Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
    exact congrArg (fun x : Int => x * 2 ^ shift) habs.symm

theorem grid_add_exact (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (z : Int) (shift : Nat)
    (hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = z * 2 ^ shift)
    (hz : z.natAbs ≤ 2 ^ 53) (hshift : shift ≤ 2043) :
    Finite (Wasm.IEEE64.add a b) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) =
      Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
  by_cases hz0 : z = 0
  · have hs0 : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0 := by
      rw [hsum, hz0, zero_mul]
    have hmax : (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs <
        2 ^ 2097 := by rw [hs0]; norm_num
    have hp := F64AddBounds.add_scaled_relative a b ha hb hmax
    have he := hp.2
    rw [hs0] at he
    norm_num at he
    have he0 : |Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b)| = 0 := by
      have hn := abs_nonneg (Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b))
      omega
    exact ⟨hp.1, by rw [hs0]; exact abs_eq_zero.mp he0⟩
  · have hd : 0 < (2 : Int) ^ shift := by positivity
    have hnz : z * (2 : Int) ^ shift ≠ 0 := mul_ne_zero hz0 hd.ne'
    have hni : z * (2 : Int) ^ shift < 0 ↔ z < 0 := by
      constructor
      · intro h
        by_contra hzn
        exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hzn) hd.le)) h
      · intro hzn
        have hm := mul_pos (neg_pos.mpr hzn) hd
        nlinarith only [hm]
    have habs : (z * (2 : Int) ^ shift).natAbs = z.natAbs * 2 ^ shift := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      rfl
    have heq : Wasm.IEEE64.add a b =
        Wasm.IEEE64.roundScaledMagnitude (z < 0) (z.natAbs * 2 ^ shift) := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, hsum, hnz, hni, habs]
    rw [heq, hsum]
    exact signed_grid_packing_exact z shift hz hshift

/-- `grid_add_exact` for a difference. -/
theorem sub_grid_exact (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (z : Int) (shift : Nat)
    (hdiff : Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b = z * 2 ^ shift)
    (hz : z.natAbs ≤ 2 ^ 53) (hshift : shift ≤ 2043) :
    Finite (Wasm.IEEE64.sub a b) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) =
      Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b := by
  have hneg := negate_spec b hb
  have h := grid_add_exact a (Wasm.IEEE64.negate b) ha hneg.1 z shift
    (by rw [hneg.2, ← sub_eq_add_neg]; exact hdiff) hz hshift
  rw [hneg.2, ← sub_eq_add_neg] at h
  exact h

/-- Rounding a magnitude in the binade `[2 ^ (52 + g), 2 ^ (53 + g))` gives `R · 2 ^ g` with
`2 ^ 52 ≤ R ≤ 2 ^ 53`. -/
theorem roundedMagnitude_binade (n g : Nat) (hg : 1 ≤ g) (hg' : g ≤ 1023)
    (hl : 2 ^ (52 + g) ≤ n) (hu : n < 2 ^ (53 + g)) :
    ∃ R : Nat, roundedMagnitude n = R * 2 ^ g ∧ 2 ^ 52 ≤ R ∧ R ≤ 2 ^ 53 := by
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ (52 + g) := by positivity
    omega
  have hlog : Nat.log2 n = 52 + g := by
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hn0).mpr
        (by rw [show (52 + g).succ = 53 + g by omega]; exact hu))
    · exact (Nat.le_log2 hn0).mpr hl
  have hmin : 2 ^ 53 ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hl
  have hmax : n < 2 ^ 1076 := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hpar : 2 ^ 52 ≤ Wasm.IEEE32.roundShift n g ∧ Wasm.IEEE32.roundShift n g ≤ 2 ^ 53 := by
    have h := rounding_parameters hmin hmax
    simp only [hlog, show 52 + g - 52 = g by omega] at h
    exact ⟨h.2.2.1, h.2.2.2⟩
  have hsh : Nat.log2 n - 52 = g := by omega
  by_cases h : Wasm.IEEE32.roundShift n g = 2 ^ 53
  · refine ⟨2 ^ 53, ?_, by norm_num, le_rfl⟩
    simp only [roundedMagnitude, not_lt.mpr hmin, ite_false, hsh, h, beq_self_eq_true, ite_true]
    rw [pow_succ]
    ring
  · refine ⟨Wasm.IEEE32.roundShift n g, ?_, hpar.1, hpar.2⟩
    have hb : (Wasm.IEEE32.roundShift n g == 2 ^ 53) = false := by simpa using h
    simp only [roundedMagnitude, not_lt.mpr hmin, ite_false, hsh, hb, Bool.false_eq_true]

/-- A positive sum in the binade `[2 ^ (52 + g), 2 ^ (53 + g))` of scaled units rounds to a
positive multiple `R · 2 ^ g`, `2 ^ 52 ≤ R ≤ 2 ^ 53`, within `2 ^ g / 2` scaled units. -/
theorem add_binade (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : Nat) (hg : 1 ≤ g)
    (hg' : g ≤ 1023)
    (hl : (2 : Int) ^ (52 + g) ≤ Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b)
    (hu : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < (2 : Int) ^ (53 + g)) :
    Finite (Wasm.IEEE64.add a b) ∧
      (∃ R : Nat, Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = (R : Int) * 2 ^ g ∧
        2 ^ 52 ≤ R ∧ R ≤ 2 ^ 53) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
        (2 : ℝ) ^ g / 2 / (2 : ℝ) ^ 1074 := by
  have hpos : 0 < Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b :=
    lt_of_lt_of_le (by positivity) hl
  let n := (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs
  have hn : (n : Int) = Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b :=
    Int.natAbs_of_nonneg hpos.le
  have hnl : 2 ^ (52 + g) ≤ n := by
    have h : ((2 ^ (52 + g) : Nat) : Int) ≤ (n : Int) := by push_cast; rw [hn]; exact hl
    exact_mod_cast h
  have hnu : n < 2 ^ (53 + g) := by
    have h : (n : Int) < ((2 ^ (53 + g) : Nat) : Int) := by push_cast; rw [hn]; exact hu
    exact_mod_cast h
  have hmax : n < 2 ^ 1076 :=
    lt_of_lt_of_le hnu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude false n := by
    have hne : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≠ 0 := hpos.ne'
    have hnn : ¬ Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0 := not_lt.mpr hpos.le
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, hne, hnn, n]
  have hspec := roundScaledMagnitude_spec false n hmax
  have hsign := sign_roundScaledMagnitude false n hmax
  have hsv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = (roundedMagnitude n : Int) := by
    rw [heq]
    simp [Wasm.IEEE64.scaledValue, hspec.2.1, hsign]
  obtain ⟨R, hR, hRl, hRu⟩ := roundedMagnitude_binade n g hg hg' hnl hnu
  refine ⟨heq ▸ hspec.1, ⟨R, by rw [hsv, hR]; push_cast; ring, hRl, hRu⟩, ?_⟩
  have herr := F64Packing.roundedMagnitude_error n
  have hlog : Nat.log2 n - 52 = g := by
    have hn0 : n ≠ 0 := by
      have : 0 < 2 ^ (52 + g) := by positivity
      omega
    have : Nat.log2 n = 52 + g := by
      apply le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hn0).mpr
          (by rw [show (52 + g).succ = 53 + g by omega]; exact hnu))
      · exact (Nat.le_log2 hn0).mpr hnl
    omega
  rw [hlog] at herr
  have hval : value (Wasm.IEEE64.add a b) - (value a + value b) =
      ((roundedMagnitude n : ℝ) - (n : ℝ)) / (2 : ℝ) ^ 1074 := by
    have hnr : (n : ℝ) = (Wasm.IEEE64.scaledValue a : ℝ) + (Wasm.IEEE64.scaledValue b : ℝ) := by
      exact_mod_cast hn
    simp only [value, hsv, hnr]
    push_cast
    ring
  rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  exact div_le_div_of_nonneg_right herr (by positivity)

#print axioms roundedMagnitude_shifted_small
#print axioms signed_grid_packing_exact
#print axioms grid_add_exact
#print axioms sub_grid_exact
#print axioms roundedMagnitude_binade
#print axioms add_binade

end LeanExe.ProofKit.F64GridExact
