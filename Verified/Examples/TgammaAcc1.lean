import Verified.Examples.TgammaFinal
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64ExactProduct

/-!
Exact operations on dyadic grids for the accurate path of `Tgamma`.  A sum of two doubles that is a
multiple `k/2^g` of `2^-g` with `|k| ≤ 2^53` is exact (`grid_add`), and so is a product of
multiples of `2^-ga` and `2^-gb` whose numerators multiply to less than `2^53` (`grid_mul`).
`splt x` returns a multiple of `2^-25` within `2^-25` of `x` and the rounded remainder, for
`|x| ≤ 2^26` (`splt_spec`); the accurate path's sums of the products of these high parts with its
double coefficients are therefore exact.
-/

namespace Verified.Examples.TgammaAcc1
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

theorem scaled_eq (w : UInt64) : (Wasm.IEEE64.scaledValue w : ℝ) = value w * 2 ^ 1074 := by
  rw [value]; field_simp

/-- **An exact sum** on the grid `2^-g`. -/
theorem grid_add (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (k : ℤ) (g : ℕ)
    (hab : value a.toBits + value b.toBits = k / 2 ^ g) (hk : |k| ≤ 2 ^ 53) (hg : g ≤ 1074) :
    Finite (a + b).toBits ∧ value (a + b).toBits = value a.toBits + value b.toBits := by
  have hsum : Wasm.IEEE64.scaledValue a.toBits + Wasm.IEEE64.scaledValue b.toBits =
      k * 2 ^ (1074 - g) := by
    have h : ((Wasm.IEEE64.scaledValue a.toBits + Wasm.IEEE64.scaledValue b.toBits : ℤ) : ℝ) =
        ((k * 2 ^ (1074 - g) : ℤ) : ℝ) := by
      push_cast
      rw [scaled_eq, scaled_eq, ← add_mul, hab]
      rw [show (2 : ℝ) ^ 1074 = 2 ^ g * 2 ^ (1074 - g) by rw [← pow_add]; congr 1; omega]
      field_simp
    exact_mod_cast h
  have hkn : k.natAbs ≤ 2 ^ 53 := by
    have : (k.natAbs : ℤ) ≤ 2 ^ 53 := by rw [Int.natCast_natAbs]; exact_mod_cast hk
    exact_mod_cast this
  obtain ⟨hf, hv⟩ := F64GridExact.grid_add_exact a.toBits b.toBits ha hb k (1074 - g) hsum hkn
    (by omega)
  rw [F64Bits.toBits_add]
  refine ⟨hf, ?_⟩
  have h1 := scaled_eq (Wasm.IEEE64.add a.toBits b.toBits)
  have h2 : ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a.toBits b.toBits) : ℤ) : ℝ) =
      ((Wasm.IEEE64.scaledValue a.toBits + Wasm.IEEE64.scaledValue b.toBits : ℤ) : ℝ) := by
    rw [hv]
  push_cast at h2
  rw [scaled_eq, scaled_eq, scaled_eq] at h2
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  nlinarith

/-- **An exact difference** on the grid `2^-g`. -/
theorem grid_sub (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (k : ℤ) (g : ℕ)
    (hab : value a.toBits - value b.toBits = k / 2 ^ g) (hk : |k| ≤ 2 ^ 53) (hg : g ≤ 1074) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  have hdiff : Wasm.IEEE64.scaledValue a.toBits - Wasm.IEEE64.scaledValue b.toBits =
      k * 2 ^ (1074 - g) := by
    have h : ((Wasm.IEEE64.scaledValue a.toBits - Wasm.IEEE64.scaledValue b.toBits : ℤ) : ℝ) =
        ((k * 2 ^ (1074 - g) : ℤ) : ℝ) := by
      push_cast
      rw [scaled_eq, scaled_eq, ← sub_mul, hab]
      rw [show (2 : ℝ) ^ 1074 = 2 ^ g * 2 ^ (1074 - g) by rw [← pow_add]; congr 1; omega]
      field_simp
    exact_mod_cast h
  have hkn : k.natAbs ≤ 2 ^ 53 := by
    have : (k.natAbs : ℤ) ≤ 2 ^ 53 := by rw [Int.natCast_natAbs]; exact_mod_cast hk
    exact_mod_cast this
  obtain ⟨hf, hv⟩ := F64GridExact.sub_grid_exact a.toBits b.toBits ha hb k (1074 - g) hdiff hkn
    (by omega)
  rw [F64Bits.toBits_sub]
  refine ⟨hf, ?_⟩
  have h2 : ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a.toBits b.toBits) : ℤ) : ℝ) =
      ((Wasm.IEEE64.scaledValue a.toBits - Wasm.IEEE64.scaledValue b.toBits : ℤ) : ℝ) := by
    rw [hv]
  push_cast at h2
  rw [scaled_eq, scaled_eq, scaled_eq] at h2
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  nlinarith

/-- The scaled magnitude of a multiple `k/2^g` of `2^-g`. -/
theorem mag_of_grid (w : UInt64) (k : ℤ) (g : ℕ) (hv : value w = k / 2 ^ g) (hg : g ≤ 1074) :
    Wasm.IEEE64.scaledMagnitude w = k.natAbs * 2 ^ (1074 - g) := by
  have h := F64Sterbenz.value_abs_scaled w
  rw [hv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g)] at h
  have h2 : ((Wasm.IEEE64.scaledMagnitude w : ℕ) : ℝ) = ((k.natAbs * 2 ^ (1074 - g) : ℕ) : ℝ) := by
    rw [← h]
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
    rw [show (2 : ℝ) ^ 1074 = 2 ^ g * 2 ^ (1074 - g) by rw [← pow_add]; congr 1; omega]
    field_simp
  exact_mod_cast h2

/-- **An exact product** of multiples of `2^-ga` and `2^-gb`. -/
theorem grid_mul (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (ka kb : ℤ)
    (ga gb : ℕ) (hva : value a.toBits = ka / 2 ^ ga) (hvb : value b.toBits = kb / 2 ^ gb)
    (hk : ka.natAbs * kb.natAbs < 2 ^ 53) (hg : ga + gb ≤ 1074) :
    Finite (a * b).toBits ∧ value (a * b).toBits = value a.toBits * value b.toBits := by
  obtain ⟨hf, hv, -, -⟩ := F64ExactProduct.mul_exact_scaled a.toBits b.toBits ha hb ka.natAbs
    kb.natAbs (1074 - ga) (1074 - gb) (mag_of_grid _ _ _ hva (by omega))
    (mag_of_grid _ _ _ hvb (by omega)) hk (by omega) (by omega)
  rw [F64Bits.toBits_mul]
  exact ⟨hf, hv⟩

/-- **`splt`** for `|x| ≤ 2^26`: a multiple of `2^-26` within `2^-25` of `x`, and the rounded
remainder. -/
theorem splt_spec (x : Float) (hx : Finite x.toBits) (hb : |value x.toBits| ≤ 2 ^ 26) :
    Finite (splt x).1.toBits ∧ Finite (splt x).2.toBits ∧
      (∃ k : ℤ, value (splt x).1.toBits = k / 2 ^ 26) ∧
      |value (splt x).1.toBits - value x.toBits| ≤ 1 / 2 ^ 25 ∧
      |value (splt x).2.toBits - (value x.toBits - value (splt x).1.toBits)| ≤ 1 / 2 ^ 77 := by
  have hw : Wasm.IEEE64.isFinite 0x41A8000000000000 = true := by decide
  have hof := TgammaWords.ofBits_finite _ hw
  have hov : value (Float.ofBits 0x41A8000000000000).toBits = 3 * 2 ^ 26 := by
    rw [TgammaWords.ofBits_value _ hw, show PolyBound.ratOfWord 0x41A8000000000000 = 3 * 2 ^ 26 by
      decide +kernel]
    norm_num
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  unfold splt
  dsimp only
  -- `s = x + off` in `[2^27 - 2^-25, 2^28]`
  have hs := fapprox_add (fapprox_self x hx) (fapprox_self _ hof) (2 ^ 28)
    (by rw [hov, abs_of_pos (by linarith : (0 : ℝ) < value x.toBits + 3 * 2 ^ 26)]; linarith)
    (by norm_num)
  have hse := hs.2
  rw [hov] at hse
  simp only [zero_add] at hse
  generalize x + Float.ofBits 0x41A8000000000000 = s at hs hse ⊢
  have hslo : 2 ^ 26 ≤ value s.toBits := by linarith [(abs_le.mp hse).1]
  have hshi : value s.toBits ≤ 2 ^ 28 + 1 := by linarith [(abs_le.mp hse).2]
  obtain ⟨ks, hks⟩ := TgammaRefl4.grid s.toBits 26 (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact hslo)
  rw [show 52 - 26 = 26 from rfl] at hks
  -- `xh = s - off` exactly
  have hd0 : value s.toBits - 3 * 2 ^ 26 = ((ks - 3 * 2 ^ 52 : ℤ) : ℝ) / 2 ^ 26 := by
    rw [hks]; push_cast; field_simp; ring
  have hd : value s.toBits - value (Float.ofBits 0x41A8000000000000).toBits =
      ((ks - 3 * 2 ^ 52 : ℤ) : ℝ) / 2 ^ 26 := by rw [hov]; exact hd0
  have hdb : |ks - 3 * 2 ^ 52| ≤ (2 : ℤ) ^ 53 := by
    have hk' : ((ks - 3 * 2 ^ 52 : ℤ) : ℝ) = (value s.toBits - 3 * 2 ^ 26) * 2 ^ 26 := by
      rw [hd0]; field_simp
    have hm : |value s.toBits - 3 * 2 ^ 26| ≤ 2 ^ 26 + 1 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hse).1, (abs_le.mp hse).2]
    have h1 : |((ks - 3 * 2 ^ 52 : ℤ) : ℝ)| ≤ 2 ^ 53 := by
      rw [hk', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 26)]
      have := mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ 2 ^ 26)
      linarith [(by norm_num : ((2 : ℝ) ^ 26 + 1) * 2 ^ 26 ≤ 2 ^ 53)]
    rw [← Int.cast_abs] at h1
    exact_mod_cast h1
  obtain ⟨hhf, hhv⟩ := grid_sub s _ hs.1 hof _ 26 hd hdb (by norm_num)
  rw [hov] at hhv
  have hxh : |value (s - Float.ofBits 0x41A8000000000000).toBits - value x.toBits| ≤
      1 / 2 ^ 25 := by
    rw [hhv]
    have : value s.toBits - 3 * 2 ^ 26 - value x.toBits =
        value s.toBits - (value x.toBits + 3 * 2 ^ 26) := by
      ring
    rw [this]
    linarith [(by norm_num : (2 : ℝ) ^ 28 / 2 ^ 53 = 1 / 2 ^ 25)]
  -- `x - xh`
  have hl := fapprox_sub (fapprox_self x hx) (fapprox_self _ hhf) (1 / 2 ^ 25)
    (by rw [abs_sub_comm]; linarith) (by norm_num)
  refine ⟨hhf, hl.1, ⟨ks - 3 * 2 ^ 52, by rw [hhv, hks]; push_cast; field_simp; ring⟩, hxh, ?_⟩
  have := hl.2
  linarith [(by norm_num : (0 : ℝ) + 0 + 1 / 2 ^ 25 / 2 ^ 53 ≤ 1 / 2 ^ 77)]

#print axioms grid_add
#print axioms grid_sub
#print axioms grid_mul
#print axioms splt_spec

end Verified.Examples.TgammaAcc1
