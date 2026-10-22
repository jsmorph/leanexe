import Library.Numerics.Float64.Exp.ExpCoreOneStep
import LeanExe.ProofKit.ExpTinyError
import LeanExe.ProofKit.F64ExponentBounds
import LeanExe.ProofKit.F64PositiveRounding

namespace Library.Numerics.Float64.Exp.ExpBranches
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64NearestBinade F64ExponentBounds

set_option exponentiation.threshold 4096

def exponentWord (x : UInt64) : UInt64 := (x >>> 52) &&& 0x7FF

theorem exponent_word_spec (x : UInt64) :
    (exponentWord x).toNat = Wasm.IEEE64.exponent x := by
  simp only [exponentWord, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.reduceToNat, Nat.reduceMod]
  change (x.toNat >>> 52) &&& (2 ^ 11 - 1) = x.toNat / 2 ^ 52 % 2 ^ 11
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem ordinary_guard (a : UInt64) (hlo : 969 ≤ a.toNat) (hhi : a.toNat < 1032) :
    ¬ a - 969 ≥ (63 : UInt64) := by
  have hs : (969 : UInt64) ≤ a := UInt64.le_iff_toNat_le.mpr hlo
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  rw [UInt64.toNat_sub_of_le _ _ hs] at hn
  change 63 ≤ a.toNat - 969 at hn
  omega

private theorem tiny_guard (a : UInt64) (ha : a.toNat < 969) :
    a - 969 ≥ (63 : UInt64) ∧ a - 969 ≥ (0x80000000 : UInt64) := by
  have hs : (a - 969).toNat = 2 ^ 64 - 969 + a.toNat := by
    rw [UInt64.toNat_sub]
    change (2 ^ 64 - 969 + a.toNat) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 63 ≤ 2 ^ 64 - 969 + a.toNat
    omega
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 0x80000000 ≤ 2 ^ 64 - 969 + a.toNat
    omega

theorem ordinary_selected (tab : Array UInt64) (x : Float)
    (hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits)
    (hhi : Wasm.IEEE64.exponent x.toBits < 1032) :
    Exp.expWith tab x = Exp.expCore tab x false := by
  have hg := ordinary_guard (exponentWord x.toBits)
    (by rw [exponent_word_spec]; exact hlo) (by rw [exponent_word_spec]; exact hhi)
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp.expWith, exponentWord, hc] at hg ⊢
  rw [ite_eq_right hg]

theorem tiny_selected (tab : Array UInt64) (x : Float)
    (hx : Wasm.IEEE64.exponent x.toBits < 969) :
    Exp.expWith tab x = 1.0 + x := by
  have hg := tiny_guard (exponentWord x.toBits) (by rw [exponent_word_spec]; exact hx)
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp.expWith, exponentWord, hc] at hg ⊢
  rw [ite_eq_left hg.1, ite_eq_left hg.2]

theorem small_boundary : value (boundary 1032) = (512 : ℝ) := by
  have h := boundary_power 1032 9 (by decide) (by decide) (by decide)
  norm_num at h
  exact h

theorem tiny_boundary : value (boundary 969) = 1 / (2 : ℝ) ^ 54 := by
  have h := boundary_power 969 (-54) (by decide) (by decide) (by decide)
  have hp : (2 : ℝ) ^ (-54 : Int) = 1 / (2 : ℝ) ^ 54 := by norm_num
  exact h.trans hp

theorem large_boundary : value (boundary 1033) = (1024 : ℝ) := by
  have h := boundary_power 1033 10 (by decide) (by decide) (by decide)
  norm_num at h
  exact h

theorem special_exponent (x : UInt64) (hxlo : 512 ≤ |value x|)
    (hxhi : |value x| < 1024) : Wasm.IEEE64.exponent x = 1032 := by
  have hehi : Wasm.IEEE64.exponent x < 1033 :=
    exponent_lt_of_magnitude_lt x 1033 (by decide) (by
      rw [large_boundary, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
      exact hxhi)
  have helo : 1032 ≤ Wasm.IEEE64.exponent x := by
    by_contra hn
    have hb := boundary_fields 1032 (by decide)
    have hord : F64Order.absBits x < F64Order.absBits (boundary 1032) := by
      rw [hb.2]
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hb.1]
      rw [F64Order.exponent_abs] at hn
      omega
    have hm := F64Order.abs_value_lt x (boundary 1032) hord
    rw [small_boundary, abs_of_pos (by norm_num : (0 : ℝ) < 512)] at hm
    exact (not_lt_of_ge hxlo) hm
  omega

theorem special_selected (tab : Array UInt64) (x : Float)
    (he : Wasm.IEEE64.exponent x.toBits = 1032) :
    Exp.expWith tab x = Exp.expCore tab x true := by
  have hw : exponentWord x.toBits = 1032 := by
    apply UInt64.toNat_inj.mp
    rw [exponent_word_spec, he]
    rfl
  change ((x.toBits >>> 52) &&& 0x7FF) = 1032 at hw
  have hg1 : (1032 : UInt64) - 0x3C9 ≥ 0x408 - 0x3C9 := by decide +kernel
  have hg2 : ¬ (1032 : UInt64) - 0x3C9 ≥ 0x80000000 := by decide +kernel
  have hg3 : ¬ (1032 : UInt64) ≥ 0x409 := by decide +kernel
  simp only [Exp.expWith, hw, ite_eq_left hg1, ite_eq_right hg2, ite_eq_right hg3]

theorem exp_small_below_overflow (x : UInt64) (hx : |value x| ≤ 512) :
    Real.exp (value x) < F64PositiveRounding.overflowThreshold := by
  have hv : value x ≤ 512 := (le_abs_self _).trans hx
  have hl := ExpReductionBounds.log_two_coarse_bounds.1
  have harg : value x ≤ (768 : ℝ) * Real.log 2 := by linarith only [hv, hl]
  have hp : Real.exp ((768 : ℝ) * Real.log 2) = (2 : ℝ) ^ 768 := by
    simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      Real.exp_nat_mul (Real.log 2) 768
  have he : Real.exp (value x) ≤ (2 : ℝ) ^ 768 := by
    rw [← hp]
    exact Real.exp_le_exp.mpr harg
  exact he.trans_lt (by norm_num [F64PositiveRounding.overflowThreshold])

theorem exp_small_one_step (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 512) :
    let w := F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))
    Finite (Exp.exp x).toBits ∧
      (Exp.exp x).toBits.toNat ≤ w.toNat + 1 ∧
      w.toNat ≤ (Exp.exp x).toBits.toNat + 1 := by
  dsimp only
  rw [F64PositiveRounding.reference_finite _
    (exp_small_below_overflow x.toBits hx.le)]
  have he : Wasm.IEEE64.exponent x.toBits < 1032 :=
    exponent_lt_of_magnitude_lt x.toBits 1032 (by decide) (by
      rw [small_boundary, abs_of_pos (by norm_num : (0 : ℝ) < 512)]
      exact hx)
  by_cases ht : Wasm.IEEE64.exponent x.toBits < 969
  · have hxt : |value x.toBits| ≤ 1 / (2 : ℝ) ^ 54 := by
      have h := magnitude_le_boundary x.toBits 969 (by decide) ht
      rw [tiny_boundary, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 54)] at h
      exact h
    rw [Exp.exp, tiny_selected _ x ht, ExpTinyError.float_result_bits]
    exact ⟨(ExpTinyError.tiny_bounds x.toBits hxf hxt).1,
      ExpTinyError.tiny_one_step x.toBits hxf hxt⟩
  · have hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits := Nat.le_of_not_gt ht
    rw [Exp.exp, ordinary_selected _ x hlo he]
    exact ⟨(ExpCoreBounds.expCore_error x hxf hx.le).1,
      ExpCoreOneStep.expCore_one_step x hxf hx.le⟩

#print axioms exponent_word_spec
#print axioms ordinary_selected
#print axioms tiny_selected
#print axioms large_boundary
#print axioms special_exponent
#print axioms special_selected
#print axioms exp_small_below_overflow
#print axioms exp_small_one_step

end Library.Numerics.Float64.Exp.ExpBranches
