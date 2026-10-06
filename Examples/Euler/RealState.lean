import Examples.Euler.Program
import Examples.Euler.Words
import LeanExe.ProofKit.F64Admissibility
import Examples.Euler.Equations.Flux

/-! The solvers' state guard implies an admissible real state: positive density and positive
pressure in exact arithmetic with γ = 7/5.  The narrow guard compares words.  The energy guard
computes the word-level check `F64Admissibility.checked`, whose soundness proof applies. -/

namespace Examples.Euler

open Examples.Euler LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)

/-- The real value of a float's bits. -/
noncomputable abbrev real (x : Float) : ℝ := value x.toBits

/-- A state's components as reals. -/
noncomputable abbrev vec (q : Conserved) : Equations.Vec4 :=
  ![real q.density, real q.mx, real q.my, real q.energy]

theorem real_pos_of_positive {x : Float} (h : 0 < x.toBits ∧ x.toBits < 0x7FF0000000000000) :
    0 < real x :=
  (F64Order.positiveBits_spec x.toBits (by simpa [F64Order.positiveBits] using h)).2

theorem admissible_iff (r m t e : ℝ) :
    Equations.Admissible ![r, m, t, e] ↔ 0 < r ∧ 0 < e - (m ^ 2 + t ^ 2) / (2 * r) := by
  show (0 < r ∧ 0 < 2 / 5 * (e - (m ^ 2 + t ^ 2) / (2 * r))) ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- Admissibility does not depend on the order of the momenta. -/
theorem admissible_swap {r m t e : ℝ} (h : Equations.Admissible ![r, m, t, e]) :
    Equations.Admissible ![r, t, m, e] := by
  rw [admissible_iff] at h ⊢
  rw [add_comm]
  exact h

theorem exponentBits_eq (b : UInt64) : exponentBits b = F64Normalize.exponentBits b := by
  show (b &&& 0x7FFFFFFFFFFFFFFF) >>> 52 = (b &&& 0x7FFFFFFFFFFFFFFF) / 0x0010000000000000
  generalize b &&& 0x7FFFFFFFFFFFFFFF = a
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_div, Nat.shiftRight_eq_div_pow]
  rfl

theorem exponentBits_toNat' (b : UInt64) :
    (exponentBits b).toNat = b.toNat % 2 ^ 63 / 2 ^ 52 := by
  rw [exponentBits_eq, F64Normalize.exponentBits, UInt64.toNat_div, F64Order.absBits_toNat]
  rfl

theorem normalized_toBits {x : Float} {top : UInt64} (hf : finite x = true)
    (hn : normalizable x top = true) (hle : (exponentBits x.toBits).toNat ≤ top.toNat) :
    (normalized x top).toBits = F64Normalize.normalizedMagnitude x.toBits top := by
  have hA : (absBits x.toBits).toNat = x.toBits.toNat % 2 ^ 63 := F64Order.absBits_toNat _
  have hE := exponentBits_toNat' x.toBits
  have hf' : x.toBits.toNat % 2 ^ 63 < 0x7FF0000000000000 := by
    rw [← hA]; exact UInt64.lt_iff_toNat_lt.mp (by simpa [finite] using hf)
  have hn' : x.toBits.toNat % 2 ^ 63 = 0 ∨ (0 < x.toBits.toNat % 2 ^ 63 / 2 ^ 52 ∧
      top.toNat < x.toBits.toNat % 2 ^ 63 / 2 ^ 52 + 1021) := by
    simp only [normalizable, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hn
    rcases hn with h | ⟨h1, h2⟩
    · left; rw [← hA, h]; rfl
    · right
      rw [UInt64.lt_iff_toNat_lt] at h1 h2
      rw [UInt64.toNat_add] at h2
      rw [hE] at h1 h2
      simp only [UInt64.reduceToNat] at h1 h2
      constructor <;> omega
  rw [hE] at hle
  unfold normalized F64Normalize.normalizedMagnitude
  dsimp only
  rw [← exponentBits_eq, show F64Order.absBits x.toBits = absBits x.toBits from rfl]
  rcases hn' with h0 | ⟨h1, h2⟩
  · have hz : absBits x.toBits = 0 := UInt64.toNat_inj.mp (by rw [hA, h0]; rfl)
    simp [hz, zero_toBits]
  · have hz : ¬absBits x.toBits = 0 := fun h => by
      have := congrArg UInt64.toNat h
      rw [hA] at this
      simp only [UInt64.toNat_zero] at this
      omega
    have hk : (exponentBits x.toBits + 1021 - top).toNat =
        x.toBits.toNat % 2 ^ 63 / 2 ^ 52 + 1021 - top.toNat := by
      have hadd : (exponentBits x.toBits + 1021).toNat = x.toBits.toNat % 2 ^ 63 / 2 ^ 52 + 1021 := by
        rw [UInt64.toNat_add, hE]
        simp only [Nat.reducePow, UInt64.reduceToNat] at *
        omega
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hadd]
    generalize exponentBits x.toBits + 1021 - top = k at hk ⊢
    have hw : ((k <<< 52) + (x.toBits &&& 0x000FFFFFFFFFFFFF)).toNat =
        k.toNat * 2 ^ 52 + x.toBits.toNat % 2 ^ 52 := by
      rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_and, Nat.shiftLeft_eq,
        show (0x000FFFFFFFFFFFFF : UInt64).toNat = 2 ^ 52 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      simp only [Nat.reducePow, UInt64.reduceToNat, Nat.reduceMod] at *
      omega
    generalize (k <<< 52) + (x.toBits &&& 0x000FFFFFFFFFFFFF) = w at hw ⊢
    have hc : ¬(absBits x.toBits == 0 || (w >>> 52) &&& 0x7FF == 0x7FF) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or]
      refine ⟨hz, fun h => ?_⟩
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
        show (0x7FF : UInt64).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hw]
        at this
      simp only [Nat.reducePow, UInt64.reduceToNat, Nat.reduceMod] at *
      omega
    rw [ite_eq_right hc, ite_eq_right (by simpa using hz)]
    rw [toBits_ofBits_of_finite]
    · apply UInt64.toNat_inj.mp
      rw [hw, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, hA]
      simp only [Nat.reducePow, UInt64.reduceToNat] at *
      omega
    · rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_and,
        show (0x7FFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 63 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, hw]
      simp only [Nat.reducePow, UInt64.reduceToNat] at *
      omega


theorem topExponent_eq (rho mx my energy : Float) :
    topExponent rho mx my energy =
      F64Admissibility.topExponent rho.toBits mx.toBits my.toBits energy.toBits := by
  unfold F64Admissibility.topExponent F64Admissibility.maxWord
  simp only [← exponentBits_eq]

theorem normalizable_eq (x : Float) (top : UInt64) :
    normalizable x top = F64Admissibility.normalizable x.toBits top := by
  unfold F64Admissibility.normalizable
  simp only [← exponentBits_eq]
  rfl

theorem finite_of_positive {x : Float} (h : positive x = true) : finite x = true := by
  simp only [positive, finite, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at h ⊢
  rw [show (absBits x.toBits).toNat = x.toBits.toNat % 2 ^ 63 from F64Order.absBits_toNat _]
  simp only [UInt64.reduceToNat] at *
  omega

theorem positive_eq (x : Float) : positive x = F64Order.positiveBits x.toBits := rfl

theorem energyResidual_toBits (rho mx my energy : Float) :
    (energyResidual rho mx my energy).toBits =
      F64InternalEnergy.residual rho.toBits mx.toBits my.toBits energy.toBits := by
  simp only [energyResidual, F64InternalEnergy.residual, F64Bits.toBits_sub, F64Bits.toBits_mul,
    F64Bits.toBits_add, half_toBits]

/-- The energy guard computes the word-level admissibility check `F64Admissibility.checked`. -/
theorem energyGuard_checked {rho mx my energy : Float} (h : energyGuard rho mx my energy = true) :
    F64Admissibility.checked rho.toBits mx.toBits my.toBits energy.toBits = true := by
  unfold energyGuard at h
  dsimp only at h
  obtain ⟨hAB, hC⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hAB
  obtain ⟨h3, he⟩ := Bool.and_eq_true_iff.mp hA
  obtain ⟨h2, hy⟩ := Bool.and_eq_true_iff.mp h3
  obtain ⟨hr, hx⟩ := Bool.and_eq_true_iff.mp h2
  obtain ⟨n3, ne⟩ := Bool.and_eq_true_iff.mp hB
  obtain ⟨n2, ny⟩ := Bool.and_eq_true_iff.mp n3
  obtain ⟨nr, nx⟩ := Bool.and_eq_true_iff.mp n2
  have htop : (topExponent rho mx my energy).toNat =
      max (max (exponentBits rho.toBits).toNat (exponentBits mx.toBits).toNat)
        (max (exponentBits my.toBits).toNat (exponentBits energy.toBits).toNat) := by
    rw [topExponent_eq]
    simp only [F64Admissibility.topExponent, F64Admissibility.maxWord_toNat, ← exponentBits_eq]
  have er := normalized_toBits (finite_of_positive hr) nr (by omega)
  have ex := normalized_toBits hx nx (by omega)
  have ey := normalized_toBits hy ny (by omega)
  have ee := normalized_toBits (finite_of_positive he) ne (by omega)
  rw [positive_eq, energyResidual_toBits, er, ex, ey, ee, topExponent_eq] at hC
  rw [normalizable_eq, normalizable_eq, normalizable_eq, normalizable_eq, topExponent_eq] at hB
  unfold F64Admissibility.checked
  split
  · dsimp only
    split
    · exact hC
    · rename_i hn
      exact absurd hB hn
  · rename_i hn
    exact absurd hA hn

theorem narrowGuard_admissible {rho mx my energy : Float}
    (h : narrowGuard rho mx my energy = true) :
    Equations.Admissible ![real rho, real mx, real my, real energy] := by
  have h' : (F64Order.positiveBits rho.toBits && F64Order.finiteBits mx.toBits &&
      F64Order.finiteBits my.toBits && F64Order.positiveBits energy.toBits &&
      decide (F64Order.absBits mx.toBits ≤ rho.toBits) &&
      decide (F64Order.absBits my.toBits ≤ rho.toBits) &&
      decide (rho.toBits < energy.toBits)) = true := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨hr, -⟩, -⟩, he⟩, hmr⟩, htr⟩, hre⟩ := h'
  have hrf := F64Order.positiveBits_spec _ hr
  have hef := F64Order.positiveBits_spec _ he
  have hmag := F64Order.abs_value_mono mx.toBits rho.toBits (by
    simpa only [F64Order.absBits_of_positive _ hr] using hmr)
  have htmag := F64Order.abs_value_mono my.toBits rho.toBits (by
    simpa only [F64Order.absBits_of_positive _ hr] using htr)
  have henergy := F64Order.abs_value_lt rho.toBits energy.toBits (by
    simpa only [F64Order.absBits_of_positive _ hr, F64Order.absBits_of_positive _ he] using hre)
  rw [abs_of_pos hrf.2] at hmag htmag
  rw [abs_of_pos hrf.2, abs_of_pos hef.2] at henergy
  have hsquare (v r : ℝ) (hv : |v| ≤ r) : v ^ 2 ≤ r ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hv
    have hp := mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ r + v)
    nlinarith
  have hm := hsquare _ _ hmag
  have ht := hsquare _ _ htmag
  rw [admissible_iff]
  refine ⟨hrf.2, ?_⟩
  have hk : (value mx.toBits ^ 2 + value my.toBits ^ 2) / (2 * value rho.toBits) ≤
      value rho.toBits := by
    rw [div_le_iff₀ (by linarith [hrf.2])]
    nlinarith [hrf.2]
  simp only [real]
  linarith

/-- A state that passes the state guard is admissible in exact arithmetic. -/
theorem stateGuard_admissible {rho mx my energy : Float}
    (h : stateGuard rho mx my energy = true) :
    Equations.Admissible ![real rho, real mx, real my, real energy] := by
  rcases Bool.or_eq_true_iff.mp h with hn | he
  · exact narrowGuard_admissible hn
  · obtain ⟨-, -, -, -, hrp, -, hi⟩ :=
      F64Admissibility.checked_sound _ _ _ _ (energyGuard_checked he)
    rw [admissible_iff]
    refine ⟨hrp, ?_⟩
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity : 0 < 2 * value rho.toBits)).mpr
    nlinarith

end Examples.Euler
