import Project.ProofKit.F64AddUlp

namespace Project.ProofKit.F64PowerRounding
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem roundedMagnitude_above_power (n e : Nat) (he : 53 ≤ e)
    (hl : 2^e ≤ n) (hu : n < 2^e + 2^(e-53)) : roundedMagnitude n = 2^e := by
  let d := 2^(e-52)
  have hd : 0 < d := by dsimp [d]; positivity
  have hp : 2^e = 2^52*d := by
    change 2^e = 2^52 * 2^(e-52)
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have hh : 2^(e-53) = d/2 := by
    have hs : e-52 = (e-53)+1 := by omega
    dsimp [d]
    rw [hs, pow_succ, Nat.mul_div_left _ (by decide)]
  have hq : n/d = 2^52 := by
    have hlo : 2^52 ≤ n/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa only [← hp] using hl)
    have hhi : n/d < 2^52+1 := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [hp, hh] at hu; omega)
    omega
  have hr : n % d < d/2 := by
    have h := Nat.mod_add_div n d
    rw [hq] at h
    rw [hp, hh] at hu
    omega
  have hround : Wasm.IEEE32.roundShift n (e-52) = 2^52 := by
    change (if n % d < d/2 then n/d else if d/2 < n % d then n/d+1
      else if n/d % 2 == 0 then n/d else n/d+1) = _
    rw [ite_eq_left hr, hq]
  have hup : n < 2^(e+1) := by
    have hle : 2^(e-53) ≤ 2^e := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ]
    omega
  have hn : n ≠ 0 := by
    have hpos : 0 < 2^e := by positivity
    omega
  have hlog : Nat.log2 n = e := (Nat.log2_eq_iff hn).mpr ⟨hl, hup⟩
  have hmin : 2^53 ≤ n := (Nat.pow_le_pow_right (by decide) he).trans hl
  rw [F64Packing.roundedMagnitude_eq_shift n hmin, hlog, hround]
  exact hp.symm

theorem add_above_power (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (e : Nat) (hel : 53 ≤ e) (heu : e ≤ 2095)
    (hl : (2 : ℝ)^e/2^1074 ≤ value a+value b)
    (hu : value a+value b < ((2 : ℝ)^e+(2 : ℝ)^(e-53))/2^1074) :
    Finite (Wasm.IEEE64.add a b) ∧ value (Wasm.IEEE64.add a b) = (2 : ℝ)^e/2^1074 := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  have hz : value a+value b = (z : ℝ)/(2 : ℝ)^1074 := by
    simp only [value, z, Int.cast_add]
    ring
  rw [hz] at hl hu
  have hs : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hli : (2 : Int)^e ≤ z := by exact_mod_cast (div_le_div_iff_of_pos_right hs).mp hl
  have hui : z < (2 : Int)^e+(2 : Int)^(e-53) := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hs).mp hu
  have hpos : 0 < z := lt_of_lt_of_le (by positivity) hli
  have habs : (z.natAbs : Int) = z := (Int.eq_natAbs_of_nonneg hpos.le).symm
  have hnlo : 2^e ≤ z.natAbs := by
    rw [← habs] at hli
    exact_mod_cast hli
  have hnhi : z.natAbs < 2^e+2^(e-53) := by
    rw [← habs] at hui
    exact_mod_cast hui
  have hmax : z.natAbs < 2^2097 := by
    have h1 : 2^e ≤ 2^2095 := Nat.pow_le_pow_right (by decide) heu
    have h2 : 2^(e-53) ≤ 2^2095 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hr : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude false z.natAbs := by
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, z,
      show z ≠ 0 by omega, show ¬z < 0 by omega]
  have hp := F64Packing.pack_spec false z.natAbs hmax
  rw [hr]
  refine ⟨hp.1, ?_⟩
  rw [value, Wasm.IEEE64.scaledValue, hp.2.1, hp.2.2,
    roundedMagnitude_above_power _ e hel hnlo hnhi]
  simp

#print axioms add_above_power
end Project.ProofKit.F64PowerRounding
