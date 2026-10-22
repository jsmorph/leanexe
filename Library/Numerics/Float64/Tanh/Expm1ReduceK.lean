import Library.Numerics.Float64.Tanh.Expm1ReduceOne

/-!
The reduction of fdlibm's `expm1` from `abs(x) ≥ 1.5 log 2` on.  For positive `x` the code takes
`k` as the truncation of the rounded `x/log 2 + 1/2`, and for negative `x` it takes `-k` as the
truncation of the rounded `1/2 - x/log 2`.  The rounding errors of these quotients are below
`2 ^ -41`, so `abs(x - k log 2) ≤ log 2 (1/2 + 2 ^ -41)`.  The product `k ln2Hi` and the difference
`hi = x - k ln2Hi` are exact, and `reduce_k_pos` and `reduce_k_neg` place `y + c` within `2 ^ -70`
of `x - k log 2`.
-/

namespace Library.Numerics.Float64.Tanh.Expm1ReduceK
open CodeLib.IEEE64 LeanExe.ProofKit Expm1ReduceConst Expm1ReduceWords Expm1ReduceOne

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem log_two_bounds : 6931471805 / 10 ^ 10 ≤ Real.log 2 ∧ Real.log 2 ≤ 6931471806 / 10 ^ 10 := by
  have h := log_two_near
  have hc : 6931471805 / 10 ^ 10 + 1 / 2 ^ 92 ≤ Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo ∧
      Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo + 1 / 2 ^ 92 ≤ 6931471806 / 10 ^ 10 := by
    decide +kernel
  have h1 := (Rat.cast_le (K := ℝ)).mpr hc.1
  have h2 := (Rat.cast_le (K := ℝ)).mpr hc.2
  push_cast at h1 h2
  have := abs_le.mp h
  constructor <;> linarith

theorem invln2_value : 14426950408 / 10 ^ 10 ≤ value invln2 ∧ value invln2 ≤ 14426950409 / 10 ^ 10 := by
  rw [← PolyBound.ratOfWord_cast]
  have h : 14426950408 / 10 ^ 10 ≤ PolyBound.ratOfWord invln2 ∧
      PolyBound.ratOfWord invln2 ≤ 14426950409 / 10 ^ 10 := by decide +kernel
  exact ⟨((Rat.cast_le (K := ℝ)).mpr h.1).trans_eq' (by norm_num),
    ((Rat.cast_le (K := ℝ)).mpr h.2).trans_eq (by norm_num)⟩

/-- The rounded `invln2 · x` against `x/log 2`. -/
theorem quotient_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 7098 / 10) :
    Finite (Wasm.IEEE64.mul invln2 x) ∧
      |value (Wasm.IEEE64.mul invln2 x) - value x / Real.log 2| ≤ 1282 * u + η := by
  obtain ⟨-, -, hILf⟩ := const_finite
  obtain ⟨hL1, hL2⟩ := log_two_bounds
  obtain ⟨hI1, hI2⟩ := invln2_value
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hLpos : 0 < Real.log 2 := by linarith
  have hprod : |value invln2 * value x| ≤ 1025 := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < value invln2)]
    calc value invln2 * |value x| ≤ 14426950409 / 10 ^ 10 * (7098 / 10) :=
          mul_le_mul hI2 hx (abs_nonneg _) (by norm_num)
      _ ≤ 1025 := by norm_num
  have hm := F64MulBounds.mul_real_mixed invln2 x hILf hxf (hprod.trans_lt (by norm_num))
  refine ⟨hm.1, ?_⟩
  have hIL := invln2_bound
  have hdiff : |value invln2 * value x - value x / Real.log 2| ≤ 1025 / 4 * u := by
    have h1 : value invln2 * value x - value x / Real.log 2 =
        (value x / Real.log 2) * (value invln2 * Real.log 2 - 1) := by
      field_simp
    rw [h1, abs_mul, abs_div, abs_of_pos hLpos]
    have h2 : |value x| / Real.log 2 ≤ 1025 := by
      rw [div_le_iff₀ hLpos]; nlinarith
    calc |value x| / Real.log 2 * |value invln2 * Real.log 2 - 1| ≤ 1025 * (1 / 2 ^ 55) :=
          mul_le_mul h2 hIL (abs_nonneg _) (by norm_num)
      _ = 1025 / 4 * u := by rw [hu]; norm_num
  calc |value (Wasm.IEEE64.mul invln2 x) - value x / Real.log 2| ≤
      |value (Wasm.IEEE64.mul invln2 x) - value invln2 * value x| +
        |value invln2 * value x - value x / Real.log 2| := abs_sub_le _ _ _
    _ ≤ (u * 1025 + η) + 1025 / 4 * u := by
        refine add_le_add (hm.2.trans ?_) hdiff
        have := mul_le_mul_of_nonneg_left hprod hu0
        linarith
    _ ≤ 1282 * u + η := by linarith

/-- A word with value in `(0, 2 ^ 62)` and its floor as a natural number. -/
theorem floor_bounds (q : UInt64) (hqf : Finite q) (hq0 : 1 < value q) (hq : value q < 2 ^ 62) :
    ((Wasm.IEEE64.truncSatI64U q).toNat : ℝ) ≤ value q ∧
      value q < (Wasm.IEEE64.truncSatI64U q).toNat + 1 ∧
      (Wasm.IEEE64.truncSatI64U q).toNat < 2 ^ 62 := by
  have hs := (F64Magnitude.normal_of_value q (lt_trans (by norm_num) hq0)).2
  exact truncSat_spec q hqf hs hq

/-- The integer word `t` with `value t = ±K` and magnitude `K · 2 ^ 1074`. -/
theorem integer_word (m : UInt64) (hm : m.toNat < 2 ^ 53) :
    Finite (Wasm.IEEE64.convertI64U m) ∧
      value (Wasm.IEEE64.convertI64U m) = m.toNat ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.convertI64U m) = m.toNat * 2 ^ 1074 := by
  obtain ⟨hf, hv⟩ := convert_spec m hm
  refine ⟨hf, ?_, ?_⟩
  · rw [value, hv]
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    field_simp
  · rw [← natAbs_scaledValue, hv]
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
    rfl

theorem negate_magnitude (w : UInt64) :
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) = Wasm.IEEE64.scaledMagnitude w := by
  have he : Wasm.IEEE64.exponent w < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  unfold Wasm.IEEE64.negate
  rw [scaledMagnitude_encodeFinite _ _ _ he hf]
  simp [Wasm.IEEE64.scaledMagnitude]

theorem ln2_gap : |Real.log 2 - value ln2Hi| ≤ 19091 / 10 ^ 14 := by
  have hs := ln2_split
  obtain ⟨hL0, hL2⟩ := ln2Lo_bound
  have h1 : Real.log 2 - value ln2Hi = (Real.log 2 - value ln2Hi - value ln2Lo) + value ln2Lo := by
    ring
  rw [h1]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_pos hL0]
  have : (1 : ℝ) / 2 ^ 86 + 1909 / 10 ^ 13 ≤ 19091 / 10 ^ 14 := by norm_num
  linarith

/-- The common end of both signs: from the exact `hi = x - K' ln2Hi` and `lo` near `K' ln2Lo`,
with `K' = ±K`, `y + c` lies within `2 ^ -70` of `x - K' log 2`. -/
theorem reduce_end (x hi lo : UInt64) (hhf : Finite hi) (hlf : Finite lo) (K : ℤ)
    (hK : |K| ≤ 1024) (hH : value hi = value x - K * value ln2Hi)
    (hXK : |value x - K * Real.log 2| ≤ 3465736 / 10 ^ 7)
    (hlo : |value lo - K * value ln2Lo| ≤ 1 / 2 ^ 74) :
    Finite (Wasm.IEEE64.sub hi lo) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) ∧
      |value (Wasm.IEEE64.sub hi lo)| ≤ 3466 / 10000 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo)| ≤ 36 / 100 * u ∧
      |value (Wasm.IEEE64.sub hi lo) +
          value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) -
        (value x - K * Real.log 2)| ≤ 1 / 2 ^ 70 := by
  have hgap := ln2_gap
  have hs := ln2_split
  obtain ⟨hL0, hL2⟩ := ln2Lo_bound
  have hKr : |(K : ℝ)| ≤ 1024 := by exact_mod_cast hK
  have hHm : |value hi| ≤ 34658 / 100000 := by
    rw [hH]
    have h1 : value x - K * value ln2Hi = (value x - K * Real.log 2) + K * (Real.log 2 - value ln2Hi) := by
      ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have : |(K : ℝ)| * |Real.log 2 - value ln2Hi| ≤ 1024 * (19091 / 10 ^ 14) :=
      mul_le_mul hKr hgap (abs_nonneg _) (by norm_num)
    have : (3465736 : ℝ) / 10 ^ 7 + 1024 * (19091 / 10 ^ 14) ≤ 34658 / 100000 := by norm_num
    linarith
  have hLm : |value lo| ≤ 2 / 10 ^ 7 := by
    have h1 := abs_sub_abs_le_abs_sub (value lo) (K * value ln2Lo)
    have h2 : |(K : ℝ) * value ln2Lo| ≤ 1024 * (1909 / 10 ^ 13) := by
      rw [abs_mul, abs_of_pos hL0]
      exact mul_le_mul hKr hL2 hL0.le (by norm_num)
    have : (1024 : ℝ) * (1909 / 10 ^ 13) + 1 / 2 ^ 74 ≤ 2 / 10 ^ 7 := by norm_num
    linarith
  obtain ⟨hyf, hcf, hy, hc, hyc⟩ := yc_spec hi lo hhf hlf hHm hLm
  refine ⟨hyf, hcf, hy, hc, ?_⟩
  have h1 : value (Wasm.IEEE64.sub hi lo) +
      value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) -
        (value x - K * Real.log 2) =
      (value (Wasm.IEEE64.sub hi lo) +
        value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) -
          (value hi - value lo)) +
      (K * (Real.log 2 - value ln2Hi - value ln2Lo) - (value lo - K * value ln2Lo)) := by
    rw [hH]; ring
  rw [h1]
  refine (abs_add_le _ _).trans ?_
  have h2 : |(K : ℝ) * (Real.log 2 - value ln2Hi - value ln2Lo) - (value lo - K * value ln2Lo)| ≤
      1024 * (1 / 2 ^ 86) + 1 / 2 ^ 74 := by
    refine (abs_sub _ _).trans (add_le_add ?_ hlo)
    rw [abs_mul]
    exact mul_le_mul hKr hs (abs_nonneg _) (by norm_num)
  have : (1 : ℝ) / 2 ^ 74 + (1024 * (1 / 2 ^ 86) + 1 / 2 ^ 74) ≤ 1 / 2 ^ 70 := by norm_num
  linarith

/-- The product `t ln2Lo` against `K' ln2Lo`. -/
theorem lo_spec (t : UInt64) (htf : Finite t) (K : ℤ) (hK : |K| ≤ 1024) (ht : value t = K) :
    Finite (Wasm.IEEE64.mul t ln2Lo) ∧
      |value (Wasm.IEEE64.mul t ln2Lo) - K * value ln2Lo| ≤ 1 / 2 ^ 74 := by
  obtain ⟨-, hLf, -⟩ := const_finite
  obtain ⟨hL0, hL2⟩ := ln2Lo_bound
  have hKr : |(K : ℝ)| ≤ 1024 := by exact_mod_cast hK
  have hp : |value t * value ln2Lo| ≤ 1024 * (1909 / 10 ^ 13) := by
    rw [ht, abs_mul, abs_of_pos hL0]
    exact mul_le_mul hKr hL2 hL0.le (by norm_num)
  have hm := F64MulBounds.mul_real_mixed t ln2Lo htf hLf (hp.trans_lt (by norm_num))
  refine ⟨hm.1, ?_⟩
  rw [← ht]
  refine hm.2.trans ?_
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have : unitRoundoff64 * |value t * value ln2Lo| ≤ 1 / 2 ^ 53 * (1024 * (1909 / 10 ^ 13)) := by
    rw [hu]; exact mul_le_mul_of_nonneg_left hp (by positivity)
  have h2 : (1 : ℝ) / 2 ^ 53 * (1024 * (1909 / 10 ^ 13)) + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 74 := by norm_num
  rw [hη]
  linarith

/-- `k ≥ 1`: the reduction for `1.0397205 ≤ x ≤ 709.782712893384`. -/
theorem reduce_k_pos (x : UInt64) (hxf : Finite x) (hlo : 10397205 / 10 ^ 7 ≤ value x)
    (hhi : value x ≤ 7097827128933840 / 10 ^ 13) :
    let m := Wasm.IEEE64.truncSatI64U (Wasm.IEEE64.add (Wasm.IEEE64.mul invln2 x) Expm1Words.half)
    let t := Wasm.IEEE64.convertI64U m
    let hi := Wasm.IEEE64.sub x (Wasm.IEEE64.mul t ln2Hi)
    let lo := Wasm.IEEE64.mul t ln2Lo
    1 ≤ m.toNat ∧ m.toNat ≤ 1024 ∧
      Finite (Wasm.IEEE64.sub hi lo) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) ∧
      |value (Wasm.IEEE64.sub hi lo)| ≤ 3466 / 10000 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo)| ≤ 36 / 100 * u ∧
      |value (Wasm.IEEE64.sub hi lo) +
          value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) -
        (value x - (m.toNat : ℤ) * Real.log 2)| ≤ 1 / 2 ^ 70 := by
  intro m t hi lo
  obtain ⟨hL1, hL2⟩ := log_two_bounds
  have hLpos : 0 < Real.log 2 := by linarith
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  obtain ⟨hpf, hp⟩ := quotient_spec x hxf (by rw [abs_of_pos (by linarith)]; linarith)
  have hhalf : value Expm1Words.half = 1 / 2 := Expm1KernelInner.const_values.2.1
  have hhf : Finite Expm1Words.half := Expm1KernelInner.const_finite.2.1
  set P := value (Wasm.IEEE64.mul invln2 x)
  have hXL : value x / Real.log 2 ≤ 10241 / 10 := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hXL0 : 14999996 / 10 ^ 7 ≤ value x / Real.log 2 := by
    rw [le_div_iff₀ hLpos]; nlinarith
  have hsmall : 1282 * u + η ≤ 1 / 2 ^ 42 := by rw [hu, hη]; norm_num
  have hpb := abs_le.mp hp
  have hP : |P + value Expm1Words.half| ≤ 1026 := by
    rw [hhalf, abs_le]; constructor <;> linarith
  have hq := F64AddBounds.add_real_relative _ _ hpf hhf (hP.trans_lt (by norm_num))
  set q := Wasm.IEEE64.add (Wasm.IEEE64.mul invln2 x) Expm1Words.half
  have hqe : |value q - (value x / Real.log 2 + 1 / 2)| ≤ 1 / 2 ^ 41 := by
    have h1 : value q - (value x / Real.log 2 + 1 / 2) =
        (value q - (P + value Expm1Words.half)) + (P - value x / Real.log 2) := by
      rw [hhalf]; ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    have h2 : u * |P + value Expm1Words.half| ≤ 1 / 2 ^ 53 * 1026 := by
      rw [hu]; exact mul_le_mul_of_nonneg_left hP (by positivity)
    have h3 : (1 : ℝ) / 2 ^ 53 * 1026 + 1 / 2 ^ 42 ≤ 1 / 2 ^ 41 := by norm_num
    linarith [hq.2]
  have hqeb := abs_le.mp hqe
  have h41 : (1 : ℝ) / 2 ^ 41 ≤ 1 / 10 ^ 12 := by norm_num
  obtain ⟨hK1r, hK2r, hK62⟩ := floor_bounds q hq.1 (by linarith) (by linarith)
  set K := m.toNat
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := by linarith
    exact_mod_cast this
  have hK2 : K ≤ 1024 := by
    have : (K : ℝ) < 1025 := by linarith
    have : K < 1025 := by exact_mod_cast this
    omega
  refine ⟨hK1, hK2, ?_⟩
  -- `abs(x/log 2 - K) ≤ 1/2 + 2 ^ -41`.
  have hXK : |value x - (K : ℤ) * Real.log 2| ≤ 3465736 / 10 ^ 7 := by
    have h1 : value x - (K : ℤ) * Real.log 2 = Real.log 2 * (value x / Real.log 2 - K) := by
      push_cast; field_simp
    rw [h1, abs_mul, abs_of_pos hLpos]
    have h2 : |value x / Real.log 2 - K| ≤ 1 / 2 + 1 / 2 ^ 41 := by
      rw [abs_le]; constructor <;> linarith
    calc Real.log 2 * |value x / Real.log 2 - K| ≤ 6931471806 / 10 ^ 10 * (1 / 2 + 1 / 2 ^ 41) :=
          mul_le_mul hL2 h2 (abs_nonneg _) (by norm_num)
      _ ≤ 3465736 / 10 ^ 7 := by norm_num
  obtain ⟨htf, htv, htm⟩ := integer_word m (by omega)
  obtain ⟨hmf, hmv⟩ := mul_ln2Hi t htf K hK2 htm
  obtain ⟨hHf, -, -⟩ := const_finite
  have hx21 : 2 ^ 1021 ∣ Wasm.IEEE64.scaledMagnitude x :=
    grid_of_magnitude x 1021 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have hL1v := ln2Hi_value
  have htL : (1 : ℝ) / 2 ≤ |value (Wasm.IEEE64.mul t ln2Hi)| := by
    rw [hmv, htv, hL1v, abs_of_pos (by positivity)]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    nlinarith
  have ht21 : 2 ^ 1021 ∣ Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul t ln2Hi) :=
    grid_of_magnitude _ 1021 (by norm_num; exact htL)
  have hgap := ln2_gap
  obtain ⟨hhif, hhiv⟩ := diff_exact x _ hxf hmf 1021 (by norm_num) hx21 ht21 (by
    rw [hmv, htv]
    have h1 : value x - K * value ln2Hi = (value x - (K : ℤ) * Real.log 2) +
        (K : ℝ) * (Real.log 2 - value ln2Hi) := by push_cast; ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.abs_cast]
    have : (K : ℝ) * |Real.log 2 - value ln2Hi| ≤ 1024 * (19091 / 10 ^ 14) :=
      mul_le_mul (by exact_mod_cast hK2) hgap (abs_nonneg _) (by norm_num)
    have h2 : (3465736 : ℝ) / 10 ^ 7 + 1024 * (19091 / 10 ^ 14) ≤ 2 ^ (53 + 1021) / 2 ^ 1074 := by
      norm_num
    linarith)
  obtain ⟨hlof, hlov⟩ := lo_spec t htf K (by rw [Nat.abs_cast]; exact_mod_cast hK2) (by rw [htv]; push_cast; rfl)
  exact reduce_end x hi lo hhif hlof K (by rw [Nat.abs_cast]; exact_mod_cast hK2)
    (by rw [hhiv, hmv, htv]; push_cast; ring) hXK hlov

/-- `k ≤ -1`: the reduction for `-38.817 ≤ x ≤ -1.0397205`, where `k = -m`. -/
theorem reduce_k_neg (x : UInt64) (hxf : Finite x) (hlo : -38817 / 1000 ≤ value x)
    (hhi : value x ≤ -10397205 / 10 ^ 7) :
    let m := Wasm.IEEE64.truncSatI64U
      (Wasm.IEEE64.negate (Wasm.IEEE64.sub (Wasm.IEEE64.mul invln2 x) Expm1Words.half))
    let t := Wasm.IEEE64.negate (Wasm.IEEE64.convertI64U m)
    let hi := Wasm.IEEE64.sub x (Wasm.IEEE64.mul t ln2Hi)
    let lo := Wasm.IEEE64.mul t ln2Lo
    1 ≤ m.toNat ∧ m.toNat ≤ 56 ∧
      Finite (Wasm.IEEE64.sub hi lo) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) ∧
      |value (Wasm.IEEE64.sub hi lo)| ≤ 3466 / 10000 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo)| ≤ 36 / 100 * u ∧
      |value (Wasm.IEEE64.sub hi lo) +
          value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) -
        (value x + (m.toNat : ℤ) * Real.log 2)| ≤ 1 / 2 ^ 70 := by
  intro m t hi lo
  obtain ⟨hL1, hL2⟩ := log_two_bounds
  have hLpos : 0 < Real.log 2 := by linarith
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  obtain ⟨hpf, hp⟩ := quotient_spec x hxf (by rw [abs_of_neg (by linarith)]; linarith)
  have hhalf : value Expm1Words.half = 1 / 2 := Expm1KernelInner.const_values.2.1
  have hhf : Finite Expm1Words.half := Expm1KernelInner.const_finite.2.1
  set P := value (Wasm.IEEE64.mul invln2 x)
  have hXL : -5601 / 100 ≤ value x / Real.log 2 := by
    rw [le_div_iff₀ hLpos]; nlinarith
  have hXL0 : value x / Real.log 2 ≤ -14999996 / 10 ^ 7 := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hsmall : 1282 * u + η ≤ 1 / 2 ^ 42 := by rw [hu, hη]; norm_num
  have hpb := abs_le.mp hp
  have hP : |P - value Expm1Words.half| ≤ 57 := by
    rw [hhalf, abs_le]; constructor <;> linarith
  have hq := F64AddBounds.sub_real_relative _ _ hpf hhf (hP.trans_lt (by norm_num))
  set q := Wasm.IEEE64.sub (Wasm.IEEE64.mul invln2 x) Expm1Words.half
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value q hq.1
  have hqe : |value (Wasm.IEEE64.negate q) - (1 / 2 - value x / Real.log 2)| ≤ 1 / 2 ^ 41 := by
    have h1 : value (Wasm.IEEE64.negate q) - (1 / 2 - value x / Real.log 2) =
        -((value q - (P - value Expm1Words.half)) + (P - value x / Real.log 2)) := by
      rw [hnv, hhalf]; ring
    rw [h1, abs_neg]
    refine (abs_add_le _ _).trans ?_
    have h2 : u * |P - value Expm1Words.half| ≤ 1 / 2 ^ 53 * 57 := by
      rw [hu]; exact mul_le_mul_of_nonneg_left hP (by positivity)
    have h3 : (1 : ℝ) / 2 ^ 53 * 57 + 1 / 2 ^ 42 ≤ 1 / 2 ^ 41 := by norm_num
    linarith [hq.2]
  have hqeb := abs_le.mp hqe
  have h41 : (1 : ℝ) / 2 ^ 41 ≤ 1 / 10 ^ 12 := by norm_num
  obtain ⟨hK1r, hK2r, hK62⟩ := floor_bounds _ hnf (by linarith) (by linarith)
  set K := m.toNat
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := by linarith
    exact_mod_cast this
  have hK2 : K ≤ 56 := by
    have : (K : ℝ) < 57 := by linarith
    have : K < 57 := by exact_mod_cast this
    omega
  refine ⟨hK1, hK2, ?_⟩
  have hXK : |value x - (-(K : ℤ)) * Real.log 2| ≤ 3465736 / 10 ^ 7 := by
    have h1 : value x - (-(K : ℤ)) * Real.log 2 = Real.log 2 * (value x / Real.log 2 + K) := by
      have h0 : Real.log 2 * (value x / Real.log 2) = value x := by field_simp
      push_cast; rw [mul_add, h0]; ring
    rw [h1, abs_mul, abs_of_pos hLpos]
    have h2 : |value x / Real.log 2 + K| ≤ 1 / 2 + 1 / 2 ^ 41 := by
      rw [abs_le]; constructor <;> linarith
    calc Real.log 2 * |value x / Real.log 2 + K| ≤ 6931471806 / 10 ^ 10 * (1 / 2 + 1 / 2 ^ 41) :=
          mul_le_mul hL2 h2 (abs_nonneg _) (by norm_num)
      _ ≤ 3465736 / 10 ^ 7 := by norm_num
  obtain ⟨hcf, hcv, hcm⟩ := integer_word m (by omega)
  obtain ⟨htf, htv⟩ := F64Magnitude.negate_value _ hcf
  have htm : Wasm.IEEE64.scaledMagnitude t = K * 2 ^ 1074 := by
    rw [negate_magnitude]; exact hcm
  obtain ⟨hmf, hmv⟩ := mul_ln2Hi t htf K (by omega) htm
  have hx21 : 2 ^ 1021 ∣ Wasm.IEEE64.scaledMagnitude x :=
    grid_of_magnitude x 1021 (by rw [abs_of_neg (by linarith)]; norm_num; linarith)
  have hL1v := ln2Hi_value
  have htL : (1 : ℝ) / 2 ≤ |value (Wasm.IEEE64.mul t ln2Hi)| := by
    rw [hmv, htv, hcv, hL1v, abs_mul, abs_neg, Nat.abs_cast, abs_of_pos (by positivity)]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    nlinarith
  have ht21 : 2 ^ 1021 ∣ Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul t ln2Hi) :=
    grid_of_magnitude _ 1021 (by norm_num; exact htL)
  have hgap := ln2_gap
  have hK56 : (K : ℝ) ≤ 56 := by exact_mod_cast hK2
  obtain ⟨hhif, hhiv⟩ := diff_exact x _ hxf hmf 1021 (by norm_num) hx21 ht21 (by
    rw [hmv, htv, hcv]
    have h1 : value x - -(K : ℝ) * value ln2Hi = (value x - (-(K : ℤ)) * Real.log 2) -
        (K : ℝ) * (Real.log 2 - value ln2Hi) := by push_cast; ring
    rw [h1]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, Nat.abs_cast]
    have : (K : ℝ) * |Real.log 2 - value ln2Hi| ≤ 56 * (19091 / 10 ^ 14) :=
      mul_le_mul hK56 hgap (abs_nonneg _) (by norm_num)
    have h2 : (3465736 : ℝ) / 10 ^ 7 + 56 * (19091 / 10 ^ 14) ≤ 2 ^ (53 + 1021) / 2 ^ 1074 := by
      norm_num
    linarith)
  have hKa : |(-(K : ℤ))| ≤ 1024 := by rw [abs_neg, Nat.abs_cast]; omega
  obtain ⟨hlof, hlov⟩ := lo_spec t htf (-(K : ℤ)) hKa (by rw [htv, hcv]; push_cast; rfl)
  have h := reduce_end x hi lo hhif hlof (-(K : ℤ)) hKa
    (by rw [hhiv, hmv, htv, hcv]; push_cast; ring) (by have h0 := hXK; push_cast at h0 ⊢; exact h0)
    hlov
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  exact (le_of_eq (congrArg abs (by push_cast; ring))).trans h.2.2.2.2

#print axioms reduce_k_pos
#print axioms reduce_k_neg

end Library.Numerics.Float64.Tanh.Expm1ReduceK
