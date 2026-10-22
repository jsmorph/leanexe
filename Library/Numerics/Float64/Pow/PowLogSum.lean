import Library.Numerics.Float64.Pow.PowLogReduce

/-!
The exact steps of `Pow.powLog` among its sums, on the grid of `2 ^ -60` (`2 ^ 1014` scaled
units).  `t1 = k ln2hi + logc` is exact on the grid of `2 ^ -43`.  A sum `s = a + b` of two words
on the grid, with `|b| ≤ 1/150`, is on the grid itself: either it is exact or `|s| ≥ 2 ^ -8`,
where every word lies on the grid.  Then `a - s` and `(a - s) + b` are exact, so `lo2` and `lo4`
are the exact errors of `t2` and `hi`.  The halving products `ar` and `arhi` are exact, and so is
`arhi2 = rhi arhi`, on the grid of `2 ^ -59`.  `lo1 = k ln2lo + logctail` carries two roundings,
and is exact for `k = 0` up to the rounding of `logctail`.
-/

namespace Library.Numerics.Float64.Pow.PowLogSum
open CodeLib.IEEE64 LeanExe.ProofKit PowLogReduce

set_option exponentiation.threshold 4096

theorem sv_cast (w : UInt64) :
    ((Wasm.IEEE64.scaledValue w : Int) : ℝ) = value w * 2 ^ 1074 := by
  rw [value]
  field_simp

theorem sv_bound_gen (z : Int) (x c : ℝ) (B : Int) (hz : (z : ℝ) = x * 2 ^ 1074)
    (hx : |x| ≤ c) (hc : c * 2 ^ 1074 ≤ (B : ℝ)) : |z| ≤ B := by
  have h : |(z : ℝ)| ≤ (B : ℝ) := by
    rw [hz, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    exact (mul_le_mul_of_nonneg_right hx (by positivity)).trans hc
  rw [← Int.cast_abs] at h
  exact_mod_cast h

theorem sv_bound (z : Int) (x : ℝ) (hz : (z : ℝ) = x * 2 ^ 1074) (hx : |x| ≤ 1 / 2 ^ 7) :
    |z| ≤ 2 ^ 53 * 2 ^ 1014 :=
  sv_bound_gen z x _ _ hz hx (by push_cast; norm_num)

theorem sv_eq_of_value {a b : UInt64} (h : value a = value b) :
    Wasm.IEEE64.scaledValue a = Wasm.IEEE64.scaledValue b := by
  have hc : ((Wasm.IEEE64.scaledValue a : Int) : ℝ) = ((Wasm.IEEE64.scaledValue b : Int) : ℝ) := by
    rw [sv_cast, sv_cast, h]
  exact_mod_cast hc

theorem dvd_of_magnitude (w : UInt64) (s : Nat) (h : 2 ^ s ∣ Wasm.IEEE64.scaledMagnitude w) :
    (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue w := by
  rw [← Int.dvd_natAbs, natAbs_scaledValue]
  exact_mod_cast h

/-- A word of magnitude at least `2 ^ -8` lies on the grid of `2 ^ -60`. -/
theorem grid_of_large (w : UInt64) (h : 1 / 2 ^ 8 ≤ |value w|) :
    (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue w := by
  have he : 1015 ≤ Wasm.IEEE64.exponent w := by
    by_contra hn
    have hm := F64Magnitude.magnitude_lt w 1015 (-8) (by norm_num) (by norm_num) (by omega)
    have h8 : (2 : ℝ) ^ (-8 : Int) = 1 / 2 ^ 8 := by norm_num
    rw [h8] at hm
    exact absurd h (not_le.mpr hm)
  apply dvd_of_magnitude
  simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, show Wasm.IEEE64.exponent w ≠ 0 by omega,
    ite_false]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _

/-- A rounded sum of two words on the grid of `2 ^ -60`, with its exact error. -/
theorem grid_sum (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hda : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue a)
    (hdb : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue b)
    (hab : |value a + value b| ≤ 2 ^ 11) (hbs : |value b| ≤ 1 / 150) :
    Finite (Wasm.IEEE64.add a b) ∧
      (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
        unitRoundoff64 * |value a + value b| ∧
      Finite (Wasm.IEEE64.add (Wasm.IEEE64.sub a (Wasm.IEEE64.add a b)) b) ∧
      value (Wasm.IEEE64.add (Wasm.IEEE64.sub a (Wasm.IEEE64.add a b)) b) =
        value a + value b - value (Wasm.IEEE64.add a b) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  obtain ⟨hsf, hse⟩ := F64AddBounds.add_real_relative a b ha hb (hab.trans_lt (by norm_num))
  set s := Wasm.IEEE64.add a b
  have hse' : |value s - (value a + value b)| ≤ 1 / 2 ^ 53 * 2 ^ 11 := by
    rw [← hu]
    exact hse.trans (mul_le_mul_of_nonneg_left hab (by rw [hu]; positivity))
  have hds : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue s := by
    by_cases hsmall : |value a + value b| ≤ 1 / 2 ^ 7
    · obtain ⟨_, hv⟩ := F64ErrorTrack.add_exact_grid a b ha hb 1014 (by norm_num) hda hdb
        (sv_bound _ (value a + value b) (by push_cast; rw [sv_cast, sv_cast]; ring) hsmall)
      have hsv : Wasm.IEEE64.scaledValue s =
          Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
        have hc : ((Wasm.IEEE64.scaledValue s : Int) : ℝ) =
            ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : Int) : ℝ) := by
          push_cast
          rw [sv_cast, sv_cast, sv_cast, hv]
          ring
        exact_mod_cast hc
      rw [hsv]
      exact dvd_add hda hdb
    · push Not at hsmall
      apply grid_of_large
      have h1 := abs_sub_abs_le_abs_sub (value a + value b) (value s)
      rw [abs_sub_comm] at h1
      have h2 : unitRoundoff64 * |value a + value b| ≤ 1 / 2 ^ 53 * 2 ^ 11 := by
        rw [hu]
        exact mul_le_mul_of_nonneg_left hab (by positivity)
      have h3 : (1 : ℝ) / 2 ^ 8 + 1 / 2 ^ 53 * 2 ^ 11 ≤ 1 / 2 ^ 7 := by norm_num
      linarith
  -- `a - s` is exact
  have hsub : |value a - value s| ≤ 1 / 2 ^ 7 := by
    have h1 := abs_le.mp hse'
    have h2 := abs_le.mp hbs
    have h3 : (1 : ℝ) / 150 + 1 / 2 ^ 53 * 2 ^ 11 ≤ 1 / 2 ^ 7 := by norm_num
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hdf, hdv⟩ := F64ErrorTrack.sub_exact_grid a s ha hsf 1014 (by norm_num) hda hds
    (sv_bound _ (value a - value s) (by push_cast; rw [sv_cast, sv_cast]; ring) hsub)
  set d := Wasm.IEEE64.sub a s
  have hdd : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue d := by
    have hc : ((Wasm.IEEE64.scaledValue d : Int) : ℝ) =
        ((Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue s : Int) : ℝ) := by
      push_cast
      rw [sv_cast, sv_cast, sv_cast, hdv]
      ring
    have hsv : Wasm.IEEE64.scaledValue d =
        Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue s := by exact_mod_cast hc
    rw [hsv]
    exact dvd_sub hda hds
  -- `(a - s) + b` is exact
  have hlast : |value d + value b| ≤ 1 / 2 ^ 7 := by
    rw [hdv, show value a - value s + value b = -(value s - (value a + value b)) by ring,
      abs_neg]
    exact hse'.trans (by norm_num)
  obtain ⟨hlf, hlv⟩ := F64ErrorTrack.add_exact_grid d b hdf hb 1014 (by norm_num) hdd hdb
    (sv_bound _ (value d + value b) (by push_cast; rw [sv_cast, sv_cast]; ring) hlast)
  refine ⟨hsf, hds, hse, hlf, ?_⟩
  rw [hlv, hdv]
  ring

/-- The word of `log 2` high: `3048493539143 · 2 ^ -42`. -/
theorem ln2hi_scaled : Wasm.IEEE64.scaledValue 0x3FE62E42FEFA3800 = 3048493539143 * 2 ^ 1032 := by
  decide +kernel

theorem ln2_words :
    Finite 0x3FE62E42FEFA3800 ∧ Finite 0x3D2EF35793C76730 ∧
      0 < value 0x3FE62E42FEFA3800 ∧ value 0x3FE62E42FEFA3800 ≤ 6932 / 10000 ∧
      |value 0x3D2EF35793C76730| ≤ 1 / 2 ^ 44 := by
  have h1 : PolyBound.ratOfWord 0x3FE62E42FEFA3800 ≤ 6932 / 10000 ∧
      0 < PolyBound.ratOfWord 0x3FE62E42FEFA3800 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0x3D2EF35793C76730) ≤ 1 / 2 ^ 44 := by decide +kernel
  obtain ⟨h1, h2, h3⟩ := h1
  have h1' := PowLogTable.rat_le h1
  have h2' : ((0 : ℚ) : ℝ) < ((PolyBound.ratOfWord 0x3FE62E42FEFA3800 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr h2
  have h3' := PowLogTable.rat_le h3
  rw [PolyBound.ratOfWord_cast] at h1' h2'
  rw [PolyBound.qabs_cast, PolyBound.ratOfWord_cast] at h3'
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, by unfold CodeLib.IEEE64.Finite; decide,
    by simpa using h2', by simpa using h1', by simpa using h3'⟩

/-- `t1 = k ln2hi + logc`, exact on the grid of `2 ^ -43`. -/
theorem t1_exact (kd lc : UInt64) (K : Int) (hkf : Finite kd) (hkv : value kd = K)
    (hK : |K| ≤ 1100) (hlf : Finite lc) (hlg : Wasm.IEEE64.scaledValue lc % 2 ^ 1031 = 0)
    (hlb : |value lc| ≤ 3466 / 10000) :
    Finite (Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc) ∧
      value (Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc) =
        K * value 0x3FE62E42FEFA3800 + value lc ∧
      (2 : Int) ^ 1014 ∣
        Wasm.IEEE64.scaledValue (Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc) ∧
      |value (Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc)| ≤ 763 := by
  obtain ⟨hhf, -, hh0, hh1, -⟩ := ln2_words
  have hksv : Wasm.IEEE64.scaledValue kd = K * 2 ^ 1074 :=
    sv_of_value kd K 1074 (by norm_num) (by rw [hkv]; norm_num)
  have hKn : K.natAbs ≤ 1100 := by
    have := abs_le.mp hK
    omega
  obtain ⟨hpf, hpv, -, -⟩ := F64ExactProduct.mul_exact_scaled kd 0x3FE62E42FEFA3800 hkf hhf
    K.natAbs 3048493539143 1074 1032 (magnitude_of_value kd K 1074 hksv)
    (by rw [magnitude_of_value _ 3048493539143 1032 ln2hi_scaled]; rfl)
    (by calc K.natAbs * 3048493539143 ≤ 1100 * 3048493539143 := Nat.mul_le_mul_right _ hKn
          _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  set p := Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800
  have hpsv : Wasm.IEEE64.scaledValue p = (K * 3048493539143) * 2 ^ 1032 := by
    apply sv_of_value p _ 1032 (by norm_num)
    rw [hpv, hkv, value_of_scaled _ _ 1032 (by norm_num) ln2hi_scaled]
    push_cast
    ring
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hlg
  have hdp : (2 : Int) ^ 1031 ∣ Wasm.IEEE64.scaledValue p :=
    ⟨K * 3048493539143 * 2, by rw [hpsv]; ring⟩
  have hdl : (2 : Int) ^ 1031 ∣ Wasm.IEEE64.scaledValue lc := ⟨c, hc⟩
  have hsum : |value p + value lc| ≤ 763 := by
    rw [hpv, hkv]
    have hK' : |(K : ℝ)| ≤ 1100 := by exact_mod_cast hK
    have h1 : |(K : ℝ) * value 0x3FE62E42FEFA3800| ≤ 1100 * (6932 / 10000) := by
      rw [abs_mul, abs_of_pos hh0]
      exact mul_le_mul hK' hh1 hh0.le (by norm_num)
    have := abs_add_le ((K : ℝ) * value 0x3FE62E42FEFA3800) (value lc)
    have h2 : (1100 : ℝ) * (6932 / 10000) + 3466 / 10000 ≤ 763 := by norm_num
    linarith
  obtain ⟨htf, htv⟩ := F64ErrorTrack.add_exact_grid p lc hpf hlf 1031 (by norm_num) hdp hdl
    (sv_bound_gen _ (value p + value lc) 763 _ (by push_cast; rw [sv_cast, sv_cast]; ring) hsum
      (by push_cast; norm_num))
  have htsv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.add p lc) =
      Wasm.IEEE64.scaledValue p + Wasm.IEEE64.scaledValue lc := by
    have hc' : ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.add p lc) : Int) : ℝ) =
        ((Wasm.IEEE64.scaledValue p + Wasm.IEEE64.scaledValue lc : Int) : ℝ) := by
      push_cast
      rw [sv_cast, sv_cast, sv_cast, htv]
      ring
    exact_mod_cast hc'
  refine ⟨htf, by rw [htv, hpv, hkv], ?_, by rw [htv]; exact hsum⟩
  rw [htsv]
  exact dvd_trans (pow_dvd_pow 2 (by norm_num)) (dvd_add hdp hdl)

/-- The halving product `A0 · a = -a/2` for a word on a grid of at least `2 ^ -1073`. -/
theorem half_exact (a : UInt64) (ha : Finite a) (q : Int) (s : Nat) (hs1 : 1 ≤ s)
    (hs2 : s ≤ 1074) (hv : Wasm.IEEE64.scaledValue a = q * 2 ^ s) (hq : q.natAbs < 2 ^ 53) :
    Finite (Wasm.IEEE64.mul 0xBFE0000000000000 a) ∧
      value (Wasm.IEEE64.mul 0xBFE0000000000000 a) = -(value a / 2) ∧
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul 0xBFE0000000000000 a) = -q * 2 ^ (s - 1) := by
  have hA : Wasm.IEEE64.scaledValue 0xBFE0000000000000 = -1 * 2 ^ 1073 := by decide +kernel
  obtain ⟨hf, hv', -, -⟩ := F64ExactProduct.mul_exact_scaled 0xBFE0000000000000 a
    (by unfold CodeLib.IEEE64.Finite; decide) ha 1 q.natAbs 1073 s
    (by rw [magnitude_of_value _ _ 1073 hA]; rfl) (magnitude_of_value a q s hv)
    (by omega) (by omega) (by omega)
  have hval : value (Wasm.IEEE64.mul 0xBFE0000000000000 a) = -(value a / 2) := by
    rw [hv', PowLogTable.a0_value]
    ring
  refine ⟨hf, hval, ?_⟩
  apply sv_of_value _ _ (s - 1) (by omega)
  rw [hval, value_of_scaled a q s hs2 hv]
  have h2 : (2 : ℝ) ^ (1074 - (s - 1)) = 2 ^ (1074 - s) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2]
  push_cast
  field_simp

/-- `arhi2 = rhi arhi = -rhi ^ 2 / 2`, exact on the grid of `2 ^ -59`. -/
theorem square_exact (rhi arhi : UInt64) (hf : Finite rhi) (hfa : Finite arhi) (m : Int)
    (hv : Wasm.IEEE64.scaledValue rhi = m * 2 ^ 1045)
    (hva : Wasm.IEEE64.scaledValue arhi = -m * 2 ^ 1044) (hm : m.natAbs ≤ 2 ^ 22) :
    Finite (Wasm.IEEE64.mul rhi arhi) ∧
      value (Wasm.IEEE64.mul rhi arhi) = value rhi * value arhi ∧
      (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul rhi arhi) := by
  obtain ⟨hpf, hpv, hpm, -⟩ := F64ExactProduct.mul_exact_scaled rhi arhi hf hfa m.natAbs
    (-m).natAbs 1045 1044 (magnitude_of_value rhi m 1045 hv) (magnitude_of_value arhi _ 1044 hva)
    (by
      rw [Int.natAbs_neg]
      calc m.natAbs * m.natAbs ≤ 2 ^ 22 * 2 ^ 22 := Nat.mul_le_mul hm hm
        _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  refine ⟨hpf, hpv, dvd_of_magnitude _ _ ?_⟩
  rw [hpm]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by norm_num)) _

/-- `lo1 = k ln2lo + logctail`: for `k = 0` only the rounding of `logctail`. -/
theorem lo1_error (kd lt : UInt64) (K : Int) (hkf : Finite kd) (hkv : value kd = K)
    (hK : |K| ≤ 1100) (hlf : Finite lt) (hlt : |value lt| ≤ 1 / 2 ^ 43) :
    Finite (Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3D2EF35793C76730) lt) ∧
      |value (Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3D2EF35793C76730) lt) -
        (K * value 0x3D2EF35793C76730 + value lt)| ≤
        3 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44 + |value lt|) + 2 * |(K : ℝ)| *
          multiplicationUnderflowEpsilon := by
  obtain ⟨-, hlof, -, -, hlo⟩ := ln2_words
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hK' : |(K : ℝ)| ≤ 1100 := by exact_mod_cast hK
  have hμ : 0 ≤ multiplicationUnderflowEpsilon := by
    norm_num [multiplicationUnderflowEpsilon]
  have hprod : |(K : ℝ) * value 0x3D2EF35793C76730| ≤ |(K : ℝ)| / 2 ^ 44 := by
    rw [abs_mul]
    calc
      _ ≤ |(K : ℝ)| * (1 / 2 ^ 44) := mul_le_mul_of_nonneg_left hlo (abs_nonneg _)
      _ = _ := by ring
  have hm := F64MulBounds.mul_real_mixed kd 0x3D2EF35793C76730 hkf hlof
    (by rw [hkv]; exact hprod.trans_lt (by
      have : |(K : ℝ)| / 2 ^ 44 ≤ 1100 / 2 ^ 44 := div_le_div_of_nonneg_right hK' (by positivity)
      linarith [show (1100 : ℝ) / 2 ^ 44 < 2 ^ 1022 by norm_num]))
  rw [hkv] at hm
  set p := Wasm.IEEE64.mul kd 0x3D2EF35793C76730
  -- the product, exact for `k = 0`
  have hpe : |value p - (K : ℝ) * value 0x3D2EF35793C76730| ≤
      1 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44) + |(K : ℝ)| * multiplicationUnderflowEpsilon := by
    by_cases hK0 : K = 0
    · have hksv : Wasm.IEEE64.scaledValue kd = 0 * 2 ^ 1074 :=
        sv_of_value kd 0 1074 (by norm_num) (by rw [hkv, hK0]; norm_num)
      obtain ⟨-, hpv, -, -⟩ := F64ExactProduct.mul_exact_scaled kd 0x3D2EF35793C76730 hkf hlof
        0 (Wasm.IEEE64.scaledMagnitude 0x3D2EF35793C76730) 1074 0
        (by rw [magnitude_of_value kd 0 1074 hksv]; rfl) (by ring)
        (by rw [zero_mul]; norm_num) (by norm_num) (by norm_num)
      rw [hpv, hkv, hK0]
      simp
    · have h1 : (1 : ℝ) ≤ |(K : ℝ)| := by
        have : (1 : Int) ≤ |K| := Int.one_le_abs hK0
        exact_mod_cast this
      calc
        _ ≤ unitRoundoff64 * |(K : ℝ) * value 0x3D2EF35793C76730| +
            multiplicationUnderflowEpsilon := hm.2
        _ ≤ 1 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44) + |(K : ℝ)| * multiplicationUnderflowEpsilon := by
          rw [hu]
          apply add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
          nlinarith
  have hpv : |value p| ≤ 2 * (|(K : ℝ)| / 2 ^ 44) + |(K : ℝ)| * multiplicationUnderflowEpsilon := by
    have := abs_sub_abs_le_abs_sub (value p) ((K : ℝ) * value 0x3D2EF35793C76730)
    have h2 : 1 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44) ≤ |(K : ℝ)| / 2 ^ 44 := by
      have := abs_nonneg (K : ℝ)
      nlinarith
    linarith
  have hsum : |value p + value lt| ≤ 2 * (|(K : ℝ)| / 2 ^ 44) +
      |(K : ℝ)| * multiplicationUnderflowEpsilon + |value lt| :=
    (abs_add_le _ _).trans (by linarith)
  obtain ⟨hf, he⟩ := F64AddBounds.add_real_relative p lt hm.1 hlf (by
    have h3 : |(K : ℝ)| * multiplicationUnderflowEpsilon ≤ 1100 * 1 := by
      apply mul_le_mul hK' (by norm_num [multiplicationUnderflowEpsilon]) hμ (by norm_num)
    have h4 : |(K : ℝ)| / 2 ^ 44 ≤ 1100 := by
      have := abs_nonneg (K : ℝ)
      linarith [div_le_self this (by norm_num : (1 : ℝ) ≤ 2 ^ 44)]
    linarith [show (2 : ℝ) * 1100 + 1100 + 1 < 2 ^ 1023 by norm_num,
      show |value lt| ≤ 1 by linarith [show (1 : ℝ) / 2 ^ 43 ≤ 1 by norm_num]])
  refine ⟨hf, ?_⟩
  have hμ' : multiplicationUnderflowEpsilon ≤ 1 := by norm_num [multiplicationUnderflowEpsilon]
  calc
    _ ≤ |value (Wasm.IEEE64.add p lt) - (value p + value lt)| +
        |value p - (K : ℝ) * value 0x3D2EF35793C76730| := by
      have := abs_add_le (value (Wasm.IEEE64.add p lt) - (value p + value lt))
        (value p - (K : ℝ) * value 0x3D2EF35793C76730)
      rw [show value (Wasm.IEEE64.add p lt) - (value p + value lt) +
        (value p - (K : ℝ) * value 0x3D2EF35793C76730) =
        value (Wasm.IEEE64.add p lt) - ((K : ℝ) * value 0x3D2EF35793C76730 + value lt) by ring]
        at this
      exact this
    _ ≤ unitRoundoff64 * (2 * (|(K : ℝ)| / 2 ^ 44) + |(K : ℝ)| * multiplicationUnderflowEpsilon +
          |value lt|) +
        (1 / 2 ^ 53 * (|(K : ℝ)| / 2 ^ 44) + |(K : ℝ)| * multiplicationUnderflowEpsilon) :=
      add_le_add (he.trans (mul_le_mul_of_nonneg_left hsum (by rw [hu]; positivity))) hpe
    _ ≤ _ := by
      rw [hu]
      have h5 := abs_nonneg (K : ℝ)
      have h6 := abs_nonneg (value lt)
      have h7 : 0 ≤ |(K : ℝ)| * multiplicationUnderflowEpsilon := mul_nonneg h5 hμ
      nlinarith

#print axioms sv_cast
#print axioms sv_bound_gen
#print axioms sv_bound
#print axioms sv_eq_of_value
#print axioms dvd_of_magnitude
#print axioms grid_of_large
#print axioms grid_sum
#print axioms ln2hi_scaled
#print axioms ln2_words
#print axioms t1_exact
#print axioms half_exact
#print axioms square_exact
#print axioms lo1_error

end Library.Numerics.Float64.Pow.PowLogSum
