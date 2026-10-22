import Library.Numerics.Float64.Tgamma.TgammaAcc2

/-!
The loop of `Tgamma.poly3`, the polynomial of the accurate path of `Tgamma` above `1/4`.  Step `k`
of the loop multiplies the triple `t = t0 + t1 + t2` by `d` with `sprod`, adds `t0 c` to `s0`, and
adds `c (t1 + t2)` to the double-double `s1 + s2`, for the next double coefficient `c`.  The
coefficients are multiples of `2 ^ -17` below `2 ^ 19` in their numerators and `t0` a multiple of
`2 ^ -26` at most 2, so every product `t0 c` and every sum `s0` lies on the grid `2 ^ -43` with a
numerator below `2 ^ 53`, and both are exact (`TgammaAcc1.grid_mul`, `TgammaAcc1.grid_add`).  The
invariant `Inv` of `step_inv` keeps `t` within `k 2 ^ -76` of `d ^ k` and `s0 + s1 + s2` within
`k 2 ^ -69` of the first `k + 1` terms of the polynomial.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccPoly3
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAcc1 TgammaAcc2

set_option exponentiation.threshold 4096

/-- The state `(t0, t1, t2, s0, s1, s2)` of the loop. -/
abbrev St := Float × Float × Float × Float × Float × Float

/-- One step of the loop of `poly3` with the coefficient `c`. -/
def step (d c : Float) (st : St) : St :=
  let r := sprod d st.1 st.2.1 st.2.2.1
  let m := mulDDD c r.2.1 r.2.2
  let u := sumDD st.2.2.2.2.1 st.2.2.2.2.2 m.1 m.2
  (r.1, r.2.1, r.2.2, st.2.2.2.1 + r.1 * c, u.1, u.2)

/-- The state after `k` steps, for the coefficients `cs` and `|d| ≤ 1`. -/
def Inv (d : Float) (cs : ℕ → ℝ) (k : ℕ) (st : St) : Prop :=
  Finite st.1.toBits ∧ Finite st.2.1.toBits ∧ Finite st.2.2.1.toBits ∧
    Finite st.2.2.2.1.toBits ∧ Finite st.2.2.2.2.1.toBits ∧ Finite st.2.2.2.2.2.toBits ∧
    (∃ z : ℤ, value st.1.toBits = z / 2 ^ 26) ∧ |value st.1.toBits| ≤ 2 ∧
    |value st.2.1.toBits| ≤ k / 2 ^ 24 ∧ |value st.2.2.1.toBits| ≤ k / 2 ^ 50 ∧
    |value st.1.toBits + value st.2.1.toBits + value st.2.2.1.toBits - value d.toBits ^ k| ≤
      k / 2 ^ 76 ∧
    (∃ n : ℤ, value st.2.2.2.1.toBits = n / 2 ^ 43) ∧ |value st.2.2.2.1.toBits| ≤ 8 * (k + 1) ∧
    |value st.2.2.2.2.1.toBits| ≤ k / 2 ^ 17 ∧ |value st.2.2.2.2.2.toBits| ≤ k / 2 ^ 43 ∧
    |value st.2.2.2.1.toBits + value st.2.2.2.2.1.toBits + value st.2.2.2.2.2.toBits -
      ∑ i ∈ Finset.range (k + 1), cs i * value d.toBits ^ i| ≤ k / 2 ^ 69

/-- A word on the grid `2 ^ -g` with value at most `B` has a numerator at most `B 2 ^ g`. -/
theorem num_le (w : UInt64) (z : ℤ) (g : ℕ) (B : ℝ) (hz : value w = z / 2 ^ g)
    (hB : |value w| ≤ B) :
    (z.natAbs : ℝ) ≤ B * 2 ^ g := by
  have h : (z.natAbs : ℝ) = |value w| * 2 ^ g := by
    rw [hz, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g), Nat.cast_natAbs, Int.cast_abs]
    field_simp
  rw [h]
  exact mul_le_mul_of_nonneg_right hB (by positivity)

/-- The triple of one step: `sprod` multiplies `t` by `d`. -/
theorem tri_step (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d t0 t1 t2 : Float) (k : ℕ) (hk : k + 1 ≤ 13)
    (hdf : Finite d.toBits) (hd : |value d.toBits| ≤ 1) (h0f : Finite t0.toBits)
    (h1f : Finite t1.toBits) (h2f : Finite t2.toBits) (h0b : |value t0.toBits| ≤ 2)
    (h1b : |value t1.toBits| ≤ k / 2 ^ 24) (h2b : |value t2.toBits| ≤ k / 2 ^ 50)
    (hT : |value t0.toBits + value t1.toBits + value t2.toBits - value d.toBits ^ k| ≤ k / 2 ^ 76) :
    Finite (sprod d t0 t1 t2).1.toBits ∧ Finite (sprod d t0 t1 t2).2.1.toBits ∧
      Finite (sprod d t0 t1 t2).2.2.toBits ∧
      (∃ z' : ℤ, value (sprod d t0 t1 t2).1.toBits = z' / 2 ^ 26) ∧
      |value (sprod d t0 t1 t2).1.toBits| ≤ 2 ∧
      |value (sprod d t0 t1 t2).2.1.toBits| ≤ (k + 1 : ℕ) / 2 ^ 24 ∧
      |value (sprod d t0 t1 t2).2.2.toBits| ≤ (k + 1 : ℕ) / 2 ^ 50 ∧
      |value (sprod d t0 t1 t2).1.toBits + value (sprod d t0 t1 t2).2.1.toBits +
          value (sprod d t0 t1 t2).2.2.toBits - value d.toBits ^ (k + 1)| ≤
        (k + 1 : ℕ) / 2 ^ 76 := by
  have hk' : (k : ℝ) + 1 ≤ 13 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set vd := value d.toBits with hvd
  have hd0 := abs_nonneg vd
  obtain ⟨hr0f, hr1f, hr2f, hz', hr0e, hr1b, hr2b, hrT⟩ := sprod_spec hF d t0 t1 t2 hdf h0f
    h1f h2f hd h0b (by linarith [(by norm_num : (12 : ℝ) / 2 ^ 24 ≤ 1 / 2 ^ 20)])
    (by linarith [(by norm_num : (12 : ℝ) / 2 ^ 50 ≤ 1 / 2 ^ 46)])
  generalize sprod d t0 t1 t2 = r at hr0f hr1f hr2f hz' hr0e hr1b hr2b hrT ⊢
  have hdt1 : |vd| * |value t1.toBits| ≤ k / 2 ^ 24 :=
    (mul_le_of_le_one_left (abs_nonneg _) hd).trans h1b
  have hdt2 : |vd| * |value t2.toBits| ≤ k / 2 ^ 50 :=
    (mul_le_of_le_one_left (abs_nonneg _) hd).trans h2b
  have hr1b' : |value r.2.1.toBits| ≤ (k + 1 : ℕ) / 2 ^ 24 := by push_cast; linarith
  have hr2b' : |value r.2.2.toBits| ≤ (k + 1 : ℕ) / 2 ^ 50 := by push_cast; linarith
  have hpow : |vd ^ (k + 1)| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ hd0 hd
  have hrT' : |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - vd ^ (k + 1)| ≤
      (k + 1 : ℕ) / 2 ^ 76 := by
    have e : value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - vd ^ (k + 1) =
        (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
          vd * (value t0.toBits + value t1.toBits + value t2.toBits)) +
        vd * (value t0.toBits + value t1.toBits + value t2.toBits - vd ^ k) := by ring
    rw [e]
    have h3 := abs_add_le (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
          vd * (value t0.toBits + value t1.toBits + value t2.toBits))
        (vd * (value t0.toBits + value t1.toBits + value t2.toBits - vd ^ k))
    have h4 : |vd * (value t0.toBits + value t1.toBits + value t2.toBits - vd ^ k)| ≤
        k / 2 ^ 76 := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hd).trans hT
    push_cast
    linarith
  refine ⟨hr0f, hr1f, hr2f, hz', ?_, hr1b', hr2b', hrT'⟩
  have h3 := abs_sub_abs_le_abs_sub (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits)
    (vd ^ (k + 1))
  have h4 := abs_sub_abs_le_abs_sub (value r.1.toBits) (-(value r.2.1.toBits + value r.2.2.toBits))
  rw [sub_neg_eq_add, abs_neg, ← add_assoc] at h4
  have h5 := abs_add_le (value r.2.1.toBits) (value r.2.2.toBits)
  push_cast at hr1b' hr2b' hrT'
  linarith [(by norm_num : (13 : ℝ) / 2 ^ 76 + 13 / 2 ^ 24 + 13 / 2 ^ 50 ≤ 1)]

/-- The exact sum `s0 + t0 c` on the grid `2 ^ -43`. -/
theorem s0_step (s0 r0 c : Float) (k : ℕ) (hk : k + 1 ≤ 13) (hs0f : Finite s0.toBits)
    (hr0f : Finite r0.toBits) (hcf : Finite c.toBits) (n z' m : ℤ)
    (hn : value s0.toBits = n / 2 ^ 43) (hs0b : |value s0.toBits| ≤ 8 * (k + 1))
    (hz' : value r0.toBits = z' / 2 ^ 26) (hr0b : |value r0.toBits| ≤ 2)
    (hcm : value c.toBits = m / 2 ^ 17) (hm : m.natAbs < 2 ^ 19) (hc4 : |value c.toBits| ≤ 4) :
    Finite (s0 + r0 * c).toBits ∧
      (∃ n' : ℤ, value (s0 + r0 * c).toBits = n' / 2 ^ 43) ∧
      value (s0 + r0 * c).toBits = value s0.toBits + value r0.toBits * value c.toBits ∧
      |value (s0 + r0 * c).toBits| ≤ 8 * ((k + 1 : ℕ) + 1) := by
  have hk' : (k : ℝ) + 1 ≤ 13 := by exact_mod_cast hk
  have hz'n : (z'.natAbs : ℝ) ≤ 2 ^ 27 := by
    have := num_le r0.toBits z' 26 2 hz' hr0b
    linarith [(by norm_num : (2 : ℝ) * 2 ^ 26 = 2 ^ 27)]
  have hz'n' : z'.natAbs ≤ 2 ^ 27 := by exact_mod_cast hz'n
  obtain ⟨hpf, hpv⟩ := grid_mul r0 c hr0f hcf z' m 26 17 hz' hcm
    (by calc z'.natAbs * m.natAbs ≤ 2 ^ 27 * m.natAbs := Nat.mul_le_mul_right _ hz'n'
      _ < 2 ^ 27 * 2 ^ 19 := Nat.mul_lt_mul_of_pos_left hm (by norm_num)
      _ ≤ 2 ^ 53 := by norm_num) (by norm_num)
  have hpv' : value (r0 * c).toBits = ((z' * m : ℤ) : ℝ) / 2 ^ 43 := by
    rw [hpv, hz', hcm]; push_cast; ring
  have hnb : (n.natAbs : ℝ) ≤ 8 * (k + 1) * 2 ^ 43 := num_le _ n 43 _ hn hs0b
  have hsum : value s0.toBits + value (r0 * c).toBits = ((n + z' * m : ℤ) : ℝ) / 2 ^ 43 := by
    rw [hn, hpv']; push_cast; ring
  have hnm : |n + z' * m| ≤ 2 ^ 53 := by
    have h1 : |((n + z' * m : ℤ) : ℝ)| ≤ 2 ^ 53 := by
      push_cast
      have h3 := abs_add_le (n : ℝ) ((z' : ℝ) * m)
      have h4 : |(n : ℝ)| ≤ 8 * 13 * 2 ^ 43 := by
        rw [← Int.cast_abs, ← Nat.cast_natAbs]
        have : 8 * ((k : ℝ) + 1) * 2 ^ 43 ≤ 8 * 13 * 2 ^ 43 := by nlinarith
        exact_mod_cast hnb.trans this
      have h5 : |(z' : ℝ) * m| ≤ 2 ^ 27 * 2 ^ 19 := by
        rw [abs_mul, ← Int.cast_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.cast_natAbs]
        have hm' : (m.natAbs : ℝ) ≤ 2 ^ 19 := by exact_mod_cast hm.le
        exact mul_le_mul hz'n hm' (by positivity) (by positivity)
      linarith [(by norm_num : (8 : ℝ) * 13 * 2 ^ 43 + 2 ^ 27 * 2 ^ 19 ≤ 2 ^ 53)]
    rw [← Int.cast_abs] at h1
    exact_mod_cast h1
  obtain ⟨hs0f', hs0v'⟩ := grid_add s0 (r0 * c) hs0f hpf (n + z' * m) 43 hsum hnm (by norm_num)
  refine ⟨hs0f', ⟨n + z' * m, by rw [hs0v', hsum]⟩, by rw [hs0v', hpv], ?_⟩
  rw [hs0v']
  have h3 := abs_add_le (value s0.toBits) (value (r0 * c).toBits)
  have h4 : |value (r0 * c).toBits| ≤ 8 := by
    rw [hpv, abs_mul]
    nlinarith [abs_nonneg (value r0.toBits), abs_nonneg (value c.toBits)]
  push_cast
  linarith

/-- The double-double of one step: `s1 + s2` plus `c (t1 + t2)` by `mulDDD` and `sumDD`. -/
theorem s12_step (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (c r1 r2 s1 s2 : Float) (k : ℕ) (hk : k + 1 ≤ 13)
    (hcf : Finite c.toBits) (hr1f : Finite r1.toBits) (hr2f : Finite r2.toBits)
    (hs1f : Finite s1.toBits) (hs2f : Finite s2.toBits) (hc4 : |value c.toBits| ≤ 4)
    (hr1b : |value r1.toBits| ≤ (k + 1 : ℕ) / 2 ^ 24)
    (hr2b : |value r2.toBits| ≤ (k + 1 : ℕ) / 2 ^ 50)
    (hs1b : |value s1.toBits| ≤ k / 2 ^ 17) (hs2b : |value s2.toBits| ≤ k / 2 ^ 43) :
    Finite (sumDD s1 s2 (mulDDD c r1 r2).1 (mulDDD c r1 r2).2).1.toBits ∧
      Finite (sumDD s1 s2 (mulDDD c r1 r2).1 (mulDDD c r1 r2).2).2.toBits ∧
      |value (sumDD s1 s2 (mulDDD c r1 r2).1 (mulDDD c r1 r2).2).1.toBits| ≤ (k + 1 : ℕ) / 2 ^ 17 ∧
      |value (sumDD s1 s2 (mulDDD c r1 r2).1 (mulDDD c r1 r2).2).2.toBits| ≤ (k + 1 : ℕ) / 2 ^ 43 ∧
      |value (sumDD s1 s2 (mulDDD c r1 r2).1 (mulDDD c r1 r2).2).1.toBits +
          value (sumDD s1 s2 (mulDDD c r1 r2).1 (mulDDD c r1 r2).2).2.toBits -
          (value s1.toBits + value s2.toBits +
            value c.toBits * (value r1.toBits + value r2.toBits))| ≤ 1 / 2 ^ 87 := by
  have hk' : (k : ℝ) + 1 ≤ 13 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 13 := by push_cast; linarith
  have hk12 : (k : ℝ) ≤ 12 := by linarith
  have hH : |value r1.toBits| * |value c.toBits| ≤ 4 * (13 / 2 ^ 24) := by
    rw [mul_comm]
    exact mul_le_mul hc4 (hr1b.trans (div_le_div_of_nonneg_right hk1 (by norm_num)))
      (abs_nonneg _) (by norm_num)
  have hLw : |value r2.toBits| * |value c.toBits| ≤ 4 * (13 / 2 ^ 50) := by
    rw [mul_comm]
    exact mul_le_mul hc4 (hr2b.trans (div_le_div_of_nonneg_right hk1 (by norm_num)))
      (abs_nonneg _) (by norm_num)
  obtain ⟨hm1f, hm2f, hme, hm2b, hm1b⟩ := mulDDD_spec hF c r1 r2 hcf hr1f hr2f _ _ hH hLw
    (by norm_num) (by norm_num)
  generalize mulDDD c r1 r2 = mm at hm1f hm2f hme hm2b hm1b ⊢
  have hm1b' : |value mm.1.toBits| ≤ 1 / 2 ^ 18 := by
    linarith [(by norm_num : (4 : ℝ) * (13 / 2 ^ 24) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 18)]
  have hm2b' : |value mm.2.toBits| ≤ 1 / 2 ^ 44 := by
    linarith [(by norm_num : (4 : ℝ) * (13 / 2 ^ 50) * (1 + 1 / 2 ^ 51) +
      4 * (13 / 2 ^ 24) / 2 ^ 52 + 1 / 2 ^ 1071 ≤ 1 / 2 ^ 44)]
  have hme' : |value mm.1.toBits + value mm.2.toBits -
      value c.toBits * (value r1.toBits + value r2.toBits)| ≤ 1 / 2 ^ 95 := by
    linarith [(by norm_num : (3 * (4 * (13 / 2 ^ 50)) + 4 * (13 / 2 ^ 24) / 2 ^ 51 : ℝ) / 2 ^ 53 +
      1 / 2 ^ 1072 ≤ 1 / 2 ^ 95)]
  have hs1b' : |value s1.toBits| ≤ 12 / 2 ^ 17 :=
    hs1b.trans (div_le_div_of_nonneg_right hk12 (by norm_num))
  have hs2b' : |value s2.toBits| ≤ 12 / 2 ^ 43 :=
    hs2b.trans (div_le_div_of_nonneg_right hk12 (by norm_num))
  have hL : |value s2.toBits| + |value mm.2.toBits| ≤ (k : ℝ) / 2 ^ 43 + 1 / 2 ^ 44 := by linarith
  obtain ⟨hu1f, hu2f, hue, hu2b, hu1b⟩ := sumDD_spec s1 s2 mm.1 mm.2 hs1f hs2f hm1f hm2f
    (by linarith [(by norm_num : (12 : ℝ) / 2 ^ 17 < 2 ^ 898)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 18 < 2 ^ 898)]) _ hL
    (by linarith [(by norm_num : (12 : ℝ) / 2 ^ 43 + 1 / 2 ^ 44 ≤ 2 ^ 800),
      div_le_div_of_nonneg_right hk12 (by norm_num : (0 : ℝ) ≤ 2 ^ 43)])
  generalize sumDD s1 s2 mm.1 mm.2 = u at hu1f hu2f hue hu2b hu1b ⊢
  have hu1b' : |value u.1.toBits| ≤ (k + 1 : ℕ) / 2 ^ 17 := by
    have h3 := abs_add_le (value s1.toBits) (value mm.1.toBits)
    have h4 : |value s1.toBits + value mm.1.toBits| * (1 + 1 / 2 ^ 51) ≤
        ((k : ℝ) / 2 ^ 17 + 1 / 2 ^ 18) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have e : ((k : ℝ) / 2 ^ 17 + 1 / 2 ^ 18) * (1 + 1 / 2 ^ 51) =
        k / 2 ^ 17 + k / 2 ^ 68 + (1 + 1 / 2 ^ 51) / 2 ^ 18 := by ring
    have h5 : (k : ℝ) / 2 ^ 68 ≤ 12 / 2 ^ 68 := div_le_div_of_nonneg_right hk12 (by norm_num)
    push_cast
    have e3 : ((k : ℝ) + 1) / 2 ^ 17 = k / 2 ^ 17 + 1 / 2 ^ 17 := by ring
    linarith [(by norm_num : (12 : ℝ) / 2 ^ 68 + (1 + 1 / 2 ^ 51) / 2 ^ 18 + 1 / 2 ^ 1073 ≤
      1 / 2 ^ 17)]
  have hu1b'' : |value u.1.toBits| ≤ 13 / 2 ^ 17 :=
    hu1b'.trans (div_le_div_of_nonneg_right hk1 (by norm_num))
  refine ⟨hu1f, hu2f, hu1b', ?_, ?_⟩
  · refine hu2b.trans ?_
    have h3 : |value u.1.toBits| / 2 ^ 51 ≤ 13 / 2 ^ 17 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hu1b'' (by norm_num)
    have e : ((k : ℝ) / 2 ^ 43 + 1 / 2 ^ 44) * (1 + 1 / 2 ^ 51) =
        k / 2 ^ 43 + k / 2 ^ 94 + (1 + 1 / 2 ^ 51) / 2 ^ 44 := by ring
    have h4 : (k : ℝ) / 2 ^ 94 ≤ 12 / 2 ^ 94 := div_le_div_of_nonneg_right hk12 (by norm_num)
    push_cast
    have e3 : ((k : ℝ) + 1) / 2 ^ 43 = k / 2 ^ 43 + 1 / 2 ^ 43 := by ring
    linarith [(by norm_num : (12 : ℝ) / 2 ^ 94 + (1 + 1 / 2 ^ 51) / 2 ^ 44 +
      13 / 2 ^ 17 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 1 / 2 ^ 43)]
  · have h3 : (k : ℝ) / 2 ^ 43 + 1 / 2 ^ 44 ≤ 12 / 2 ^ 43 + 1 / 2 ^ 44 := by
      have : (k : ℝ) / 2 ^ 43 ≤ 12 / 2 ^ 43 := div_le_div_of_nonneg_right hk12 (by norm_num)
      linarith
    have h5 : (3 * ((k : ℝ) / 2 ^ 43 + 1 / 2 ^ 44) + |value u.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
        2 ^ 53 ≤
          (3 * (12 / 2 ^ 43 + 1 / 2 ^ 44) + 13 / 2 ^ 17 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
      gcongr
    have e : value u.1.toBits + value u.2.toBits -
        (value s1.toBits + value s2.toBits + value c.toBits * (value r1.toBits + value r2.toBits)) =
        (value u.1.toBits + value u.2.toBits -
          (value s1.toBits + value s2.toBits + (value mm.1.toBits + value mm.2.toBits))) +
        (value mm.1.toBits + value mm.2.toBits -
          value c.toBits * (value r1.toBits + value r2.toBits)) := by ring
    rw [e]
    have h6 := abs_add_le (value u.1.toBits + value u.2.toBits -
          (value s1.toBits + value s2.toBits + (value mm.1.toBits + value mm.2.toBits)))
      (value mm.1.toBits + value mm.2.toBits - value c.toBits * (value r1.toBits + value r2.toBits))
    linarith [(by norm_num : (3 * (12 / 2 ^ 43 + 1 / 2 ^ 44) + 13 / 2 ^ 17 / 2 ^ 52 +
      1 / 2 ^ 1074 : ℝ) / 2 ^ 53 + 1 / 2 ^ 95 ≤ 1 / 2 ^ 87)]

/-- **One step of the loop** keeps the invariant. -/
theorem step_inv (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d c : Float) (cs : ℕ → ℝ) (k : ℕ) (st : St)
    (hk : k + 1 ≤ 13) (hdf : Finite d.toBits) (hd : |value d.toBits| ≤ 1) (hcf : Finite c.toBits)
    (hcs : value c.toBits = cs (k + 1)) (m : ℤ) (hcm : value c.toBits = m / 2 ^ 17)
    (hm : m.natAbs < 2 ^ 19) (hc4 : |value c.toBits| ≤ 4) (h : Inv d cs k st) :
    Inv d cs (k + 1) (step d c st) := by
  obtain ⟨t0, t1, t2, s0, s1, s2⟩ := st
  obtain ⟨h0f, h1f, h2f, hs0f, hs1f, hs2f, -, h0b, h1b, h2b, hT, ⟨n, hn⟩, hs0b, hs1b, hs2b,
    hE⟩ := h
  dsimp only at h0f h1f h2f hs0f hs1f hs2f h0b h1b h2b hT hn hs0b hs1b hs2b hE
  unfold step
  dsimp only
  obtain ⟨hr0f, hr1f, hr2f, ⟨z', hz'⟩, hr0b, hr1b, hr2b, hrT⟩ := tri_step hF d t0 t1 t2 k hk hdf hd
    h0f h1f h2f h0b h1b h2b hT
  generalize sprod d t0 t1 t2 = r at hr0f hr1f hr2f hz' hr0b hr1b hr2b hrT ⊢
  obtain ⟨hs0f', hn', hs0v, hs0b'⟩ := s0_step s0 r.1 c k hk hs0f hr0f hcf n z' m hn hs0b hz' hr0b
    hcm hm hc4
  obtain ⟨hu1f, hu2f, hu1b, hu2b, hue⟩ := s12_step hF c r.2.1 r.2.2 s1 s2 k hk hcf hr1f hr2f hs1f
    hs2f hc4 hr1b hr2b hs1b hs2b
  generalize hU : sumDD s1 s2 (mulDDD c r.2.1 r.2.2).1 (mulDDD c r.2.1 r.2.2).2 = u
  rw [hU] at hu1f hu2f hu1b hu2b hue
  generalize s0 + r.1 * c = s0' at hs0f' hn' hs0v hs0b' ⊢
  unfold Inv
  dsimp only
  refine ⟨hr0f, hr1f, hr2f, hs0f', hu1f, hu2f, ⟨z', hz'⟩, hr0b, hr1b, hr2b, hrT, hn', hs0b', hu1b,
    hu2b, ?_⟩
  rw [hs0v, Finset.sum_range_succ, ← hcs]
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 13 := by exact_mod_cast hk
  have h3 : |value c.toBits * (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
      value d.toBits ^ (k + 1))| ≤ 4 * (13 / 2 ^ 76) := by
    rw [abs_mul]
    exact mul_le_mul hc4 (hrT.trans (div_le_div_of_nonneg_right hk1 (by norm_num))) (abs_nonneg _)
      (by norm_num)
  have e : value s0.toBits + value r.1.toBits * value c.toBits + value u.1.toBits +
      value u.2.toBits - (∑ i ∈ Finset.range (k + 1), cs i * value d.toBits ^ i +
        value c.toBits * value d.toBits ^ (k + 1)) =
      (value s0.toBits + value s1.toBits + value s2.toBits -
        ∑ i ∈ Finset.range (k + 1), cs i * value d.toBits ^ i) +
      (value u.1.toBits + value u.2.toBits -
        (value s1.toBits + value s2.toBits +
          value c.toBits * (value r.2.1.toBits + value r.2.2.toBits))) +
      value c.toBits * (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        value d.toBits ^ (k + 1)) := by ring
  rw [e]
  have a1 := abs_add_le ((value s0.toBits + value s1.toBits + value s2.toBits -
        ∑ i ∈ Finset.range (k + 1), cs i * value d.toBits ^ i) +
      (value u.1.toBits + value u.2.toBits -
        (value s1.toBits + value s2.toBits +
          value c.toBits * (value r.2.1.toBits + value r.2.2.toBits))))
    (value c.toBits * (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        value d.toBits ^ (k + 1)))
  have a2 := abs_add_le (value s0.toBits + value s1.toBits + value s2.toBits -
        ∑ i ∈ Finset.range (k + 1), cs i * value d.toBits ^ i)
    (value u.1.toBits + value u.2.toBits -
        (value s1.toBits + value s2.toBits +
          value c.toBits * (value r.2.1.toBits + value r.2.2.toBits)))
  push_cast
  have e2 : ((k : ℝ) + 1) / 2 ^ 69 = k / 2 ^ 69 + 1 / 2 ^ 69 := by ring
  linarith [(by norm_num : (1 : ℝ) / 2 ^ 87 + 4 * (13 / 2 ^ 76) ≤ 1 / 2 ^ 69)]

/-- The index `oh + k + 1` of the coefficient of step `k`. -/
theorem idx1 (oh : UInt64) (k : ℕ) (h : oh.toNat + k + 1 < 2 ^ 63) :
    (oh + UInt64.ofNat k + 1).toNat = oh.toNat + k + 1 := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hoh := oh.toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]
  simp only [UInt64.reduceToNat]
  omega

/-- The double coefficients of the loop: finite, multiples of `2 ^ -17` with numerators below
`2 ^ 19`, and at most 4 in magnitude. -/
structure Coeffs (tab : Array UInt64) (oh n : ℕ) : Prop where
  fin : ∀ k < n, Wasm.IEEE64.isFinite tab[oh + k]! = true
  grid : ∀ k < n, ∃ m : ℤ, ((PolyBound.ratOfWord tab[oh + k]! : ℚ) : ℝ) = m / 2 ^ 17 ∧
    m.natAbs < 2 ^ 19
  mag : ∀ k < n, |((PolyBound.ratOfWord tab[oh + k]! : ℚ) : ℝ)| ≤ 4

/-- The coefficient `i` of the loop, as a real number. -/
noncomputable def coef (tab : Array UInt64) (oh : UInt64) (i : ℕ) : ℝ :=
  value (Float.ofBits tab[oh.toNat + i]!).toBits

/-- **The loop of `poly3`** after `k` steps. -/
theorem loop_inv (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (tab : Array UInt64) (d : Float) (oh : UInt64) (n : ℕ)
    (hn : n ≤ 14) (hoh : oh.toNat + n < 2 ^ 63) (hdf : Finite d.toBits) (hd : |value d.toBits| ≤ 1)
    (hC : Coeffs tab oh.toNat n) :
    ∀ k, k + 1 ≤ n → Inv d (coef tab oh) k (LeanExe.loop (UInt64.ofNat k)
      ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
      (fun k st => step d (entry tab (oh + k + 1)) st)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : LeanExe.loop (UInt64.ofNat 0)
        ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
        (fun k st => step d (entry tab (oh + k + 1)) st) =
        ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float),
          (0.0 : Float)) := by
      simp [LeanExe.loop]
    rw [h0]
    have he : entry tab oh = Float.ofBits tab[oh.toNat + 0]! := TgammaPolyDDD.entry_eq _ _ _ rfl
    have hf0 := hC.fin 0 (by omega)
    obtain ⟨m, hm, hmb⟩ := hC.grid 0 (by omega)
    have hc4 := hC.mag 0 (by omega)
    have hv : value (entry tab oh).toBits = m / 2 ^ 17 := by
      rw [he, TgammaWords.ofBits_value _ hf0, hm]
    have hv4 : |value (entry tab oh).toBits| ≤ 4 := by
      rw [he, TgammaWords.ofBits_value _ hf0]; exact hc4
    unfold Inv
    dsimp only
    rw [TgammaRecip.one_value, TgammaMainRed.zero_value]
    refine ⟨TgammaRecip.one_finite, TgammaMainRed.zero_finite, TgammaMainRed.zero_finite,
      by rw [he]; exact TgammaWords.ofBits_finite _ hf0, TgammaMainRed.zero_finite,
      TgammaMainRed.zero_finite, ⟨2 ^ 26, by norm_num⟩, by norm_num, by norm_num, by norm_num,
      by norm_num, ⟨m * 2 ^ 26, by rw [hv]; push_cast; ring⟩, by
        push_cast; linarith, by norm_num, by norm_num, ?_⟩
    have hc0 : coef tab oh 0 = value (entry tab oh).toBits := by rw [coef, ← he]
    simp [hc0]
  | succ k ih =>
    intro hk
    have hst := ih (by omega)
    rw [TgammaPoly.loop_succ k (by omega)]
    generalize LeanExe.loop (UInt64.ofNat k)
      ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
      (fun k st => step d (entry tab (oh + k + 1)) st) = st at hst ⊢
    have he : entry tab (oh + UInt64.ofNat k + 1) = Float.ofBits tab[oh.toNat + (k + 1)]! :=
      TgammaPolyDDD.entry_eq _ _ _ (by rw [idx1 oh k (by omega)]; omega)
    have hf := hC.fin (k + 1) (by omega)
    obtain ⟨m, hm, hmb⟩ := hC.grid (k + 1) (by omega)
    have hc4 := hC.mag (k + 1) (by omega)
    show Inv d (coef tab oh) (k + 1) (step d (entry tab (oh + UInt64.ofNat k + 1)) st)
    rw [he]
    exact step_inv hF d _ (coef tab oh) k st (by omega) hdf hd (TgammaWords.ofBits_finite _ hf)
      rfl m (by rw [TgammaWords.ofBits_value _ hf, hm]) hmb
      (by rw [TgammaWords.ofBits_value _ hf]; exact hc4) hst

/-- The last steps of `poly3`: the sum of the loop's low parts with the double-double polynomial,
and the two `fastTwoSum` steps. -/
theorem final_stage (s0 s1 s2 q1 q2 : Float) (hs0f : Finite s0.toBits) (hs1f : Finite s1.toBits)
    (hs2f : Finite s2.toBits) (hq1f : Finite q1.toBits) (hq2f : Finite q2.toBits)
    (hs0 : |value s0.toBits| ≤ 112) (hs1 : |value s1.toBits| ≤ 13 / 2 ^ 17)
    (hs2 : |value s2.toBits| ≤ 13 / 2 ^ 43) (hq1 : |value q1.toBits| ≤ 1 / 2 ^ 12)
    (hq2 : |value q2.toBits| ≤ 1 / 2 ^ 44) :
    Finite (fastTwoSum s0 (sumDD s1 s2 q1 q2).1).1.toBits ∧
      Finite (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q1 q2).1).2 (sumDD s1 s2 q1 q2).2).1.toBits ∧
      |value (fastTwoSum s0 (sumDD s1 s2 q1 q2).1).1.toBits +
          value (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q1 q2).1).2
            (sumDD s1 s2 q1 q2).2).1.toBits -
          (value s0.toBits + value s1.toBits + value s2.toBits +
            (value q1.toBits + value q2.toBits))| ≤ 3 / 2 ^ 66 + 1 / 2 ^ 88 ∧
      |value (fastTwoSum s0 (sumDD s1 s2 q1 q2).1).1.toBits| ≤ 120 ∧
      |value (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q1 q2).1).2
        (sumDD s1 s2 q1 q2).2).1.toBits| ≤ 1 / 2 ^ 37 := by
  have hL : |value s2.toBits| + |value q2.toBits| ≤ 13 / 2 ^ 43 + 1 / 2 ^ 44 := by linarith
  obtain ⟨hv1f, hv2f, hve, hv2b, hv1b⟩ := sumDD_spec s1 s2 q1 q2 hs1f hs2f hq1f hq2f
    (by linarith [(by norm_num : (13 : ℝ) / 2 ^ 17 < 2 ^ 898)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 12 < 2 ^ 898)]) _ hL (by norm_num)
  generalize sumDD s1 s2 q1 q2 = v at hv1f hv2f hve hv2b hv1b ⊢
  have hv1b' : |value v.1.toBits| ≤ 3 / 2 ^ 13 := by
    have := abs_add_le (value s1.toBits) (value q1.toBits)
    have h3 : |value s1.toBits + value q1.toBits| * (1 + 1 / 2 ^ 51) ≤
        (13 / 2 ^ 17 + 1 / 2 ^ 12) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : ((13 : ℝ) / 2 ^ 17 + 1 / 2 ^ 12) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
      3 / 2 ^ 13)]
  have hv2b' : |value v.2.toBits| ≤ 1 / 2 ^ 38 := by
    have : |value v.1.toBits| / 2 ^ 51 ≤ 3 / 2 ^ 13 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hv1b' (by norm_num)
    linarith [(by norm_num : ((13 : ℝ) / 2 ^ 43 + 1 / 2 ^ 44) * (1 + 1 / 2 ^ 51) +
      3 / 2 ^ 13 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 1 / 2 ^ 38)]
  have hve' : |value v.1.toBits + value v.2.toBits -
      (value s1.toBits + value s2.toBits + (value q1.toBits + value q2.toBits))| ≤ 1 / 2 ^ 89 := by
    have : |value v.1.toBits| / 2 ^ 52 ≤ 3 / 2 ^ 13 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hv1b' (by norm_num)
    have h3 : (3 * (13 / 2 ^ 43 + 1 / 2 ^ 44) + |value v.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53
        ≤ (3 * (13 / 2 ^ 43 + 1 / 2 ^ 44) + 3 / 2 ^ 13 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
      gcongr
    linarith [(by norm_num : (3 * (13 / 2 ^ 43 + 1 / 2 ^ 44) + 3 / 2 ^ 13 / 2 ^ 52 +
      1 / 2 ^ 1074 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 89)]
  obtain ⟨hw1f, hw2f, hwe, hw1b, hw2b⟩ := fts_approx s0 v.1 hs0f hv1f 112 (3 / 2 ^ 13) hs0 hv1b'
    (by norm_num)
  generalize fastTwoSum s0 v.1 = w at hw1f hw2f hwe hw1b hw2b ⊢
  have hx : (fastTwoSum w.2 v.2).1 = w.2 + v.2 := rfl
  have hxa := fapprox_add (fapprox_self w.2 hw2f) (fapprox_self v.2 hv2f) (1 / 2 ^ 37) (by
      simp only [add_zero]
      have := abs_add_le (value w.2.toBits) (value v.2.toBits)
      linarith [(by norm_num : ((112 : ℝ) + 3 / 2 ^ 13) / 2 ^ 51 + 1 / 2 ^ 38 ≤ 1 / 2 ^ 37)])
    (by norm_num)
  rw [← hx] at hxa
  have hxe : |value (fastTwoSum w.2 v.2).1.toBits - (value w.2.toBits + value v.2.toBits)| ≤
      1 / 2 ^ 90 := by
    have h := hxa.2
    simp only [zero_add] at h
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 37 / 2 ^ 53 = 1 / 2 ^ 90)]
  refine ⟨hw1f, hxa.1, ?_, by linarith [(by norm_num : ((112 : ℝ) + 3 / 2 ^ 13) *
    (1 + 1 / 2 ^ 53) ≤ 120)], ?_⟩
  · have e : value w.1.toBits + value (fastTwoSum w.2 v.2).1.toBits -
        (value s0.toBits + value s1.toBits + value s2.toBits +
          (value q1.toBits + value q2.toBits)) =
        (value (fastTwoSum w.2 v.2).1.toBits - (value w.2.toBits + value v.2.toBits)) +
        (value w.1.toBits + value w.2.toBits - (value s0.toBits + value v.1.toBits)) +
        (value v.1.toBits + value v.2.toBits -
          (value s1.toBits + value s2.toBits + (value q1.toBits + value q2.toBits))) := by ring
    rw [e]
    have a1 := abs_add_le ((value (fastTwoSum w.2 v.2).1.toBits -
        (value w.2.toBits + value v.2.toBits)) +
        (value w.1.toBits + value w.2.toBits - (value s0.toBits + value v.1.toBits)))
      (value v.1.toBits + value v.2.toBits -
          (value s1.toBits + value s2.toBits + (value q1.toBits + value q2.toBits)))
    have a2 := abs_add_le (value (fastTwoSum w.2 v.2).1.toBits -
        (value w.2.toBits + value v.2.toBits))
      (value w.1.toBits + value w.2.toBits - (value s0.toBits + value v.1.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 90 + (3 / 2 ^ 13 / 2 ^ 53 +
      (112 + 3 / 2 ^ 13) / 2 ^ 104) + 1 / 2 ^ 89 ≤ 3 / 2 ^ 66 + 1 / 2 ^ 88)]
  · have := abs_sub_abs_le_abs_sub (value (fastTwoSum w.2 v.2).1.toBits)
      (value w.2.toBits + value v.2.toBits)
    have := abs_add_le (value w.2.toBits) (value v.2.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 90 + ((112 + 3 / 2 ^ 13) / 2 ^ 51 + 1 / 2 ^ 38) ≤
      1 / 2 ^ 37)]

/-- The last sums of `poly3` after the loop and the double-double polynomial `q`. -/
def finish (st : St) (q : Float × Float) : Float × Float :=
  let v := sumDD st.2.2.2.2.1 st.2.2.2.2.2 q.1 q.2
  let w := fastTwoSum st.2.2.2.1 v.1
  (w.1, (fastTwoSum w.2 v.2).1)

theorem poly3_eq (tab : Array UInt64) (d : Float) (oh imax ol jmax : UInt64) :
    poly3 tab d oh imax ol jmax =
      finish (LeanExe.loop (imax - 1)
        ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
        (fun k st => step d (entry tab (oh + k + 1)) st)) (polyDDD tab ol jmax d 0.0) := by
  unfold poly3
  generalize hA : LeanExe.loop (imax - 1)
    ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
    (fun k (st : St) =>
      let (t0, t1, t2, s0, s1, s2) := st
      let c := entry tab (oh + k + 1)
      let (t0, t1, t2) := sprod d t0 t1 t2
      let s0 := s0 + t0 * c
      let (fh, fl) := mulDDD c t1 t2
      let (s1, s2) := sumDD s1 s2 fh fl
      (t0, t1, t2, s0, s1, s2)) = A
  generalize hB : LeanExe.loop (imax - 1)
    ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
    (fun k st => step d (entry tab (oh + k + 1)) st) = B
  have hAB : A = B := by
    rw [← hA, ← hB]
    congr 1
  subst hAB
  generalize polyDDD tab ol jmax d 0.0 = q
  obtain ⟨t0, t1, t2, s0, s1, s2⟩ := A
  obtain ⟨q1, q2⟩ := q
  rfl

/-- The conditions on the double-double coefficients of `poly3`: finite, high parts at most
`2 ^ -16`, low parts at most `2 ^ -70`, and magnitudes summing to at most `2 ^ -13`. -/
structure DDCoeffs (tab : Array UInt64) (ol : UInt64) (N : ℕ) : Prop where
  fh : ∀ k < N, Finite (Float.ofBits tab[ol.toNat + 2 * k]!).toBits
  fl : ∀ k < N, Finite (Float.ofBits tab[ol.toNat + 2 * k + 1]!).toBits
  hi : ∀ k < N, |value (Float.ofBits tab[ol.toNat + 2 * k]!).toBits| ≤ 1 / 2 ^ 16
  lo : ∀ k < N, |value (Float.ofBits tab[ol.toNat + 2 * k + 1]!).toBits| ≤ 1 / 2 ^ 70
  sum : (∑ k ∈ Finset.range N, |TgammaPolyDDD.cDD tab ol k|) ≤ 1 / 2 ^ 13

/-- **`poly3`** within `2 ^ -63` of its two polynomials, for `|d| ≤ 1`. -/
theorem poly3_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (tab : Array UInt64) (d : Float)
    (oh imax ol jmax : UInt64) (hn1 : 1 ≤ imax.toNat) (hn : imax.toNat ≤ 14)
    (hoh : oh.toNat + imax.toNat < 2 ^ 63) (hC : Coeffs tab oh.toNat imax.toNat)
    (hN1 : 1 ≤ jmax.toNat) (hN : jmax.toNat ≤ 34) (hol : ol.toNat + 2 * jmax.toNat < 2 ^ 63)
    (hD : DDCoeffs tab ol jmax.toNat) (hdf : Finite d.toBits) (hd : |value d.toBits| ≤ 1) :
    Finite (poly3 tab d oh imax ol jmax).1.toBits ∧ Finite (poly3 tab d oh imax ol jmax).2.toBits ∧
      |value (poly3 tab d oh imax ol jmax).1.toBits + value (poly3 tab d oh imax ol jmax).2.toBits -
          ((∑ i ∈ Finset.range imax.toNat, coef tab oh i * value d.toBits ^ i) +
            ∑ k ∈ Finset.range jmax.toNat, TgammaPolyDDD.cDD tab ol k * value d.toBits ^ k)| ≤
        1 / 2 ^ 63 ∧
      |value (poly3 tab d oh imax ol jmax).1.toBits| ≤ 120 ∧
      |value (poly3 tab d oh imax ol jmax).2.toBits| ≤ 1 / 2 ^ 37 := by
  set n := imax.toNat with hndef
  set N := jmax.toNat with hNdef
  set vd := value d.toBits with hvd
  rw [poly3_eq]
  -- the loop
  have hL := loop_inv hF tab d oh n hn hoh hdf hd hC (n - 1) (by omega)
  have hi1 : imax - 1 = UInt64.ofNat (n - 1) := by
    have hs : UInt64.size = 2 ^ 64 := rfl
    have h1 : (1 : UInt64) ≤ imax := by
      rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
    have h2 : (imax - 1).toNat = n - 1 := by rw [UInt64.toNat_sub_of_le _ _ h1]; rfl
    apply UInt64.toNat_inj.mp
    rw [h2, UInt64.toNat_ofNat_of_lt' (by omega)]
  rw [hi1]
  generalize LeanExe.loop (UInt64.ofNat (n - 1))
    ((1.0 : Float), (0.0 : Float), (0.0 : Float), entry tab oh, (0.0 : Float), (0.0 : Float))
    (fun k st => step d (entry tab (oh + k + 1)) st) = st at hL ⊢
  obtain ⟨t0, t1, t2, s0, s1, s2⟩ := st
  obtain ⟨-, -, -, hs0f, hs1f, hs2f, -, -, -, -, -, -, hs0b, hs1b, hs2b, hE⟩ := hL
  dsimp only at hs0f hs1f hs2f hs0b hs1b hs2b hE
  have hn13 : ((n - 1 : ℕ) : ℝ) ≤ 13 := by exact_mod_cast (by omega : n - 1 ≤ 13)
  -- the double-double polynomial
  have hz0 : |value (0.0 : Float).toBits - 0| ≤ 0 := by rw [TgammaMainRed.zero_value]; norm_num
  have hz0' : |value (0.0 : Float).toBits| ≤ 0 := by rw [TgammaMainRed.zero_value]; norm_num
  have hM : ∀ m, m + 1 ≤ N →
      |TgammaPoly.horner (TgammaPolyDDD.cDD tab ol) N 0 vd m| ≤ 1 / 2 ^ 13 := by
    intro m hm
    have := TgammaPoly.horner_bound (TgammaPolyDDD.cDD tab ol) N 0 vd hd m hm
    rw [abs_zero, add_zero] at this
    exact this.trans hD.sum
  have hN33 : ((N - 1 : ℕ) : ℝ) ≤ 33 := by exact_mod_cast (by omega : N - 1 ≤ 33)
  have hg : TgammaPolyDDD.polyGrow (1 / 2 ^ 13) (1 / 2 ^ 16) (1 / 2 ^ 70) (1 / 2 ^ 44) ≤
      6 / 2 ^ 52 := by
    simp only [TgammaPolyDDD.polyGrow]; norm_num
  have he : TgammaPolyDDD.polyEps 1 (1 / 2 ^ 13) (1 / 2 ^ 16) (1 / 2 ^ 70) (1 / 2 ^ 44) ≤
      7 / 2 ^ 97 := by
    simp only [TgammaPolyDDD.polyEps, TgammaPolyDDD.polyLow]; norm_num
  have ht : TgammaPolyDDD.polyT (1 / 2 ^ 16) 0 ≤ 1 / 2 ^ 67 := by
    simp only [TgammaPolyDDD.polyT]; norm_num
  have hg0 : 0 ≤ TgammaPolyDDD.polyGrow (1 / 2 ^ 13) (1 / 2 ^ 16) (1 / 2 ^ 70) (1 / 2 ^ 44) := by
    simp only [TgammaPolyDDD.polyGrow]; positivity
  have he0 : 0 ≤ TgammaPolyDDD.polyEps 1 (1 / 2 ^ 13) (1 / 2 ^ 16) (1 / 2 ^ 70) (1 / 2 ^ 44) := by
    simp only [TgammaPolyDDD.polyEps, TgammaPolyDDD.polyLow]; positivity
  have ht0 : 0 ≤ TgammaPolyDDD.polyT (1 / 2 ^ 16) 0 := by
    simp only [TgammaPolyDDD.polyT]; positivity
  have hNg := mul_le_mul hN33 hg hg0 (by norm_num)
  have hNe := mul_le_mul hN33 he he0 (by norm_num)
  obtain ⟨hq1f, hq2f, hqe, hq2b⟩ := TgammaPolyDDD.polyDDD_damped hF tab ol jmax d 0.0 hN1 hol hD.fh
    hD.fl 1 (1 / 2 ^ 13) (1 / 2 ^ 16) (1 / 2 ^ 70) (1 / 2 ^ 44) 0 0 0 hdf hd le_rfl hD.hi hD.lo
    TgammaMainRed.zero_finite hz0 hz0' (hz0'.trans (abs_nonneg _)) hM
    (by linarith [(by norm_num : ((1 : ℝ) / 2 ^ 67 + 1 / 2 ^ 70) * (1 + 1 / 2 ^ 53) +
      33 * (6 / 2 ^ 52) ≤ 1 / 2 ^ 44),
      mul_le_mul_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)])
    (by linarith [(by norm_num : (0 : ℝ) + (1 / 2 ^ 67 + 1 / 2 ^ 70) / 2 ^ 53 + 33 * (7 / 2 ^ 97) +
      1 / 2 ^ 44 ≤ 1), div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 53)])
    (by norm_num) (by norm_num) (by norm_num)
  generalize polyDDD tab ol jmax d 0.0 = q at hq1f hq2f hqe hq2b ⊢
  rw [TgammaPoly.horner_eval _ N hN1, zero_mul, add_zero, one_pow, one_mul] at hqe
  set P2 := ∑ k ∈ Finset.range N, TgammaPolyDDD.cDD tab ol k * vd ^ k with hP2
  have hP2b : |P2| ≤ 1 / 2 ^ 13 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hD.sum)
    apply Finset.sum_le_sum
    intro k _
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hd)
  have hqe' : |value q.1.toBits + value q.2.toBits - P2| ≤ 1 / 2 ^ 88 := by
    refine hqe.trans ?_
    have : (0 + (TgammaPolyDDD.polyT (1 / 2 ^ 16) 0 + 1 / 2 ^ 70) / 2 ^ 53) ≤
        (1 / 2 ^ 67 + 1 / 2 ^ 70) / 2 ^ 53 := by
      rw [zero_add]; exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 67 + 1 / 2 ^ 70) / 2 ^ 53 + 33 * (7 / 2 ^ 97) ≤
      1 / 2 ^ 88)]
  have hq1b : |value q.1.toBits| ≤ 1 / 2 ^ 12 := by
    have h3 := abs_sub_abs_le_abs_sub (value q.1.toBits + value q.2.toBits) P2
    have h4 := abs_sub_abs_le_abs_sub (value q.1.toBits) (-(value q.2.toBits))
    rw [sub_neg_eq_add, abs_neg] at h4
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 13 + 1 / 2 ^ 88 + 1 / 2 ^ 44 ≤ 1 / 2 ^ 12)]
  -- the last sums
  have hs0b' : |value s0.toBits| ≤ 112 := by
    have : (8 : ℝ) * ((n - 1 : ℕ) + 1) ≤ 112 := by linarith
    linarith
  have hs1b' : |value s1.toBits| ≤ 13 / 2 ^ 17 :=
    hs1b.trans (div_le_div_of_nonneg_right hn13 (by norm_num))
  have hs2b' : |value s2.toBits| ≤ 13 / 2 ^ 43 :=
    hs2b.trans (div_le_div_of_nonneg_right hn13 (by norm_num))
  obtain ⟨hp1f, hp2f, hpe, hp1b, hp2b⟩ := final_stage s0 s1 s2 q.1 q.2 hs0f hs1f hs2f hq1f hq2f
    hs0b' hs1b' hs2b' hq1b hq2b
  have hfin : finish (t0, t1, t2, s0, s1, s2) q =
      ((fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).1,
        (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).2 (sumDD s1 s2 q.1 q.2).2).1) := rfl
  rw [hfin]
  refine ⟨hp1f, hp2f, ?_, hp1b, hp2b⟩
  dsimp only
  have hS : ∑ i ∈ Finset.range n, coef tab oh i * vd ^ i =
      ∑ i ∈ Finset.range (n - 1 + 1), coef tab oh i * vd ^ i := by
    rw [show n - 1 + 1 = n by omega]
  rw [hS]
  have e : value (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).1.toBits +
      value (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).2
        (sumDD s1 s2 q.1 q.2).2).1.toBits -
      ((∑ i ∈ Finset.range (n - 1 + 1), coef tab oh i * vd ^ i) + P2) =
      (value (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).1.toBits +
        value (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).2
          (sumDD s1 s2 q.1 q.2).2).1.toBits -
        (value s0.toBits + value s1.toBits + value s2.toBits +
          (value q.1.toBits + value q.2.toBits))) +
      (value s0.toBits + value s1.toBits + value s2.toBits -
        ∑ i ∈ Finset.range (n - 1 + 1), coef tab oh i * vd ^ i) +
      (value q.1.toBits + value q.2.toBits - P2) := by ring
  rw [e]
  have a1 := abs_add_le ((value (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).1.toBits +
        value (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).2
          (sumDD s1 s2 q.1 q.2).2).1.toBits -
        (value s0.toBits + value s1.toBits + value s2.toBits +
          (value q.1.toBits + value q.2.toBits))) +
      (value s0.toBits + value s1.toBits + value s2.toBits -
        ∑ i ∈ Finset.range (n - 1 + 1), coef tab oh i * vd ^ i))
    (value q.1.toBits + value q.2.toBits - P2)
  have a2 := abs_add_le (value (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).1.toBits +
        value (fastTwoSum (fastTwoSum s0 (sumDD s1 s2 q.1 q.2).1).2
          (sumDD s1 s2 q.1 q.2).2).1.toBits -
        (value s0.toBits + value s1.toBits + value s2.toBits +
          (value q.1.toBits + value q.2.toBits)))
      (value s0.toBits + value s1.toBits + value s2.toBits -
        ∑ i ∈ Finset.range (n - 1 + 1), coef tab oh i * vd ^ i)
  have hE' : |value s0.toBits + value s1.toBits + value s2.toBits -
      ∑ i ∈ Finset.range (n - 1 + 1), coef tab oh i * vd ^ i| ≤ 13 / 2 ^ 69 :=
    hE.trans (div_le_div_of_nonneg_right hn13 (by norm_num))
  linarith [(by norm_num : (3 : ℝ) / 2 ^ 66 + 1 / 2 ^ 88 + 13 / 2 ^ 69 + 1 / 2 ^ 88 ≤ 1 / 2 ^ 63)]

#print axioms num_le
#print axioms tri_step
#print axioms s0_step
#print axioms s12_step
#print axioms step_inv
#print axioms loop_inv
#print axioms final_stage
#print axioms poly3_spec

end Library.Numerics.Float64.Tgamma.TgammaAccPoly3
