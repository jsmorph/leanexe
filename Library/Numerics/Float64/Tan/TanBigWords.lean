import Library.Numerics.Float64.Tan.TanBigReal
import Library.Numerics.Float64.Tan.TanEven
import Library.Numerics.Float64.Trig.TrigReduce

/-!
The steps of `Tan.kernelTan` from `0x3FE59428` on, on words.  `arg_spec` bounds the argument
`x' = (π/4 - |x|) + (π/4 lo - |y|)`: the first difference is exact by Sterbenz's lemma, so
`x'` lies within `u |x'|` and `2 ^ -100` of `P - |x + y|`, where `P` is the two-word value of
`π/4`.  `chain_spec` evaluates the kernel at `x'` and gives a real `τ`, to which the result
before the sign is nearest, within `4.8 u |x'|` and a few `η` of `v - 2 W v/(W + v)`.
-/

namespace Library.Numerics.Float64.Tan.TanBigWords

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanOdd TanEven TanPoly TanTrunc TanBigReal
  Library.Numerics.Float64.Trig.TrigKernelWords Library.Numerics.Float64.Trig.TrigApprox

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

theorem mag_split (v : UInt64) : ∃ m : ℕ,
    Wasm.IEEE64.scaledMagnitude v = m * 2 ^ (Wasm.IEEE64.exponent v - 1) ∧ m < 2 ^ 53 := by
  have hf : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  by_cases he : Wasm.IEEE64.exponent v = 0
  · refine ⟨Wasm.IEEE64.fraction v, ?_, by omega⟩
    simp only [Wasm.IEEE64.scaledMagnitude, he, beq_self_eq_true, ite_true, Nat.zero_sub,
      pow_zero, mul_one]
  · refine ⟨2 ^ 52 + Wasm.IEEE64.fraction v, ?_, by omega⟩
    simp only [Wasm.IEEE64.scaledMagnitude, show (Wasm.IEEE64.exponent v == 0) = false by
      simpa using he, Bool.false_eq_true, ite_false]

/-- Multiplication by a word of magnitude `2 ^ k` scaled units is exact. -/
theorem pow_mul (c h : UInt64) (k : ℕ) (hcf : Finite c) (hhf : Finite h)
    (hc : Wasm.IEEE64.scaledMagnitude c = 1 * 2 ^ k) (hk : 1074 ≤ k)
    (he : Wasm.IEEE64.exponent h - 1 + k ≤ 1074 + 2043) :
    Finite (Wasm.IEEE64.mul c h) ∧ value (Wasm.IEEE64.mul c h) = value c * value h := by
  obtain ⟨m, hm, hm53⟩ := mag_split h
  obtain ⟨hf, hv, -, -⟩ := F64ExactProduct.mul_exact_scaled c h hcf hhf 1 m k
    (Wasm.IEEE64.exponent h - 1) hc hm (by omega) (by omega) (by omega)
  exact ⟨hf, hv⟩

theorem finite_words : Finite one ∧ Finite negOne ∧ Finite two ∧ Finite wpio4 ∧
    Finite wpio4lo ∧ Finite (0 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem mag_one : Wasm.IEEE64.scaledMagnitude one = 1 * 2 ^ 1074 := by decide +kernel

theorem mag_negOne : Wasm.IEEE64.scaledMagnitude negOne = 1 * 2 ^ 1074 := by decide +kernel

theorem mag_two : Wasm.IEEE64.scaledMagnitude two = 1 * 2 ^ 1075 := by decide +kernel

theorem exp_pio4 : Wasm.IEEE64.exponent wpio4 ≤ 2044 := by decide

theorem value_two : value two = 2 := by
  rw [Library.Numerics.Float64.Trig.TrigReduce.value_word two 2 0 (by norm_num) (by decide +kernel)]
  norm_num

theorem value_zero : value (0 : UInt64) = 0 := by
  rw [Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled]
  have : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide
  rw [this]
  simp

theorem value_pio4 : value wpio4 = 7074237752028440 / 2 ^ 53 :=
  Library.Numerics.Float64.Trig.TrigReduce.value_word _ _ 53 (by norm_num) (by decide +kernel)

theorem value_pio4lo : value wpio4lo = 4967757600021511 / 2 ^ 107 :=
  Library.Numerics.Float64.Trig.TrigReduce.value_word _ _ 107 (by norm_num) (by decide +kernel)

/-- The two words of `π/4` against `π/4`. -/
theorem pi_close : |value wpio4 + value wpio4lo - Real.pi / 4| ≤ 1 / 2 ^ 68 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  norm_num at h1 h2
  rw [value_pio4, value_pio4lo, abs_le]
  constructor <;> linarith

theorem sign_bit (x : UInt64) : (x >>> 32 >>> 31 == 1) = Wasm.IEEE64.sign x := by
  have hlt := x.toNat_lt
  have hs : (x >>> 32 >>> 31).toNat = x.toNat / 2 ^ 63 := by
    have h32 : (32 : UInt64).toNat % 64 = 32 := rfl
    have h31 : (31 : UInt64).toNat % 64 = 31 := rfl
    rw [Library.Numerics.Float64.Trig.TrigWords.shr_toNat, Library.Numerics.Float64.Trig.TrigWords.shr_toNat, h32, h31, Nat.div_div_eq_div_mul, ← pow_add]
  unfold Wasm.IEEE64.sign
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, hs,
    UInt64.toNat_one]
  omega

theorem sign_true (x : UInt64) (h : Wasm.IEEE64.sign x = true) : value x = -|value x| := by
  have hv : Wasm.IEEE64.scaledValue x = -(Wasm.IEEE64.scaledMagnitude x : ℤ) := by
    unfold Wasm.IEEE64.scaledValue
    simp [h]
  have hn : value x ≤ 0 := by
    rw [Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, hv]
    push_cast
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  rw [abs_of_nonpos hn, neg_neg]

theorem sign_false (x : UInt64) (h : Wasm.IEEE64.sign x = false) : value x = |value x| := by
  have hv : Wasm.IEEE64.scaledValue x = (Wasm.IEEE64.scaledMagnitude x : ℤ) := by
    unfold Wasm.IEEE64.scaledValue
    simp [h]
  have hn : 0 ≤ value x := by
    rw [Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, hv]
    push_cast
    positivity
  rw [abs_of_nonneg hn]

/-- The argument from nonnegative `xt` and the tail `yt`. -/
theorem arg_core (xt yt : UInt64) (Xt : ℝ) (hxf : Finite xt) (hyf : Finite yt)
    (hX : value xt = Xt) (hX0 : 6743 / 10000 ≤ Xt) (hX1 : Xt ≤ 78541 / 100000)
    (hy : |value yt| ≤ Xt / 2 ^ 52) :
    Finite (Wasm.IEEE64.add (Wasm.IEEE64.sub wpio4 xt) (Wasm.IEEE64.sub wpio4lo yt)) ∧
      |value (Wasm.IEEE64.add (Wasm.IEEE64.sub wpio4 xt) (Wasm.IEEE64.sub wpio4lo yt)) -
          (value wpio4 + value wpio4lo - (Xt + value yt))| ≤
        𝐮 * |value wpio4 + value wpio4lo - (Xt + value yt)| + 1 / 2 ^ 100 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨-, -, -, hpf, hlf, -⟩ := finite_words
  have hp := value_pio4
  have hl := value_pio4lo
  have h4 : (4 : ℝ) < 2 ^ 1023 := four_lt 1023 (by norm_num)
  have hxa : |value xt| = Xt := by rw [hX]; exact abs_of_pos (by linarith)
  have hpa : |value wpio4| = 7074237752028440 / 2 ^ 53 := by
    rw [hp]; exact abs_of_pos (by positivity)
  obtain ⟨hzf, hzv⟩ := sterbenz wpio4 xt hpf hxf
    (by rw [hp, hX]; exact mul_nonneg (by positivity) (by linarith))
    (by rw [hxa, hpa]; linarith) (by rw [hxa, hpa]; linarith) exp_pio4
  have hyb : |value wpio4lo - value yt| ≤ 1 / 2 ^ 50 := by
    rw [hl]
    have := sub_abs (4967757600021511 / 2 ^ 107 : ℝ) (value yt)
    rw [abs_of_pos (by positivity : (0 : ℝ) < 4967757600021511 / 2 ^ 107)] at this
    have : Xt / 2 ^ 52 ≤ 1 / 2 ^ 52 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have : (4967757600021511 : ℝ) / 2 ^ 107 + 1 / 2 ^ 52 ≤ 1 / 2 ^ 50 := by norm_num
    linarith
  obtain ⟨hwf, hwe⟩ := F64AddBounds.sub_real_relative wpio4lo yt hlf hyf (by
    have : (1 : ℝ) / 2 ^ 50 ≤ 4 := by norm_num
    linarith)
  have hzb : |value (Wasm.IEEE64.sub wpio4 xt)| ≤ 1 := by
    rw [hzv, hp, hX]
    rw [abs_le]
    constructor <;> linarith
  have hwb : |value (Wasm.IEEE64.sub wpio4lo yt)| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value (Wasm.IEEE64.sub wpio4lo yt))
      (value wpio4lo - value yt)
    have : 𝐮 * |value wpio4lo - value yt| ≤ 1 / 2 ^ 50 := by
      rw [hu]
      have := abs_nonneg (value wpio4lo - value yt)
      linarith
    have : (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 50 ≤ 1 := by norm_num
    linarith
  obtain ⟨hsf, hse⟩ := F64AddBounds.add_real_relative _ _ hzf hwf (by
    have := abs_add_le (value (Wasm.IEEE64.sub wpio4 xt)) (value (Wasm.IEEE64.sub wpio4lo yt))
    linarith)
  refine ⟨hsf, ?_⟩
  rw [hzv] at hse
  set S := value (Wasm.IEEE64.sub wpio4lo yt) with hS
  set D := value wpio4 + value wpio4lo - (Xt + value yt) with hD
  have hSD : value wpio4 - value xt + S - D = S - (value wpio4lo - value yt) := by
    rw [hD, hX]; ring
  have t1 := abs_sub_abs_le_abs_sub (value wpio4 - value xt + S) D
  have t2 : |S - (value wpio4lo - value yt)| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 50) := by
    rw [hu] at hwe
    have : 1 / 2 ^ 53 * |value wpio4lo - value yt| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 50) :=
      mul_le_mul_of_nonneg_left hyb (by positivity)
    linarith
  rw [hSD] at t1
  have t3 : |value (Wasm.IEEE64.add (Wasm.IEEE64.sub wpio4 xt) (Wasm.IEEE64.sub wpio4lo yt)) - D| ≤
      |value (Wasm.IEEE64.add (Wasm.IEEE64.sub wpio4 xt) (Wasm.IEEE64.sub wpio4lo yt)) -
        (value wpio4 - value xt + S)| + |value wpio4 - value xt + S - D| := abs_sub_le _ _ _
  rw [hSD] at t3
  rw [hu] at hse ⊢
  have : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 53 * (1 / 2 ^ 50)) + 1 / 2 ^ 53 * (1 / 2 ^ 50) ≤
      1 / 2 ^ 100 := by norm_num
  linarith

theorem arg_spec (x y : UInt64) (X : ℝ) (hxf : Finite x) (hyf : Finite y) (hX : |value x| = X)
    (hX0 : 6743 / 10000 ≤ X) (hX1 : X ≤ 78541 / 100000) (hy : |value y| ≤ X / 2 ^ 52) :
    Finite (bigArg x y) ∧
      |value (bigArg x y) - (value wpio4 + value wpio4lo - |value x + value y|)| ≤
        𝐮 * |(value wpio4 + value wpio4lo - |value x + value y|)| + 1 / 2 ^ 100 := by
  have hyX : |value y| < X := by
    have : X / 2 ^ 52 < X := div_lt_self (by linarith) (by norm_num)
    linarith
  unfold bigArg negZero
  rw [sign_bit]
  rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x) with hs | hs
  · rw [hs, if_pos rfl, F64Sign.sub_negZero, F64Sign.sub_negZero,
      if_neg (by simp [not_nan_of_finite hxf]), if_neg (by simp [not_nan_of_finite hyf])]
    obtain ⟨hnxf, hnxv⟩ := F64Magnitude.negate_value x hxf
    obtain ⟨hnyf, hnyv⟩ := F64Magnitude.negate_value y hyf
    have hxv := sign_true x hs
    have hsum : |value x + value y| = X + value (Wasm.IEEE64.negate y) := by
      rw [hnyv, hxv, hX, abs_of_neg (by linarith [le_abs_self (value y)])]
      ring
    rw [hsum]
    exact arg_core _ _ X hnxf hnyf (by rw [hnxv, hxv, hX, neg_neg]) hX0 hX1
      (by rw [hnyv, abs_neg]; exact hy)
  · rw [hs, if_neg (by simp)]
    have hxv := sign_false x hs
    have hsum : |value x + value y| = X + value y := by
      rw [hxv, hX, abs_of_nonneg (by linarith [neg_abs_le (value y)])]
    rw [hsum]
    exact arg_core _ _ X hxf hyf (by rw [hxv, hX]) hX0 hX1 hy

/-- The correction at `x'` with no tail stays below `|x'| / 100` and `9 η`. -/
theorem r_small (x : UInt64) (X : ℝ) (hxf : Finite x) (hX : |value x| = X) (hX1 : X ≤ 12 / 100) :
    |value (corrW x 0)| ≤ X / 100 + 9 * η := by
  obtain ⟨-, -, -, -, -, h0f⟩ := finite_words
  have hX0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨M, ⟨⟨-, he⟩, hM⟩, hMb⟩ := corr_AB x 0 X hxf h0f hX (by linarith)
    (by rw [value_zero, abs_zero]; positivity)
  have h2 : X ^ 2 ≤ (12 / 100) ^ 2 := pow_le_pow_left₀ hX0 hX1 2
  have h3 : X ^ 3 ≤ (12 / 100) ^ 2 * X := by
    rw [show X ^ 3 = X ^ 2 * X by ring]
    exact mul_le_mul_of_nonneg_right h2 hX0
  have h4 : X ^ 4 ≤ ((12 / 100) ^ 2) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h5 : X ^ 5 ≤ ((12 / 100) ^ 2) ^ 2 * X := by
    rw [show X ^ 5 = X ^ 4 * X by ring]
    exact mul_le_mul_of_nonneg_right h4 hX0
  have h6 := abs_sub_abs_le_abs_sub (value (corrW x 0)) (corrT (value x) (value 0))
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl] at he
  norm_num at h3 h5 he hMb
  rw [show η = 1 / 2 ^ 1075 from rfl] at he ⊢
  linarith

/-- The kernel from `0x3FE59428` on at the argument `x'`, before the sign. -/
theorem chain_spec (x' v r w ww den q e1 f g h : UInt64) (X : ℝ)
    (hr : corrW x' 0 = r) (hw : Wasm.IEEE64.add x' r = w) (hww : Wasm.IEEE64.mul w w = ww)
    (hden : Wasm.IEEE64.add w v = den) (hq : Wasm.IEEE64.div ww den = q)
    (he1 : Wasm.IEEE64.sub q r = e1) (hf : Wasm.IEEE64.sub x' e1 = f)
    (hg : Wasm.IEEE64.mul two f = g) (hh : Wasm.IEEE64.sub v g = h)
    (hxf : Finite x') (hX : |value x'| = X) (hX1 : X ≤ 12 / 100) (hv : v = one ∨ v = negOne) :
    |value x' + value r - Real.tan (value x')| ≤ even_err X ∧ Finite h ∧
      (∀ u : UInt64, |value h - (value v - value g)| ≤ |value u - (value v - value g)|) ∧
      |value v - value g - (value v - 2 * ((value x' + value r) * value v /
        (value x' + value r + value v)))| ≤ 2 * (24 / 10 * 𝐮 * (X + 900 * η) + 4 * η) ∧
      |value v| = 1 ∧ |value x' + value r| ≤ 1213 / 10000 ∧ |value v - value g| ≤ 2 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hX0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨hof, hnf, htf, -, -, h0f⟩ := finite_words
  have h4 : (4 : ℝ) < 2 ^ 1022 := four_lt 1022 (by norm_num)
  have h4' : (4 : ℝ) < 2 ^ 1023 := four_lt 1023 (by norm_num)
  obtain ⟨hrf, -, hE, -, -⟩ := even_sum x' 0 (value x') X hxf h0f hX (by linarith)
    (by rw [value_zero, abs_zero]; positivity)
    (by rw [value_zero, add_zero, sub_self, abs_zero]; positivity)
  have hrb := r_small x' X hxf hX hX1
  rw [hr] at hrf hE hrb
  have hvv : |value v| = 1 := by
    rcases hv with rfl | rfl
    · rw [value_one, abs_one]
    · rw [value_negOne, abs_neg, abs_one]
  have hvf : Finite v := by rcases hv with rfl | rfl <;> assumption
  rw [hη] at hrb
  have hW : |value x' + value r| ≤ 1213 / 10000 := by
    have := abs_add_le (value x') (value r)
    have : (9 : ℝ) * (1 / 2 ^ 1075) ≤ 1 / 10000 := by norm_num
    linarith
  obtain ⟨hwf, hwe⟩ := F64AddBounds.add_real_relative x' r hxf hrf (by linarith)
  rw [hw] at hwf hwe
  have hwb : |value w| ≤ 1214 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value w) (value x' + value r)
    have : 𝐮 * |value x' + value r| ≤ 1 / 10000 := by
      rw [hu]
      have := abs_nonneg (value x' + value r)
      linarith
    linarith
  have hww2 : |value w * value w| ≤ 1214 / 10000 * (1214 / 10000) := by
    rw [abs_mul]
    exact mul_le_mul hwb hwb (abs_nonneg _) (by norm_num)
  obtain ⟨hwwf, hwwe⟩ := F64MulBounds.mul_real_mixed w w hwf hwf (by linarith)
  rw [hww] at hwwf hwwe
  have hwvu : |value w + value v| ≤ 2 := by
    have := abs_add_le (value w) (value v)
    linarith
  obtain ⟨hdf, hde⟩ := F64AddBounds.add_real_relative w v hwf hvf (by linarith)
  rw [hden] at hdf hde
  have hdl : 878 / 1000 ≤ |value den| := by
    have h1 := near_one (value w) (value v) hvv
    have h2 := abs_sub_abs_le_abs_sub (value w + value v) (value den)
    rw [abs_sub_comm] at h2
    have : 𝐮 * |value w + value v| ≤ 1 / 10000 := by
      rw [hu]
      have := abs_nonneg (value w + value v)
      linarith
    linarith
  have hdm : Wasm.IEEE64.scaledMagnitude den ≠ 0 := by
    intro h0
    have := F64RoundNearest.abs_value den
    rw [h0, Nat.cast_zero, zero_div] at this
    linarith
  have hwwb : |value ww| ≤ 149 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value ww) (value w * value w)
    have : 𝐮 * |value w * value w| + η ≤ 1 / 10000 := by
      rw [hu, hη]
      have := abs_nonneg (value w * value w)
      linarith
    linarith
  have hqd : |value ww / value den| ≤ 18 / 1000 := by
    rw [abs_div, div_le_iff₀ (by linarith)]
    linarith
  obtain ⟨hqf, hqe⟩ := F64DivBounds.div_real_mixed ww den hwwf hdf hdm (by linarith)
  rw [hq] at hqf hqe
  have hqb : |value q| ≤ 181 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value q) (value ww / value den)
    have : 𝐮 * |value ww / value den| + η ≤ 1 / 10000 := by
      rw [hu, hη]
      have := abs_nonneg (value ww / value den)
      linarith
    linarith
  have hqr : |value q - value r| ≤ 2 / 100 := by
    have := sub_abs (value q) (value r)
    have : (12 / 100 : ℝ) / 100 + 9 * (1 / 2 ^ 1075) ≤ 19 / 10000 := by norm_num
    linarith
  obtain ⟨he1f, he1e⟩ := F64AddBounds.sub_real_relative q r hqf hrf (by linarith)
  rw [he1] at he1f he1e
  have he1b : |value e1| ≤ 201 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value e1) (value q - value r)
    have : 𝐮 * |value q - value r| ≤ 1 / 10000 := by
      rw [hu]
      have := abs_nonneg (value q - value r)
      linarith
    linarith
  have hxe : |value x' - value e1| ≤ 15 / 100 := by
    have := sub_abs (value x') (value e1)
    linarith
  obtain ⟨hff, hfe⟩ := F64AddBounds.sub_real_relative x' e1 hxf he1f (by linarith)
  rw [hf] at hff hfe
  have hfb : |value f| ≤ 16 / 100 := by
    have := abs_sub_abs_le_abs_sub (value f) (value x' - value e1)
    have : 𝐮 * |value x' - value e1| ≤ 1 / 100 := by
      rw [hu]
      have := abs_nonneg (value x' - value e1)
      linarith
    linarith
  have hfx := exp_upper f 1 (by rw [pow_one]; linarith)
  obtain ⟨hgf, hgv⟩ := pow_mul two f 1075 htf hff mag_two (by norm_num) (by omega)
  rw [hg, value_two] at hgv
  rw [hg] at hgf
  have hb : |value v - value g| < 2 ^ 1023 := by
    rw [hgv]
    have := sub_abs (value v) (2 * value f)
    rw [abs_mul, abs_two] at this
    linarith
  obtain ⟨hhf, -⟩ := F64AddBounds.sub_real_relative v g hvf hgf hb
  rw [hh] at hhf
  refine ⟨hE, hhf,
    fun u => by rw [← hh]; exact F64SignedNearestSum.sub_nearest v g hvf hgf hb u, ?_,
    hvv, hW, ?_⟩
  rotate_left
  · rw [hgv]
    have := sub_abs (value v) (2 * value f)
    rw [abs_mul, abs_two] at this
    linarith
  have key := big_real (value v) (value x') (value r) (value w) (value ww) (value den) (value q)
    (value e1) (value f) (X + 900 * η) hvv (by rw [hη]; linarith) (by rw [hη]; linarith)
    (by rw [hη]; linarith) hwe hwwe hde hqe he1e hfe
  rw [hgv]
  have hid : value v - 2 * value f - (value v - 2 * ((value x' + value r) * value v /
      (value x' + value r + value v))) = -2 * (value f - (value x' + value r) * value v /
      (value x' + value r + value v)) := by ring
  rw [hid, abs_mul, abs_neg, abs_two]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

#print axioms arg_spec
#print axioms chain_spec

end Library.Numerics.Float64.Tan.TanBigWords
