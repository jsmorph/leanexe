import Library.Numerics.Float64.Log1p.Log1pTheoremBranches
import Library.Numerics.Float64.Log1p.Log1pKernelPoly
import LeanExe.ProofKit.F64Approx
import LeanExe.ProofKit.F64Exact

/-!
The polynomial part of `Log1p.log1pTail`: `f²/2` as `0.5 * f * f`, `s = f/(2 + f)`, and
`P = s (f²/2 + R)` with `R = z (Lp1 + ... + z Lp7)`, `z = s s`, in the order of `s_log1p.c`.  The
bounds are relative to `σ = |f|` and come from `F64Approx` with each step rounded up to a short
rational, for four ranges of `f`.  In exact arithmetic `f - (f²/2 - P) = 2 s + s R(s)` with the
exact `s = f/(2 + f)`, which `Log1pKernelPoly.log1p_kernel_error` compares with
`log (1 + f) = log (1 + s) - log (1 - s)`.
-/

namespace Library.Numerics.Float64.Log1p.Log1pTheoremCore
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound Log1pTheoremBranches

set_option exponentiation.threshold 4096

/-- `R` in exact arithmetic for the argument `s`. -/
noncomputable def polyR (s : ℝ) : ℝ :=
  s * s * (value 0x3FE5555555555593 + s * s * (value 0x3FD999999997FA04 +
    s * s * (value 0x3FD2492494229359 + s * s * (value 0x3FCC71C51D8E78AF +
    s * s * (value 0x3FC7466496CB03DE + s * s * (value 0x3FC39A09D078C69F +
    s * s * value 0x3FC2F112DF3E5244))))))

noncomputable def sStar (v : ℝ) : ℝ := v / (2 + v)

/-- `P` in exact arithmetic. -/
noncomputable def Pstar (v : ℝ) : ℝ := sStar v * (v / 2 * v + polyR (sStar v))

theorem kernel_link (s : ℝ) :
    2 * s + s * polyR s = s * eval Log1pKernelPoly.log1pKernel (s ^ 2) := by
  simp only [polyR, Log1pKernelPoly.log1pKernel, eval_cons, eval_nil, ratOfWord_cast]
  push_cast
  ring

theorem tail_identity (v : ℝ) (hv : 2 + v ≠ 0) :
    v - (v / 2 * v - Pstar v) = 2 * sStar v + sStar v * polyR (sStar v) := by
  simp only [Pstar, sStar]
  field_simp
  ring

/-- `log (1 + v)` against the exact kernel at `s = v/(2 + v)`. -/
theorem log_kernel (v : ℝ) (hv : -1 < v) (hs : |sStar v| ≤ 1716 / 10000) :
    |Real.log (1 + v) - (2 * sStar v + sStar v * polyR (sStar v))| ≤
      |sStar v| * ((93 / 128) / 2 ^ 58) := by
  have h := Log1pKernelPoly.log1p_kernel_error (sStar v) hs
  rw [← kernel_link] at h
  have h2 : 0 < 2 + v := by linarith
  have h1 : 0 < 1 + sStar v := by
    rw [sStar, show 1 + v / (2 + v) = (2 + 2 * v) / (2 + v) by field_simp; ring]
    apply div_pos _ h2
    linarith
  have h1' : 0 < 1 - sStar v := by
    rw [sStar, show 1 - v / (2 + v) = 2 / (2 + v) by field_simp; ring]
    positivity
  have hl : Real.log (1 + sStar v) - Real.log (1 - sStar v) = Real.log (1 + v) := by
    rw [← Real.log_div h1.ne' h1'.ne']
    congr 1
    rw [sStar]
    field_simp
    ring
  rw [hl] at h
  exact h

theorem half_float (f : Float) (hf : Finite f.toBits) (h : 1 / 2 ^ 1000 ≤ |value f.toBits|) :
    Finite (0.5 * f).toBits ∧ value (0.5 * f).toBits = value f.toBits / 2 := by
  rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
  exact F64Exact.mul_half_exact f.toBits hf (F64Exact.exponent_two_of_value _ h)

theorem half_approx (f : Float) (σ : ℝ) (hfa : FSApprox f (value f.toBits) σ 1 0)
    (h : 1 / 2 ^ 1000 ≤ |value f.toBits|) : FSApprox (0.5 * f) (value f.toBits / 2) σ (1 / 2) 0 := by
  obtain ⟨hff, hv⟩ := half_float f hfa.approx.1 h
  refine ⟨hfa.1, hfa.2.1, ?_, ?_⟩
  · have := hfa.2.2.1
    rw [abs_div, abs_two]
    linarith
  · exact ⟨hff, by rw [hv, sub_self, abs_zero, zero_mul]⟩

theorem two_approx : FSApprox (2.0 : Float) 2 1 2 0 := by
  have hv : value 0x4000000000000000 = 2 := by
    rw [← ratOfWord_cast, show ratOfWord 0x4000000000000000 = 2 by decide +kernel]
    norm_num
  unfold FSApprox
  rw [show (2.0 : Float).toBits = 0x4000000000000000 from rfl]
  exact ⟨one_pos, le_rfl, by norm_num, by unfold CodeLib.IEEE64.Finite; decide +kernel,
    by rw [hv]; norm_num⟩

/-- The chain for `|f| ≤ 0.293` and `2 + f ≥ 1.707`. -/
theorem core_P1 (f : Float) (hf : Finite f.toBits) (hσ1 : |value f.toBits| ≤ (293 / 1000))
    (hσ0 : 1 / 2 ^ 30 ≤ |value f.toBits|) (hmb0 : (1707 / 1000) ≤ 2 + value f.toBits) :
    FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) (1 / 2) ((5001 / 10000) / 2 ^ 53) ∧
    FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) (537 / 1250)
        ((3227 / 1000) / 2 ^ 53) := by
  set σ := |value f.toBits| with hσ
  have hs : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hfa : FSApprox f (value f.toBits) σ 1 0 :=
    fsapprox_input f hf σ hs (hσ1.trans (by norm_num)) le_rfl
  have hh := half_approx f σ hfa (le_trans (by norm_num) hσ0)
  have h2c := two_approx
  have hmb : (1707 / 1000) ≤ |2 + value f.toBits| := hmb0.trans (le_abs_self _)
  have hss : 1 / 2 ^ 60 ≤ σ * σ := by
    have := mul_le_mul hσ0 hσ0 (by positivity) hs.le
    norm_num at this ⊢
    linarith
  have hpos2 : 0 < σ * σ := mul_pos hs hs
  have hle2 : σ * σ ≤ 1 := by nlinarith
  have hk1 : σ ≤ (293 / 1000) * 1 := by rw [mul_one]; exact hσ1
  have hk2 : σ * σ ≤ (293 / 1000) ^ 2 * 1 := by nlinarith
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hη2 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ) := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 60) ≤ 1 / 2 ^ 960 * (σ * σ) :=
      mul_le_mul_of_nonneg_left hss (by positivity)
    norm_num at this ⊢
    linarith
  have hη21 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ * 1) := by rw [mul_one]; exact hη2
  have hη3 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) := by
    have h3 : 1 / 2 ^ 30 * (1 / 2 ^ 60) ≤ σ * (σ * σ) := mul_le_mul hσ0 hss (by positivity) hs.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30 * (1 / 2 ^ 60)) ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    norm_num at this ⊢
    linarith
  have hq := (fsapprox_mul hh hfa (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (1 / 2)) (e' := (5001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hf1 := (hfa.rescale 1 ((293 / 1000)) one_pos le_rfl hk1).mono
    (M' := (293 / 1000)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have hd := (fsapprox_add' h2c hf1 (by norm_num)).mono
    (M' := (2293 / 1000)) (e' := (2293 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs := (fsapprox_div hfa hd (1707 / 1000) hmb (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (5859 / 10000)) (e' := (858 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have hz := (fsapprox_mul hs hs (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (3433 / 10000)) (e' := (244 / 125) / 2 ^ 53) (by norm_num) (by norm_num)
  have hzk := (hz.rescale 1 ((293 / 1000) ^ 2) one_pos le_rfl hk2).mono
    (M' := (59 / 2000)) (e' := (419 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have c6 := fsapprox_const 0x3FC2F112DF3E5244 (by decide +kernel) (((73991 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have p5 := (fsapprox_mul hzk c6 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (8731 / 2000000)) (e' := (73 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have q5 := (p5.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (8731 / 2000000)) (e' := (73 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3FC39A09D078C69F (by decide +kernel) (((153139 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a5 := (fsapprox_add' c5 q5 (by norm_num)).mono
    (M' := (197 / 1250)) (e' := (467 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have p4 := (fsapprox_mul hzk a5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (11623 / 2500000)) (e' := (183 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q4 := (p4.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (11623 / 2500000)) (e' := (183 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c4 := fsapprox_const 0x3FC7466496CB03DE (by decide +kernel) (((45459 / 250000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a4 := (fsapprox_add' c4 q4 (by norm_num)).mono
    (M' := (373 / 2000)) (e' := (2231 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p3 := (fsapprox_mul hzk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (27509 / 5000000)) (e' := (217 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q3 := (p3.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (27509 / 5000000)) (e' := (217 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c3 := fsapprox_const 0x3FCC71C51D8E78AF (by decide +kernel) (((111111 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a3 := (fsapprox_add' c3 q3 (by norm_num)).mono
    (M' := (1139 / 5000)) (e' := (339 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have p2 := (fsapprox_mul hzk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (67201 / 10000000)) (e' := (529 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q2 := (p2.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (67201 / 10000000)) (e' := (529 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c2 := fsapprox_const 0x3FD2492494229359 (by decide +kernel) (((57143 / 200000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a2 := (fsapprox_add' c2 q2 (by norm_num)).mono
    (M' := (117 / 400)) (e' := (1727 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := (fsapprox_mul hzk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (5393 / 625000)) (e' := (679 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q1 := (p1.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (5393 / 625000)) (e' := (679 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c1 := fsapprox_const 0x3FD999999997FA04 (by decide +kernel) (((2 / 5) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a1 := (fsapprox_add' c1 q1 (by norm_num)).mono
    (M' := (4087 / 10000)) (e' := (2383 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul hzk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (121 / 10000)) (e' := (947 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q0 := (p0.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (121 / 10000)) (e' := (947 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c0 := fsapprox_const 0x3FE5555555555593 (by decide +kernel) (((666667 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a0 := (fsapprox_add' c0 q0 (by norm_num)).mono
    (M' := (1697 / 2500)) (e' := (1547 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR0 := (fsapprox_mul hz a0 (1 / 2 ^ 960) hη21 (by norm_num)).mono
    (M' := (2331 / 10000)) (e' := (4559 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR := (hR0.rescale (σ * σ) (1) hpos2 hle2 (by rw [mul_one, one_mul])).mono
    (M' := (2331 / 10000)) (e' := (4559 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have hhR := (fsapprox_add' hq hR (by norm_num)).mono
    (M' := (7331 / 10000)) (e' := (30569 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hP := (fsapprox_mul hs hhR (1 / 2 ^ 960) hη3 (by norm_num)).mono
    (M' := (537 / 1250)) (e' := (3227 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact ⟨hq, hP⟩

/-- The chain for `|f| ≤ 0.285` and `2 + f ≥ 2.0`. -/
theorem core_P2 (f : Float) (hf : Finite f.toBits) (hσ1 : |value f.toBits| ≤ (57 / 200))
    (hσ0 : 1 / 2 ^ 30 ≤ |value f.toBits|) (hmb0 : 2 ≤ 2 + value f.toBits) :
    FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) (1 / 2) ((5001 / 10000) / 2 ^ 53) ∧
    FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) (209 / 625)
        ((11289 / 5000) / 2 ^ 53) := by
  set σ := |value f.toBits| with hσ
  have hs : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hfa : FSApprox f (value f.toBits) σ 1 0 :=
    fsapprox_input f hf σ hs (hσ1.trans (by norm_num)) le_rfl
  have hh := half_approx f σ hfa (le_trans (by norm_num) hσ0)
  have h2c := two_approx
  have hmb : 2 ≤ |2 + value f.toBits| := hmb0.trans (le_abs_self _)
  have hss : 1 / 2 ^ 60 ≤ σ * σ := by
    have := mul_le_mul hσ0 hσ0 (by positivity) hs.le
    norm_num at this ⊢
    linarith
  have hpos2 : 0 < σ * σ := mul_pos hs hs
  have hle2 : σ * σ ≤ 1 := by nlinarith
  have hk1 : σ ≤ (57 / 200) * 1 := by rw [mul_one]; exact hσ1
  have hk2 : σ * σ ≤ (57 / 200) ^ 2 * 1 := by nlinarith
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hη2 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ) := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 60) ≤ 1 / 2 ^ 960 * (σ * σ) :=
      mul_le_mul_of_nonneg_left hss (by positivity)
    norm_num at this ⊢
    linarith
  have hη21 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ * 1) := by rw [mul_one]; exact hη2
  have hη3 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) := by
    have h3 : 1 / 2 ^ 30 * (1 / 2 ^ 60) ≤ σ * (σ * σ) := mul_le_mul hσ0 hss (by positivity) hs.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30 * (1 / 2 ^ 60)) ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    norm_num at this ⊢
    linarith
  have hq := (fsapprox_mul hh hfa (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (1 / 2)) (e' := (5001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hf1 := (hfa.rescale 1 ((57 / 200)) one_pos le_rfl hk1).mono
    (M' := (57 / 200)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have hd := (fsapprox_add' h2c hf1 (by norm_num)).mono
    (M' := (457 / 200)) (e' := (457 / 200) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs := (fsapprox_div hfa hd 2 hmb (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (1 / 2)) (e' := (10713 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hz := (fsapprox_mul hs hs (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (1 / 4)) (e' := (6607 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hzk := (hz.rescale 1 ((57 / 200) ^ 2) one_pos le_rfl hk2).mono
    (M' := (51 / 2500)) (e' := (537 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c6 := fsapprox_const 0x3FC2F112DF3E5244 (by decide +kernel) (((73991 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have p5 := (fsapprox_mul hzk c6 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (30189 / 10000000)) (e' := (19 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q5 := (p5.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (30189 / 10000000)) (e' := (19 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3FC39A09D078C69F (by decide +kernel) (((153139 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a5 := (fsapprox_add' c5 q5 (by norm_num)).mono
    (M' := (781 / 5000)) (e' := (219 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have p4 := (fsapprox_mul hzk a5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (6373 / 2000000)) (e' := (59 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have q4 := (p4.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (6373 / 2000000)) (e' := (59 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have c4 := fsapprox_const 0x3FC7466496CB03DE (by decide +kernel) (((45459 / 250000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a4 := (fsapprox_add' c4 q4 (by norm_num)).mono
    (M' := (1851 / 10000)) (e' := (2087 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p3 := (fsapprox_mul hzk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (37761 / 10000000)) (e' := (7 / 250) / 2 ^ 53) (by norm_num) (by norm_num)
  have q3 := (p3.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (37761 / 10000000)) (e' := (7 / 250) / 2 ^ 53) (by norm_num) (by norm_num)
  have c3 := fsapprox_const 0x3FCC71C51D8E78AF (by decide +kernel) (((111111 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a3 := (fsapprox_add' c3 q3 (by norm_num)).mono
    (M' := (113 / 500)) (e' := (127 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have p2 := (fsapprox_mul hzk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (5763 / 1250000)) (e' := (341 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q2 := (p2.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (5763 / 1250000)) (e' := (341 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c2 := fsapprox_const 0x3FD2492494229359 (by decide +kernel) (((57143 / 200000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a2 := (fsapprox_add' c2 q2 (by norm_num)).mono
    (M' := (363 / 1250)) (e' := (649 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := (fsapprox_mul hzk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (29621 / 5000000)) (e' := (219 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q1 := (p1.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (29621 / 5000000)) (e' := (219 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c1 := fsapprox_const 0x3FD999999997FA04 (by decide +kernel) (((2 / 5) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a1 := (fsapprox_add' c1 q1 (by norm_num)).mono
    (M' := (203 / 500)) (e' := (2249 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul hzk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (10353 / 1250000)) (e' := (611 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q0 := (p0.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (10353 / 1250000)) (e' := (611 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c0 := fsapprox_const 0x3FE5555555555593 (by decide +kernel) (((666667 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a0 := (fsapprox_add' c0 q0 (by norm_num)).mono
    (M' := (27 / 40)) (e' := (7361 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR0 := (fsapprox_mul hz a0 (1 / 2 ^ 960) hη21 (by norm_num)).mono
    (M' := (211 / 1250)) (e' := (778 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR := (hR0.rescale (σ * σ) (1) hpos2 hle2 (by rw [mul_one, one_mul])).mono
    (M' := (211 / 1250)) (e' := (778 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have hhR := (fsapprox_add' hq hR (by norm_num)).mono
    (M' := (418 / 625)) (e' := (12069 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hP := (fsapprox_mul hs hhR (1 / 2 ^ 960) hη3 (by norm_num)).mono
    (M' := (209 / 625)) (e' := (11289 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact ⟨hq, hP⟩

/-- The chain for `|f| ≤ 0.41422` and `2 + f ≥ 2.285`. -/
theorem core_P3 (f : Float) (hf : Finite f.toBits) (hσ1 : |value f.toBits| ≤ (20711 / 50000))
    (hσ0 : 1 / 2 ^ 30 ≤ |value f.toBits|) (hmb0 : (457 / 200) ≤ 2 + value f.toBits) :
    FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) (1 / 2) ((5001 / 10000) / 2 ^ 53) ∧
    FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) (69 / 250)
        ((8761 / 5000) / 2 ^ 53) := by
  set σ := |value f.toBits| with hσ
  have hs : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hfa : FSApprox f (value f.toBits) σ 1 0 :=
    fsapprox_input f hf σ hs (hσ1.trans (by norm_num)) le_rfl
  have hh := half_approx f σ hfa (le_trans (by norm_num) hσ0)
  have h2c := two_approx
  have hmb : (457 / 200) ≤ |2 + value f.toBits| := hmb0.trans (le_abs_self _)
  have hss : 1 / 2 ^ 60 ≤ σ * σ := by
    have := mul_le_mul hσ0 hσ0 (by positivity) hs.le
    norm_num at this ⊢
    linarith
  have hpos2 : 0 < σ * σ := mul_pos hs hs
  have hle2 : σ * σ ≤ 1 := by nlinarith
  have hk1 : σ ≤ (20711 / 50000) * 1 := by rw [mul_one]; exact hσ1
  have hk2 : σ * σ ≤ (20711 / 50000) ^ 2 * 1 := by nlinarith
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hη2 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ) := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 60) ≤ 1 / 2 ^ 960 * (σ * σ) :=
      mul_le_mul_of_nonneg_left hss (by positivity)
    norm_num at this ⊢
    linarith
  have hη21 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ * 1) := by rw [mul_one]; exact hη2
  have hη3 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) := by
    have h3 : 1 / 2 ^ 30 * (1 / 2 ^ 60) ≤ σ * (σ * σ) := mul_le_mul hσ0 hss (by positivity) hs.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30 * (1 / 2 ^ 60)) ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    norm_num at this ⊢
    linarith
  have hq := (fsapprox_mul hh hfa (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (1 / 2)) (e' := (5001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hf1 := (hfa.rescale 1 ((20711 / 50000)) one_pos le_rfl hk1).mono
    (M' := (4143 / 10000)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have hd := (fsapprox_add' h2c hf1 (by norm_num)).mono
    (M' := (24143 / 10000)) (e' := (24143 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs := (fsapprox_div hfa hd (457 / 200) hmb (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (4377 / 10000)) (e' := (9001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hz := (fsapprox_mul hs hs (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (479 / 2500)) (e' := (2449 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have hzk := (hz.rescale 1 ((20711 / 50000) ^ 2) one_pos le_rfl hk2).mono
    (M' := (329 / 10000)) (e' := (1681 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c6 := fsapprox_const 0x3FC2F112DF3E5244 (by decide +kernel) (((73991 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have p5 := (fsapprox_mul hzk c6 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (48687 / 10000000)) (e' := (149 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q5 := (p5.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (48687 / 10000000)) (e' := (149 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3FC39A09D078C69F (by decide +kernel) (((153139 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a5 := (fsapprox_add' c5 q5 (by norm_num)).mono
    (M' := (1581 / 10000)) (e' := (1879 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p4 := (fsapprox_mul hzk a5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (10403 / 2000000)) (e' := (19 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have q4 := (p4.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (10403 / 2000000)) (e' := (19 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have c4 := fsapprox_const 0x3FC7466496CB03DE (by decide +kernel) (((45459 / 250000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a4 := (fsapprox_add' c4 q4 (by norm_num)).mono
    (M' := (1871 / 10000)) (e' := (2251 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p3 := (fsapprox_mul hzk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (15389 / 2500000)) (e' := (451 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q3 := (p3.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (15389 / 2500000)) (e' := (451 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c3 := fsapprox_const 0x3FCC71C51D8E78AF (by decide +kernel) (((111111 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a3 := (fsapprox_add' c3 q3 (by norm_num)).mono
    (M' := (571 / 2500)) (e' := (547 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p2 := (fsapprox_mul hzk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (9393 / 1250000)) (e' := (11 / 200) / 2 ^ 53) (by norm_num) (by norm_num)
  have q2 := (p2.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (9393 / 1250000)) (e' := (11 / 200) / 2 ^ 53) (by norm_num) (by norm_num)
  have c2 := fsapprox_const 0x3FD2492494229359 (by decide +kernel) (((57143 / 200000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a2 := (fsapprox_add' c2 q2 (by norm_num)).mono
    (M' := (2933 / 10000)) (e' := (3483 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := (fsapprox_mul hzk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (6031 / 625000)) (e' := (141 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q1 := (p1.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (6031 / 625000)) (e' := (141 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c1 := fsapprox_const 0x3FD999999997FA04 (by decide +kernel) (((2 / 5) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a1 := (fsapprox_add' c1 q1 (by norm_num)).mono
    (M' := (4097 / 10000)) (e' := (2401 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul hzk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (27 / 2000)) (e' := (491 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q0 := (p0.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (27 / 2000)) (e' := (491 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c0 := fsapprox_const 0x3FE5555555555593 (by decide +kernel) (((666667 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a0 := (fsapprox_add' c0 q0 (by norm_num)).mono
    (M' := (3401 / 5000)) (e' := (973 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR0 := (fsapprox_mul hz a0 (1 / 2 ^ 960) hη21 (by norm_num)).mono
    (M' := (163 / 1250)) (e' := (4729 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR := (hR0.rescale (σ * σ) (1) hpos2 hle2 (by rw [mul_one, one_mul])).mono
    (M' := (163 / 1250)) (e' := (4729 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hhR := (fsapprox_add' hq hR (by norm_num)).mono
    (M' := (394 / 625)) (e' := (5191 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have hP := (fsapprox_mul hs hhR (1 / 2 ^ 960) hη3 (by norm_num)).mono
    (M' := (69 / 250)) (e' := (8761 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact ⟨hq, hP⟩

/-- The chain for `|f| ≤ 0.41422` and `2 + f ≥ 1.707`. -/
theorem core_P4 (f : Float) (hf : Finite f.toBits) (hσ1 : |value f.toBits| ≤ (20711 / 50000))
    (hσ0 : 1 / 2 ^ 30 ≤ |value f.toBits|) (hmb0 : (1707 / 1000) ≤ 2 + value f.toBits) :
    FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) (1 / 2) ((5001 / 10000) / 2 ^ 53) ∧
    FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) (4321 / 10000)
        ((33293 / 10000) / 2 ^ 53) := by
  set σ := |value f.toBits| with hσ
  have hs : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hfa : FSApprox f (value f.toBits) σ 1 0 :=
    fsapprox_input f hf σ hs (hσ1.trans (by norm_num)) le_rfl
  have hh := half_approx f σ hfa (le_trans (by norm_num) hσ0)
  have h2c := two_approx
  have hmb : (1707 / 1000) ≤ |2 + value f.toBits| := hmb0.trans (le_abs_self _)
  have hss : 1 / 2 ^ 60 ≤ σ * σ := by
    have := mul_le_mul hσ0 hσ0 (by positivity) hs.le
    norm_num at this ⊢
    linarith
  have hpos2 : 0 < σ * σ := mul_pos hs hs
  have hle2 : σ * σ ≤ 1 := by nlinarith
  have hk1 : σ ≤ (20711 / 50000) * 1 := by rw [mul_one]; exact hσ1
  have hk2 : σ * σ ≤ (20711 / 50000) ^ 2 * 1 := by nlinarith
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hη2 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ) := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 60) ≤ 1 / 2 ^ 960 * (σ * σ) :=
      mul_le_mul_of_nonneg_left hss (by positivity)
    norm_num at this ⊢
    linarith
  have hη21 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ * 1) := by rw [mul_one]; exact hη2
  have hη3 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) := by
    have h3 : 1 / 2 ^ 30 * (1 / 2 ^ 60) ≤ σ * (σ * σ) := mul_le_mul hσ0 hss (by positivity) hs.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 30 * (1 / 2 ^ 60)) ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    norm_num at this ⊢
    linarith
  have hq := (fsapprox_mul hh hfa (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (1 / 2)) (e' := (5001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hf1 := (hfa.rescale 1 ((20711 / 50000)) one_pos le_rfl hk1).mono
    (M' := (4143 / 10000)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have hd := (fsapprox_add' h2c hf1 (by norm_num)).mono
    (M' := (24143 / 10000)) (e' := (24143 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs := (fsapprox_div hfa hd (1707 / 1000) hmb (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (5859 / 10000)) (e' := (884 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have hz := (fsapprox_mul hs hs (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := (3433 / 10000)) (e' := (20007 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hzk := (hz.rescale 1 ((20711 / 50000) ^ 2) one_pos le_rfl hk2).mono
    (M' := (59 / 1000)) (e' := (3433 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c6 := fsapprox_const 0x3FC2F112DF3E5244 (by decide +kernel) (((73991 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have p5 := (fsapprox_mul hzk c6 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (8731 / 1000000)) (e' := (149 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have q5 := (p5.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (8731 / 1000000)) (e' := (149 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3FC39A09D078C69F (by decide +kernel) (((153139 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a5 := (fsapprox_add' c5 q5 (by norm_num)).mono
    (M' := (1619 / 10000)) (e' := (443 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p4 := (fsapprox_mul hzk a5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (95521 / 10000000)) (e' := (783 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q4 := (p4.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (95521 / 10000000)) (e' := (783 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c4 := fsapprox_const 0x3FC7466496CB03DE (by decide +kernel) (((45459 / 250000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a4 := (fsapprox_add' c4 q4 (by norm_num)).mono
    (M' := (957 / 5000)) (e' := (2697 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p3 := (fsapprox_mul hzk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (113 / 10000)) (e' := (93 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q3 := (p3.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (113 / 10000)) (e' := (93 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c3 := fsapprox_const 0x3FCC71C51D8E78AF (by decide +kernel) (((111111 / 500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a3 := (fsapprox_add' c3 q3 (by norm_num)).mono
    (M' := (146 / 625)) (e' := (1633 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p2 := (fsapprox_mul hzk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (69 / 5000)) (e' := (1133 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q2 := (p2.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (69 / 5000)) (e' := (1133 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c2 := fsapprox_const 0x3FD2492494229359 (by decide +kernel) (((57143 / 200000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a2 := (fsapprox_add' c2 q2 (by norm_num)).mono
    (M' := (749 / 2500)) (e' := (4129 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := (fsapprox_mul hzk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (177 / 10000)) (e' := (1449 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q1 := (p1.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (177 / 10000)) (e' := (1449 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c1 := fsapprox_const 0x3FD999999997FA04 (by decide +kernel) (((2 / 5) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a1 := (fsapprox_add' c1 q1 (by norm_num)).mono
    (M' := (4177 / 10000)) (e' := (5627 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul hzk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (247 / 10000)) (e' := (2013 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have q0 := (p0.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (247 / 10000)) (e' := (2013 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c0 := fsapprox_const 0x3FE5555555555593 (by decide +kernel) (((666667 / 1000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have a0 := (fsapprox_add' c0 q0 (by norm_num)).mono
    (M' := (3457 / 5000)) (e' := (8927 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR0 := (fsapprox_mul hz a0 (1 / 2 ^ 960) hη21 (by norm_num)).mono
    (M' := (1187 / 5000)) (e' := (2409 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have hR := (hR0.rescale (σ * σ) (1) hpos2 hle2 (by rw [mul_one, one_mul])).mono
    (M' := (1187 / 5000)) (e' := (2409 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have hhR := (fsapprox_add' hq hR (by norm_num)).mono
    (M' := (3687 / 5000)) (e' := (1978 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have hP := (fsapprox_mul hs hhR (1 / 2 ^ 960) hη3 (by norm_num)).mono
    (M' := (4321 / 10000)) (e' := (33293 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact ⟨hq, hP⟩

#print axioms log_kernel
#print axioms core_P1
#print axioms core_P4

end Library.Numerics.Float64.Log1p.Log1pTheoremCore
