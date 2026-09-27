import Project.SpectralKL.ScalarStats
import Project.SpectralKL.KernelContinuity
import Project.ProofKit.F64Approximation

namespace Project.SpectralKL.Scalar
open CodeLib.IEEE64 Project.ProofKit Project.ProofKit.F64Horner
open LeanExe.Examples.SpectralKL
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

theorem tighten {w : UInt64} {r b e rb : ℝ} (h : Approximation w r b e)
    (hr : |r| ≤ rb) : Approximation w r (rb+e) e :=
  ⟨h.finite, F64ArithmeticBounds.magnitude_of_error _ _ _ _ h.accuracy hr, h.accuracy⟩

theorem approx_sub {a b : UInt64} {p q ba bb ea eb B : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hB : 1 ≤ B) (hmax : B < (2:ℝ)^1023) (hmag : ba+bb ≤ B) :
    Approximation (Wasm.IEEE64.sub a b) (p-q) (B+arithmeticEpsilon*B)
      (arithmeticEpsilon*B+ea+eb) := by
  have hval : |value a-value b| ≤ B :=
    (abs_sub _ _).trans ((add_le_add ha.magnitude hb.magnitude).trans hmag)
  have hs := F64ArithmeticBounds.sub_error a b ha.finite hb.finite B hB hmax hval
  have he : |(value a-value b)-(p-q)| ≤ ea+eb := by
    rw [show (value a-value b)-(p-q) = (value a-p)-(value b-q) by ring]
    exact (abs_sub _ _).trans (add_le_add ha.accuracy hb.accuracy)
  exact ⟨hs.1,F64ArithmeticBounds.magnitude_of_error _ _ _ _ hs.2 hval,
    (abs_sub_le _ _ _).trans ((add_le_add hs.2 he).trans_eq (by ring))⟩

theorem input_approx (w : UInt64) (r : ℝ) (hf : Finite w)
    (he : |value w-r| ≤ 1/100000000) (hr : |r| ≤ 1/2) :
    Approximation w r 1 (1/100000000) := by
  refine ⟨hf,?_,he⟩
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ _ he hr).trans (by norm_num)

theorem ridge_approx (w eta : UInt64) (r : ℝ) (hf : Finite w)
    (he : |value w-r| ≤ 1/100000000) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (heta : Finite eta ∧ 1 ≤ value eta ∧ value eta ≤ 256) :
    Approximation (Wasm.IEEE64.add w eta) (r+value eta) 257 (2/100000000) := by
  have hw := input_approx w r hf he (by rw [abs_of_nonneg hr0]; linarith)
  have he0 : Approximation eta (value eta) 256 0 :=
    Approximation.exact eta heta.1 256 (by rw [abs_of_nonneg (by linarith [heta.2.1])]; exact heta.2.2)
  have h := hw.add he0 (bound := 257) (by norm_num) (by norm_num) (by norm_num)
  have ht := tighten h (show |r+value eta| ≤ 1025/4 by
    rw [abs_of_nonneg (by linarith [heta.2.1])]; linarith [heta.2.2])
  exact ht.weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])

/-- A numerical proof of the computation from its four moment inputs, including
all arithmetic and the sensitivity of the analytic kernel to its argument. -/
theorem score_error (mp mq sp sq eta : UInt64) (MP MQ SP SQ : ℝ)
    (hmp : Finite mp ∧ |value mp-MP| ≤ 1/100000000)
    (hmq : Finite mq ∧ |value mq-MQ| ≤ 1/100000000)
    (hsp : Finite sp ∧ |value sp-SP| ≤ 1/100000000)
    (hsq : Finite sq ∧ |value sq-SQ| ≤ 1/100000000)
    (bMP : |MP| ≤ 1/2) (bMQ : |MQ| ≤ 1/2)
    (bSP : 0 ≤ SP ∧ SP ≤ 1/4) (bSQ : 0 ≤ SQ ∧ SQ ≤ 1/4)
    (heta : Finite eta ∧ 1 ≤ value eta ∧ value eta ≤ 256) :
    Finite (scalarScore mp mq sp sq eta) ∧
      |value (scalarScore mp mq sp sq eta) -
        (MP-MQ)^2/(SQ+value eta)*kernel ((SP+value eta)/(SQ+value eta))| ≤ 1/1000000 := by
  let a := Wasm.IEEE64.add sp eta
  let b := Wasm.IEEE64.add sq eta
  let t := Wasm.IEEE64.div a b
  let delta := Wasm.IEEE64.sub t 0x3FF0000000000000
  let d := Wasm.IEEE64.sub mp mq
  let w := Wasm.IEEE64.mul d d
  let scale := Wasm.IEEE64.div w b
  have ha : Approximation a (SP+value eta) 257 (2/100000000) := ridge_approx sp eta SP hsp.1 hsp.2 bSP.1 bSP.2 heta
  have hb : Approximation b (SQ+value eta) 257 (2/100000000) := ridge_approx sq eta SQ hsq.1 hsq.2 bSQ.1 bSQ.2 heta
  have hbpos : 9/10 ≤ value b := by linarith [(abs_le.mp hb.accuracy).1,bSQ.1,heta.2.1]
  have hSQ : 0 < SQ+value eta := by linarith [bSQ.1,heta.2.1]
  have hratioBound : |(SP+value eta)/(SQ+value eta)| ≤ 5/4 := by
    rw [abs_div, abs_of_pos hSQ, abs_of_nonneg (by linarith [bSP.1,heta.2.1] : 0 ≤ SP+value eta)]
    apply (div_le_iff₀ hSQ).mpr
    nlinarith [bSP.2,bSQ.1,heta.2.1]
  have hratioDomain : |(SP+value eta)/(SQ+value eta)-1| ≤ 1/4 := by
    have hlo : 3/4 ≤ (SP+value eta)/(SQ+value eta) := (le_div_iff₀ hSQ).mpr (by linarith [bSP.1,bSQ.2,heta.2.1])
    have hhi := (le_abs_self ((SP+value eta)/(SQ+value eta))).trans hratioBound
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have ht0 := ha.div_pos hb (lower := 9/10) (bound := 300) (by norm_num) hbpos hSQ
    hratioBound (by norm_num) (by norm_num) (by norm_num)
  have ht : Approximation t ((SP+value eta)/(SQ+value eta)) (13/10) (6/100000000) :=
    (tighten ht0 hratioBound).weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hone : Approximation 0x3FF0000000000000 1 1 0 := by
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide,?_,?_⟩ <;> simp [value_one]
  have hdelta0 := approx_sub ht hone (B := 3) (by norm_num) (by norm_num) (by norm_num)
  have hdelta : Approximation delta ((SP+value eta)/(SQ+value eta)-1) 1 (7/100000000) :=
    (tighten hdelta0 hratioDomain).weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hdtrue : |MP-MQ| ≤ 1 := (abs_sub _ _).trans (by linarith)
  have hd0 := approx_sub (input_approx mp MP hmp.1 hmp.2 bMP)
    (input_approx mq MQ hmq.1 hmq.2 bMQ) (B := 2) (by norm_num) (by norm_num) (by norm_num)
  have hd : Approximation d (MP-MQ) (11/10) (3/100000000) :=
    (tighten hd0 hdtrue).weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hwtrue : |(MP-MQ)*(MP-MQ)| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (MP-MQ)]
  have hw0 := hd.mul hd hdtrue (bound := 2) (by norm_num) (by norm_num) (by norm_num)
  have hw : Approximation w ((MP-MQ)*(MP-MQ)) (11/10) (7/100000000) :=
    (tighten hw0 hwtrue).weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hsTrue : |(MP-MQ)*(MP-MQ)/(SQ+value eta)| ≤ 1 := by
    rw [abs_div, abs_of_pos hSQ]
    apply (div_le_iff₀ hSQ).mpr
    linarith [bSQ.1,heta.2.1]
  have hs0 := hw.div_pos hb (lower := 9/10) (bound := 2) (by norm_num) hbpos hSQ
    hsTrue (by norm_num) (by norm_num) (by norm_num)
  have hs : Approximation scale ((MP-MQ)*(MP-MQ)/(SQ+value eta)) (11/10) (11/100000000) :=
    (tighten hs0 hsTrue).weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hdeltaDomain : |value delta| ≤ 1/2 := by
    have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hdelta.accuracy hratioDomain
    linarith
  have hk0 := Executable.kernel40Polynomial_error delta hdelta.finite hdeltaDomain
  have harg : |(1+value delta)-(SP+value eta)/(SQ+value eta)| ≤ 7/100000000 := by
    convert hdelta.accuracy using 1 <;> congr 1 <;> ring
  have hker := kernel_lipschitz (1+value delta) ((SP+value eta)/(SQ+value eta))
    (by simpa using hdeltaDomain) (hratioDomain.trans (by norm_num))
  have hkt := kernel_abs_le ((SP+value eta)/(SQ+value eta)) (hratioDomain.trans (by norm_num))
  have hkError : |value (kernel40Polynomial delta)-kernel ((SP+value eta)/(SQ+value eta))| ≤ 29/100000000 := by
    have htriangle := abs_sub_le (value (kernel40Polynomial delta)) (kernel (1+value delta))
      (kernel ((SP+value eta)/(SQ+value eta)))
    linarith [hk0.2]
  have hk : Approximation (kernel40Polynomial delta) (kernel ((SP+value eta)/(SQ+value eta))) 2 (29/100000000) :=
    ⟨hk0.1,(F64ArithmeticBounds.magnitude_of_error _ _ _ _ hkError hkt).trans (by norm_num),hkError⟩
  have hout := hs.mul hk hkt (bound := 3) (by norm_num) (by norm_num) (by norm_num)
  have heq : scalarScore mp mq sp sq eta =
      Wasm.IEEE64.mul scale (kernel40Polynomial delta) := by
    simp only [scalarScore, scale, w, d, delta, t, a, b,
      Operations.add, Operations.sub, Operations.div, Operations.mul]
  rw [heq]
  refine ⟨hout.finite,?_⟩
  simpa only [pow_two] using hout.accuracy.trans (by norm_num [arithmeticEpsilon])

#print axioms score_error
end Project.SpectralKL.Scalar
