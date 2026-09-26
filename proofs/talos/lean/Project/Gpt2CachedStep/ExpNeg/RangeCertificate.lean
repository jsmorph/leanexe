import Project.Gpt2CachedStep.ExpNeg.RangeCheck
import Project.Gpt2CachedStep.ExpNeg.ForwardError
import Project.ProofKit.F32RangeCertificate
import Project.ProofKit.F32Absolute
import Project.ProofKit.F32HornerRangeCertificate

namespace Project.Gpt2CachedStep.ExpNeg.RangeCertificate
open Project.ProofKit CodeLib.IEEE32

theorem cutoff (input : UInt32) (p : Parameters) (h : check input p = true)
    (hCutoff : input > 0xC2800000) : value input ≤ -64 := by
  simp only [check, hCutoff, ite_true, decide_eq_true_eq] at h
  have hr : (Wasm.IEEE32.scaledValue input : ℝ) ≤ -64 * 2 ^ 149 := by exact_mod_cast h
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 149)).mpr hr

theorem sound (input : UInt32) (p : Parameters) (h : check input p = true)
    (hInner : input ≤ 0xC2800000) :
    ForwardError.Ranges input (fun _ => p.multiplication) (fun _ => p.addition) (fun _ => p.squaring) := by
  have hn : ¬input > 0xC2800000 := by
    change ¬(0xC2800000 : UInt32).toNat < input.toNat
    change input.toNat ≤ (0xC2800000 : UInt32).toNat at hInner
    omega
  simp only [check, hn, ite_false, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨hf, hm, hr, hPolynomial, hs⟩ := h
  have hp := F32HornerRangeCertificate.checks _ _ _ _ _ _ hPolynomial
  have hMagnitude : |value (reducePrefix input 6).1| ≤ 1 := by
    rw [F32Order.abs_value_scaledMagnitude]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ 149)).mpr
    exact_mod_cast hm
  have hRescale := F32RangeCertificate.rescaling_sound input (reducePrefix input 6).1 (reducePrefix input 6).2 hr
  simp only [F32RangeCertificate.multiplication, F32RangeCertificate.addition,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hp hs
  refine ⟨hf, hMagnitude, ?_, fun i hi => (hp i hi).2.2.1,
    fun i hi => (hp i hi).2.2.2.1, fun i hi => (hp i hi).2.2.2.2.1,
    fun i hi => (hp i hi).2.2.2.2.2.2.2.1, fun i hi => (hp i hi).2.2.2.2.2.2.2.2,
    fun i hi => (hs i hi).2.2.1, fun i hi => (hs i hi).2.2.2.1,
    fun i hi => (hs i hi).2.2.2.2⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hRescale

#print axioms cutoff
#print axioms sound
end Project.Gpt2CachedStep.ExpNeg.RangeCertificate
