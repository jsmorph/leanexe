import Project.Gpt2QuantizedCached.Numerical.ProjectionRangeSound
import Project.ProofKit.PackedExtractSource
import Project.ProofKit.QuantizedRangeCertificate
import Project.ProofKit.F32Absolute
import Project.Gpt2QuantizedGroupedRows.ForwardError

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

theorem activation_conditions (input : ByteArray) (width scaleMagnitude group : Nat)
    (hs : input.size = width * 4) (hg : group < width / 64)
    (h : checkActivations input scaleMagnitude = true) :
    let scale := Gpt2QuantizedGroupedRows.ForwardError.inputScale input width 1 0 group
    CodeLib.IEEE32.Finite scale ∧ Wasm.IEEE32.scaledMagnitude scale ≤ scaleMagnitude ∧
      ∀ i < 64,
        |CodeLib.IEEE32.value scale * QuantizedGroupError.byteValue
            (Quantized.quantizeRows input 64 (width / 64)).values (group * 64 + i) -
          CodeLib.IEEE32.value (word input (group * 64 + i))| ≤
            CodeLib.IEEE32.value scale * (1 / 2 + 1 / 65536) := by
  have hgroups : input.size / 256 = width / 64 := by omega
  have hfit : (group * 64 + 64) * 4 ≤ input.size := by omega
  simp only [checkActivations, hgroups, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at h
  have hc := h.2 group hg
  let scale := word (Quantized.quantizeRows input 64 (width / 64)).scales group
  let values := input.extract (group * 256) ((group + 1) * 256)
  have hr : QuantizedExport.checkRow values (Quantized.quantizeRows input 64 (width / 64)).values
      (group * 64) 64 scale = true := hc.1
  have hf := QuantizedExport.checked_row _ _ _ _ _ hr
  simp only [Gpt2QuantizedGroupedRows.ForwardError.inputScale, Nat.one_mul, Nat.zero_mul, Nat.zero_add]
  change CodeLib.IEEE32.Finite scale ∧ Wasm.IEEE32.scaledMagnitude scale ≤ scaleMagnitude ∧ _
  refine ⟨hf.2.2.2.1, hc.2.1, ?_⟩
  intro i hi
  have hi' : word values i = word input (group * 64 + i) := by
    simpa only [values, word, Nat.add_mul, Nat.mul_assoc, Nat.one_mul,
      show (64 : Nat) * 4 = 256 from rfl] using
      PackedSource.extract_read input (group * 64) 64 i hfit hi
  have hq : |CodeLib.IEEE32.value (LeanExe.Float32.divBits (word values i) scale)| ≤
      127 + 1 / 131072 := by
    rw [F32Order.abs_value_scaledMagnitude]
    have hm : (Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.divBits (word values i) scale) : ℝ) ≤
        (127 : ℝ) * 2 ^ 149 + 2 ^ 132 := by exact_mod_cast hc.2.2 i hi
    exact (div_le_iff₀ (by positivity)).mpr (by norm_num at hm ⊢; exact hm)
  have he := QuantizedRangeCertificate.reconstruction _ _ _ _ _ hr i hi hq
  rw [hi'] at he
  exact he

#print axioms activation_conditions
end Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
