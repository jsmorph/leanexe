import Project.Gpt2QuantizedCached.ExportCheck
import Project.ProofKit.QuantizedExport
import Project.ProofKit.PackedSource
import LeanExe.Models.Gpt2.Quantized.Format
import LeanExe.Models.Gpt2.Inference

namespace Project.Gpt2QuantizedCached.Export
open Project.ProofKit
open LeanExe.Models

theorem parameter_counts :
    (projections.map (fun p => p.inputWidth * p.outputWidth)).sum = 123532032 ∧
    (projections.map (fun p => p.outputWidth)).sum = 133201 ∧
    (retained.map (fun t => t.count)).sum = 907776 := by decide +kernel

theorem sourceRow_word (source : ByteArray) (projection : Projection) (row i : Nat)
    (hi : i < projection.inputWidth) :
    Gpt2.word (sourceRow source projection row) i =
      Gpt2.word source (projection.sourceOffset + row * projection.rowStride + i * projection.columnStride) := by
  unfold sourceRow Gpt2.word
  rw [Nat.mul_comm i 4]
  exact PackedSource.generate_read _ _ i hi

theorem projection_checked (source target : ByteArray) (h : check source target = true)
    (projection : Projection) (hp : projection ∈ projections) (row : Nat) (hr : row < projection.outputWidth) :
    QuantizedExport.checkRow (sourceRow source projection row) target
      (projection.coefficientOffset + row * projection.inputWidth) projection.inputWidth
      (LeanExe.Packed.getUInt32LE! target (projection.scaleOffset + row * 4)) = true := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at h
  have hpCheck := h.2.2.1 projection hp
  simp only [checkProjection, List.all_eq_true, List.mem_range] at hpCheck
  exact hpCheck row hr

theorem retained_checked (source target : ByteArray) (h : check source target = true)
    (tensor : Retained) (ht : tensor ∈ retained) (i : Nat) (hi : i < tensor.count) :
    CodeLib.IEEE32.Finite (Gpt2.word source (tensor.sourceOffset + i)) ∧
      Gpt2.word source (tensor.sourceOffset + i) =
        LeanExe.Packed.getUInt32LE! target (tensor.targetOffset + i * 4) := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at h
  have htCheck := h.2.2.2 tensor ht
  simp only [checkRetained, CodeLib.IEEE32.Finite, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at htCheck
  exact htCheck i hi

#print axioms projection_checked
#print axioms retained_checked
end Project.Gpt2QuantizedCached.Export
