import Project.TinyGpt2Seq.SoftmaxCode
import Project.SequenceSoftmax.Maximum
import Project.SequenceSoftmax.Total
import Project.SequenceSoftmax.Release

namespace Project.TinyGpt2Seq.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution Project.SequenceSoftmax Project.SequenceSoftmax.Spec

theorem softmax_nonempty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner : UInt64) (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source input)
    (hNonempty : 0 < input.size)
    (hBudget : OutputBudget initial heap (computeBytes input.size+remaining) pageLimit module) :
    TerminatesWith env module 49 initial [.i64 source.root, .i64 owner]
      (SoftmaxPost heap initial input remaining pageLimit) := by
  let need := mapCapacity input.size
  let heap1 := heap.allocate need
  let node1 := allocatedNode heap.top need heap.nodes
  let heap2 := heap1.allocate need
  let node2 := allocatedNode heap1.top need heap1.nodes
  let weighted := Project.SequenceSoftmax.weights input (Project.SequenceSoftmax.maximum input)
  have hSize : weighted.size = input.size := by simp [weighted, Project.SequenceSoftmax.weights]
  have hOutSize : (Project.SequenceSoftmax.normalize weighted (Project.SequenceSoftmax.total weighted)).size = input.size := by simp [Project.SequenceSoftmax.normalize, hSize]
  have hNeed := (map_capacity initial source.root input hInput.buffer.values).1
  have hSourceBudget : OutputBudget initial heap (computeBytes input.size+remaining) pageLimit SequenceSoftmax.module := hBudget.transfer rfl
  have hBudget1 : OutputBudget initial heap (48+need.toNat+(48+need.toNat+remaining)) pageLimit SequenceSoftmax.module := by
    simpa only [need, hNeed, computeBytes, two_mul, Nat.add_assoc] using hSourceBudget
  have hBump1 := hBudget1.bump need (by omega)
  have hLengthNe : UInt64.ofNat input.size ≠ 0 := by
    intro hZero
    have hNat := congrArg UInt64.toNat hZero
    rw [UInt64.toNat_ofNat_of_lt' hInput.buffer.values.size_lt] at hNat
    change input.size = 0 at hNat
    omega
  refine TerminatesWith.of_wp_entry_for (f := func49Def) rfl ?_ (by decide)
  change wp module func49 _ initial (func49Def.toLocals [.i64 owner, .i64 source.root]) env
  rw [softmax_shape]
  simp only [func49, List.take, List.cons_append, List.nil_append]
  wp_fixed_frame [func49Def]
  simp [hInput.buffer.values.pointerAddress_eq, hInput.buffer.values.lengthRead,
    hInput.buffer.values.generatedLengthBound]
  try simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp [hLengthNe])]
  wp_fixed_frame
  try simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp)]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp)]
  unfold softmaxNonempty
  wp_fixed_frame
  refine wp_call_exact_append (sequence_exact 8 (by decide) (maximum_exact env initial owner source.root input hInput.buffer.values hNonempty))
    rfl rfl rfl [] rfl ?_
  wp_fixed_frame
  refine wp_call_tw (sequence_exact 6 (by decide) (weights_owned env initial heap owner (Project.SequenceSoftmax.maximum input) source input
    (48+need.toNat+remaining) pageLimit hHeap hInput hBudget1)) ?_
  rintro first values ⟨hValues, hHeap1, hWeights, hPreserved1, hBudget2⟩
  simp only [Project.SequenceSoftmax.weights, Array.size_map] at hValues hHeap1 hWeights hPreserved1 hBudget2
  subst values
  change heap1.At first at hHeap1
  change heap1.OwnsWords first node1 weighted at hWeights
  change OutputBudget first heap1 (48+need.toNat+remaining) pageLimit SequenceSoftmax.module at hBudget2
  wp_fixed_frame
  refine wp_call_exact_append (sequence_exact 10 (by decide) (total_exact env first node1.root node1.root weighted hWeights.buffer.values))
    rfl rfl rfl [] rfl ?_
  wp_fixed_frame
  refine wp_call_tw (sequence_exact 9 (by decide) (normalize_owned env first heap1 node1.root (Project.SequenceSoftmax.total weighted) node1 weighted
    remaining pageLimit hHeap1 hWeights (by simpa only [hSize] using hBudget2))) ?_
  rintro second values ⟨hValues, hHeap2, hOutput, hPreserved2, hBudget3⟩
  simp only [hOutSize] at hValues hHeap2 hOutput hPreserved2 hBudget3
  subst values
  change heap2.At second at hHeap2
  change heap2.OwnsWords second node2 (Project.SequenceSoftmax.normalize weighted (Project.SequenceSoftmax.total weighted)) at hOutput
  have hTemp : heap2.OwnsWords second node1 weighted := hPreserved2.ownsWords hHeap2 hWeights
  have hRoot : mapRoot heap input.size ≠ 0 := by
    change node1.root ≠ 0
    have h48 := hTemp.buffer.rootBound
    intro hZero
    rw [hZero] at h48
    contradiction
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp [hRoot])]
  wp_fixed_frame
  refine wp_call_tw (Project.FunctionRegion.terminatesWith releaseRegion 15 rfl (release_exact env second heap2 node1 weighted hHeap2 hTemp)) ?_
  rintro final values ⟨rfl, rfl, hHeap3⟩
  wp_fixed_frame [func49Def]
  have hBump2 := hBudget2.bump need (by omega)
  have hOutSep := regionsDisjoint_symm
    (hWeights.allocation_disjoint need (fun h => (hBump2 h).1.le))
  have hOutFinal := hOutput.released node1 hTemp.buffer.rootBound
    (by have := hTemp.buffer.addressBound; omega) hOutSep
  refine ⟨heap2.release node1, node2, rfl, hHeap3, ?_, ?_, (hBudget3.released node1).transfer rfl⟩
  · simpa only [Project.SequenceSoftmax.compute, Array.isEmpty_iff_size_eq_zero, Nat.ne_of_gt hNonempty,
      ↓reduceIte] using hOutFinal
  · exact (hPreserved1.trans hPreserved2).released node1 hTemp.buffer.rootBound
      (by have := hTemp.buffer.addressBound; omega)
      (fun _ _ h => h.allocated_disjoint need (fun h => (hBump1 h).1.le))
#print axioms softmax_nonempty_exact
end Project.TinyGpt2Seq.Spec
