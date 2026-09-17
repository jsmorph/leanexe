import Project.SequenceSoftmax.ComputeState
import Project.SequenceSoftmax.Maximum
import Project.SequenceSoftmax.Total
import Project.SequenceSoftmax.Release
import Project.SequenceSoftmax.AnnotationMatches

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution AnnotationMatches

theorem compute_nonempty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source input)
    (hNonempty : 0 < input.size)
    (hBudget : OutputBudget initial heap (computeBytes input.size+remaining) pageLimit module) :
    TerminatesWith env module 11 initial [.i64 source.root]
      (ComputePost heap initial input remaining pageLimit) := by
  let need := mapCapacity input.size
  let heap1 := heap.allocate need
  let node1 := allocatedNode heap.top need heap.nodes
  let heap2 := heap1.allocate need
  let node2 := allocatedNode heap1.top need heap1.nodes
  let weighted := weights input (maximum input)
  have hSize : weighted.size = input.size := by simp [weighted, weights]
  have hOutSize : (normalize weighted (total weighted)).size = input.size := by simp [normalize, hSize]
  have hNeed := (map_capacity initial source.root input hInput.buffer.values).1
  have hBudget1 : OutputBudget initial heap (48+need.toNat+(48+need.toNat+remaining)) pageLimit module := by
    simpa only [need, hNeed, computeBytes, two_mul, Nat.add_assoc] using hBudget
  have hBump1 := hBudget1.bump need (by omega)
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_ (by decide)
  change wp module func11 _ initial (func11Def.toLocals [.i64 source.root]) env
  rw [function_11_length_dispatch_0_function_eq]
  unfold function_11_length_dispatch_0_dispatch_program
  apply FixedArrayLengthDispatch.eqProgram_spec (booleanResults := [.i64]) 21 0 _ _ _ module env initial _ source.root input
    rfl rfl (by decide) (by change 21 < 31; decide) (by decide) hInput.buffer.values
  · intro _
    unfold function_11_length_dispatch_0_invalid_branch_program
    wp_fixed_frame [FixedArrayLengthDispatch.branchFrame, func11Def]
    refine wp_call_exact_append (maximum_exact env initial 0 source.root input hInput.buffer.values hNonempty)
      rfl rfl rfl [] rfl ?_
    wp_fixed_frame
    refine wp_call_tw (weights_owned env initial heap 0 (maximum input) source input
      (48+need.toNat+remaining) pageLimit hHeap hInput hBudget1) ?_
    rintro first values ⟨hValues, hHeap1, hWeights, hPreserved1, hBudget2⟩
    simp only [weights, Array.size_map] at hValues hHeap1 hWeights hPreserved1 hBudget2
    subst values
    change heap1.At first at hHeap1
    change heap1.OwnsWords first node1 weighted at hWeights
    change OutputBudget first heap1 (48+need.toNat+remaining) pageLimit module at hBudget2
    wp_fixed_frame
    refine wp_call_exact_append (total_exact env first node1.root node1.root weighted hWeights.buffer.values)
      rfl rfl rfl [] rfl ?_
    wp_fixed_frame
    refine wp_call_tw (normalize_owned env first heap1 node1.root (total weighted) node1 weighted
      remaining pageLimit hHeap1 hWeights (by simpa only [hSize] using hBudget2)) ?_
    rintro second values ⟨hValues, hHeap2, hOutput, hPreserved2, hBudget3⟩
    simp only [hOutSize] at hValues hHeap2 hOutput hPreserved2 hBudget3
    subst values
    change heap2.At second at hHeap2
    change heap2.OwnsWords second node2 (normalize weighted (total weighted)) at hOutput
    have hTemp : heap2.OwnsWords second node1 weighted := hPreserved2 node1 weighted hWeights
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
    refine wp_call_tw (release_exact env second heap2 node1 weighted hHeap2 hTemp) ?_
    rintro final values ⟨rfl, rfl, hHeap3⟩
    wp_fixed_frame [FixedArrayEqNode.branchPost, function_11_length_dispatch_0_suffix_program, func11Def]
    have hBump2 := hBudget2.bump need (by omega)
    have hOutSep := regionsDisjoint_symm
      (hWeights.allocation_disjoint need (fun h => (hBump2 h).1.le))
    have hOutFinal := hOutput.released node1 hTemp.buffer.rootBound
      (by have := hTemp.buffer.addressBound; omega) hOutSep
    refine ⟨heap2.release node1, node2, rfl, hHeap3, ?_, ?_, hBudget3.released node1⟩
    · simpa only [compute, Array.isEmpty_iff_size_eq_zero, Nat.ne_of_gt hNonempty,
        ↓reduceIte] using hOutFinal
    · intro saved words hSaved
      have hSep := hSaved.allocation_disjoint need (fun h => (hBump1 h).1.le)
      exact (hPreserved2 saved words (hPreserved1 saved words hSaved)).released node1
        hTemp.buffer.rootBound (by have := hTemp.buffer.addressBound; omega) hSep
  · intro hEmpty
    omega

#print axioms compute_nonempty_exact
end Project.SequenceSoftmax.Spec
