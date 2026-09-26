import Project.Beck.ExecutionMemberSet
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit

def membershipParams (count wordsOwner wordsPointer position categories rowOwner rowPointer : UInt64) : List Value :=
  [.i64 count, .i64 wordsOwner, .i64 wordsPointer, .i64 position, .i64 categories, .i64 rowOwner, .i64 rowPointer]

def membershipZeroFrame (wordsOwner wordsPointer position categories rowOwner rowPointer : UInt64) : Locals :=
  { params := membershipParams 0 wordsOwner wordsPointer position categories rowOwner rowPointer
    locals := List.replicate 39 (.i64 0) }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem readMemberships_zero_exact (env : HostEnv Unit) (initial : Store Unit)
    (wordsOwner wordsPointer position categories rowOwner rowPointer : UInt64) :
    TerminatesWith env Project.Beck.«module» 2 initial
      (membershipParams 0 wordsOwner wordsPointer position categories rowOwner rowPointer).reverse
      (fun final values => final = initial ∧ values = [.i64 rowPointer, .i64 rowOwner, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_
  change wp Project.Beck.«module» func2 _ initial
    (membershipZeroFrame wordsOwner wordsPointer position categories rowOwner rowPointer) env
  simp only [func2, membershipZeroFrame, membershipParams]
  wp_fixed_frame
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 membershipBody]] ++ func2.drop 7) _ initial
    (membershipZeroFrame wordsOwner wordsPointer position categories rowOwner rowPointer) env
  let inv : AssertionF Unit := fun store frame => store = initial ∧
    frame = membershipZeroFrame wordsOwner wordsPointer position categories rowOwner rowPointer
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ membershipBody inv inv (fun _ _ => 0)
  · rintro store frame ⟨_, rfl⟩; rfl
  · rintro store frame ⟨_, rfl⟩; rfl
  · exact ⟨rfl, rfl⟩
  · rintro store frame ⟨rfl, rfl⟩
    simp only [membershipBody, func2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      membershipZeroFrame, membershipParams]
    wp_fixed_frame
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_fixed_frame [List.take, List.drop, List.append_nil, BlockLoop.stepPost]
    exact ⟨rfl, rfl⟩
  · rintro store frame ⟨rfl, rfl⟩
    simp only [func2, List.drop, membershipZeroFrame, membershipParams]
    wp_fixed_frame
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_fixed_frame [List.take, List.drop, List.append_nil, func2Def]
    simp

#print axioms readMemberships_zero_exact

end Project.Beck.Execution
