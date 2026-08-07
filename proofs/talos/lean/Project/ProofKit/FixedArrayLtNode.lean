import Project.ProofKit.FixedArrayEqNode

namespace Project.ProofKit.FixedArrayLtNode

open Wasm

def program (offset index keyLocal : Nat)
    (lessBranch notLessBranch : Wasm.Program) : Wasm.Program :=
  [.localGet keyLocal] ++
    (FixedArrayTraversalInput.program offset index ++
      [.ltUI64, .iff 0 0 lessBranch notLessBranch])

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec
    (offset index keyLocal : Nat)
    (lessBranch notLessBranch rest : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr key : UInt64) (input : Array UInt64)
    (hSearch : FixedArrayEqNode.SearchFrame offset keyLocal frame inputPtr key)
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit)
    (hLess : key < input[index] ->
      wp module_ lessBranch (FixedArrayEqNode.branchPost module_ env rest Q) st
        (FixedArrayEqNode.branchFrame offset frame inputPtr index input[index]) env)
    (hNotLess : ¬key < input[index] ->
      wp module_ notLessBranch (FixedArrayEqNode.branchPost module_ env rest Q) st
        (FixedArrayEqNode.branchFrame offset frame inputPtr index input[index]) env) :
    wp module_ (program offset index keyLocal lessBranch notLessBranch ++ rest)
      Q st frame env := by
  rcases hSearch with ⟨hParams, hLocals, hValues, hKey⟩
  unfold program
  simp only [List.cons_append, wp_localGet_cons, hKey, hValues]
  rw [List.append_assoc]
  apply FixedArrayTraversalInput.program_stacked_spec offset module_ env st
    { frame with values := [.i64 key] } inputPtr input index [.i64 key]
    hParams hLocals rfl hInput hIndex
  simp only [wp_simp]
  refine wp_iff_cons rfl ?_
  by_cases hLt : key < input[index]
  · rw [if_pos (by simpa using hLt)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [FixedArrayEqNode.branchFrame,
        FixedArrayTraversalInput.resultFrame,
        FixedArrayTraversalInput.stackedResultFrame] using hLess hLt
  · rw [if_neg (by simpa using hLt)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [FixedArrayEqNode.branchFrame,
        FixedArrayTraversalInput.resultFrame,
        FixedArrayTraversalInput.stackedResultFrame] using hNotLess hLt

macro "wp_fixed_array_lt_node " offset:term ", " index:term ", " keyLocal:term : tactic =>
  `(tactic|
    (change wp _ (program $offset $index $keyLocal _ _ ++ _) _ _ _ _
     apply program_spec))

end Project.ProofKit.FixedArrayLtNode
