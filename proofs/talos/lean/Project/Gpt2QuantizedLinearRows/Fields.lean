import Project.Gpt2QuantizedLinearRows.Program
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedLinearRows
open Wasm Project.ProofKit.PackedFloatFrame

theorem values_exact (env : HostEnv Unit) (initial : Store Unit)
    (valueOwner valuePtr valueSize scaleOwner scalePtr scaleSize : UInt64) :
    TerminatesWith env «module» 5 initial
      [.i64 scaleSize, .i64 scalePtr, .i64 scaleOwner, .i64 valueSize, .i64 valuePtr, .i64 valueOwner]
      (fun final values => final = initial ∧
        values = [.i64 valueSize, .i64 valuePtr, .i64 valueOwner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_
  change wp «module» func5 _ initial
    { params := [.i64 valueOwner, .i64 valuePtr, .i64 valueSize,
        .i64 scaleOwner, .i64 scalePtr, .i64 scaleSize],
      locals := List.replicate 3 (.i64 0), values := [] } env
  simp only [func5]
  wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact ⟨trivial, rfl⟩

theorem scales_exact (env : HostEnv Unit) (initial : Store Unit)
    (valueOwner valuePtr valueSize scaleOwner scalePtr scaleSize : UInt64) :
    TerminatesWith env «module» 7 initial
      [.i64 scaleSize, .i64 scalePtr, .i64 scaleOwner, .i64 valueSize, .i64 valuePtr, .i64 valueOwner]
      (fun final values => final = initial ∧
        values = [.i64 scaleSize, .i64 scalePtr, .i64 scaleOwner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_
  change wp «module» func7 _ initial
    { params := [.i64 valueOwner, .i64 valuePtr, .i64 valueSize,
        .i64 scaleOwner, .i64 scalePtr, .i64 scaleSize],
      locals := List.replicate 3 (.i64 0), values := [] } env
  simp only [func7]
  wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact ⟨trivial, rfl⟩

#print axioms values_exact
#print axioms scales_exact

end Project.Gpt2QuantizedLinearRows
