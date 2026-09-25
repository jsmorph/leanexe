import Project.LebU32.Frames

namespace Project.LebU32.Spec
open Wasm Project.ProofKit PackedFloatFrame

theorem return_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel pointer length : UInt64) (hFrame : FinishedFrame frame fuel pointer length)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store { frame with values := [.i64 length, .i64 pointer, .i64 pointer] } env) :
    wp «module» (func0.drop 5 ++ rest) Q store frame env := by
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hOwner := hFrame.owner
  have hPointer := hFrame.pointer
  have hLength := hFrame.length
  have hDone := hFrame.done
  have hShape : func0.drop 5 =
      [.localGet 9, .constI64 0, .eqI64,
       .iff 0 0 [.localGet 2, .localSet 6, .localGet 3, .localSet 7, .localGet 4, .localSet 8] [],
       .localGet 6, .localGet 7, .localGet 8] := rfl
  rw [hShape]
  wp_packed_frame [hParams, hLocals, hValues, hDone]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLocals, hOwner, hPointer, hLength]
  exact hNext

#print axioms return_spec
end Project.LebU32.Spec
