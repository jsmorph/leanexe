import Project.EulerGridStep.RejectedShape
import Project.EulerGridStep.WriterCalls

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow

def rejectedPrefixFrame (base : Locals) (source : UInt64) (count : Nat) : Locals :=
  { base with
    locals := (((((base.locals.set 52 (.i64 source)).set 53 (.i64 0)).set
      57 (.i64 source)).set 58 (.i64 0)).set 63 (.i64 1)).set 59 (.i64 (UInt64.ofNat count)),
    values := [.i32 1] }

/-- The rejection prefix reads the original header and establishes the index-zero bound. -/
theorem rejected_prefix_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (unused source : UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hParams : base.params = writerParameters unused source index cell)
    (hLocals : base.locals.length = 72) (hValues : base.values = [])
    (hArray : UInt64Array.At initial source output) (hNonempty : 0 < output.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (rejectedPrefixFrame base source output.size) env) :
    wp m (rejectedPrefix ++ rest) Q initial base env := by
  have hLengthBound := hArray.generatedLengthBound
  have hPointerAddress := hArray.pointerAddress_eq
  have hLengthRead := hArray.lengthRead
  have hPositive : (0 : UInt64) < UInt64.ofNat output.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero, UInt64.toNat_ofNat_of_lt' hArray.size_lt]
    exact hNonempty
  wp_alloc_window_lists [rejectedPrefix, hParams, writerParameters, hLocals, hValues,
    hLengthBound, hPointerAddress, hLengthRead, hPositive]
  rw [ite_eq_right (Nat.not_lt.mpr hLengthBound)]
  simpa [rejectedPrefixFrame, hParams, writerParameters] using hNext

#print axioms rejected_prefix_spec
end Project.EulerGridStep.Execution
