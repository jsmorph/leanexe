import Project.EulerGridStep.InitializationShape
import Project.EulerGridStep.FieldIndexing

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def initialDimensionsFrame (frame : Locals) (pointer : UInt64) (length : Nat) : Locals :=
  let cells := length / 3
  let cellsWord := UInt64.ofNat cells
  let countWord := UInt64.ofNat (1 + 6 * cells)
  let ls := frame.locals.set 33 (.i64 pointer)
  let ls := ls.set 31 (.i64 (UInt64.ofNat length))
  let ls := ls.set 32 (.i64 3)
  let ls := ls.set 2 (.i64 cellsWord)
  let ls := ls.set 31 (.i64 1)
  let ls := ls.set 34 (.i64 6)
  let ls := ls.set 35 (.i64 cellsWord)
  let ls := ls.set 32 (.i64 (UInt64.ofNat (6 * cells)))
  let ls := ls.set 33 (.i64 countWord)
  let ls := ls.set 3 (.i64 countWord)
  let ls := ls.set 31 (.i64 countWord)
  { frame with
    locals := ls.set 34 (.i64 0)
    values := [] }

/-- The valid entry computes the cell count and output length without integer overflow. -/
theorem initial_dimensions_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (pointer : UInt64) (input : Array UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hPointer : frame.params[1]? = some (.i64 pointer))
    (hArray : UInt64Array.At initial pointer input)
    (hPositive : 0 < input.size / 3)
    (hSize : 1 + 6 * (input.size / 3) < 4294967296)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (initialDimensionsFrame frame pointer input.size) env) :
    wp m (gridValidBody.take 36 ++ rest) Q initial frame env := by
  have hPointerGet : frame.params[1] = .i64 pointer := by
    have h := hPointer
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hSize64 := hArray.size_lt
  have hDiv : UInt64.ofNat input.size / 3 = UInt64.ofNat (input.size / 3) :=
    (UInt64.ofNat_div hSize64 (by decide)).symm
  have hCells64 : input.size / 3 < UInt64.size := by omega
  have hCellsNZ : UInt64.ofNat (input.size / 3) ≠ 0 := by
    intro h
    have hh := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hCells64, UInt64.toNat_zero] at hh
    omega
  have hMulGuard := six_mul_guard (input.size / 3) (by omega) hPositive
  have hMul : (6 : UInt64) * UInt64.ofNat (input.size / 3) = UInt64.ofNat (6 * (input.size / 3)) :=
    (UInt64.ofNat_mul _ _).symm
  have hAdd : (1 : UInt64) + UInt64.ofNat (6 * (input.size / 3)) = UInt64.ofNat (1 + 6 * (input.size / 3)) :=
    (UInt64.ofNat_add _ _).symm
  have hAddGuard := small_add_guard 1 (6 * (input.size / 3)) hSize
  have hCount64 : 1 + 6 * (input.size / 3) < UInt64.size := by
    change 1 + 6 * (input.size / 3) < 18446744073709551616
    omega
  have hCountNZ : (1 : UInt64) + 6 * UInt64.ofNat (input.size / 3) ≠ 0 := by
    rw [hMul, hAdd]
    intro h
    have hh := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hCount64, UInt64.toNat_zero] at hh
    omega
  have hLengthBound := hArray.generatedLengthBound
  have hPointerAddress := hArray.pointerAddress_eq
  have hLengthRead := hArray.lengthRead
  repeat first
    | wp_run [gridValidBody, func36, List.take, hParams, hLocals, hValues, hPointerGet,
        List.length_set, List.getElem?_set, Wasm.Locals.get, Wasm.Locals.set?]
    | simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
    | rw [ite_eq_right (Nat.not_lt.mpr hLengthBound)]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
  wp_alloc_window_lists [hParams, hLocals, hValues, hCountNZ]
  simp only [hDiv, hCountNZ, ite_false]
  wp_alloc_window_lists [hParams, hLocals, hValues]
  simpa only [initialDimensionsFrame, hValues, hDiv, hMul, hAdd] using hNext

#print axioms initial_dimensions_spec
end Project.EulerGridStep.Execution
