import Project.EulerGridStep.WriterShape

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def writerParameters (unused source : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : List Value :=
  [.i64 unused, .i64 source, .i64 (UInt64.ofNat index), .i64 cell.status,
    .i64 cell.density, .i64 cell.momentum, .i64 cell.energy,
    .i64 cell.pressure, .i64 cell.alpha, .i64 cell.courant]

def writerEntryFrame (unused source : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Locals :=
  { params := writerParameters unused source index cell, locals := List.replicate 72 (.i64 0), values := [] }

def writerFirstFrame (base : Locals) (unused source : UInt64) (index : Nat) (value : UInt64) : Locals :=
  { base with locals := ((((base.locals.set 0 (.i64 unused)).set 1 (.i64 source)).set
      2 (.i64 (UInt64.ofNat index))).set 3 (.i64 0)).set 4 (.i64 value), values := [] }

def writerNextFrame (base : Locals) (field : Nat) (pointer : UInt64) (index : Nat) (value : UInt64) : Locals :=
  let slot := 9 * field + 6 - 10
  { base with locals := ((((((((base.locals.set (slot + 1) (.i64 pointer)).set slot (.i64 pointer)).set
      (slot + 2) (.i64 pointer)).set (slot + 3) (.i64 pointer)).set (slot + 4) (.i64 pointer)).set
      (slot + 5) (.i64 pointer)).set (slot + 6) (.i64 (UInt64.ofNat index))).set
      (slot + 7) (.i64 (UInt64.ofNat field))).set (slot + 8) (.i64 value), values := [] }

/-- Exact first-call setup, generic in the terminating field-call postcondition. -/
theorem writer_first_call_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (unused source target : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (P : Store Unit → Prop)
    (hParams : base.params = writerParameters unused source index cell)
    (hLocals : base.locals.length = 72) (hValues : base.values = [])
    (hCall : TerminatesWith env m 27 initial
      [.i64 cell.density, .i64 0, .i64 (UInt64.ofNat index), .i64 source, .i64 unused]
      (fun final values => values = [.i64 target, .i64 target] ∧ P final))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, P final → wp m rest Q final
      { writerFirstFrame base unused source index cell.density with values := [.i64 target, .i64 target] } env) :
    wp m (writerFirstCall ++ rest) Q initial base env := by
  wp_alloc_window_lists [writerFirstCall, hParams, writerParameters, hLocals, hValues]
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hP⟩
  simpa [writerFirstFrame, hParams, writerParameters] using hNext final hP

/-- Exact local handoff from one cloned array to the next field call. -/
theorem writer_next_call_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (unused source pointer target : UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (P : Store Unit → Prop)
    (hFieldLo : 1 ≤ field) (hFieldHi : field ≤ 5)
    (hParams : base.params = writerParameters unused source index cell)
    (hLocals : base.locals.length = 72) (hValues : base.values = [.i64 pointer, .i64 pointer])
    (hCall : TerminatesWith env m 27 initial
      [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
        .i64 (UInt64.ofNat index), .i64 pointer, .i64 pointer]
      (fun final values => values = [.i64 target, .i64 target] ∧ P final))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, P final → wp m rest Q final
      { writerNextFrame base field pointer index ((Model.payload cell).getD field 0)
        with values := [.i64 target, .i64 target] } env) :
    wp m (writerNextCall field ++ rest) Q initial base env := by
  interval_cases field <;>
    wp_alloc_window_lists [writerNextCall, hParams, writerParameters, hLocals, hValues]
  all_goals
    refine wp_call_tw hCall ?_
    rintro final values ⟨rfl, hP⟩
    simpa [writerNextFrame, Model.payload, hParams, writerParameters] using hNext final hP

#print axioms writer_first_call_spec
#print axioms writer_next_call_spec
end Project.EulerGridStep.Execution
