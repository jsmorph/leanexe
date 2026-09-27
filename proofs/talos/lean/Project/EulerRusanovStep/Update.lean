import Project.EulerRusanovStep.Program
import Project.EulerRusanovStep.Model
import Project.TalosCompat

/-!
# Exact execution of the Euler--Rusanov update helper

The generated helper at function index two implements one conservative
quarter-step component using the source association exactly:

`round(state - round((1/4) * round(fluxRight - fluxLeft)))`.

Its public ABI carries binary64 encodings as `i64` words.  The theorem below
is fuel-independent, quantifies over every input bit pattern and arbitrary
host/store state, and records that this arithmetic-only helper preserves the
complete WebAssembly store.
-/

namespace Project.EulerRusanovStep.Spec

open Wasm

/-- Generated function two returns the pure binary64 update model for every
raw-word input and leaves the caller's complete WebAssembly store unchanged.
The operand stack is top-first, so the three source parameters are supplied
in reverse order. -/
theorem func2_exact
    (env : HostEnv Unit) (initial : Store Unit)
    (state fluxLeft fluxRight : UInt64) :
    TerminatesWith env Project.EulerRusanovStep.«module» 2 initial
      [.i64 fluxRight, .i64 fluxLeft, .i64 state]
      (fun final values =>
        final = initial ∧
          values =
            [.i64
              (Project.EulerRusanovStep.Model.quarterUpdateComponentBits
                state fluxLeft fluxRight)]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := Project.EulerRusanovStep.func2Def)
  · simp [Project.EulerRusanovStep.«module»]
  · change wp Project.EulerRusanovStep.«module»
      Project.EulerRusanovStep.func2 _ initial
      { params := [.i64 state, .i64 fluxLeft, .i64 fluxRight],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.EulerRusanovStep.func2
    wp_run
    simp [Project.EulerRusanovStep.func2Def,
      Project.EulerRusanovStep.Model.quarterUpdateComponentBits,
      Project.EulerRusanovStep.Model.quarterBits,
      Project.EulerRusanovStep.Model.signMask,
      Wasm.f64Add, Wasm.f64Mul]

#print axioms func2_exact

end Project.EulerRusanovStep.Spec
