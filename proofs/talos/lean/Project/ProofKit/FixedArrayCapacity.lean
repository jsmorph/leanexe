import Project.ProofKit.Frame
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.FixedArrayCapacity

open Wasm

def unnormalizedCapacity (length stride : UInt64) : UInt64 :=
  ((8 + length * stride * 8 + 7) / 8) * 8

def normalizedCapacity (length stride : UInt64) : UInt64 :=
  if unnormalizedCapacity length stride < 8 then 8
  else unnormalizedCapacity length stride

def constantProgram (length stride : UInt64)
    (capacityLocal : Nat) : Wasm.Program :=
  [
  .constI64 8,
  .constI64 length,
  .constI64 stride,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet capacityLocal,
  .localGet capacityLocal,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [.constI64 8, .localSet capacityLocal] []
  ]

def capacityFrame (frame : Locals) (capacityLocal : Nat)
    (capacity : UInt64) : Locals :=
  { frame with
    locals := frame.locals.set
      (capacityLocal - frame.params.length) (.i64 capacity)
    values := [] }

theorem capacityFrame_params (frame : Locals) (capacityLocal : Nat)
    (capacity : UInt64) :
    (capacityFrame frame capacityLocal capacity).params = frame.params := rfl

theorem capacityFrame_locals_length (frame : Locals) (capacityLocal : Nat)
    (capacity : UInt64) :
    (capacityFrame frame capacityLocal capacity).locals.length =
      frame.locals.length := by
  simp [capacityFrame]

theorem capacityFrame_values (frame : Locals) (capacityLocal : Nat)
    (capacity : UInt64) :
    (capacityFrame frame capacityLocal capacity).values = [] := rfl

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem constantProgram_spec
    (length stride : UInt64) (capacityLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.params.length ≤ capacityLocal)
    (hCapacityValid : frame.validIndex capacityLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (capacityFrame frame capacityLocal
        (normalizedCapacity length stride)) env) :
    wp module_ (constantProgram length stride capacityLocal ++ rest)
      Q st frame env := by
  have hNotParam : ¬capacityLocal < frame.params.length :=
    Nat.not_lt.mpr hCapacityLocal
  have hCapacityBound :
      capacityLocal < frame.params.length + frame.locals.length :=
    hCapacityValid
  have hLocal :
      capacityLocal - frame.params.length < frame.locals.length := by
    omega
  unfold constantProgram
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length_set, hValues,
    hNotParam, hCapacityBound, hLocal]
  refine wp_iff_cons rfl ?_
  by_cases hSmall : unnormalizedCapacity length stride < 8
  · have hSmall' : (8 + length * stride * 8 + 7) / 8 * 8 < 8 := by
      simpa [unnormalizedCapacity] using hSmall
    simp only [hSmall', if_pos]
    simpa [wp_simp, capacityFrame, normalizedCapacity, hSmall, hValues,
      hNotParam, hCapacityBound] using hNext
  · have hSmall' : ¬(8 + length * stride * 8 + 7) / 8 * 8 < 8 := by
      simpa [unnormalizedCapacity] using hSmall
    simp only [hSmall', if_false]
    simpa [capacityFrame, normalizedCapacity, unnormalizedCapacity, hSmall,
      hSmall', hValues, hNotParam, hCapacityBound] using hNext

end Project.ProofKit.FixedArrayCapacity
