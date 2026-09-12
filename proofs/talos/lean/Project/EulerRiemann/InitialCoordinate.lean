import Project.EulerRiemann.InitialCoordinateMul
import Project.ProofKit.CheckedDivMod
import Project.ProofKit.NatSub

namespace Project.EulerRiemann.Execution
open Wasm
open Project.ProofKit

def coordinateIndex (remainder : Bool) (n index : Nat) : Nat :=
  if remainder then index % n else index / n

def initialCoordinateProgram (remainder : Bool) : Wasm.Program :=
  [.constI64 5, .localSet 43, .localGet 1, .localSet 45,
    .localGet 0, .localSet 46] ++
    CheckedDivMod.program remainder 45 46 ++ [.localSet 44]

theorem initial_x_coordinate_region : Annotation.region func87 [] 10 21 =
    some (initialCoordinateProgram true) := rfl

theorem initial_y_coordinate_region : Annotation.region func87 [] 43 54 =
    some (initialCoordinateProgram false) := rfl

def initialCoordinateFrame (frame : Locals) (remainder : Bool) (n index : Nat)
    (tail : List Value) : Locals :=
  { frame with
    locals := (((frame.locals.set 41 (.i64 5)).set 43 (.i64 (UInt64.ofNat index))).set 44
      (.i64 (UInt64.ofNat n))).set 42 (.i64 (UInt64.ofNat (coordinateIndex remainder n index)))
    values := tail }

theorem initial_coordinate_spec (remainder : Bool) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (n index : Nat) (tail : List Value)
    (hn : n ≤ 800) (hi : index < 1048576)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 45)
    (hValues : frame.values = tail)
    (hN : frame.get 0 = some (.i64 (UInt64.ofNat n)))
    (hIndex : frame.get 1 = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (initialCoordinateFrame frame remainder n index tail) env) :
    wp Project.EulerRiemann.«module» (initialCoordinateProgram remainder ++ rest)
      Q store frame env := by
  let staged : Locals := { frame with
    locals := ((frame.locals.set 41 (.i64 5)).set 43 (.i64 (UInt64.ofNat index))).set 44
      (.i64 (UInt64.ofNat n))
    values := tail }
  have hn64 : n < 2 ^ 64 := by omega
  have hi64 : index < 2 ^ 64 := by omega
  have hResult : CheckedDivMod.result remainder (UInt64.ofNat index) (UInt64.ofNat n) =
      UInt64.ofNat (coordinateIndex remainder n index) := by
    cases remainder <;> simp [CheckedDivMod.result, coordinateIndex,
      UInt64.ofNat_div hi64 hn64, UInt64.ofNat_mod hi64 hn64]
  have hDiv : wp Project.EulerRiemann.«module»
      (CheckedDivMod.program remainder 45 46 ++ [.localSet 44] ++ rest) Q store staged env := by
    rw [List.append_assoc]
    apply CheckedDivMod.program_spec remainder 45 46 _ env store staged
      (UInt64.ofNat index) (UInt64.ofNat n) tail rfl
    · simp [staged, Locals.get, hParams, hLocals]
    · simp [staged, Locals.get, hParams, hLocals]
    · simpa [wp_simp, hResult, staged, initialCoordinateFrame, hParams, hLocals] using hNext
  have hNRead := Frame.parameter_getElem_of_get frame 0
    (.i64 (UInt64.ofNat n)) (by omega) hN
  have hIndexRead := Frame.parameter_getElem_of_get frame 1
    (.i64 (UInt64.ofNat index)) (by omega) hIndex
  simpa [initialCoordinateProgram, wp_simp, staged, List.append_assoc,
    hParams, hLocals, hValues, hNRead, hIndexRead] using hDiv

#print axioms initial_x_coordinate_region
#print axioms initial_y_coordinate_region
#print axioms initial_coordinate_spec

end Project.EulerRiemann.Execution
