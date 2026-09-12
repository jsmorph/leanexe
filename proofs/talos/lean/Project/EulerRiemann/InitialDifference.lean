import Project.EulerRiemann.InitialCoordinate

namespace Project.EulerRiemann.Execution
open Wasm
open Project.ProofKit

def initialDifferenceProgram (remainder : Bool) : Wasm.Program :=
  quadrupleProgram ++ initialCoordinateProgram remainder ++
    CheckedNatMul.program 43 44 ++ [.localSet 42] ++ NatSub.program 41 42

theorem initial_x_difference_region : Annotation.region func87 [] 1 30 =
    some (initialDifferenceProgram true) := rfl

theorem initial_y_difference_region : Annotation.region func87 [] 34 63 =
    some (initialDifferenceProgram false) := rfl

def initialDifferenceFrame (frame : Locals) (remainder : Bool) (n index : Nat)
    (tail : List Value) : Locals :=
  let coordinates := initialCoordinateFrame (quadrupleFrame frame n tail) remainder n index tail
  { coordinates with
    locals := coordinates.locals.set 40 (.i64 (UInt64.ofNat (5 * coordinateIndex remainder n index)))
    values := .i64 (UInt64.ofNat (4 * n - 5 * coordinateIndex remainder n index)) :: tail }

theorem initial_difference_spec (remainder : Bool) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (n index : Nat) (tail : List Value)
    (hn : n ≤ 800) (hi : index < 1048576)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 45)
    (hValues : frame.values = tail)
    (hN : frame.get 0 = some (.i64 (UInt64.ofNat n)))
    (hIndex : frame.get 1 = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (initialDifferenceFrame frame remainder n index tail) env) :
    wp Project.EulerRiemann.«module» (initialDifferenceProgram remainder ++ rest)
      Q store frame env := by
  let c := coordinateIndex remainder n index
  let coordinates := initialCoordinateFrame (quadrupleFrame frame n tail) remainder n index tail
  let multiplied : Locals := { coordinates with
    locals := coordinates.locals.set 40 (.i64 (UInt64.ofNat (5 * c))) }
  have hc : c ≤ index := by
    cases remainder
    · exact Nat.div_le_self index n
    · exact Nat.mod_le index n
  have hc64 : c < UInt64.size := by change c < 18446744073709551616; omega
  have hFour : 4 * n < UInt64.size := by change 4 * n < 18446744073709551616; omega
  have hFive : 5 * c < UInt64.size := by change 5 * c < 18446744073709551616; omega
  have hSub : wp Project.EulerRiemann.«module» (NatSub.program 41 42 ++ rest)
      Q store multiplied env := by
    apply NatSub.program_spec 41 42 _ env store multiplied
      (UInt64.ofNat (4 * n)) (UInt64.ofNat (5 * c)) tail rfl
    · simp [multiplied, coordinates, initialCoordinateFrame, quadrupleFrame,
        Locals.get, hParams, hLocals]
    · simp [multiplied, coordinates, initialCoordinateFrame, quadrupleFrame,
        Locals.get, hParams, hLocals]
    · rw [UInt64.toNat_ofNat_of_lt' hFour, UInt64.toNat_ofNat_of_lt' hFive]
      simpa only [multiplied, coordinates, c, initialDifferenceFrame] using hNext
  have hMul : wp Project.EulerRiemann.«module»
      (CheckedNatMul.program 43 44 ++ [.localSet 42] ++ NatSub.program 41 42 ++ rest)
      Q store coordinates env := by
    simp only [List.append_assoc]
    apply CheckedNatMul.program_spec 43 44 _ env store coordinates 5 (UInt64.ofNat c) tail rfl
    · simp [coordinates, initialCoordinateFrame, quadrupleFrame, Locals.get, hParams, hLocals]
    · simp [coordinates, initialCoordinateFrame, quadrupleFrame, Locals.get, hParams, hLocals, c]
    · simpa [UInt64.toNat_ofNat_of_lt' hc64] using hFive
    · simpa [wp_simp, coordinates, initialCoordinateFrame, quadrupleFrame,
        hParams, hLocals, multiplied, UInt64.ofNat_mul] using hSub
  simp only [initialDifferenceProgram, List.append_assoc]
  apply quadruple_spec env store frame n tail hn hParams hLocals hValues hN
  apply initial_coordinate_spec remainder env store (quadrupleFrame frame n tail)
    n index tail hn hi hParams
  · simp [quadrupleFrame, hLocals]
  · rfl
  · have hNRead := Frame.parameter_getElem_of_get frame 0
      (.i64 (UInt64.ofNat n)) (by omega) hN
    simp [quadrupleFrame, Locals.get, hParams, hNRead]
  · have hIndexRead := Frame.parameter_getElem_of_get frame 1
      (.i64 (UInt64.ofNat index)) (by omega) hIndex
    simp [quadrupleFrame, Locals.get, hParams, hIndexRead]
  · simpa [List.append_assoc] using hMul

#print axioms initial_x_difference_region
#print axioms initial_y_difference_region
#print axioms initial_difference_spec

end Project.EulerRiemann.Execution
