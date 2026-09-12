import Project.EulerRiemann.InitialDifference

namespace Project.EulerRiemann.Execution
open Wasm
open Project.ProofKit

structure InitialScratchFrame (before after : Locals) : Prop where
  params : after.params = before.params
  length : after.locals.length = before.locals.length
  preservedLocals : after.locals.take 39 = before.locals.take 39

theorem initial_difference_scratch (frame : Locals) (remainder : Bool) (n index : Nat)
    (tail values : List Value) :
    InitialScratchFrame frame
      { initialDifferenceFrame frame remainder n index tail with values := values } := by
  constructor
  · rfl
  · simp [initialDifferenceFrame, initialCoordinateFrame, quadrupleFrame]
  · simp [initialDifferenceFrame, initialCoordinateFrame, quadrupleFrame, List.take_set_of_le]

def initialWeightProgram (remainder : Bool) : Wasm.Program :=
  [.constI64 5] ++ initialDifferenceProgram remainder ++
    [.leUI64, .iff 0 1 [.constI64 5] (initialDifferenceProgram remainder) [] [.i64]]

theorem initial_x_weight_region : Annotation.region func87 [] 0 32 =
    some (initialWeightProgram true) := rfl

theorem initial_y_weight_region : Annotation.region func87 [] 33 65 =
    some (initialWeightProgram false) := rfl

theorem initial_weight_spec (remainder : Bool) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (n index : Nat) (tail : List Value)
    (hn : n ≤ 800) (hi : index < 1048576)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 45)
    (hValues : frame.values = tail)
    (hN : frame.get 0 = some (.i64 (UInt64.ofNat n)))
    (hIndex : frame.get 1 = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ resultFrame, InitialScratchFrame frame resultFrame →
      resultFrame.values = .i64 (UInt64.ofNat (min 5
        (4 * n - 5 * coordinateIndex remainder n index))) :: tail →
      wp Project.EulerRiemann.«module» rest Q store resultFrame env) :
    wp Project.EulerRiemann.«module» (initialWeightProgram remainder ++ rest)
      Q store frame env := by
  let d := 4 * n - 5 * coordinateIndex remainder n index
  have hD : d < UInt64.size := by change d < 18446744073709551616; dsimp [d]; omega
  have hCompare : ((5 : UInt64) ≤ UInt64.ofNat d) ↔ 5 ≤ d := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hD]
    rfl
  have hNRead := Frame.parameter_getElem_of_get frame 0
    (.i64 (UInt64.ofNat n)) (by omega) hN
  have hIndexRead := Frame.parameter_getElem_of_get frame 1
    (.i64 (UInt64.ofNat index)) (by omega) hIndex
  simp only [initialWeightProgram, List.append_assoc, List.cons_append, List.nil_append,
    wp_simp, hValues]
  apply initial_difference_spec remainder env store { frame with values := .i64 5 :: tail }
    n index (.i64 5 :: tail) hn hi hParams hLocals rfl hN hIndex
  simp only [wp_simp, initialDifferenceFrame]
  refine wp_iff_cons rfl ?_
  by_cases hMin : 5 ≤ d
  · have hWord := hCompare.mpr hMin
    simp [show (5 : UInt64) ≤ UInt64.ofNat (4 * n - 5 * coordinateIndex remainder n index)
      from hWord, wp_simp]
    apply hNext
    · simpa [initialDifferenceFrame, initialCoordinateFrame, quadrupleFrame] using
        initial_difference_scratch frame remainder n index tail (.i64 5 :: tail)
    · change .i64 5 :: tail = .i64 (UInt64.ofNat (min 5 d)) :: tail
      rw [Nat.min_eq_left hMin]
      rfl
  · have hWord := hCompare.not.mpr hMin
    simp [show ¬ (5 : UInt64) ≤ UInt64.ofNat (4 * n - 5 * coordinateIndex remainder n index)
      from hWord, wp_simp]
    apply initial_difference_spec remainder env store _ n index tail hn hi
    · exact hParams
    · simp [initialCoordinateFrame, quadrupleFrame, hLocals]
    · rfl
    · simp [initialCoordinateFrame, quadrupleFrame, Locals.get, hParams, hNRead]
    · simp [initialCoordinateFrame, quadrupleFrame, Locals.get, hParams, hIndexRead]
    · simp only [wp_simp, initialDifferenceFrame, List.take]
      apply hNext
      · constructor
        · rfl
        · simp [initialCoordinateFrame, quadrupleFrame]
        · simp [initialCoordinateFrame, quadrupleFrame, List.take_set_of_le]
      · simp [Nat.min_eq_right (by omega : d ≤ 5), d]

#print axioms initial_difference_scratch
#print axioms initial_x_weight_region
#print axioms initial_y_weight_region
#print axioms initial_weight_spec

end Project.EulerRiemann.Execution
