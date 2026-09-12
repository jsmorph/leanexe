import Project.EulerRiemann.InitialWeight

namespace Project.EulerRiemann.Execution
open Wasm
open Project.ProofKit

def initialWeight (remainder : Bool) (n index : Nat) : Nat :=
  min 5 (4 * n - 5 * coordinateIndex remainder n index)

theorem initial_weights_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n index : Nat) (hn : n ≤ 800) (hi : index < 1048576)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 45)
    (hValues : frame.values = [])
    (hN : frame.get 0 = some (.i64 (UInt64.ofNat n)))
    (hIndex : frame.get 1 = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ resultFrame, resultFrame.params = frame.params →
      resultFrame.locals.length = 45 → resultFrame.values = [] →
      resultFrame.locals[0]? = some (.i64 (UInt64.ofNat (initialWeight true n index))) →
      resultFrame.locals[1]? = some (.i64 (UInt64.ofNat (initialWeight false n index))) →
      wp Project.EulerRiemann.«module» rest Q store resultFrame env) :
    wp Project.EulerRiemann.«module» (func87.take 66 ++ rest) Q store frame env := by
  have hShape : func87.take 66 = initialWeightProgram true ++ [.localSet 2] ++
      initialWeightProgram false ++ [.localSet 3] := rfl
  have hNRead := Frame.parameter_getElem_of_get frame 0
    (.i64 (UInt64.ofNat n)) (by omega) hN
  have hIndexRead := Frame.parameter_getElem_of_get frame 1
    (.i64 (UInt64.ofNat index)) (by omega) hIndex
  rw [hShape]
  simp only [List.append_assoc]
  apply initial_weight_spec true env store frame n index [] hn hi hParams hLocals hValues hN hIndex
  intro xFrame hXFrame hXValues
  simp [List.cons_append, List.nil_append, wp_simp, hXValues,
    hXFrame.params, hParams, hXFrame.length, hLocals]
  apply initial_weight_spec false env store _ n index [] hn hi
  · exact hParams
  · simp [hXFrame.length, hLocals]
  · rfl
  · simp [Locals.get, hParams, hNRead]
  · simp [Locals.get, hParams, hIndexRead]
  · intro yFrame hYFrame hYValues
    have hYParams : yFrame.params = frame.params := hYFrame.params
    have hYLength : yFrame.locals.length = 45 := by
      simpa [hXFrame.length, hLocals] using hYFrame.length
    have hX : yFrame.locals[0]? =
        some (.i64 (UInt64.ofNat (initialWeight true n index))) := by
      have h := congrArg (fun values : List Value => values[0]?) hYFrame.preservedLocals
      simpa [List.getElem?_take, hXFrame.length, hLocals, initialWeight] using h
    simp [wp_simp, hYValues,
      hYParams, hParams, hYLength]
    apply hNext
    · rfl
    · simp [hYLength]
    · rfl
    · simpa using hX
    · simp [hYLength, initialWeight]

#print axioms initial_weights_spec

end Project.EulerRiemann.Execution
