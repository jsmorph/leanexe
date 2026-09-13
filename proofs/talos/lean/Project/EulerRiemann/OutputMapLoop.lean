import Project.EulerRiemann.OutputMapCursor
import Project.ProofKit.ArrayPrefix
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def outputMapResult (pressure : Bool) (grid : Array Traversal.Cell) : Array UInt64 :=
  grid.map (outputCellWord pressure)

def outputMapMeasure (size : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 39 with
  | some (.i64 word) => size - word.toNat
  | _ => size

theorem output_map_loop_shape (pressure : Bool) : outputMapLoop pressure =
    [.localGet 39, .localGet 37, .geUI64, .br_if 1] ++
      outputMapLoads (outputItemStart pressure) ++
      ArrayField.storeProgram 38 39 (if pressure then 20 else 6) 1 0 ++
      [.localGet 39, .constI64 1, .addI64, .localSet 39, .br 0] := by
  cases pressure <;> rfl

theorem output_map_loop_spec (pressure : Bool) (env : HostEnv Unit)
    (initial : Store Unit) (base : Locals) (index : Nat) (source target : UInt64)
    (grid : Array Traversal.Cell) (hi : index ≤ grid.size)
    (hFrame : OutputMapFrameAt pressure base index base)
    (hSource : base.get 36 = some (.i64 source))
    (hCount : base.get 37 = some (.i64 (UInt64.ofNat grid.size)))
    (hTarget : base.get 38 = some (.i64 target))
    (hGrid : Memory.GridAt initial source grid)
    (hPrefix : UInt64Array.PrefixAt initial target (outputMapResult pressure grid) index)
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (grid.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      Memory.GridAt final source grid →
      UInt64Array.At final target (outputMapResult pressure grid) →
      ProofKit.Memory.WritesRange initial final target.toNat (target.toNat + 8 * (grid.size + 1)) →
      OutputMapFrameAt pressure base grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 (outputMapLoop pressure)]] ++ rest)
      Q initial base env := by
  let Inv : AssertionF Unit := fun store frame =>
    Memory.GridAt store source grid ∧
      ProofKit.Memory.WritesRange initial store target.toNat (target.toNat + 8 * (grid.size + 1)) ∧
      ∃ i : Nat, i ≤ grid.size ∧ OutputMapFrameAt pressure base i frame ∧
        UInt64Array.PrefixAt store target (outputMapResult pressure grid) i
  let Done : AssertionF Unit := fun store frame =>
    Memory.GridAt store source grid ∧ UInt64Array.At store target (outputMapResult pressure grid) ∧
      ProofKit.Memory.WritesRange initial store target.toNat (target.toNat + 8 * (grid.size + 1)) ∧
      OutputMapFrameAt pressure base grid.size frame
  have hSize64 := hGrid.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  have hOutSize : (outputMapResult pressure grid).size = grid.size := Array.size_map ..
  have hItems : outputItemStart pressure + 7 ≤ 36 := by cases pressure <;> decide
  refine BlockLoop.program_spec module env initial base (outputMapLoop pressure)
    Inv Done (outputMapMeasure grid.size) ?_ ?_ ?_ ?_ Q rest ?_
  · rintro _ _ ⟨_, _, i, _, hCurrent, _⟩
    exact hCurrent.values
  · rintro _ _ ⟨_, _, _, hCurrent⟩
    exact hCurrent.values
  · exact ⟨hGrid, ProofKit.Memory.WritesRange.refl .., index, hi, hFrame, hPrefix⟩
  · rintro current frame ⟨hCurrentGrid, hWrites, i, hi, hCurrent, hCurrentPrefix⟩
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    have hCountGet := (hCurrent.preserved 37 (by omega) (by decide)).trans hCount
    have hEmpty : ({ frame with values := [] } : Locals) = frame :=
      Frame.ext _ _ rfl rfl hCurrent.values.symm
    rw [output_map_loop_shape]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, hCurrent.counter, hCountGet,
      hCurrent.values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hEnd : i = grid.size
    · have hGuard : UInt64.ofNat i ≥ UInt64.ofNat grid.size := by rw [hEnd]; simp
      rw [ite_eq_left hGuard]
      have hFull : UInt64Array.At current target (outputMapResult pressure grid) := by
        apply UInt64Array.PrefixAt.complete
        simpa only [hOutSize, hEnd] using hCurrentPrefix
      have hDone : Done current frame := ⟨hCurrentGrid, hFull, hWrites, hEnd ▸ hCurrent⟩
      simpa [BlockLoop.stepPost, hEmpty] using hDone
    · have hlt : i < grid.size := by omega
      have hOutIndex : i < (outputMapResult pressure grid).size := by omega
      have hGuard : ¬UInt64.ofNat i ≥ UInt64.ofNat grid.size := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hiNat, hSizeNat]
        omega
      rw [ite_eq_right hGuard]
      simp only [hEmpty]
      refine output_map_load_spec pressure env current frame source grid i
        hCurrent.paramsLength hCurrent.localsLength hCurrent.values
        ((hCurrent.preserved 36 (by omega) (by decide)).trans hSource)
        hCurrent.counter hCurrentGrid hlt _ _ ?_
      let loaded := outputLoadedFrame pressure frame grid[i]
      have hLoadedIndex : loaded.get 39 = some (.i64 (UInt64.ofNat i)) := by
        rw [output_loaded_get_other _ _ _ _ hCurrent.paramsLength (by omega)]
        exact hCurrent.counter
      refine ArrayField.store_spec 38 39 (if pressure then 20 else 6) 1 0 module env current
        loaded target (outputCellWord pressure grid[i]) i [] rfl ?_ hLoadedIndex
        (output_loaded_word _ _ _ hCurrent.paramsLength hCurrent.localsLength) ?_ _ _ ?_
      · rw [output_loaded_get_other _ _ _ _ hCurrent.paramsLength (by omega)]
        exact (hCurrent.preserved 38 (by omega) (by decide)).trans hTarget
      · simpa only [Nat.one_mul, Nat.add_zero] using hCurrentPrefix.elementBound i hOutIndex
      simp only [Nat.one_mul, Nat.add_zero]
      change wp module _ _ (UInt64Array.writeElement current target i (outputCellWord pressure grid[i]))
        loaded env
      refine output_map_increment_spec env _ loaded i (hCurrent.loaded_valid grid[i])
        rfl hLoadedIndex _ ?_
      have hCell : (outputMapResult pressure grid)[i] = outputCellWord pressure grid[i] :=
        Array.getElem_map ..
      have hNextPrefix := hCurrentPrefix.write_next hOutIndex
      rw [hCell] at hNextPrefix
      have hFit : target.toNat + 8 * (grid.size + 1) ≤ 4294967296 := by
        simpa only [hOutSize] using hCurrentPrefix.1
      have hWrite := UInt64Array.writeElement_frame current target grid.size i
        (outputCellWord pressure grid[i]) hFit hlt
      have hNextGrid := hCurrentGrid.frame hWrite.2.1.ge
        (fun _ hLow hHigh => hWrite.2.2 _ (by omega))
      refine ⟨⟨hNextGrid, hWrites.trans hWrite, i + 1, by omega,
        hCurrent.next grid[i], hNextPrefix⟩, ?_⟩
      have hSucc64 : i + 1 < UInt64.size := by omega
      simp only [outputMapMeasure, FixedArrayCopy.counterFrame_get_counter, hCurrent.counter,
        UInt64.toNat_ofNat_of_lt' hSucc64, hiNat]
      omega
  · rintro final resultFrame ⟨hSourceGrid, hResult, hWrites, hResultFrame⟩
    exact hNext final resultFrame hSourceGrid hResult hWrites hResultFrame

#print axioms output_map_loop_shape
#print axioms output_map_loop_spec

end Project.EulerRiemann.Execution
