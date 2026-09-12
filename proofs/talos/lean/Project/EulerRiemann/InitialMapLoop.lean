import Project.EulerRiemann.InitialMapCursor
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialMapOutput (n offset : Nat) (grid : Array Traversal.Cell) : Array Traversal.Cell :=
  grid.map (fun cell => Traversal.initialCell n (cell.index + offset))

def initialMapMeasure (size : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 51 with
  | some (.i64 word) => size - word.toNat
  | _ => size

theorem initial_map_region : initialGrowBody[53]? =
    some (.block 0 0 [.loop 0 0 initialMapLoop]) := by
  rfl

theorem initial_map_loop_parts : initialMapLoop =
    [.localGet 51, .localGet 49, .geUI64, .br_if 1] ++
      (initialMapLoop.drop 4).take 206 ++ initialMapLoop.drop 210 := by
  have hGuard : initialMapLoop.take 4 =
      [.localGet 51, .localGet 49, .geUI64, .br_if 1] := rfl
  have hTail : initialMapLoop.drop 4 =
      (initialMapLoop.drop 4).take 206 ++ initialMapLoop.drop 210 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_append_drop 206 (initialMapLoop.drop 4)).symm
  calc
    initialMapLoop = initialMapLoop.take 4 ++ initialMapLoop.drop 4 :=
      (List.take_append_drop 4 initialMapLoop).symm
    _ = initialMapLoop.take 4 ++
        ((initialMapLoop.drop 4).take 206 ++ initialMapLoop.drop 210) :=
      congrArg (initialMapLoop.take 4 ++ ·) hTail
    _ = _ := by rw [hGuard, List.append_assoc]

theorem initial_map_loop_spec (env : HostEnv Unit) (initial : Store Unit) (base : Locals)
    (n offset index : Nat) (source target : UInt64) (grid : Array Traversal.Cell)
    (hn : n ≤ 800) (hi : index ≤ grid.size)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + offset < 1048576)
    (hFrame : InitialMapFrameAt base index base)
    (hN : base.get 1 = some (.i64 (UInt64.ofNat n)))
    (hOffset : base.get 10 = some (.i64 (UInt64.ofNat offset)))
    (hSource : base.get 48 = some (.i64 source))
    (hCount : base.get 49 = some (.i64 (UInt64.ofNat grid.size)))
    (hTarget : base.get 50 = some (.i64 target))
    (hGrid : Memory.GridAt initial source grid)
    (hPrefix : Memory.PrefixAt initial target (initialMapOutput n offset grid) (7 * index))
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * grid.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      Memory.GridAt final source grid →
      Memory.GridAt final target (initialMapOutput n offset grid) →
      Memory.WritesGrid initial final target grid.size →
      InitialMapFrameAt base grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 initialMapLoop]] ++ rest) Q initial base env := by
  let Inv : AssertionF Unit := fun store frame =>
    Memory.GridAt store source grid ∧ Memory.WritesGrid initial store target grid.size ∧
      ∃ i : Nat, i ≤ grid.size ∧ InitialMapFrameAt base i frame ∧
        Memory.PrefixAt store target (initialMapOutput n offset grid) (7 * i)
  let Done : AssertionF Unit := fun store frame =>
    Memory.GridAt store source grid ∧
      Memory.GridAt store target (initialMapOutput n offset grid) ∧
      Memory.WritesGrid initial store target grid.size ∧ InitialMapFrameAt base grid.size frame
  have hSize64 := hGrid.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  have hOutSize : (initialMapOutput n offset grid).size = grid.size := by
    simp only [initialMapOutput, Array.size_map]
  refine BlockLoop.program_spec module env initial base initialMapLoop
    Inv Done (initialMapMeasure grid.size) ?_ ?_ ?_ ?_ Q rest ?_
  · rintro _ _ ⟨_, _, i, _, hCurrent, _⟩
    exact hCurrent.values
  · rintro _ _ ⟨_, _, _, hCurrent⟩
    exact hCurrent.values
  · exact ⟨hGrid, Memory.WritesGrid.refl .., index, hi, hFrame, hPrefix⟩
  · rintro current frame ⟨hCurrentGrid, hWrites, i, hi, hCurrent, hCurrentPrefix⟩
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    have hCountGet := (hCurrent.get 49 (by decide) (by decide) (by decide)).trans hCount
    have hEmpty : ({ frame with values := [] } : Locals) = frame :=
      Frame.ext _ _ rfl rfl hCurrent.values.symm
    rw [initial_map_loop_parts]
    simp only [List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, hCurrent.counter, hCountGet,
      hCurrent.values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hEnd : i = grid.size
    · have hGuard : UInt64.ofNat i ≥ UInt64.ofNat grid.size := by
        rw [hEnd]
        simp
      rw [ite_eq_left hGuard]
      have hFull : Memory.GridAt current target (initialMapOutput n offset grid) := by
        apply Memory.PrefixAt.complete
        simpa only [hOutSize, hEnd] using hCurrentPrefix
      have hDone : Done current frame := ⟨hCurrentGrid, hFull, hWrites, hEnd ▸ hCurrent⟩
      simpa [BlockLoop.stepPost, hEmpty] using hDone
    · have hlt : i < grid.size := by omega
      have hGuard : ¬UInt64.ofNat i ≥ UInt64.ofNat grid.size := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hiNat, hSizeNat]
        omega
      rw [ite_eq_right hGuard]
      simp only [hEmpty]
      have hFit : target.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296 := by
        simpa only [hOutSize] using hCurrentPrefix.1
      have hFitMemory : target.toNat + 8 * (7 * grid.size + 1) ≤ current.mem.pages * 65536 := by
        simpa only [hOutSize] using hCurrentPrefix.2.1
      refine initial_map_update_spec env current frame n offset i source target grid hn hlt
        (hSum i hlt) hCurrent.paramsLength hCurrent.localsLength hCurrent.values
        ((hCurrent.get 1 (by decide) (by decide) (by decide)).trans hN)
        ((hCurrent.get 10 (by decide) (by decide) (by decide)).trans hOffset)
        ((hCurrent.get 48 (by decide) (by decide) (by decide)).trans hSource)
        ((hCurrent.get 50 (by decide) (by decide) (by decide)).trans hTarget)
        hCurrent.counter hCurrentGrid hFit hFitMemory _ _ ?_
      let cell := Traversal.initialCell n (grid[i].index + offset)
      let written := Memory.writeCell current target i cell
      let mapped := initialMappedFrame frame n offset grid[i]
      have hMappedCounter : mapped.get 51 = some (.i64 (UInt64.ofNat i)) := by
        rw [initial_mapped_get_other _ _ _ _ _ hCurrent.paramsLength (by decide) (by decide)]
        exact hCurrent.counter
      refine initial_map_increment_spec env written mapped i (hCurrent.mapped_valid n offset grid[i])
        rfl hMappedCounter _ ?_
      have hNextFrame := hCurrent.next n offset grid[i]
      have hOutIndex : i < (initialMapOutput n offset grid).size := by omega
      have hCell : (initialMapOutput n offset grid)[i] = cell := by
        simp only [initialMapOutput, Array.getElem_map, cell]
      have hNextPrefix := hCurrentPrefix.write_cell hOutIndex
      rw [hCell] at hNextPrefix
      have hNextGrid := hCurrentGrid.writeCell_disjoint (cell := cell) hFit hlt hDisjoint
      have hNextWrites := hWrites.trans (Memory.writeCell_frame cell hFit hlt)
      refine ⟨⟨hNextGrid, hNextWrites, i + 1, by omega, hNextFrame, hNextPrefix⟩, ?_⟩
      have hSucc64 : i + 1 < UInt64.size := by omega
      simp only [initialMapMeasure, FixedArrayCopy.counterFrame_get_counter, hCurrent.counter,
        UInt64.toNat_ofNat_of_lt' hSucc64, hiNat]
      omega
  · rintro final resultFrame ⟨hSourceGrid, hResult, hWrites, hResultFrame⟩
    exact hNext final resultFrame hSourceGrid hResult hWrites hResultFrame

#print axioms initial_map_loop_parts
#print axioms initial_map_region
#print axioms initial_map_loop_spec

end Project.EulerRiemann.Execution
