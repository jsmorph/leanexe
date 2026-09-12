import Project.EulerRiemann.SweepLoopShape

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "sweep_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [sweepFrame, cellValues, Memory.cellWords, Array.getD, List.set,
        Mem.write64_pages, List.cons_append, List.nil_append, List.length_append,
        ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
        Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, *]
    | refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

macro "sweep_write_peel" h:Lean.Parser.Tactic.simpLemma : tactic => `(tactic|
  simp only [wp_localGet_cons, wp_localSet_cons, wp_constI64_cons,
    wp_mulI64_cons, wp_addI64_cons, wp_wrapI64_cons, wp_br_cons,
    Locals.get, Locals.set?, List.length,
    sweepFrame, cellValues, Memory.cellWords, Array.getD, List.set,
    List.cons_append, List.nil_append, List.length_append,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, $h])

theorem sweep_loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (axis : Bool) (ratio owner source target : UInt64)
    (grid : Array Traversal.Cell) (hn : 2 ≤ n ∧ n ≤ 800)
    (hIndexed : Traversal.Indexed n grid)
    (hGrid : Memory.GridAt initial source grid)
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * grid.size + 1) ≤ source.toNat)
    (index : Nat) (hIndex : index ≤ grid.size)
    (hPrefix : Memory.PrefixAt initial target (Traversal.sweep n axis ratio grid) (7 * index))
    (scratch : SweepScratch) (allocation : List Wasm.Value) (hAllocation : allocation.length = 8)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (scratch : SweepScratch),
      Memory.GridAt final source grid →
      Memory.GridAt final target (Traversal.sweep n axis ratio grid) →
      Memory.WritesGrid initial final target grid.size →
      wp Project.EulerRiemann.«module» rest Q final
        (sweepFrame n axis ratio owner source target grid.size grid.size scratch allocation) env) :
    wp Project.EulerRiemann.«module» ([.block 0 0 [.loop 0 0 sweepLoop]] ++ rest) Q initial
      (sweepFrame n axis ratio owner source target grid.size index scratch allocation) env := by
  have hSize64 := hGrid.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  have hOutSize := Traversal.sweep_size n axis ratio grid
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := sweepInvariant initial n axis ratio owner source target grid allocation)
    (μ := sweepMeasure grid.size)
  · exact ⟨hGrid, Memory.WritesGrid.refl .., index, scratch, hIndex, hPrefix, rfl⟩
  · rintro current frame ⟨hCurrentGrid, hWrites, i, sc, hi, hPrefix, hFrame⟩
    subst frame
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    unfold sweepLoop func70
    dsimp only
    by_cases hlt : i < grid.size
    · have hEncoded : ¬ UInt64.ofNat grid.size ≤ UInt64.ofNat i := by
        simpa only [UInt64.le_iff_toNat_le, hiNat, hSizeNat] using Nat.not_le.mpr hlt
      have hSucc64 : i + 1 < UInt64.size := by omega
      have hSuccNat := UInt64.toNat_ofNat_of_lt' hSucc64
      have hAdd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := (UInt64.ofNat_add i 1).symm
      have hOutIndex : i < (Traversal.sweep n axis ratio grid).size := by omega
      have hCellIndex : grid[i].index < n * n := by rw [hIndexed.2 i hlt, ← hIndexed.1]; exact hlt
      have hFit : target.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296 := by
        simpa only [hOutSize] using hPrefix.1
      have hOffset0 : (UInt64.ofNat i * 7 + 1) * 8 =
          UInt64.ofNat (8 * (7 * i + 0 + 1)) := Memory.field_offset i 0
      have hBound0 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 0 hlt (by decide))
      have hRead0 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 0 + 1))).toUInt32 = UInt64.ofNat grid[i].index :=
        hCurrentGrid.fieldRead i 0 hlt (by decide)
      have hWriteBound0 := Nat.not_lt.mpr (hPrefix.fieldBound i 0 hOutIndex (by decide))
      have hOffset1 : (UInt64.ofNat i * 7 + 2) * 8 =
          UInt64.ofNat (8 * (7 * i + 1 + 1)) := Memory.field_offset i 1
      have hBound1 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 1 hlt (by decide))
      have hRead1 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 1 + 1))).toUInt32 = grid[i].state.density :=
        hCurrentGrid.fieldRead i 1 hlt (by decide)
      have hWriteBound1 := Nat.not_lt.mpr (hPrefix.fieldBound i 1 hOutIndex (by decide))
      have hOffset2 : (UInt64.ofNat i * 7 + 3) * 8 =
          UInt64.ofNat (8 * (7 * i + 2 + 1)) := Memory.field_offset i 2
      have hBound2 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 2 hlt (by decide))
      have hRead2 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 2 + 1))).toUInt32 = grid[i].state.mx :=
        hCurrentGrid.fieldRead i 2 hlt (by decide)
      have hWriteBound2 := Nat.not_lt.mpr (hPrefix.fieldBound i 2 hOutIndex (by decide))
      have hOffset3 : (UInt64.ofNat i * 7 + 4) * 8 =
          UInt64.ofNat (8 * (7 * i + 3 + 1)) := Memory.field_offset i 3
      have hBound3 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 3 hlt (by decide))
      have hRead3 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 3 + 1))).toUInt32 = grid[i].state.my :=
        hCurrentGrid.fieldRead i 3 hlt (by decide)
      have hWriteBound3 := Nat.not_lt.mpr (hPrefix.fieldBound i 3 hOutIndex (by decide))
      have hOffset4 : (UInt64.ofNat i * 7 + 5) * 8 =
          UInt64.ofNat (8 * (7 * i + 4 + 1)) := Memory.field_offset i 4
      have hBound4 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 4 hlt (by decide))
      have hRead4 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 4 + 1))).toUInt32 = grid[i].state.energy :=
        hCurrentGrid.fieldRead i 4 hlt (by decide)
      have hWriteBound4 := Nat.not_lt.mpr (hPrefix.fieldBound i 4 hOutIndex (by decide))
      have hOffset5 : (UInt64.ofNat i * 7 + 6) * 8 =
          UInt64.ofNat (8 * (7 * i + 5 + 1)) := Memory.field_offset i 5
      have hBound5 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 5 hlt (by decide))
      have hRead5 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 5 + 1))).toUInt32 = grid[i].pressure :=
        hCurrentGrid.fieldRead i 5 hlt (by decide)
      have hWriteBound5 := Nat.not_lt.mpr (hPrefix.fieldBound i 5 hOutIndex (by decide))
      have hOffset6 : (UInt64.ofNat i * 7 + 7) * 8 =
          UInt64.ofNat (8 * (7 * i + 6 + 1)) := Memory.field_offset i 6
      have hBound6 := Nat.not_lt.mpr (hCurrentGrid.fieldBound i 6 hlt (by decide))
      have hRead6 : current.mem.read64
          (source + UInt64.ofNat (8 * (7 * i + 6 + 1))).toUInt32 = grid[i].status :=
        hCurrentGrid.fieldRead i 6 hlt (by decide)
      have hWriteBound6 := Nat.not_lt.mpr (hPrefix.fieldBound i 6 hOutIndex (by decide))
      sweep_peel
      refine wp_call_tw
        (updateCell_exact env current n axis ratio owner source grid grid[i]
          hn hIndexed.1 hCellIndex hCurrentGrid) ?_
      rintro final values ⟨hFinal, rfl⟩
      subst final
      have hOutCell : (Traversal.sweep n axis ratio grid)[i] =
          Traversal.updateCell n axis ratio grid grid[i] := by
        simp only [Traversal.sweep, Array.getElem_map]
      have hWritten := hPrefix.write_cell hOutIndex
      rw [hOutCell] at hWritten
      have hSource := hCurrentGrid.writeCell_disjoint
        (cell := Traversal.updateCell n axis ratio grid grid[i]) hFit hlt hDisjoint
      have hFrame := hWrites.trans
        (Memory.writeCell_frame (Traversal.updateCell n axis ratio grid grid[i]) hFit hlt)
      let written0 := Memory.writeField current target i 0
        (UInt64.ofNat (Traversal.updateCell n axis ratio grid grid[i]).index)
      let written1 := Memory.writeField written0 target i 1
        ((Traversal.updateCell n axis ratio grid grid[i]).state.density)
      let written2 := Memory.writeField written1 target i 2
        ((Traversal.updateCell n axis ratio grid grid[i]).state.mx)
      let written3 := Memory.writeField written2 target i 3
        ((Traversal.updateCell n axis ratio grid grid[i]).state.my)
      let written4 := Memory.writeField written3 target i 4
        ((Traversal.updateCell n axis ratio grid grid[i]).state.energy)
      let written5 := Memory.writeField written4 target i 5
        ((Traversal.updateCell n axis ratio grid grid[i]).pressure)
      let written6 := Memory.writeField written5 target i 6
        ((Traversal.updateCell n axis ratio grid grid[i]).status)
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        hOffset0, hWriteBound0, reduceIte]
      change wp _ _ _ written0 _ _
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        written0, Memory.writeField_pages, hOffset1, hWriteBound1, reduceIte]
      change wp _ _ _ written1 _ _
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        written0, written1, Memory.writeField_pages, hOffset2, hWriteBound2, reduceIte]
      change wp _ _ _ written2 _ _
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        written0, written1, written2, Memory.writeField_pages, hOffset3, hWriteBound3, reduceIte]
      change wp _ _ _ written3 _ _
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        written0, written1, written2, written3, Memory.writeField_pages, hOffset4, hWriteBound4, reduceIte]
      change wp _ _ _ written4 _ _
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        written0, written1, written2, written3, written4, Memory.writeField_pages, hOffset5, hWriteBound5, reduceIte]
      change wp _ _ _ written5 _ _
      sweep_write_peel hAllocation
      simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        written0, written1, written2, written3, written4, written5, Memory.writeField_pages, hOffset6, hWriteBound6, reduceIte]
      change wp _ _ _ written6 _ _
      sweep_write_peel hAllocation
      simp only [hAdd]
      refine ⟨?_, ?_⟩
      · exact ⟨hSource, hFrame, i + 1,
          ⟨grid[i], Traversal.updateCell n axis ratio grid grid[i],
            UInt64.ofNat n, boolWord axis, ratio, owner, source⟩,
          by omega, hWritten, rfl⟩
      · simp only [sweepMeasure, Locals.get, List.length, hAllocation,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
          List.getElem?_cons_zero, List.getElem?_cons_succ, hiNat, hSuccNat]
        omega
    · have heq : i = grid.size := by omega
      have hEncoded : UInt64.ofNat grid.size ≤ UInt64.ofNat i := by simp [heq]
      have hComplete : Memory.GridAt current target (Traversal.sweep n axis ratio grid) := by
        apply Memory.PrefixAt.complete
        simpa only [heq, hOutSize] using hPrefix
      sweep_peel
      simpa [sweepFrame, heq] using hNext current sc hCurrentGrid hComplete hWrites

#print axioms sweep_loop_spec

end Project.EulerRiemann.Execution
