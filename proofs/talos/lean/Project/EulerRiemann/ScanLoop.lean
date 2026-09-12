import Project.EulerRiemann.ScanLoopShape

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "scan_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [scanFrame, Memory.cellWords, Array.getD, List.set,
        ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
        Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem scan_loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid)
    (index : Nat) (hIndex : index ≤ grid.size) (scratch : ScanScratch)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ scratch : ScanScratch,
      wp Project.EulerRiemann.«module» rest Q initial
        (scanFrame owner pointer grid.size grid.size (scanPrefix grid grid.size) scratch) env) :
    wp Project.EulerRiemann.«module» ([.block 0 0 [.loop 0 0 scanLoop]] ++ rest) Q initial
      (scanFrame owner pointer grid.size index (scanPrefix grid index) scratch) env := by
  have hSize64 := hGrid.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := scanInvariant initial owner pointer grid)
    (μ := scanMeasure grid.size)
  · exact ⟨rfl, index, scratch, hIndex, rfl⟩
  · rintro current frame ⟨hCurrent, i, sc, hi, hFrame⟩
    subst current
    subst frame
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    unfold scanLoop func25
    dsimp only
    by_cases hlt : i < grid.size
    · have hEncoded : ¬ UInt64.ofNat grid.size ≤ UInt64.ofNat i := by
        simpa only [UInt64.le_iff_toNat_le, hiNat, hSizeNat] using Nat.not_le.mpr hlt
      have hSucc64 : i + 1 < UInt64.size := by omega
      have hSuccNat := UInt64.toNat_ofNat_of_lt' hSucc64
      have hAdd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := (UInt64.ofNat_add i 1).symm
      have hOffset0 : (UInt64.ofNat i * 7 + 1) * 8 =
          UInt64.ofNat (8 * (7 * i + 0 + 1)) := Memory.field_offset i 0
      have hBound0 := Nat.not_lt.mpr (hGrid.fieldBound i 0 hlt (by decide))
      have hRead0 := hGrid.fieldRead i 0 hlt (by decide)
      have hOffset1 : (UInt64.ofNat i * 7 + 2) * 8 =
          UInt64.ofNat (8 * (7 * i + 1 + 1)) := Memory.field_offset i 1
      have hBound1 := Nat.not_lt.mpr (hGrid.fieldBound i 1 hlt (by decide))
      have hRead1 := hGrid.fieldRead i 1 hlt (by decide)
      have hOffset2 : (UInt64.ofNat i * 7 + 3) * 8 =
          UInt64.ofNat (8 * (7 * i + 2 + 1)) := Memory.field_offset i 2
      have hBound2 := Nat.not_lt.mpr (hGrid.fieldBound i 2 hlt (by decide))
      have hRead2 := hGrid.fieldRead i 2 hlt (by decide)
      have hOffset3 : (UInt64.ofNat i * 7 + 4) * 8 =
          UInt64.ofNat (8 * (7 * i + 3 + 1)) := Memory.field_offset i 3
      have hBound3 := Nat.not_lt.mpr (hGrid.fieldBound i 3 hlt (by decide))
      have hRead3 := hGrid.fieldRead i 3 hlt (by decide)
      have hOffset4 : (UInt64.ofNat i * 7 + 5) * 8 =
          UInt64.ofNat (8 * (7 * i + 4 + 1)) := Memory.field_offset i 4
      have hBound4 := Nat.not_lt.mpr (hGrid.fieldBound i 4 hlt (by decide))
      have hRead4 := hGrid.fieldRead i 4 hlt (by decide)
      have hOffset5 : (UInt64.ofNat i * 7 + 6) * 8 =
          UInt64.ofNat (8 * (7 * i + 5 + 1)) := Memory.field_offset i 5
      have hBound5 := Nat.not_lt.mpr (hGrid.fieldBound i 5 hlt (by decide))
      have hRead5 := hGrid.fieldRead i 5 hlt (by decide)
      have hOffset6 : (UInt64.ofNat i * 7 + 7) * 8 =
          UInt64.ofNat (8 * (7 * i + 6 + 1)) := Memory.field_offset i 6
      have hBound6 := Nat.not_lt.mpr (hGrid.fieldBound i 6 hlt (by decide))
      have hRead6 := hGrid.fieldRead i 6 hlt (by decide)
      scan_peel
      refine wp_call_tw (scanCell_exact env initial (scanPrefix grid i) grid[i]) ?_
      rintro final values ⟨hFinal, rfl⟩
      subst final
      scan_peel
      refine ⟨?_, ?_⟩
      · refine ⟨rfl, i + 1,
          ⟨grid[i], scanPrefix grid i, 0, 1⟩, by omega, ?_⟩
        rw [scanPrefix_succ grid i hlt]
        rfl
      · change grid.size - (UInt64.ofNat (i + 1)).toNat + 1 <
          grid.size - (UInt64.ofNat i).toNat + 1
        rw [hiNat, hSuccNat]
        omega
    · have heq : i = grid.size := by omega
      have hEncoded : UInt64.ofNat grid.size ≤ UInt64.ofNat i := by
        simp [heq]
      scan_peel
      simpa [scanFrame, heq] using hNext sc

#print axioms scan_loop_spec

end Project.EulerRiemann.Execution
