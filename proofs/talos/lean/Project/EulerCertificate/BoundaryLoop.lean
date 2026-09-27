import Project.EulerCertificate.BoundaryLoopShape

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)
open Project.EulerRiemann.Execution (cellValues boolWord)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "boundary_loop_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [boundaryFrame, vectorValues, boundsValues, cellValues,
        boolWord, List.replicate, List.reverse_cons, List.reverse_nil, List.append_assoc,
        List.cons_append, List.nil_append, Memory.cellWords, Array.getD, List.set,
        ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
        Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem boundary_loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (trials : UInt64) (axis : Bool) (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hGrid : Memory.GridAt initial pointer grid)
    (index : Nat) (hIndex : index ≤ n) (scratch : BoundaryScratch)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ scratch : BoundaryScratch,
      wp Project.EulerCertificate.«module» rest Q initial
        (boundaryFrame n trials axis owner pointer grid.size n
          (boundaryPrefix n trials.toNat axis grid n) scratch) env) :
    wp Project.EulerCertificate.«module» ([.block 0 0 [.loop 0 0 boundaryLoop]] ++ rest) Q initial
      (boundaryFrame n trials axis owner pointer grid.size index
        (boundaryPrefix n trials.toNat axis grid index) scratch) env := by
  have hSize64 := hGrid.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  have hnSize : n ≤ grid.size := by rw [hIndexed.1]; nlinarith [hn.1]
  have hn64 : n < UInt64.size := lt_of_le_of_lt hnSize hSize64
  have hnNat := UInt64.toNat_ofNat_of_lt' hn64
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := boundaryInvariant initial n trials axis owner pointer grid)
    (μ := boundaryMeasure n)
  · exact ⟨rfl, index, scratch, hIndex, rfl⟩
  · rintro current frame ⟨hCurrent, i, sc, hi, hFrame⟩
    subst current
    subst frame
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    unfold boundaryLoop func173
    dsimp only
    by_cases hlt : i < n
    · have hEncoded : ¬ UInt64.ofNat n ≤ UInt64.ofNat i := by
        simpa only [UInt64.le_iff_toNat_le, hiNat, hnNat] using Nat.not_le.mpr hlt
      have hSucc64 : i + 1 < UInt64.size := by omega
      have hSuccNat := UInt64.toNat_ofNat_of_lt' hSucc64
      have hAdd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := (UInt64.ofNat_add i 1).symm
      have hiGrid : i < grid.size := lt_of_lt_of_le hlt hnSize
      have hCellIndex := hIndexed.2 i hiGrid
      have hOffset0 : (UInt64.ofNat i * 7 + 1) * 8 =
          UInt64.ofNat (8 * (7 * i + 0 + 1)) := Memory.field_offset i 0
      have hBound0 := Nat.not_lt.mpr (hGrid.fieldBound i 0 hiGrid (by decide))
      have hRead0 := hGrid.fieldRead i 0 hiGrid (by decide)
      have hOffset1 : (UInt64.ofNat i * 7 + 2) * 8 =
          UInt64.ofNat (8 * (7 * i + 1 + 1)) := Memory.field_offset i 1
      have hBound1 := Nat.not_lt.mpr (hGrid.fieldBound i 1 hiGrid (by decide))
      have hRead1 := hGrid.fieldRead i 1 hiGrid (by decide)
      have hOffset2 : (UInt64.ofNat i * 7 + 3) * 8 =
          UInt64.ofNat (8 * (7 * i + 2 + 1)) := Memory.field_offset i 2
      have hBound2 := Nat.not_lt.mpr (hGrid.fieldBound i 2 hiGrid (by decide))
      have hRead2 := hGrid.fieldRead i 2 hiGrid (by decide)
      have hOffset3 : (UInt64.ofNat i * 7 + 4) * 8 =
          UInt64.ofNat (8 * (7 * i + 3 + 1)) := Memory.field_offset i 3
      have hBound3 := Nat.not_lt.mpr (hGrid.fieldBound i 3 hiGrid (by decide))
      have hRead3 := hGrid.fieldRead i 3 hiGrid (by decide)
      have hOffset4 : (UInt64.ofNat i * 7 + 5) * 8 =
          UInt64.ofNat (8 * (7 * i + 4 + 1)) := Memory.field_offset i 4
      have hBound4 := Nat.not_lt.mpr (hGrid.fieldBound i 4 hiGrid (by decide))
      have hRead4 := hGrid.fieldRead i 4 hiGrid (by decide)
      have hOffset5 : (UInt64.ofNat i * 7 + 6) * 8 =
          UInt64.ofNat (8 * (7 * i + 5 + 1)) := Memory.field_offset i 5
      have hBound5 := Nat.not_lt.mpr (hGrid.fieldBound i 5 hiGrid (by decide))
      have hRead5 := hGrid.fieldRead i 5 hiGrid (by decide)
      have hOffset6 : (UInt64.ofNat i * 7 + 7) * 8 =
          UInt64.ofNat (8 * (7 * i + 6 + 1)) := Memory.field_offset i 6
      have hBound6 := Nat.not_lt.mpr (hGrid.fieldBound i 6 hiGrid (by decide))
      have hRead6 := hGrid.fieldRead i 6 hiGrid (by decide)
      boundary_loop_peel
      have lineCall := boundary_line_exact env initial n trials axis owner pointer grid i
        hn hIndexed.1 hlt hGrid
      generalize hFlux : Boundary.line n trials.toNat axis grid i = flux at lineCall
      refine wp_call_tw lineCall ?_
      rintro final values ⟨hFinal, rfl⟩
      subst final
      boundary_loop_peel
      have addCall := vector_add_exact env initial (boundaryPrefix n trials.toNat axis grid i) flux
      generalize hOut : Vectors.add (boundaryPrefix n trials.toNat axis grid i) flux = next at addCall
      have hPrefix : boundaryPrefix n trials.toNat axis grid (i + 1) = next := by
        rw [boundaryPrefix_succ n trials.toNat axis grid i hiGrid, hCellIndex, hFlux, hOut]
      refine wp_call_tw addCall ?_
      rintro final values ⟨hFinal, rfl⟩
      subst final
      boundary_loop_peel
      refine ⟨?_, ?_⟩
      · refine ⟨rfl, i + 1,
          ⟨grid[i], boundaryPrefix n trials.toNat axis grid i, flux, true⟩, by omega, ?_⟩
        simp [boundaryFrame, vectorValues, boundsValues, cellValues, boolWord, hPrefix, hCellIndex]
      · change n - (UInt64.ofNat (i + 1)).toNat + 1 <
          n - (UInt64.ofNat i).toNat + 1
        rw [hiNat, hSuccNat]
        omega
    · have heq : i = n := by omega
      have hEncoded : UInt64.ofNat n ≤ UInt64.ofNat i := by
        simp [heq]
      boundary_loop_peel
      simpa [boundaryFrame, vectorValues, boundsValues, cellValues,
        boolWord, List.replicate, List.reverse_cons, List.reverse_nil, List.append_assoc,
        List.cons_append, List.nil_append, heq] using hNext sc

#print axioms boundary_loop_spec

end Project.EulerCertificate.Execution
