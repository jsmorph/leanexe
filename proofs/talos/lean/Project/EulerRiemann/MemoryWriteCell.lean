import Project.EulerRiemann.MemoryWrite

namespace Project.EulerRiemann.Memory
open Wasm

def writeCell (store : Store Unit) (ptr : UInt64) (index : Nat)
    (cell : Traversal.Cell) : Store Unit :=
  let s0 := writeField store ptr index 0 (UInt64.ofNat cell.index)
  let s1 := writeField s0 ptr index 1 cell.state.density
  let s2 := writeField s1 ptr index 2 cell.state.mx
  let s3 := writeField s2 ptr index 3 cell.state.my
  let s4 := writeField s3 ptr index 4 cell.state.energy
  let s5 := writeField s4 ptr index 5 cell.pressure
  writeField s5 ptr index 6 cell.status

@[simp] theorem writeCell_pages (store : Store Unit) (ptr : UInt64)
    (index : Nat) (cell : Traversal.Cell) :
    (writeCell store ptr index cell).mem.pages = store.mem.pages := by
  simp only [writeCell, writeField_pages]

@[simp] theorem writeCell_globals (store : Store Unit) (ptr : UInt64)
    (index : Nat) (cell : Traversal.Cell) :
    (writeCell store ptr index cell).globals = store.globals := rfl

theorem PrefixAt.write_cell {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} {i : Nat}
    (h : PrefixAt store ptr grid (7 * i)) (hi : i < grid.size) :
    PrefixAt (writeCell store ptr i grid[i]) ptr grid (7 * (i + 1)) := by
  have h0 := PrefixAt.write_next (i := i) (field := 0) h hi (by decide)
  have h1 := PrefixAt.write_next (i := i) (field := 1) h0 hi (by decide)
  have h2 := PrefixAt.write_next (i := i) (field := 2) h1 hi (by decide)
  have h3 := PrefixAt.write_next (i := i) (field := 3) h2 hi (by decide)
  have h4 := PrefixAt.write_next (i := i) (field := 4) h3 hi (by decide)
  have h5 := PrefixAt.write_next (i := i) (field := 5) h4 hi (by decide)
  have h6 := PrefixAt.write_next (i := i) (field := 6) h5 hi (by decide)
  change PrefixAt (writeCell store ptr i grid[i]) ptr grid (7 * i + 7) at h6
  simpa only [Nat.mul_add, Nat.mul_one] using h6

theorem GridAt.writeCell_disjoint {store : Store Unit} {source target : UInt64}
    {grid : Array Traversal.Cell} {size i : Nat} {cell : Traversal.Cell}
    (hGrid : GridAt store source grid)
    (hFit32 : target.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hi : i < size)
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.toNat) :
    GridAt (writeCell store target i cell) source grid := by
  have h0 := GridAt.writeField_disjoint (field := 0) (value := UInt64.ofNat cell.index)
    hGrid hFit32 hi (by decide) hDisjoint
  have h1 := GridAt.writeField_disjoint (field := 1) (value := cell.state.density)
    h0 hFit32 hi (by decide) hDisjoint
  have h2 := GridAt.writeField_disjoint (field := 2) (value := cell.state.mx)
    h1 hFit32 hi (by decide) hDisjoint
  have h3 := GridAt.writeField_disjoint (field := 3) (value := cell.state.my)
    h2 hFit32 hi (by decide) hDisjoint
  have h4 := GridAt.writeField_disjoint (field := 4) (value := cell.state.energy)
    h3 hFit32 hi (by decide) hDisjoint
  have h5 := GridAt.writeField_disjoint (field := 5) (value := cell.pressure)
    h4 hFit32 hi (by decide) hDisjoint
  exact GridAt.writeField_disjoint (field := 6) (value := cell.status)
    h5 hFit32 hi (by decide) hDisjoint

#print axioms PrefixAt.write_cell
#print axioms GridAt.writeCell_disjoint

end Project.EulerRiemann.Memory
