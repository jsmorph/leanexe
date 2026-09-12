import Project.EulerRiemann.Traversal
import Project.ProofKit.Array

namespace Project.EulerRiemann.Memory
open Wasm
open Project.ProofKit.Memory

def cellWords (cell : Traversal.Cell) : Array UInt64 :=
  #[UInt64.ofNat cell.index, cell.state.density, cell.state.mx,
    cell.state.my, cell.state.energy, cell.pressure, cell.status]

def GridAt (store : Store Unit) (ptr : UInt64) (grid : Array Traversal.Cell) : Prop :=
  ptr.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296 ∧
  ptr.toNat + 8 * (7 * grid.size + 1) ≤ store.mem.pages * 65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat grid.size ∧
  ∀ (i : Nat) (hi : i < grid.size) (field : Nat), field < 7 →
    store.mem.read64 (ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 =
      (cellWords grid[i]).getD field 0

theorem GridAt.size_lt {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid) :
    grid.size < UInt64.size := by
  have hbound := h.1
  change grid.size < 18446744073709551616
  omega

theorem GridAt.pointerAddress_toNat {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid) :
    ptr.toUInt32.toNat = ptr.toNat := by
  have hbound := h.1
  rw [toUInt32_toNat, Nat.mod_eq_of_lt]
  omega

theorem GridAt.lengthRead {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid) :
    store.mem.read64 ptr.toUInt32 = UInt64.ofNat grid.size :=
  h.2.2.1

theorem GridAt.lengthBound {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid) :
    ptr.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
  rw [h.pointerAddress_toNat]
  have hbound := h.2.1
  omega

theorem GridAt.fieldAddress_toNat {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid)
    (i field : Nat) (hi : i < grid.size) (hf : field < 7) :
    ((ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32).toNat =
      ptr.toNat + 8 * (7 * i + field + 1) := by
  exact Project.ProofKit.UInt64Array.wordAddress_toNat h.1 (by omega)

theorem GridAt.fieldBound {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid)
    (i field : Nat) (hi : i < grid.size) (hf : field < 7) :
    ((ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32).toNat + 8 ≤
      store.mem.pages * 65536 := by
  rw [h.fieldAddress_toNat i field hi hf]
  have hbound := h.2.1
  omega

theorem GridAt.fieldRead {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid)
    (i field : Nat) (hi : i < grid.size) (hf : field < 7) :
    store.mem.read64 (ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 =
      (cellWords grid[i]).getD field 0 :=
  h.2.2.2 i hi field hf

theorem GridAt.generatedField {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt store ptr grid)
    (i field : Nat) (hi : i < grid.size) (hf : field < 7) :
    (ptr.toNat + 8 * (7 * i + field + 1)) % 4294967296 + 8 ≤
        store.mem.pages * 65536 ∧
      store.mem.read64
        (UInt32.ofNat ((ptr.toNat + 8 * (7 * i + field + 1)) % 4294967296)) =
        (cellWords grid[i]).getD field 0 := by
  have hFit : ptr.toNat + 8 * (7 * i + field + 1) < 4294967296 := by
    have hbound := h.1
    omega
  have hAddress :
      UInt32.ofNat ((ptr.toNat + 8 * (7 * i + field + 1)) % 4294967296) =
        (ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 := by
    apply UInt32.toNat.inj
    rw [h.fieldAddress_toNat i field hi hf]
    simp [Nat.mod_eq_of_lt hFit]
  constructor
  · rw [Nat.mod_eq_of_lt hFit]
    have hbound := h.2.1
    omega
  · rw [hAddress]
    exact h.fieldRead i field hi hf

theorem field_offset (i field : Nat) :
    (UInt64.ofNat i * 7 + UInt64.ofNat (field + 1)) * 8 =
      UInt64.ofNat (8 * (7 * i + field + 1)) := by
  change (UInt64.ofNat i * UInt64.ofNat 7 + UInt64.ofNat (field + 1)) *
    UInt64.ofNat 8 = UInt64.ofNat (8 * (7 * i + field + 1))
  rw [← UInt64.ofNat_mul, ← UInt64.ofNat_add, ← UInt64.ofNat_mul]
  congr 1
  omega

theorem GridAt.frame {initial final : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : GridAt initial ptr grid)
    (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address : Nat,
      ptr.toNat ≤ address → address < ptr.toNat + 8 * (7 * grid.size + 1) →
      final.mem.bytes address = initial.mem.bytes address) :
    GridAt final ptr grid := by
  refine ⟨h.1, le_trans h.2.1 (Nat.mul_le_mul_right 65536 hPages), ?_, ?_⟩
  · apply (read64_congr ptr.toUInt32 ?_).trans h.lengthRead
    intro byte hbyte
    apply hBytes <;> rw [h.pointerAddress_toNat] <;> omega
  · intro i hi field hf
    apply (read64_congr
      (ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 ?_).trans
      (h.fieldRead i field hi hf)
    intro byte hbyte
    apply hBytes <;> rw [h.fieldAddress_toNat i field hi hf] <;> omega

#print axioms GridAt.fieldAddress_toNat
#print axioms GridAt.fieldBound
#print axioms GridAt.generatedField
#print axioms field_offset
#print axioms GridAt.frame

end Project.EulerRiemann.Memory
