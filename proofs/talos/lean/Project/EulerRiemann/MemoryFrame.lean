import Project.EulerRiemann.MemoryWriteCell

namespace Project.EulerRiemann.Memory
open Wasm

def WritesGrid (initial final : Store Unit) (ptr : UInt64) (size : Nat) : Prop :=
  final = { initial with mem := final.mem } ∧
  final.mem.pages = initial.mem.pages ∧
  ∀ address : Nat,
    address < ptr.toNat ∨ ptr.toNat + 8 * (7 * size + 1) ≤ address →
    final.mem.bytes address = initial.mem.bytes address

theorem WritesGrid.refl (store : Store Unit) (ptr : UInt64) (size : Nat) :
    WritesGrid store store ptr size := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem WritesGrid.trans {initial middle final : Store Unit} {ptr : UInt64} {size : Nat}
    (hFirst : WritesGrid initial middle ptr size)
    (hSecond : WritesGrid middle final ptr size) :
    WritesGrid initial final ptr size := by
  refine ⟨?_, hSecond.2.1.trans hFirst.2.1, ?_⟩
  · calc
      final = { middle with mem := final.mem } := hSecond.1
      _ = { initial with mem := final.mem } := by rw [hFirst.1]
  · intro address hOutside
    exact (hSecond.2.2 address hOutside).trans (hFirst.2.2 address hOutside)

theorem writeField_frame {store : Store Unit} {ptr : UInt64} {size index field : Nat}
    (value : UInt64)
    (hFit : ptr.toNat + 8 * (7 * size + 1) ≤ 4294967296) (hi : index < size) :
    field < 7 → WritesGrid store (writeField store ptr index field value) ptr size := by
  intro hf
  exact ⟨rfl, writeField_pages .., fun _ hOutside =>
    writeField_bytes_outside hFit hi hf hOutside⟩

theorem writeCell_frame {store : Store Unit} {ptr : UInt64} {size index : Nat}
    (cell : Traversal.Cell)
    (hFit : ptr.toNat + 8 * (7 * size + 1) ≤ 4294967296) (hi : index < size) :
    WritesGrid store (writeCell store ptr index cell) ptr size := by
  have h0 := writeField_frame (store := store) (field := 0)
    (UInt64.ofNat cell.index) hFit hi (by decide)
  have h1 := h0.trans (writeField_frame (field := 1) cell.state.density hFit hi (by decide))
  have h2 := h1.trans (writeField_frame (field := 2) cell.state.mx hFit hi (by decide))
  have h3 := h2.trans (writeField_frame (field := 3) cell.state.my hFit hi (by decide))
  have h4 := h3.trans (writeField_frame (field := 4) cell.state.energy hFit hi (by decide))
  have h5 := h4.trans (writeField_frame (field := 5) cell.pressure hFit hi (by decide))
  exact h5.trans (writeField_frame (field := 6) cell.status hFit hi (by decide))

theorem PrefixAt.fieldBound {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} {words : Nat} (h : PrefixAt store ptr grid words)
    (i field : Nat) (hi : i < grid.size) (hf : field < 7) :
    ((ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32).toNat + 8 ≤
      store.mem.pages * 65536 := by
  rw [fieldAddress_toNat h.1 hi hf]
  have hBound := h.2.1
  omega

#print axioms WritesGrid.trans
#print axioms writeCell_frame
#print axioms PrefixAt.fieldBound

end Project.EulerRiemann.Memory
