import Project.EulerRiemann.Memory
import Project.ProofKit.MemoryRoundtrip

namespace Project.EulerRiemann.Memory
open Wasm Project.ProofKit.Memory

def PrefixAt (store : Store Unit) (ptr : UInt64)
    (grid : Array Traversal.Cell) (words : Nat) : Prop :=
  ptr.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296 ∧
  ptr.toNat + 8 * (7 * grid.size + 1) ≤ store.mem.pages * 65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat grid.size ∧
  ∀ (i : Nat) (hi : i < grid.size) (field : Nat), field < 7 →
    7 * i + field < words →
    store.mem.read64 (ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 =
      (cellWords grid[i]).getD field 0

theorem PrefixAt.empty (store : Store Unit) (ptr : UInt64)
    (grid : Array Traversal.Cell)
    (hFit32 : ptr.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296)
    (hFitMemory : ptr.toNat + 8 * (7 * grid.size + 1) ≤ store.mem.pages * 65536)
    (hLength : store.mem.read64 ptr.toUInt32 = UInt64.ofNat grid.size) :
    PrefixAt store ptr grid 0 :=
  ⟨hFit32, hFitMemory, hLength, fun _ _ _ _ h => False.elim (by omega)⟩

theorem PrefixAt.complete {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} (h : PrefixAt store ptr grid (7 * grid.size)) :
    GridAt store ptr grid :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi field hf => h.2.2.2 i hi field hf (by omega)⟩

def writeField (store : Store Unit) (ptr : UInt64) (i field : Nat)
    (value : UInt64) : Store Unit :=
  { store with mem := (store.mem.write64
      (ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 value) }

@[simp] theorem writeField_pages (store : Store Unit) (ptr : UInt64)
    (i field : Nat) (value : UInt64) :
    (writeField store ptr i field value).mem.pages = store.mem.pages :=
  Mem.write64_pages ..

@[simp] theorem writeField_globals (store : Store Unit) (ptr : UInt64)
    (i field : Nat) (value : UInt64) :
    (writeField store ptr i field value).globals = store.globals := rfl

theorem fieldAddress_toNat {ptr : UInt64} {size i field : Nat}
    (hFit32 : ptr.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hi : i < size) (hf : field < 7) :
    ((ptr + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32).toNat =
      ptr.toNat + 8 * (7 * i + field + 1) :=
  Project.ProofKit.UInt64Array.wordAddress_toNat hFit32 (by omega)

theorem PrefixAt.write_next {store : Store Unit} {ptr : UInt64}
    {grid : Array Traversal.Cell} {i field : Nat}
    (h : PrefixAt store ptr grid (7 * i + field))
    (hi : i < grid.size) (hf : field < 7) :
    PrefixAt (writeField store ptr i field ((cellWords grid[i]).getD field 0))
      ptr grid (7 * i + field + 1) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · simpa only [writeField_pages] using h.2.1
  · apply (read64_write64_disjoint store.mem _ _ ptr.toUInt32 ?_).trans h.2.2.1
    left
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by have := h.1; omega),
      fieldAddress_toNat h.1 hi hf]
    omega
  · intro j hj f hfield hw
    by_cases heq : 7 * j + f = 7 * i + field
    · have hjEq : j = i := by omega
      have hfEq : f = field := by omega
      subst j
      subst f
      exact read64_write64 ..
    · apply (read64_write64_disjoint store.mem _ _ _ ?_).trans
        (h.2.2.2 j hj f hfield (by omega))
      rw [fieldAddress_toNat h.1 hj hfield, fieldAddress_toNat h.1 hi hf]
      omega

theorem writeField_bytes_outside {store : Store Unit} {ptr : UInt64}
    {size i field address : Nat} {value : UInt64}
    (hFit32 : ptr.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hi : i < size) (hf : field < 7)
    (hOutside : address < ptr.toNat ∨ ptr.toNat + 8 * (7 * size + 1) ≤ address) :
    (writeField store ptr i field value).mem.bytes address = store.mem.bytes address := by
  apply write64_bytes_outside
  rw [fieldAddress_toNat hFit32 hi hf]
  omega

theorem GridAt.writeField_disjoint {store : Store Unit} {source target : UInt64}
    {grid : Array Traversal.Cell} {size i field : Nat} {value : UInt64}
    (hGrid : GridAt store source grid)
    (hFit32 : target.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hi : i < size) (hf : field < 7)
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.toNat) :
    GridAt (writeField store target i field value) source grid := by
  apply hGrid.frame
  · simp only [writeField_pages, Nat.le_refl]
  · intro address hLow hHigh
    apply writeField_bytes_outside hFit32 hi hf
    omega

#print axioms PrefixAt.empty
#print axioms PrefixAt.complete
#print axioms PrefixAt.write_next
#print axioms GridAt.writeField_disjoint

end Project.EulerRiemann.Memory
