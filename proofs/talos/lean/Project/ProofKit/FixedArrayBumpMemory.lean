import Project.ProofKit.FixedArrayBump
import Project.ProofKit.FixedArrayHeader
import Project.ProofKit.FreeListMemory

namespace Project.ProofKit.FixedArrayBump
open Wasm Project.Clob Project.Runtime MemoryGrowth

theorem allocated_of_fits (initial : Store Unit) (base need stride : UInt64)
    (hFit : base.toNat + 48 + need.toNat ≤ initial.mem.pages * 65536) :
    allocated initial base need stride = fixedArrayAllocBumpStore initial base need stride := by
  have hPages : requiredPages base need ≤ initial.mem.pages := by
    unfold requiredPages
    omega
  simp only [allocated, ensured, Nat.not_lt.mpr hPages, ↓reduceIte]

theorem allocated_bytes_outside (initial : Store Unit) (base need stride : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (allocated initial base need stride).mem.bytes address = initial.mem.bytes address := by
  change (fixedArrayHeaderMem (ensured initial (requiredPages base need)).mem base need stride).bytes
    address = initial.mem.bytes address
  rw [FixedArrayHeader.bytes_outside _ base need stride hFit32 address hOutside, ensured_bytes]

theorem allocated_pages (initial : Store Unit) (base need stride : UInt64) :
    (allocated initial base need stride).mem.pages =
      max initial.mem.pages (requiredPages base need) := by
  change (ensured initial (requiredPages base need)).mem.pages = _
  exact ensured_pages ..

theorem allocated_freeList (initial : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) (hList : FreeListAt initial.mem nodes)
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hBelow : ∀ node ∈ nodes, node.root.toNat ≤ base.toNat) :
    FreeListAt (allocated initial base need stride).mem nodes := by
  apply FreeListMemory.frame_headers hList
  · rw [allocated_pages]
    exact Nat.le_max_left ..
  · intro node hNode address _ hHigh
    exact allocated_bytes_outside initial base need stride hFit32 address
      (Or.inl (hHigh.trans_le (hBelow node hNode)))

#print axioms allocated_of_fits
#print axioms allocated_bytes_outside
#print axioms allocated_freeList
end Project.ProofKit.FixedArrayBump
