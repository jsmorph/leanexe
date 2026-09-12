import Project.Runtime.FreeList
import Project.ProofKit.FixedArrayHeader

namespace Project.ClobMatchFuel.BookAllocFit
open Wasm Project.Common Project.Runtime Project.Clob

def fixedArrayAllocFitMem (mem : Mem) (choice : FreeChoice)
    (stride : UInt64) : Mem :=
  ((((((unlinkFreeChoice mem choice).write64
      ((choice.node.root - 48).toUInt32) 5501223100278326855).write64
      ((choice.node.root - 40).toUInt32) 1).write64
      ((choice.node.root - 32).toUInt32) choice.node.capacity).write64
      ((choice.node.root - 24).toUInt32) 2).write64
      ((choice.node.root - 16).toUInt32) stride).write64
      ((choice.node.root - 8).toUInt32) 0

def fixedArrayAllocFitStore (st : Store Unit) (choice : FreeChoice)
    (stride : UInt64) : Store Unit :=
  { st with
    globals := if choice.previous = 0 then
      { globals := st.globals.globals.set 1 (.i64 choice.next) }
    else
      st.globals
    mem := fixedArrayAllocFitMem st.mem choice stride }

abbrev bookAllocFitMem (mem : Mem) (choice : FreeChoice) : Mem :=
  fixedArrayAllocFitMem mem choice 5

abbrev bookAllocFitStore (st : Store Unit) (choice : FreeChoice) :
    Store Unit :=
  fixedArrayAllocFitStore st choice 5

theorem freeListAt_fixedArrayAllocFitMem
    {mem : Mem} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice}
    (stride : UInt64)
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreeListAt (fixedArrayAllocFitMem mem choice stride)
      choice.remaining := by
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  obtain ⟨hNode48, hNode32, _⟩ := hList.mem_bounds hChoiceMem
  have hsep := hList.takeFirstFitFrom_node_disjoint hTake
  have h0 := hList.unlink_takeFirstFitFrom hTake
  have h1 := h0.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 48)
    (value := 5501223100278326855) hNode48 hNode32
    (by decide) (by decide) hsep
  have h2 := h1.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 40) (value := 1)
    hNode48 hNode32 (by decide) (by decide) hsep
  have h3 := h2.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 32)
    (value := choice.node.capacity) hNode48 hNode32
    (by decide) (by decide) hsep
  have h4 := h3.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 24) (value := 2)
    hNode48 hNode32 (by decide) (by decide) hsep
  have h5 := h4.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 16) (value := stride)
    hNode48 hNode32 (by decide) (by decide) hsep
  have h6 := h5.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 8) (value := 0)
    hNode48 hNode32 (by decide) (by decide) hsep
  exact h6

theorem freeListAt_bookAllocFitMem {mem : Mem} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreeListAt (bookAllocFitMem mem choice) choice.remaining := by
  exact freeListAt_fixedArrayAllocFitMem 5 hList hTake

theorem freshFixedArrayAt_fixedArrayAllocFitStore
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} (stride : UInt64)
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreshFixedArrayAt (fixedArrayAllocFitStore st choice stride)
      choice.node.root choice.node.capacity stride := by
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  obtain ⟨hRoot48, hRoot32, _⟩ := hList.mem_bounds hChoiceMem
  have hBase : (choice.node.root - 48).toNat + 48 ≤ 4294967296 := by
    rw [Project.ProofKit.Memory.toNat_sub_of_le choice.node.root 48 hRoot48]
    change choice.node.root.toNat - 48 + 48 ≤ 4294967296
    omega
  let unlinked : Store Unit := { st with mem := unlinkFreeChoice st.mem choice }
  have hFresh := Project.ProofKit.FixedArrayHeader.fresh unlinked
    (choice.node.root - 48) choice.node.capacity stride hBase
  rw [Project.ProofKit.FixedArrayHeader.from_root _ _ _ _ hRoot48 (by omega)] at hFresh
  simpa only [FreshFixedArrayAt, UInt64.sub_add_cancel, unlinked,
    fixedArrayAllocFitStore, fixedArrayAllocFitMem] using hFresh

#print axioms freeListAt_fixedArrayAllocFitMem
#print axioms freeListAt_bookAllocFitMem
#print axioms freshFixedArrayAt_fixedArrayAllocFitStore

end Project.ClobMatchFuel.BookAllocFit
