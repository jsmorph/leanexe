import Project.Pipeline.Allocation
import Project.Pipeline.RuntimeSpec

/-! The allocator budget.  `units g nodes` counts the blocks of `g` payload bytes, with their
headers, that the free blocks `nodes` can supply by splitting.  `Heap.Budget g spare limit` states
that `top`, raised by `spare` blocks of `g + 48` bytes beyond those the free list supplies, stays
within `limit`.  An allocation of at most `g` bytes uses one spare, a release of a block of at
least `g` bytes returns one, and merging free blocks never lowers the count, so a program whose
live objects never exceed `spare` such blocks never moves `top` past `limit`. -/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- The blocks of `g` payload bytes, with their headers, that a free block holds. -/
def pieces (g : UInt64) (node : FreeNode) : Nat :=
  (node.capacity.toNat + 48) / (g.toNat + 48)

/-- The blocks of `g` payload bytes, with their headers, that the free blocks hold. -/
def units (g : UInt64) (nodes : List FreeNode) : Nat :=
  (nodes.map (pieces g)).sum

theorem units_cons (g : UInt64) (node : FreeNode) (nodes : List FreeNode) :
    units g (node :: nodes) = pieces g node + units g nodes := by
  simp [units]

theorem units_append (g : UInt64) (a b : List FreeNode) :
    units g (a ++ b) = units g a + units g b := by
  simp [units]

/-- Joining a block with the next free block never lowers the count. -/
theorem units_joinNodes (g : UInt64) (block : FreeNode) (rest : List FreeNode)
    (hBlock : block.capacity.toNat < 2 ^ 62) (hRest : ∀ n ∈ rest, n.capacity.toNat < 2 ^ 62) :
    units g (block :: rest) ≤ units g (joinNodes block rest) := by
  cases rest with
  | nil => simp [joinNodes]
  | cons next rest =>
    have hn := hRest next List.mem_cons_self
    simp only [joinNodes]
    split_ifs with hJoin
    · have hCap : (block.capacity + 48 + next.capacity).toNat =
          block.capacity.toNat + 48 + next.capacity.toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_add]
        simp only [UInt64.reduceToNat]
        omega
      have hSum : (block.capacity.toNat + 48) / (g.toNat + 48) +
          (next.capacity.toNat + 48) / (g.toNat + 48) ≤
          (block.capacity.toNat + 48 + next.capacity.toNat + 48) / (g.toNat + 48) := by
        have := Nat.div_add_div_le_add_div (x := block.capacity.toNat + 48)
          (y := next.capacity.toNat + 48) (z := g.toNat + 48)
        rwa [show block.capacity.toNat + 48 + (next.capacity.toNat + 48) =
          block.capacity.toNat + 48 + next.capacity.toNat + 48 by omega] at this
      simp only [units_cons, pieces, hCap]
      omega
    · exact le_rfl

/-- The blocks of `joinNodes block rest` hold at most `2 ^ 34` bytes when `block` and `rest`
hold fewer than `2 ^ 32`. -/
theorem joinNodes_capacity (block : FreeNode) (rest : List FreeNode)
    (hBlock : block.capacity.toNat < 2 ^ 32) (hRest : ∀ n ∈ rest, n.capacity.toNat < 2 ^ 32) :
    ∀ n ∈ joinNodes block rest, n.capacity.toNat < 2 ^ 34 := by
  cases rest with
  | nil =>
    intro n hn
    simp only [joinNodes, List.mem_singleton] at hn
    subst hn
    omega
  | cons next rest =>
    have hn := hRest next List.mem_cons_self
    simp only [joinNodes]
    split_ifs with hJoin
    · intro n hn'
      rcases List.mem_cons.mp hn' with rfl | hn'
      · simp only
        rw [UInt64.toNat_add, UInt64.toNat_add]
        simp only [UInt64.reduceToNat]
        omega
      · have := hRest n (List.mem_cons_of_mem _ hn')
        omega
    · intro n hn'
      rcases List.mem_cons.mp hn' with rfl | hn'
      · omega
      · have := hRest n hn'
        omega

/-- Returning a block to the free list adds at least its own blocks to the count. -/
theorem units_insertFree (g root capacity : UInt64) (nodes : List FreeNode)
    (hCap : capacity.toNat < 2 ^ 32) (hNodes : ∀ n ∈ nodes, n.capacity.toNat < 2 ^ 32) :
    units g nodes + pieces g ⟨root, capacity⟩ ≤ units g (insertFree root capacity nodes) := by
  have hSplit := nodes_split root nodes
  have hAbove : ∀ n ∈ aboveNodes root nodes, n.capacity.toNat < 2 ^ 32 := fun n hn =>
    hNodes n (by rw [hSplit]; exact List.mem_append_right _ hn)
  have hJoin := units_joinNodes g ⟨root, capacity⟩ (aboveNodes root nodes)
    (by simp only; omega) (fun n hn => by have := hAbove n hn; omega)
  rw [units_cons] at hJoin
  unfold insertFree
  split
  · rename_i hNone
    have hBelow : belowNodes root nodes = [] := List.getLast?_eq_none_iff.mp hNone
    conv => lhs; rw [hSplit, hBelow, List.nil_append]
    omega
  · rename_i p hp
    have hDrop := List.dropLast_append_getLast? p hp
    have hp' : p ∈ nodes := by
      rw [hSplit]
      exact List.mem_append_left _ (List.mem_of_getLast? hp)
    have hInner := joinNodes_capacity ⟨root, capacity⟩ (aboveNodes root nodes)
      (by simp only; omega) hAbove
    have hOuter := units_joinNodes g p (joinNodes ⟨root, capacity⟩ (aboveNodes root nodes))
      (by have := hNodes p hp'; omega) (fun n hn => by have := hInner n hn; omega)
    rw [units_cons] at hOuter
    conv => lhs; rw [hSplit, ← hDrop]
    rw [units_append, units_append, units_append, units_cons]
    simp only [units, List.map_nil, List.sum_nil] at hOuter hJoin ⊢
    omega

/-- An allocation of at most `g` bytes, `g` at least 8, lowers the count by at most one, and
when no free block fits it the count is zero. -/
theorem units_allocated (g need : UInt64) (nodes : List FreeNode) (hNeed : need ≤ g)
    (hg : 8 ≤ g.toNat) (hNodes : ∀ n ∈ nodes, n.capacity.toNat < 2 ^ 32) :
    units g nodes ≤ units g (allocatedNodes need nodes) + 1 ∧
      (takeFirstFitFrom 0 need nodes = none → units g nodes = 0) := by
  have hNeedNat := UInt64.le_iff_toNat_le.mp hNeed
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    refine ⟨by simp [allocatedNodes, hTake], fun _ => ?_⟩
    have hFit : takeFirstFit need nodes = none := by
      rw [← takeFirstFitFrom_project 0 need nodes, hTake]
      rfl
    have hSmall := (takeFirstFit_none_iff need nodes).mp hFit
    have hZero : ∀ n ∈ nodes, pieces g n = 0 := fun n hn => by
      have := UInt64.lt_iff_toNat_lt.mp (hSmall n hn)
      unfold pieces
      exact Nat.div_eq_of_lt (by omega)
    unfold units
    rw [List.map_congr_left hZero]
    simp
  | some choice =>
    refine ⟨?_, fun h => nomatch h⟩
    have hFits := UInt64.le_iff_toNat_le.mp (takeFirstFitFrom_some_capacity hTake)
    obtain ⟨skipped, tail, hNodesEq, -, -, hRemaining, -⟩ := takeFirstFitFrom_some_decompose hTake
    have hc : choice.node.capacity.toNat < 2 ^ 32 :=
      hNodes _ (by rw [hNodesEq]; simp)
    simp only [allocatedNodes, hTake]
    split
    · rename_i hSplits
      obtain ⟨skipped', tail', hNodesEq', hShrink⟩ := shrinkFirstFit_decompose hTake
      have hSplitNat : 56 ≤ choice.node.capacity.toNat - need.toNat := by
        have := UInt64.le_iff_toNat_le.mp (by simpa [splitsFit] using hSplits)
        rw [UInt64.toNat_sub_of_le _ _ (takeFirstFitFrom_some_capacity hTake)] at this
        simpa using this
      have hNew : (choice.node.capacity - need - 48).toNat =
          choice.node.capacity.toNat - need.toNat - 48 := by
        rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le _ _ (takeFirstFitFrom_some_capacity hTake)]
        · rfl
        · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _
            (takeFirstFitFrom_some_capacity hTake)]
          simp only [UInt64.reduceToNat]
          omega
      rw [hShrink, hNodesEq', units_append, units_append, units_cons, units_cons]
      have hPiece : pieces g choice.node ≤
          pieces g { choice.node with capacity := choice.node.capacity - need - 48 } + 1 := by
        unfold pieces
        simp only [hNew]
        rw [← Nat.add_div_right _ (by omega : 0 < g.toNat + 48)]
        exact Nat.div_le_div_right (by omega)
      omega
    · rename_i hSplits
      have hSplitNat : choice.node.capacity.toNat - need.toNat < 56 := by
        have : ¬(56 : UInt64) ≤ choice.node.capacity - need := by simpa [splitsFit] using hSplits
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _
          (takeFirstFitFrom_some_capacity hTake)] at this
        simp only [UInt64.reduceToNat] at this
        omega
      have hPiece : pieces g choice.node ≤ 1 := by
        unfold pieces
        apply Nat.le_of_lt_succ
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      rw [hRemaining, hNodesEq, units_append, units_append, units_cons]
      omega

/-- `top`, raised by `spare` blocks of `g` payload bytes and their headers beyond those the free
list supplies, stays within `limit`. -/
def Heap.Budget (heap : Heap) (g : UInt64) (spare limit : Nat) : Prop :=
  heap.top.toNat + (spare - units g heap.free) * (g.toNat + 48) ≤ limit

/-- The capacities of the free blocks lie below `2 ^ 32`. -/
theorem Heap.At.capacities {heap : Heap} {store : Store Unit} (h : heap.At store) :
    ∀ n ∈ heap.free, n.capacity.toNat < 2 ^ 32 := fun n hn => by
  have hBelow := h.below n hn
  have hTop := h.top
  have hPages := h.pages
  omega

theorem Heap.Budget.top_le {heap : Heap} {g : UInt64} {spare limit : Nat}
    (h : heap.Budget g spare limit) : heap.top.toNat ≤ limit :=
  le_trans (Nat.le_add_right _ _) h

theorem Heap.Budget.mono {heap : Heap} {g : UInt64} {spare smaller limit : Nat}
    (h : heap.Budget g spare limit) (hSmaller : smaller ≤ spare) :
    heap.Budget g smaller limit :=
  le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hSmaller _)) _) h

/-- With a spare left, an allocation of at most `g` bytes that no free block fits ends
within `limit`. -/
theorem Heap.Budget.bump {heap : Heap} {store : Store Unit} {g need : UInt64} {spare limit : Nat}
    (h : heap.Budget g spare limit) (hHeap : heap.At store) (hSpare : 0 < spare)
    (hNeed : need ≤ g) (hg : 8 ≤ g.toNat) (hNone : takeFirstFitFrom 0 need heap.free = none) :
    heap.top.toNat + 48 + need.toNat ≤ limit := by
  have hZero := (units_allocated g need heap.free hNeed hg hHeap.capacities).2 hNone
  have hNeedNat := UInt64.le_iff_toNat_le.mp hNeed
  unfold Heap.Budget at h
  rw [hZero, Nat.sub_zero] at h
  have : g.toNat + 48 ≤ spare * (g.toNat + 48) := Nat.le_mul_of_pos_left _ hSpare
  omega

/-- An allocation of at most `g` bytes uses one spare. -/
theorem Heap.Budget.allocate {heap : Heap} {store : Store Unit} {g need : UInt64}
    {spare limit : Nat} (h : heap.Budget g spare limit) (hHeap : heap.At store)
    (hSpare : 0 < spare) (hNeed : need ≤ g) (hg : 8 ≤ g.toNat) (hLimit : limit ≤ 4294967296) :
    (heap.allocate need).Budget g (spare - 1) limit := by
  obtain ⟨hUnits, hZero⟩ := units_allocated g need heap.free hNeed hg hHeap.capacities
  have hNeedNat := UInt64.le_iff_toNat_le.mp hNeed
  have hTop := allocatedTop_toNat heap.top need heap.free fun hNone =>
    (h.bump hHeap hSpare hNeed hg hNone).trans hLimit
  unfold Heap.Budget at h ⊢
  simp only [Heap.allocate]
  rw [hTop]
  split
  · rename_i hNone
    have hU := hZero hNone
    simp only [allocatedNodes, hNone] at hUnits ⊢
    rw [hU] at h ⊢
    have hMul : (spare - 1 - 0) * (g.toNat + 48) + (g.toNat + 48) = (spare - 0) * (g.toNat + 48) := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    omega
  · have hLe : spare - 1 - units g (allocatedNodes need heap.free) ≤
        spare - units g heap.free := by omega
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLe) _) h

/-- A release returns the spares of the blocks the freed block holds. -/
theorem Heap.Budget.release {heap : Heap} {store : Store Unit} {g : UInt64} {spare limit : Nat}
    (h : heap.Budget g spare limit) (hHeap : heap.At store) (ptr capacity : UInt64)
    (hCap : capacity.toNat < 2 ^ 32) :
    (heap.release ptr capacity).Budget g (spare + pieces g ⟨ptr, capacity⟩) limit := by
  have hUnits := units_insertFree g ptr capacity heap.free hCap hHeap.capacities
  unfold Heap.Budget at h ⊢
  simp only [Heap.release]
  have hLe : spare + pieces g ⟨ptr, capacity⟩ - units g (insertFree ptr capacity heap.free) ≤
      spare - units g heap.free := by omega
  exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLe) _) h

/-- A block of at least `g` bytes holds at least one block of `g` bytes. -/
theorem pieces_pos {g : UInt64} {node : FreeNode} (h : g.toNat ≤ node.capacity.toNat) :
    1 ≤ pieces g node := by
  unfold pieces
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

/-- With a spare left and `limit` within the pages the cap allows, memory has room for an
allocation of at most `g` bytes. -/
theorem Heap.Budget.room {heap : Heap} {store : Store Unit} {m : Wasm.Module} {g need : UInt64}
    {spare limit pages : Nat} (h : heap.Budget g spare limit) (hHeap : heap.At store)
    (hSpare : 0 < spare) (hNeed : need ≤ g) (hg : 8 ≤ g.toNat) (hLimit : limit ≤ pages * 65536)
    (hPages : pages ≤ store.memoryCap m 0) (hPages32 : pages ≤ 65536) :
    heap.Room store m need := fun hNone => by
  have hBump := h.bump hHeap hSpare hNeed hg hNone
  refine ⟨by omega, fun _ => ?_⟩
  unfold FixedArrayBump.requiredPages
  have : (heap.top.toNat + 48 + need.toNat - 1) / 65536 < pages :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)
  omega

/-- The store an allocation leaves has at most `pages` pages when the store before had at most
`pages` and a bump stays within them. -/
theorem Heap.allocateStore_pages_le (heap : Heap) (store : Store Unit) (need : UInt64)
    {pages : Nat} (hPages : store.mem.pages ≤ pages)
    (hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ pages * 65536) :
    (heap.allocateStore store need 1).mem.pages ≤ pages :=
  allocated_pages_le store heap.top need 1 heap.free pages hPages hBump

/-- With a spare left, an allocation of at most `g` bytes keeps the store within `pages` pages
when `limit` lies within them. -/
theorem Heap.Budget.allocate_pages {heap : Heap} {store : Store Unit} {g need : UInt64}
    {spare limit pages : Nat} (h : heap.Budget g spare limit) (hHeap : heap.At store)
    (hSpare : 0 < spare) (hNeed : need ≤ g) (hg : 8 ≤ g.toNat) (hLimit : limit ≤ pages * 65536)
    (hPages : store.mem.pages ≤ pages) :
    (heap.allocateStore store need 1).mem.pages ≤ pages :=
  heap.allocateStore_pages_le store need hPages fun hNone =>
    (h.bump hHeap hSpare hNeed hg hNone).trans hLimit

/-- A release of a block of at least `g` bytes returns at least one spare. -/
theorem Heap.Budget.release_one {heap : Heap} {store : Store Unit} {g : UInt64} {spare limit : Nat}
    (h : heap.Budget g spare limit) (hHeap : heap.At store) (ptr capacity : UInt64)
    (hCap : capacity.toNat < 2 ^ 32) (hFit : g.toNat ≤ capacity.toNat) :
    (heap.release ptr capacity).Budget g (spare + 1) limit :=
  (h.release hHeap ptr capacity hCap).mono (Nat.add_le_add_left (pieces_pos hFit) _)

/-- `heap.Budget g spare` within `pages` pages: memory has at most `pages` pages, which the cap
allows, and `top` with `spare` more blocks of `g` bytes stays within them. -/
structure Heap.Bounded (heap : Heap) (store : Store Unit) (m : Wasm.Module) (g : UInt64)
    (spare pages : Nat) : Prop where
  budget : heap.Budget g spare (pages * 65536)
  within : store.mem.pages ≤ pages
  cap : pages ≤ store.memoryCap m 0

/-- The capacity in the header of an owned array lies below `2 ^ 32`. -/
theorem Heap.Owned.capacity_lt {heap : Heap} {store : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.Owned store ptr words) :
    (store.mem.read64 (ptr - 32).toUInt32).toNat < 2 ^ 32 := by
  have := h.object.address
  unfold capacityAt at this
  omega

theorem Store.memoryCap_eq {s store : Store Unit} {m : Wasm.Module}
    (h : s.memoryCaps = store.memoryCaps) : s.memoryCap m 0 = store.memoryCap m 0 := by
  simp only [Store.memoryCap, h]

theorem Heap.Bounded.mono {heap : Heap} {store : Store Unit} {m : Wasm.Module} {g : UInt64}
    {spare smaller pages : Nat} (h : heap.Bounded store m g spare pages)
    (hSmaller : smaller ≤ spare) : heap.Bounded store m g smaller pages :=
  ⟨h.budget.mono hSmaller, h.within, h.cap⟩

/-- The bound carries over to a store with the same page count and caps. -/
theorem Heap.Bounded.store {heap : Heap} {store s : Store Unit} {m : Wasm.Module} {g : UInt64}
    {spare pages : Nat} (h : heap.Bounded store m g spare pages)
    (hPages : s.mem.pages = store.mem.pages) (hCaps : s.memoryCaps = store.memoryCaps) :
    heap.Bounded s m g spare pages :=
  ⟨h.budget, hPages ▸ h.within, (Store.memoryCap_eq hCaps).symm ▸ h.cap⟩

/-- With a spare left, memory has room for an allocation of at most `g` bytes. -/
theorem Heap.Bounded.room {heap : Heap} {store : Store Unit} {m : Wasm.Module} {g need : UInt64}
    {spare pages : Nat} (h : heap.Bounded store m g spare pages) (hHeap : heap.At store)
    (hSpare : 0 < spare) (hNeed : need ≤ g) (hg : 8 ≤ g.toNat)
    (hCap : store.memoryCap m 0 ≤ 65535) : heap.Room store m need :=
  h.budget.room hHeap hSpare hNeed hg le_rfl h.cap (by have := h.cap; omega)

/-- An allocation of at most `g` bytes uses one spare and keeps memory within `pages` pages. -/
theorem Heap.Bounded.allocate {heap : Heap} {store s : Store Unit} {m : Wasm.Module}
    {g need : UInt64} {spare pages : Nat} (h : heap.Bounded store m g (spare + 1) pages)
    (hHeap : heap.At store) (hNeed : need ≤ g) (hg : 8 ≤ g.toNat)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hPages : s.mem.pages = (heap.allocateStore store need 1).mem.pages)
    (hCaps : s.memoryCaps = store.memoryCaps) :
    (heap.allocate need).Bounded s m g spare pages := by
  have hP := h.cap
  refine ⟨by simpa using h.budget.allocate hHeap (by omega) hNeed hg (by omega), ?_,
    (Store.memoryCap_eq hCaps).symm ▸ hP⟩
  rw [hPages]
  exact h.budget.allocate_pages hHeap (by omega) hNeed hg le_rfl h.within

/-- A release of an owned array keeps the bound. -/
theorem Heap.Bounded.release {heap : Heap} {store s : Store Unit} {m : Wasm.Module} {g : UInt64}
    {spare pages : Nat} {ptr : UInt64} {words : Array UInt64}
    (h : heap.Bounded store m g spare pages) (hHeap : heap.At store)
    (hOwned : heap.Owned store ptr words)
    (hPages : s.mem.pages = store.mem.pages) (hCaps : s.memoryCaps = store.memoryCaps) :
    (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).Bounded s m g spare pages :=
  ⟨(h.budget.release hHeap ptr _ hOwned.capacity_lt).mono (Nat.le_add_right _ _),
    hPages ▸ h.within, (Store.memoryCap_eq hCaps).symm ▸ h.cap⟩

/-- A release of an owned array of at least `g` bytes returns one spare. -/
theorem Heap.Bounded.release_one {heap : Heap} {store s : Store Unit} {m : Wasm.Module}
    {g : UInt64} {spare pages : Nat} {ptr : UInt64} {words : Array UInt64}
    (h : heap.Bounded store m g spare pages) (hHeap : heap.At store)
    (hOwned : heap.Owned store ptr words) (hFit : g.toNat ≤ 8 * (words.size + 1))
    (hPages : s.mem.pages = store.mem.pages) (hCaps : s.memoryCaps = store.memoryCaps) :
    (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).Bounded s m g (spare + 1) pages :=
  ⟨h.budget.release_one hHeap ptr _ hOwned.capacity_lt (le_trans hFit hOwned.capacity),
    hPages ▸ h.within, (Store.memoryCap_eq hCaps).symm ▸ h.cap⟩

end Project.Pipeline
