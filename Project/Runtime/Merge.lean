import Project.ProofKit.FreeListMemory

/-!
# Returning a block to the free list

`release` keeps the free list in address order.  It inserts a freed block before
the first block at a higher address and merges it with the blocks on either side
when they touch, as in Knuth's liberation with a sorted list (TAOCP vol. 1,
§2.5, Algorithm B).  This file models the resulting list and memory and proves
that the list stays laid out.
-/

namespace Project.Runtime

open Wasm Project.Common

theorem headerWord_toNat {r k : UInt64} (hk : k.toNat ≤ 48) (h48 : 48 ≤ r.toNat)
    (h32 : r.toNat < 4294967296) : (r - k).toUInt32.toNat = r.toNat - k.toNat := by
  rw [toUInt32_toNat, toNat_sub_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A word of a header keeps its value when the bytes of that header keep theirs. -/
theorem read64_header {m m' : Mem} {r k : UInt64} (hk8 : 8 ≤ k.toNat) (hk : k.toNat ≤ 48)
    (h48 : 48 ≤ r.toNat) (h32 : r.toNat < 4294967296)
    (hBytes : ∀ a, r.toNat - 48 ≤ a → a < r.toNat → m'.bytes a = m.bytes a) :
    m'.read64 (r - k).toUInt32 = m.read64 (r - k).toUInt32 := by
  apply read64_congr
  intro i hi
  rw [headerWord_toNat hk h48 h32]
  exact hBytes _ (by omega) (by omega)

theorem adjoins_toNat {root capacity next : UInt64}
    (h32 : root.toNat + capacity.toNat < 4294967296) (h : root + capacity + 48 = next) :
    root.toNat + capacity.toNat + 48 = next.toNat := by
  have := congrArg UInt64.toNat h
  rw [UInt64.toNat_add, UInt64.toNat_add] at this
  simp only [UInt64.reduceToNat] at this
  omega

theorem merged_toNat {a b : UInt64} (ha : a.toNat < 4294967296) (hb : b.toNat < 4294967296) :
    (a + 48 + b).toNat = a.toNat + 48 + b.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

theorem FreeListAt.header {mem : Mem} {nodes : List FreeNode} (h : FreeListAt mem nodes)
    {node : FreeNode} (hNode : node ∈ nodes) :
    mem.read64 (node.root - 40).toUInt32 = 0 ∧
      mem.read64 (node.root - 32).toUInt32 = node.capacity := by
  induction h with
  | nil => simp at hNode
  | cons _ _ _ hRc hCapacity _ _ _ ih =>
    rcases List.mem_cons.mp hNode with rfl | hNode
    · exact ⟨hRc, hCapacity⟩
    · exact ih hNode

/-- `block` followed by `rest`, with the first block of `rest` merged into `block`
when it begins where `block` ends. -/
def joinNodes (block : FreeNode) : List FreeNode → List FreeNode
  | next :: rest =>
      if block.root + block.capacity + 48 = next.root then
        { block with capacity := block.capacity + 48 + next.capacity } :: rest
      else block :: next :: rest
  | [] => [block]

/-- Memory after the size and link words of `block` are set for
`joinNodes block rest`. -/
def joinMem (mem : Mem) (block : FreeNode) : List FreeNode → Mem
  | next :: rest =>
      if block.root + block.capacity + 48 = next.root then
        (mem.write64 (block.root - 32).toUInt32 (block.capacity + 48 + next.capacity)).write64
          (block.root - 8).toUInt32 (freeHead rest)
      else mem.write64 (block.root - 8).toUInt32 next.root
  | [] => mem.write64 (block.root - 8).toUInt32 0

theorem freeHead_joinNodes (block : FreeNode) (rest : List FreeNode) :
    freeHead (joinNodes block rest) = block.root := by
  cases rest with
  | nil => rfl
  | cons next rest =>
    simp only [joinNodes]
    split <;> rfl

theorem joinMem_pages (mem : Mem) (block : FreeNode) (rest : List FreeNode) :
    (joinMem mem block rest).pages = mem.pages := by
  cases rest with
  | nil => simp [joinMem, Wasm.Mem.write64_pages]
  | cons next rest =>
    simp only [joinMem]
    split <;> simp [Wasm.Mem.write64_pages]

/-- `joinMem` writes only inside the header of `block`. -/
theorem joinMem_bytes (mem : Mem) {block : FreeNode} (rest : List FreeNode)
    (h48 : 48 ≤ block.root.toNat) (h32 : block.root.toNat < 4294967296) {address : Nat}
    (h : address < block.root.toNat - 48 ∨ block.root.toNat ≤ address) :
    (joinMem mem block rest).bytes address = mem.bytes address := by
  have h8 := headerWord_toNat (r := block.root) (k := 8) (by decide) h48 h32
  have h32' := headerWord_toNat (r := block.root) (k := 32) (by decide) h48 h32
  simp only [UInt64.reduceToNat] at h8 h32'
  cases rest with
  | nil => exact Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)
  | cons next rest =>
    simp only [joinMem]
    split
    · rw [Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega),
        Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)]
    · exact Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)

/-- The blocks of `joinNodes block rest` start at or above 48 and end inside the
32-bit address space when those of `block` and `rest` do. -/
theorem joinNodes_bounds {block : FreeNode} {rest : List FreeNode}
    (h48 : 48 ≤ block.root.toNat) (h32 : block.root.toNat + block.capacity.toNat < 4294967296)
    (hRest : ∀ n ∈ rest, 48 ≤ n.root.toNat ∧ n.root.toNat + n.capacity.toNat < 4294967296) :
    ∀ n ∈ joinNodes block rest,
      48 ≤ n.root.toNat ∧ n.root.toNat + n.capacity.toNat < 4294967296 := by
  cases rest with
  | nil =>
    intro n hn
    simp only [joinNodes, List.mem_singleton] at hn
    subst hn
    exact ⟨h48, h32⟩
  | cons next tail =>
    simp only [joinNodes]
    split
    · rename_i hAdj
      have hAdjN := adjoins_toNat h32 hAdj
      obtain ⟨hn48, hn32⟩ := hRest next List.mem_cons_self
      have hCap := merged_toNat (a := block.capacity) (b := next.capacity) (by omega) (by omega)
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · refine ⟨h48, ?_⟩
        simp only
        rw [hCap]
        omega
      · exact hRest n (List.mem_cons_of_mem _ hn)
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨h48, h32⟩
      · exact hRest n hn

/-- A region apart from `block` and from every block of `rest` is apart from every
block of `joinNodes block rest`. -/
theorem joinNodes_apart {block : FreeNode} {rest : List FreeNode} {region : Nat × Nat}
    (h48 : 48 ≤ block.root.toNat) (h32 : block.root.toNat + block.capacity.toNat < 4294967296)
    (hRest : ∀ n ∈ rest, 48 ≤ n.root.toNat ∧ n.root.toNat + n.capacity.toNat < 4294967296)
    (hSize : 0 < region.2) (hBlock : regionsDisjoint region block.region)
    (hApart : ∀ n ∈ rest, regionsDisjoint region n.region) :
    ∀ n ∈ joinNodes block rest, regionsDisjoint region n.region := by
  cases rest with
  | nil =>
    intro n hn
    simp only [joinNodes, List.mem_singleton] at hn
    subst hn
    exact hBlock
  | cons next tail =>
    simp only [joinNodes]
    split
    · rename_i hAdj
      have hAdjN := adjoins_toNat h32 hAdj
      obtain ⟨hn48, hn32⟩ := hRest next List.mem_cons_self
      have hCap := merged_toNat (a := block.capacity) (b := next.capacity) (by omega) (by omega)
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · have hNext := hApart next List.mem_cons_self
        simp only [regionsDisjoint, FreeNode.region] at hBlock hNext ⊢
        rw [hCap]
        omega
      · exact hApart n (List.mem_cons_of_mem _ hn)
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hBlock
      · exact hApart n hn

/-- Joining a block laid out at `block.root` to a laid-out list keeps it laid
out. -/
theorem FreeListAt.join {mem : Mem} {block : FreeNode} {rest : List FreeNode}
    (hRest : FreeListAt mem rest) (h48 : 48 ≤ block.root.toNat)
    (h32 : block.root.toNat + block.capacity.toNat < 4294967296)
    (hFit : block.root.toNat + block.capacity.toNat ≤ mem.pages * 65536)
    (hCount : mem.read64 (block.root - 40).toUInt32 = 0)
    (hCapacity : mem.read64 (block.root - 32).toUInt32 = block.capacity)
    (hApart : ∀ n ∈ rest, regionsDisjoint block.region n.region) :
    FreeListAt (joinMem mem block rest) (joinNodes block rest) := by
  have h40a := headerWord_toNat (r := block.root) (k := 40) (by decide) h48 (by omega)
  have h32a := headerWord_toNat (r := block.root) (k := 32) (by decide) h48 (by omega)
  have h8a := headerWord_toNat (r := block.root) (k := 8) (by decide) h48 (by omega)
  simp only [UInt64.reduceToNat] at h40a h32a h8a
  have hFrame : ∀ (l : List FreeNode), FreeListAt mem l →
      (∀ n ∈ l, regionsDisjoint block.region n.region) →
      FreeListAt (joinMem mem block rest) l := fun l hl hSep =>
    Project.ProofKit.FreeListMemory.frame_headers hl (by rw [joinMem_pages]) fun n hn a hLow hHigh => by
      have hs := hSep n hn
      have hn48 := (hl.mem_bounds hn).1
      simp only [regionsDisjoint, FreeNode.region] at hs
      exact joinMem_bytes mem rest h48 (by omega) (by omega)
  cases rest with
  | nil =>
    simp only [joinNodes]
    refine .cons h48 h32 (by rw [joinMem_pages]; exact hFit) ?_ ?_ ?_ (by simp) .nil
    · simp only [joinMem]
      rw [read64_write64_ne _ _ _ _ (by omega)]
      exact hCount
    · simp only [joinMem]
      rw [read64_write64_ne _ _ _ _ (by omega)]
      exact hCapacity
    · exact Project.ProofKit.Memory.read64_write64 _ _ _
  | cons next tail =>
    have hTail := hFrame tail
    cases hRest with
    | cons hn48 hn32 hnFit hnRc hnCapacity hnNext hnSep hnTail =>
      by_cases hAdj : block.root + block.capacity + 48 = next.root
      · have hAdjN := adjoins_toNat h32 hAdj
        have hCap := merged_toNat (a := block.capacity) (b := next.capacity) (by omega) (by omega)
        have hTail' := hTail hnTail fun n hn => hApart n (List.mem_cons_of_mem _ hn)
        have hList : joinNodes block (next :: tail) =
            { block with capacity := block.capacity + 48 + next.capacity } :: tail := by
          simp [joinNodes, hAdj]
        have hMem : joinMem mem block (next :: tail) =
            (mem.write64 (block.root - 32).toUInt32 (block.capacity + 48 + next.capacity)).write64
              (block.root - 8).toUInt32 (freeHead tail) := by
          simp [joinMem, hAdj]
        have hEnd : block.root.toNat + (block.capacity + 48 + next.capacity).toNat < 4294967296 := by
          rw [hCap]
          omega
        have hEndFit : block.root.toNat + (block.capacity + 48 + next.capacity).toNat ≤
            ((mem.write64 (block.root - 32).toUInt32 (block.capacity + 48 + next.capacity)).write64
              (block.root - 8).toUInt32 (freeHead tail)).pages * 65536 := by
          simp only [Wasm.Mem.write64_pages]
          rw [hCap]
          omega
        rw [hList]
        rw [hMem] at hTail' ⊢
        refine .cons h48 hEnd hEndFit ?_ ?_ ?_ ?_ hTail'
        · dsimp only
          rw [read64_write64_ne _ _ _ _ (by omega), read64_write64_ne _ _ _ _ (by omega)]
          exact hCount
        · dsimp only
          rw [read64_write64_ne _ _ _ _ (by omega)]
          exact Project.ProofKit.Memory.read64_write64 _ _ _
        · exact Project.ProofKit.Memory.read64_write64 _ _ _
        · intro other hOther
          have hb := hApart other (List.mem_cons_of_mem _ hOther)
          have hn := hnSep other hOther
          simp only [regionsDisjoint, FreeNode.region] at hb hn ⊢
          rw [hCap]
          omega
      · have hList : joinNodes block (next :: tail) = block :: next :: tail := by
          simp [joinNodes, hAdj]
        have hMem : joinMem mem block (next :: tail) =
            mem.write64 (block.root - 8).toUInt32 next.root := by
          simp [joinMem, hAdj]
        have hNext := hFrame (next :: tail) (.cons hn48 hn32 hnFit hnRc hnCapacity hnNext hnSep
          hnTail) hApart
        rw [hList]
        rw [hMem] at hNext ⊢
        refine .cons h48 h32 (by simp [Wasm.Mem.write64_pages]; omega) ?_ ?_ ?_ hApart hNext
        · rw [read64_write64_ne _ _ _ _ (by omega)]
          exact hCount
        · rw [read64_write64_ne _ _ _ _ (by omega)]
          exact hCapacity
        · exact Project.ProofKit.Memory.read64_write64 _ _ _

/-- The free blocks at or below `root`, in list order, up to the first block above
it. -/
def belowNodes (root : UInt64) (nodes : List FreeNode) : List FreeNode :=
  nodes.takeWhile fun n => decide (n.root ≤ root)

/-- The free blocks from the first block above `root` on. -/
def aboveNodes (root : UInt64) (nodes : List FreeNode) : List FreeNode :=
  nodes.dropWhile fun n => decide (n.root ≤ root)

theorem nodes_split (root : UInt64) (nodes : List FreeNode) :
    nodes = belowNodes root nodes ++ aboveNodes root nodes :=
  (List.takeWhile_append_dropWhile ..).symm

/-- The free list after `release` returns the block with payload `root` and
capacity `capacity`: placed before the first block above it, and merged with the
blocks before and after it when they touch. -/
def insertFree (root capacity : UInt64) (nodes : List FreeNode) : List FreeNode :=
  match (belowNodes root nodes).getLast? with
  | none => joinNodes { root, capacity } (aboveNodes root nodes)
  | some p => (belowNodes root nodes).dropLast ++
      joinNodes p (joinNodes { root, capacity } (aboveNodes root nodes))

/-- Memory after `release` returns that block: its count word cleared, its size and
link words set, and the size and link words of the block before it set. -/
def releaseMem (mem : Mem) (root capacity : UInt64) (nodes : List FreeNode) : Mem :=
  match (belowNodes root nodes).getLast? with
  | none => joinMem (mem.write64 (root - 40).toUInt32 0) { root, capacity } (aboveNodes root nodes)
  | some p => joinMem (joinMem (mem.write64 (root - 40).toUInt32 0) { root, capacity }
      (aboveNodes root nodes)) p (joinNodes { root, capacity } (aboveNodes root nodes))

theorem releaseMem_pages (mem : Mem) (root capacity : UInt64) (nodes : List FreeNode) :
    (releaseMem mem root capacity nodes).pages = mem.pages := by
  unfold releaseMem
  split <;> simp [joinMem_pages, Wasm.Mem.write64_pages]

theorem freeHead_insertFree (root capacity : UInt64) (nodes : List FreeNode) :
    freeHead (insertFree root capacity nodes) =
      if belowNodes root nodes = [] then root else freeHead nodes := by
  have hSplit := nodes_split root nodes
  unfold insertFree
  split
  · rename_i hLast
    simp [List.getLast?_eq_none_iff.mp hLast, freeHead_joinNodes]
  · rename_i p hLast
    obtain ⟨pre, hPre⟩ := List.getLast?_eq_some_iff.mp hLast
    have hNe : belowNodes root nodes ≠ [] := by simp [hPre]
    rw [ite_eq_right hNe]
    conv => rhs; rw [hSplit, hPre]
    rw [hPre]
    cases pre with
    | nil =>
      simp only [List.nil_append, List.dropLast_singleton]
      rw [freeHead_joinNodes]
      rfl
    | cons x pre =>
      have hDrop : (x :: pre ++ [p]).dropLast = x :: pre := by
        rw [List.dropLast_concat]
      rw [hDrop]
      rfl

/-- `release` writes only in the header of the freed block and in the header of the
free block below it. -/
theorem releaseMem_bytes (mem : Mem) {root capacity : UInt64} {nodes : List FreeNode}
    (h48 : 48 ≤ root.toNat) (h32 : root.toNat < 4294967296)
    (hNodes : ∀ n ∈ nodes, 48 ≤ n.root.toNat ∧ n.root.toNat < 4294967296) {address : Nat}
    (hRoot : address < root.toNat - 48 ∨ root.toNat ≤ address)
    (hFree : ∀ n ∈ nodes, address < n.root.toNat - 48 ∨ n.root.toNat ≤ address) :
    (releaseMem mem root capacity nodes).bytes address = mem.bytes address := by
  have h40 := headerWord_toNat (r := root) (k := 40) (by decide) h48 h32
  simp only [UInt64.reduceToNat] at h40
  have hFirst : (joinMem (mem.write64 (root - 40).toUInt32 0) { root, capacity }
      (aboveNodes root nodes)).bytes address = mem.bytes address := by
    rw [joinMem_bytes (block := { root, capacity }) _ _ h48 h32 hRoot,
      Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)]
  unfold releaseMem
  split
  · exact hFirst
  · rename_i p hLast
    have hp : p ∈ nodes := by
      rw [nodes_split root nodes]
      exact List.mem_append_left _ (List.mem_of_getLast? hLast)
    rw [joinMem_bytes _ _ (hNodes p hp).1 (hNodes p hp).2 (hFree p hp), hFirst]

/-- Returning a block that lies apart from every free block keeps the free list
laid out. -/
theorem FreeListAt.release {mem : Mem} {nodes : List FreeNode} {root capacity : UInt64}
    (h : FreeListAt mem nodes) (h48 : 48 ≤ root.toNat)
    (h32 : root.toNat + capacity.toNat < 4294967296)
    (hFit : root.toNat + capacity.toNat ≤ mem.pages * 65536)
    (hCapacity : mem.read64 (root - 32).toUInt32 = capacity)
    (hApart : ∀ n ∈ nodes, regionsDisjoint (root.toNat - 48, 48 + capacity.toNat) n.region) :
    FreeListAt (releaseMem mem root capacity nodes) (insertFree root capacity nodes) := by
  have hSplit := nodes_split root nodes
  have hAboveMem : ∀ n ∈ aboveNodes root nodes, n ∈ nodes := fun n hn => by
    rw [hSplit]
    exact List.mem_append_right _ hn
  have hBounds : ∀ n ∈ nodes, 48 ≤ n.root.toNat ∧ n.root.toNat + n.capacity.toNat < 4294967296 :=
    fun n hn => ⟨(h.mem_bounds hn).1, (h.mem_bounds hn).2.1⟩
  have hAbove : FreeListAt mem (aboveNodes root nodes) := by
    have h' := h
    rw [hSplit] at h'
    exact h'.suffix
  have hA40 := headerWord_toNat (r := root) (k := 40) (by decide) h48 (by omega)
  have hA32 := headerWord_toNat (r := root) (k := 32) (by decide) h48 (by omega)
  simp only [UInt64.reduceToNat] at hA40 hA32
  have hAbove1 : FreeListAt (mem.write64 (root - 40).toUInt32 0) (aboveNodes root nodes) :=
    Project.ProofKit.FreeListMemory.frame_headers hAbove (by simp [Wasm.Mem.write64_pages]) fun n hn a hLow hHigh => by
      have hq := hApart n (hAboveMem n hn)
      have := (hAbove.mem_bounds hn).1
      simp only [regionsDisjoint, FreeNode.region] at hq
      exact Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)
  have hBlock := FreeListAt.join (block := { root, capacity }) hAbove1 h48 h32
    (by simp [Wasm.Mem.write64_pages]; omega) (Project.ProofKit.Memory.read64_write64 _ _ _)
    (by dsimp only; rw [read64_write64_ne _ _ _ _ (by omega)]; exact hCapacity)
    (fun n hn => hApart n (hAboveMem n hn))
  unfold insertFree releaseMem
  split
  · exact hBlock
  · rename_i p hLast
    obtain ⟨pre, hPre⟩ := List.getLast?_eq_some_iff.mp hLast
    rw [hPre, List.dropLast_concat]
    have hNodes : nodes = pre ++ p :: aboveNodes root nodes := by
      calc nodes = belowNodes root nodes ++ aboveNodes root nodes := hSplit
        _ = pre ++ p :: aboveNodes root nodes := by rw [hPre]; simp
    have hP : p ∈ nodes := by
      rw [hNodes]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨hp48, hp32, hpFit⟩ := h.mem_bounds hP
    have hpq := hApart p hP
    have hPair := h.pairwise
    rw [hNodes, List.pairwise_append] at hPair
    obtain ⟨_, hSuffixPair, hCross⟩ := hPair
    have hpAbove : ∀ n ∈ aboveNodes root nodes, regionsDisjoint p.region n.region :=
      fun n hn => List.rel_of_pairwise_cons hSuffixPair hn
    set mem2 := joinMem (mem.write64 (root - 40).toUInt32 0) { root, capacity }
      (aboveNodes root nodes) with hMem2
    have hBytes2 : ∀ a, a < root.toNat - 48 ∨ root.toNat ≤ a → mem2.bytes a = mem.bytes a :=
      fun a ha => by
        rw [hMem2, joinMem_bytes (block := { root, capacity }) _ _ h48 (by dsimp only; omega) ha,
          Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by omega)]
    have hpHeader := h.header hP
    simp only [regionsDisjoint, FreeNode.region] at hpq
    have hpBytes : ∀ a, p.root.toNat - 48 ≤ a → a < p.root.toNat → mem2.bytes a = mem.bytes a :=
      fun a hLow hHigh => hBytes2 a (by omega)
    have hJoin := FreeListAt.join (mem := mem2) (block := p) hBlock hp48 hp32
      (by rw [hMem2, joinMem_pages]; simp [Wasm.Mem.write64_pages]; omega)
      ((read64_header (by decide) (by decide) hp48 (by omega) hpBytes).trans hpHeader.1)
      ((read64_header (by decide) (by decide) hp48 (by omega) hpBytes).trans hpHeader.2)
      (joinNodes_apart h48 h32 (fun n hn => hBounds n (hAboveMem n hn))
        (by simp only [FreeNode.region]; omega)
        (by simp only [regionsDisjoint, FreeNode.region]; omega) hpAbove)
    have h' := h
    rw [hNodes] at h'
    have hAboveBounds := fun n hn => hBounds n (hAboveMem n hn)
    refine FreeListAt.replace_suffix (old := p :: aboveNodes root nodes) h' hJoin
      (fun _ => by rw [freeHead_joinNodes]; rfl) ?_ ?_ ?_
    · intro x hx
      have hxp := hCross x hx p List.mem_cons_self
      have hxMem : x ∈ nodes := by
        rw [hNodes]
        exact List.mem_append_left _ hx
      have hxq := hApart x hxMem
      obtain ⟨hx48, hx32, _⟩ := h.mem_bounds hxMem
      refine joinNodes_apart hp48 hp32 (joinNodes_bounds h48 h32 hAboveBounds)
        (by simp only [FreeNode.region]; omega) hxp ?_
      refine joinNodes_apart h48 h32 hAboveBounds (by simp only [FreeNode.region]; omega)
        (regionsDisjoint_symm hxq) ?_
      exact fun n hn => hCross x hx n (List.mem_cons_of_mem _ hn)
    · intro x hx offset hOffset
      have hxp := hCross x hx p List.mem_cons_self
      have hxMem : x ∈ nodes := by
        rw [hNodes]
        exact List.mem_append_left _ hx
      have hxq := hApart x hxMem
      obtain ⟨hx48, hx32, _⟩ := h.mem_bounds hxMem
      simp only [regionsDisjoint, FreeNode.region] at hxp hxq
      have hxBytes : ∀ a, x.root.toNat - 48 ≤ a → a < x.root.toNat →
          (joinMem mem2 p (joinNodes { root, capacity } (aboveNodes root nodes))).bytes a =
            mem.bytes a := fun a hLow hHigh => by
        rw [joinMem_bytes _ _ hp48 (by omega) (by omega)]
        exact hBytes2 a (by omega)
      rcases hOffset with rfl | rfl | rfl <;>
        exact read64_header (by decide) (by decide) hx48 (by omega) hxBytes
    · rw [joinMem_pages, hMem2, joinMem_pages]
      simp [Wasm.Mem.write64_pages]

/-- The walk that stops at the first block above `root` splits the list there. -/
theorem belowNodes_append {root : UInt64} {visited remaining : List FreeNode}
    (hVisited : ∀ n ∈ visited, n.root ≤ root)
    (hRemaining : ∀ n, remaining.head? = some n → root < n.root) :
    belowNodes root (visited ++ remaining) = visited ∧
      aboveNodes root (visited ++ remaining) = remaining := by
  induction visited with
  | nil =>
    cases remaining with
    | nil => simp [belowNodes, aboveNodes]
    | cons n rest =>
      have hLt := hRemaining n rfl
      have hNot : ¬ n.root ≤ root := by
        rw [UInt64.le_iff_toNat_le]
        rw [UInt64.lt_iff_toNat_lt] at hLt
        omega
      simp [belowNodes, aboveNodes, List.takeWhile_cons, List.dropWhile_cons, hNot]
  | cons v visited ih =>
    have hv := hVisited v List.mem_cons_self
    obtain ⟨hBelow, hAbove⟩ := ih fun n hn => hVisited n (List.mem_cons_of_mem _ hn)
    simp only [belowNodes, aboveNodes] at hBelow hAbove ⊢
    simp [List.takeWhile_cons, List.dropWhile_cons, hv, hBelow, hAbove]

/-- Each block of `joinNodes block rest` starts where `block` or a block of `rest`
starts and ends where one of them ends. -/
theorem joinNodes_cover {block : FreeNode} {rest : List FreeNode}
    (h32 : block.root.toNat + block.capacity.toNat < 4294967296)
    (hRest : ∀ n ∈ rest, n.root.toNat + n.capacity.toNat < 4294967296) :
    ∀ n ∈ joinNodes block rest,
      (n.root = block.root ∨ ∃ m ∈ rest, n.root = m.root) ∧
      (n.root.toNat + n.capacity.toNat = block.root.toNat + block.capacity.toNat ∨
        ∃ m ∈ rest, n.root.toNat + n.capacity.toNat = m.root.toNat + m.capacity.toNat) := by
  cases rest with
  | nil =>
    intro n hn
    simp only [joinNodes, List.mem_singleton] at hn
    subst hn
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  | cons next tail =>
    simp only [joinNodes]
    split
    · rename_i hAdj
      have hAdjN := adjoins_toNat h32 hAdj
      have hn32 := hRest next List.mem_cons_self
      have hCap := merged_toNat (a := block.capacity) (b := next.capacity) (by omega) (by omega)
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · refine ⟨Or.inl rfl, Or.inr ⟨next, List.mem_cons_self, ?_⟩⟩
        simp only
        rw [hCap]
        omega
      · exact ⟨Or.inr ⟨n, List.mem_cons_of_mem _ hn, rfl⟩,
          Or.inr ⟨n, List.mem_cons_of_mem _ hn, rfl⟩⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr ⟨n, hn, rfl⟩, Or.inr ⟨n, hn, rfl⟩⟩

/-- Each block of the list after a release starts where the freed block or an old
free block starts and ends where one of them ends. -/
theorem insertFree_cover {root capacity : UInt64} {nodes : List FreeNode}
    (h32 : root.toNat + capacity.toNat < 4294967296)
    (hNodes : ∀ n ∈ nodes, n.root.toNat + n.capacity.toNat < 4294967296) :
    ∀ n ∈ insertFree root capacity nodes,
      (n.root = root ∨ ∃ m ∈ nodes, n.root = m.root) ∧
      (n.root.toNat + n.capacity.toNat = root.toNat + capacity.toNat ∨
        ∃ m ∈ nodes, n.root.toNat + n.capacity.toNat = m.root.toNat + m.capacity.toNat) := by
  have hSplit := nodes_split root nodes
  have hAboveMem : ∀ n ∈ aboveNodes root nodes, n ∈ nodes := fun n hn => by
    rw [hSplit]
    exact List.mem_append_right _ hn
  have hBlock := joinNodes_cover (block := { root, capacity }) h32
    (fun n hn => hNodes n (hAboveMem n hn))
  have hLift : ∀ n ∈ joinNodes { root, capacity } (aboveNodes root nodes),
      (n.root = root ∨ ∃ m ∈ nodes, n.root = m.root) ∧
      (n.root.toNat + n.capacity.toNat = root.toNat + capacity.toNat ∨
        ∃ m ∈ nodes, n.root.toNat + n.capacity.toNat = m.root.toNat + m.capacity.toNat) := by
    intro n hn
    obtain ⟨hr, he⟩ := hBlock n hn
    refine ⟨hr.imp id fun ⟨m, hm, h⟩ => ⟨m, hAboveMem m hm, h⟩,
      he.imp id fun ⟨m, hm, h⟩ => ⟨m, hAboveMem m hm, h⟩⟩
  unfold insertFree
  split
  · exact hLift
  · rename_i p hLast
    have hp : p ∈ nodes := by
      rw [hSplit]
      exact List.mem_append_left _ (List.mem_of_getLast? hLast)
    have hEnds : ∀ n ∈ joinNodes { root, capacity } (aboveNodes root nodes),
        n.root.toNat + n.capacity.toNat < 4294967296 := fun n hn => by
      rcases (hLift n hn).2 with h | ⟨m, hm, h⟩
      · omega
      · have := hNodes m hm
        omega
    have hOuter := joinNodes_cover (block := p) (hNodes p hp) hEnds
    intro n hn
    rcases List.mem_append.mp hn with hPre | hJoin
    · have hn : n ∈ nodes := by
        rw [hSplit]
        exact List.mem_append_left _ (List.dropLast_subset _ hPre)
      exact ⟨Or.inr ⟨n, hn, rfl⟩, Or.inr ⟨n, hn, rfl⟩⟩
    · obtain ⟨hr, he⟩ := hOuter n hJoin
      refine ⟨?_, ?_⟩
      · rcases hr with h | ⟨m, hm, h⟩
        · exact Or.inr ⟨p, hp, h⟩
        · rcases (hLift m hm).1 with h' | ⟨m', hm', h'⟩
          · exact Or.inl (h.trans h')
          · exact Or.inr ⟨m', hm', h.trans h'⟩
      · rcases he with h | ⟨m, hm, h⟩
        · exact Or.inr ⟨p, hp, h⟩
        · rcases (hLift m hm).2 with h' | ⟨m', hm', h'⟩
          · exact Or.inl (h.trans h')
          · exact Or.inr ⟨m', hm', h.trans h'⟩

/-- A region apart from the freed block and from every free block is apart from
every block of the list after the release. -/
theorem insertFree_apart {root capacity : UInt64} {nodes : List FreeNode} {region : Nat × Nat}
    (h48 : 48 ≤ root.toNat) (h32 : root.toNat + capacity.toNat < 4294967296)
    (hNodes : ∀ n ∈ nodes, 48 ≤ n.root.toNat ∧ n.root.toNat + n.capacity.toNat < 4294967296)
    (hSize : 0 < region.2)
    (hBlock : regionsDisjoint region (root.toNat - 48, 48 + capacity.toNat))
    (hApart : ∀ n ∈ nodes, regionsDisjoint region n.region) :
    ∀ n ∈ insertFree root capacity nodes, regionsDisjoint region n.region := by
  have hSplit := nodes_split root nodes
  have hAboveMem : ∀ n ∈ aboveNodes root nodes, n ∈ nodes := fun n hn => by
    rw [hSplit]
    exact List.mem_append_right _ hn
  have hInner := joinNodes_apart (block := { root, capacity }) (region := region) h48 h32
    (fun n hn => hNodes n (hAboveMem n hn)) hSize hBlock (fun n hn => hApart n (hAboveMem n hn))
  unfold insertFree
  split
  · exact hInner
  · rename_i p hLast
    have hp : p ∈ nodes := by
      rw [hSplit]
      exact List.mem_append_left _ (List.mem_of_getLast? hLast)
    intro n hn
    rcases List.mem_append.mp hn with hPre | hJoin
    · exact hApart n (by rw [hSplit]; exact List.mem_append_left _ (List.dropLast_subset _ hPre))
    · exact joinNodes_apart (hNodes p hp).1 (hNodes p hp).2
        (joinNodes_bounds h48 h32 fun n hn => hNodes n (hAboveMem n hn)) hSize (hApart p hp)
        hInner n hJoin

end Project.Runtime
