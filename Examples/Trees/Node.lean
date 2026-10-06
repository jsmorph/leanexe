import Examples.Trees.Encode
import Project.IR.Recursion
import Project.Pipeline.Records

/-! Facts about a node of a `KeyTree` that code consumes: its blocks, the premises of calls on its
children, and the record rebuilt from the children's results by three slot stores. -/

namespace Examples.Trees

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Trees

/-- The blocks of a node: its record's, then its subtrees'. -/
theorem blocks_node (store : Store Unit) (p k : UInt64) (l r : KeyTree) :
    Node.blocks store p (encode (.node l k r)) = block store p ::
      (Node.blocks store (store.mem.read64 (slotAddress p 0)) (encode l) ++
        Node.blocks store (store.mem.read64 (slotAddress p 2)) (encode r)) := by
  simp [encode, Node.blocks, slotsBlocks]

/-- The consumed blocks of a moved tree are its blocks. -/
theorem gone_eq (store : Store Unit) (p : UInt64) (t : KeyTree) :
    (Represent.moves store [.i64 p] (Moved.mk t)).map (block store) =
      Node.blocks store p (encode t) :=
  Node.pointers_blocks store p (encode t)

/-- The bound at the three stores of a node whose children the code rebuilds in turn: the
root's block, kept by both rebuilds, is a region of `heap2`, which lies in `store2`'s
memory. -/
theorem node_bound {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {p k q1 q2 : UInt64} {l r ml mr : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (h1 : heap.Rebuilt initial
      ((Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)).map
        (block initial)) heap1 store1 q1 (Encode.encode ml))
    (h2 : heap1.Rebuilt store1
      ((Represent.moves store1 [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r)).map
        (block store1)) heap2 store2 q2 (Encode.encode mr)) :
    p.toNat + 24 ≤ store2.mem.pages * 65536 := by
  obtain ⟨p', hp, hOwned, hDisjoint⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  rw [gone_eq] at h1 h2
  obtain ⟨hHead, -, -, hr, -⟩ := hOwned
  simp only [Nat.zero_add, Nat.reduceAdd] at hr
  change (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint at hDisjoint
  rw [blocks_node] at hDisjoint
  obtain ⟨hP0, hPlr⟩ := List.pairwise_cons.mp hDisjoint
  obtain ⟨-, -, hlr⟩ := List.pairwise_append.mp hPlr
  obtain ⟨-, hReg1, -⟩ := h1.region _ hHead.region (block_pos initial p)
    fun b hb => hP0 b (List.mem_append_left _ hb)
  obtain ⟨-, hrBlocks1, -⟩ := h1.keepNode hr fun b hb g hg => regionsDisjoint_symm (hlr g hg b hb)
  have hIn := h2.inMemory hReg1 (block_pos initial p) fun b hb => by
    rw [hrBlocks1] at hb
    exact hP0 b (List.mem_append_right _ hb)
  have hBase := hHead.base
  have hRoom := hHead.capacity
  simp only [List.length_cons, List.length_nil, block] at hRoom hIn
  omega

/-- The premises of the first self-call, from the internal function's own premises. -/
theorem node_call1 {heap : Heap} {initial : Store Unit} {p k : UInt64} {l r : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r))) :
    Represent.borrowed heap initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l) ∧
      Separate initial
        (Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l))
        (Represent.reads initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)) := by
  obtain ⟨p', hp, hOwned, hDisjoint⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  obtain ⟨-, hl, -, -, -⟩ := hOwned
  change (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint at hDisjoint
  rw [blocks_node] at hDisjoint
  have hPl := (List.pairwise_append.mp (List.pairwise_cons.mp hDisjoint).2).1
  refine ⟨⟨_, rfl, hl, hPl⟩, ?_, fun _ h => nomatch h⟩
  rw [gone_eq]
  exact hPl

/-- The premises of the second self-call, from the first call's result. -/
theorem node_call2 {heap heap1 : Heap} {initial store1 : Store Unit} {p k q1 : UInt64}
    {l r ml : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (h1 : heap.Rebuilt initial
      ((Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)).map
        (block initial)) heap1 store1 q1 (Encode.encode ml)) :
    Represent.borrowed heap1 store1 [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r) ∧
      Separate store1
        (Represent.moves store1 [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r))
        (Represent.reads initial [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r)) := by
  obtain ⟨p', hp, hOwned, hDisjoint⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  obtain ⟨-, -, -, hr, -⟩ := hOwned
  simp only [Nat.zero_add, Nat.reduceAdd] at hr
  change (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint at hDisjoint
  rw [blocks_node] at hDisjoint
  obtain ⟨-, hPr, hlr⟩ := List.pairwise_append.mp (List.pairwise_cons.mp hDisjoint).2
  rw [gone_eq] at h1
  obtain ⟨hr1, hBlocks1, -⟩ := h1.keepNode hr fun b hb g hg => regionsDisjoint_symm (hlr g hg b hb)
  have hPr1 : (Node.blocks store1 (initial.mem.read64 (slotAddress p 2)) (encode r)).Pairwise
      regionsDisjoint := by
    rw [hBlocks1]; exact hPr
  refine ⟨⟨_, rfl, hr1, hPr1⟩, ?_, fun _ h => nomatch h⟩
  rw [gone_eq]
  exact hPr1

/-- The node case: the record rebuilt from the two calls' results and the three slot writes. -/
theorem node_rebuilt {heap heap1 heap2 : Heap} {initial store1 store2 final : Store Unit}
    {p k k' q1 q2 : UInt64} {l r ml mr : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (h1 : heap.Rebuilt initial
      ((Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)).map
        (block initial)) heap1 store1 q1 (Encode.encode ml))
    (h2 : heap1.Rebuilt store1
      ((Represent.moves store1 [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r)).map
        (block store1)) heap2 store2 q2 (Encode.encode mr))
    (hWrites : Memory.WritesRange store2 final p.toNat (p.toNat + 24))
    (hq1 : final.mem.read64 (slotAddress p 0) = q1)
    (hk : final.mem.read64 (slotAddress p 1) = k')
    (hq2 : final.mem.read64 (slotAddress p 2) = q2) :
    heap.Rebuilt initial
      ((Represent.moves initial [.i64 p] (Moved.mk (KeyTree.node l k r))).map (block initial))
      heap2 final p (Encode.encode (KeyTree.node ml k' mr)) := by
  obtain ⟨p', hp, hOwned, hDisjoint⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  rw [gone_eq] at h1 h2 ⊢
  exact Heap.Rebuilt.node hOwned hDisjoint h1 h2 hWrites hq1 hk hq2

/-- The three slot stores of the code, in order, write only the record's slots. -/
theorem writes3 (store : Store Unit) (p a b c : UInt64) (hAddress : p.toNat + 24 < 4294967296) :
    Memory.WritesRange store
      { store with
        mem := (((store.mem.write64 (slotAddress p 0) a).write64 (slotAddress p 1) b).write64
          (slotAddress p 2) c) } p.toNat (p.toNat + 24) := by
  have h0 := slotAddress_toNat (p := p) (i := 0) (by omega)
  have h1 := slotAddress_toNat (p := p) (i := 1) (by omega)
  have h2 := slotAddress_toNat (p := p) (i := 2) (by omega)
  exact ((Memory.WritesRange.write64 store _ a _ _ (by omega) (by omega)).trans
    (Memory.WritesRange.write64 _ _ b _ _ (by omega) (by omega))).trans
    (Memory.WritesRange.write64 _ _ c _ _ (by omega) (by omega))

/-- The children of an owned node with disjoint blocks are owned with disjoint blocks. -/
theorem node_children {heap : Heap} {store : Store Unit} {p k : UInt64} {l r : KeyTree}
    (h : NodeOwned heap store p (encode (.node l k r)))
    (hd : (Node.blocks store p (encode (.node l k r))).Pairwise regionsDisjoint) :
    NodeOwned heap store (store.mem.read64 (slotAddress p 0)) (encode l) ∧
      (Node.blocks store (store.mem.read64 (slotAddress p 0)) (encode l)).Pairwise
        regionsDisjoint ∧
      NodeOwned heap store (store.mem.read64 (slotAddress p 2)) (encode r) ∧
      (Node.blocks store (store.mem.read64 (slotAddress p 2)) (encode r)).Pairwise
        regionsDisjoint := by
  obtain ⟨-, hl, -, hr, -⟩ := h
  rw [blocks_node] at hd
  obtain ⟨hPl, hPr, -⟩ := List.pairwise_append.mp (List.pairwise_cons.mp hd).2
  simp only [Nat.zero_add, Nat.reduceAdd] at hr
  exact ⟨hl, hPl, hr, hPr⟩

/-- A rebuilt tree paired with a word is the owned pair, with the rebuild's frame. -/
theorem Heap.Rebuilt.wordPair {heap heap' : Heap} {initial store : Store Unit}
    {gone : List (Nat × Nat)} {w q : UInt64} {u : KeyTree}
    (h : heap.Rebuilt initial gone heap' store q (encode u)) :
    Represent.owned heap' store [.i64 w, .i64 q] (w, u) ∧
      heap.Keeps initial gone heap' store (Represent.blocks store [.i64 w, .i64 q] (w, u)) :=
  ⟨⟨[.i64 w], [.i64 q], rfl, rfl, ⟨q, rfl, h.owned, h.disjoint⟩, fun _ hb => nomatch hb⟩,
    Heap.Keeps.mono h.region (fun _ hb => hb) fun b hb => by
      simp [Represent.blocks, Represent.width, Scalar.values] at hb
      exact hb⟩

end Examples.Trees
