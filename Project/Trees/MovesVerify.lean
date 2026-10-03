import Project.Trees.Moves
import Project.Trees.Encode
import Project.IR.Recursion
import Project.IR.Release
import Project.Pipeline.Records
import Project.Encoding.RoundTrip

/-! The functions in `treeMoves.module` consume their tree and compute their Lean definitions
exactly.  `KeyTree.setKey` writes the new key into the root's record and returns the record;
`KeyTree.incr` is an entry and an internal function that recurses with a depth parameter and
rewrites every record in place. -/

namespace Project.Trees

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Trees

/-- `setKey` with its two arguments as one pair, the tree consumed. -/
def setKeyMoved (x : UInt64 × Moved KeyTree) : KeyTree := KeyTree.setKey x.1 x.2.val

theorem setKey_implements : Implements treeMoves.module 2 setKeyMoved := by
  refine Func.implements_moves treeMoves.funcs 0 treeMoves.setKey.ir "setKey" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨k, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - -
  have hMoves : Represent.moves initial (Scalar.values k ++ [.i64 p]) (k, Moved.mk t) =
      Node.pointers initial p (encode t) := rfl
  rw [hMoves]
  rw [show Scalar.values k ++ [Value.i64 p] = [.i64 k, .i64 p] from rfl]
  let start : State := { params := [.i64 k, .i64 p], locals := List.replicate 4 (.i64 0) }
  show Triple _ (.ite (.eq (.get 1) (.const 0)) (.assign 2 (.const 0))
      (.seq (.load .u64 3 (.bin .add (.get 1) (.const 0)))
        (.seq (.load .u64 4 (.bin .add (.get 1) (.const 8)))
          (.seq (.load .u64 5 (.bin .add (.get 1) (.const 16)))
            (.seq (.store (.bin .add (.get 1) (.const 8)) (.get 0)) (.assign 2 (.get 1))))))) 6
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      refine ⟨0, start, start, rfl, rfl, heap, hHeap, rfl, [.i64 0], start,
        by simp [treeMoves.setKey.ir, Func.scratch, Expr.evalResults, Expr.eval, start, State.get],
        ⟨0, rfl, rfl, .nil⟩, fun _ hg _ _ => ⟨fun _ _ _ => rfl, hg, fun b hb => ?_⟩⟩
      change b ∈ Node.blocks _ 0 .null at hb
      cases hb
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l key r =>
    let slots : List Slot := [.child (encode l), .word key, .child (encode r)]
    have hRecord : NodeOwned heap initial p (.record slots) := hOwned
    obtain ⟨hWrites, hAt, hOwned', hBlocks⟩ :=
      NodeOwned.writeWord (i := 1) (w := k) hHeap hRecord hDisjoint ⟨key, rfl⟩
    have hResult :
        Encode.encode (setKeyMoved (k, ⟨.node l key r⟩)) = .record (slots.set 1 (.word k)) := rfl
    obtain ⟨hHead, -, hKey, -, -⟩ := hRecord
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [slots, List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let ps : List Value := [.i64 k, .i64 p]
    let s1 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 0, .i64 0] }
    let s2 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 key, .i64 0] }
    let s3 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 key, .i64 pr] }
    let s4 : State := { params := ps, locals := [.i64 p, .i64 pl, .i64 key, .i64 pr] }
    let final : Store Unit := { initial with mem := initial.mem.write64 (slotAddress p 1) k }
    have hRoot : p ∈ Node.pointers initial p (encode (.node l key r)) := by
      simp [encode, Node.pointers]
    -- Bytes of a region apart from the root's block keep their values.
    have hKeep : ∀ r : Nat × Nat, regionsDisjoint r (block initial p) →
        ∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = initial.mem.bytes a :=
      fun r hr a hLow hHigh => hWrites.2.2 a (by
        simp only [regionsDisjoint, block] at hr
        omega)
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = final ∧ st = s3) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, ?_, rfl, rfl⟩
        rw [h0]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hKey]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, ?_, rfl, rfl⟩
        rw [h2]
        rfl
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s3, k, s3, rfl, rfl, by rw [h1, hs1]; omega, ?_⟩
        rw [h1]
        exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p, s3, s4, rfl, rfl, heap, hAt, rfl, [.i64 p], s4,
          by simp [treeMoves.setKey.ir, Func.scratch, Expr.evalResults, Expr.eval, State.get, s4, ps],
          ⟨p, rfl, hResult ▸ hOwned', by rw [hResult, hBlocks]; exact hDisjoint⟩,
          fun g hg _ hApart => ⟨hKeep g (hApart _ (List.mem_map_of_mem hRoot)), hg, fun b hb => ?_⟩⟩
        change b ∈ Node.blocks final p (Encode.encode (setKeyMoved (k, ⟨.node l key r⟩))) at hb
        rw [hResult, hBlocks] at hb
        exact hApart b (by rw [Node.pointers_blocks]; exact hb)
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

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

/-- The bound at `incr_rec`'s three stores: the root's block, kept by both
calls, is a region of `heap2`, which lies in `store2`'s memory. -/
theorem incr_bound {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {p k q1 q2 : UInt64} {l r : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (h1 : heap.Rebuilt initial
      ((Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)).map
        (block initial)) heap1 store1 q1 (Encode.encode (KeyTree.incr l)))
    (h2 : heap1.Rebuilt store1
      ((Represent.moves store1 [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r)).map
        (block store1)) heap2 store2 q2 (Encode.encode (KeyTree.incr r))) :
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

/-- The bound at `insert_rec`'s store into slot 0. -/
theorem insertLeft_bound {heap heap1 : Heap} {initial store1 : Store Unit} {p k q1 x : UInt64}
    {l r : KeyTree} (hOwned : NodeOwned heap initial p (encode (.node l k r)))
    (hDisjoint : (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint)
    (h1 : heap.Rebuilt initial (Node.blocks initial (initial.mem.read64 (slotAddress p 0))
      (encode l)) heap1 store1 q1 (encode (KeyTree.insert x l))) :
    p.toNat + 24 ≤ store1.mem.pages * 65536 := by
  obtain ⟨hHead, -, -, -, -⟩ := hOwned
  rw [blocks_node] at hDisjoint
  have hIn := h1.inMemory hHead.region (block_pos initial p)
    fun b hb => (List.pairwise_cons.mp hDisjoint).1 b (List.mem_append_left _ hb)
  have hBase := hHead.base
  have hRoom := hHead.capacity
  simp only [List.length_cons, List.length_nil, block] at hRoom hIn
  omega

/-- The bound at `insert_rec`'s store into slot 2, and at the stores after
the release in `dropRight` and `trim`, where the result is the null pointer. -/
theorem right_bound {heap heap2 : Heap} {initial store2 : Store Unit} {p k q2 : UInt64}
    {l r : KeyTree} {n : Node} (hOwned : NodeOwned heap initial p (encode (.node l k r)))
    (hDisjoint : (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint)
    (h2 : heap.Rebuilt initial (Node.blocks initial (initial.mem.read64 (slotAddress p 2))
      (encode r)) heap2 store2 q2 n) :
    p.toNat + 24 ≤ store2.mem.pages * 65536 := by
  obtain ⟨hHead, -, -, -, -⟩ := hOwned
  rw [blocks_node] at hDisjoint
  have hIn := h2.inMemory hHead.region (block_pos initial p)
    fun b hb => (List.pairwise_cons.mp hDisjoint).1 b (List.mem_append_right _ hb)
  have hBase := hHead.base
  have hRoom := hHead.capacity
  simp only [List.length_cons, List.length_nil, block] at hRoom hIn
  omega

/-- The premises of the first self-call, from the internal function's own premises. -/
theorem incr_call1 {heap : Heap} {initial : Store Unit} {p k : UInt64} {l r : KeyTree}
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
theorem incr_call2 {heap heap1 : Heap} {initial store1 : Store Unit} {p k q1 : UInt64}
    {l r : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (h1 : heap.Rebuilt initial
      ((Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)).map
        (block initial)) heap1 store1 q1 (Encode.encode (KeyTree.incr l))) :
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
theorem incr_node {heap heap1 heap2 : Heap} {initial store1 store2 final : Store Unit}
    {p k q1 q2 : UInt64} {l r : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (h1 : heap.Rebuilt initial
      ((Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)).map
        (block initial)) heap1 store1 q1 (Encode.encode (KeyTree.incr l)))
    (h2 : heap1.Rebuilt store1
      ((Represent.moves store1 [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r)).map
        (block store1)) heap2 store2 q2 (Encode.encode (KeyTree.incr r)))
    (hWrites : Memory.WritesRange store2 final p.toNat (p.toNat + 24))
    (hq1 : final.mem.read64 (slotAddress p 0) = q1)
    (hk : final.mem.read64 (slotAddress p 1) = k + 1)
    (hq2 : final.mem.read64 (slotAddress p 2) = q2) :
    heap.Rebuilt initial
      ((Represent.moves initial [.i64 p] (Moved.mk (KeyTree.node l k r))).map (block initial))
      heap2 final p (Encode.encode (KeyTree.incr (.node l k r))) := by
  obtain ⟨p', hp, hOwned, hDisjoint⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  rw [gone_eq] at h1 h2 ⊢
  exact Heap.Rebuilt.node hOwned hDisjoint h1 h2 hWrites hq1 hk hq2

/-- The leaf case. -/
theorem incr_leaf {heap : Heap} {initial : Store Unit} {p : UInt64} (hHeap : heap.At initial)
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk KeyTree.leaf)) :
    p = 0 ∧ heap.Rebuilt initial
      ((Represent.moves initial [.i64 p] (Moved.mk KeyTree.leaf)).map (block initial))
      heap initial 0 (Encode.encode (KeyTree.incr .leaf)) := by
  obtain ⟨p', hp, hOwned, -⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  exact ⟨hOwned, Heap.Rebuilt.null hHeap⟩

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

/-- `incr` with its argument consumed. -/
def incrMoved (t : Moved KeyTree) : KeyTree := t.val.incr

/-- The internal function of `incr`, at any depth, consumes its tree and returns the tree with
every key incremented, rebuilt in the same records. -/
theorem incr_rec : ∀ t, Rebuilds (compile treeMoves.funcs) (2 + 12) incrMoved t := by
  refine Func.rebuildRecursion treeMoves.funcs 12 treeMoves.incr.rec.ir "incr.rec" rfl incrMoved
    (fun t => sizeOf t.val) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl)
    fun ⟨t⟩ ih heap initial vs d hHeap hArgs _ hCap => ?_
  have hArg := hArgs
  obtain ⟨p, rfl, hOwned, -⟩ := hArgs
  have hCallee : (compile treeMoves.funcs).funcs[2 + 12 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.incr.rec.ir.function (2 + 12)) := compile_funcs (i := 12) rfl
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 6 (.i64 0) }
  have hStart : treeMoves.incr.rec.ir.state ([.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + 12) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call (2 + 12) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [7])
                  (.seq (.store (.bin .add (.get 0) (.const 0)) (.get 6))
                    (.seq (.store (.bin .add (.get 0) (.const 8)) (.bin .add (.get 4) (.const 1)))
                      (.seq (.store (.bin .add (.get 0) (.const 16)) (.get 7))
                        (.assign 2 (.get 0)))))))))))) 8
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
    ((Stmt.ite_spec (PThen := fun _ _ => True) (PElse := fun s st => s = initial ∧ st = start)
      Stmt.abort_spec (Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h)).mono ?_
        fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    refine ⟨decide ((999 : UInt64) < d), start, by simp [Expr.eval, start, State.get], ?_⟩
    split <;> trivial
  cases t with
  | leaf =>
    obtain ⟨rfl, hLeaf⟩ := incr_leaf hHeap hArg
    let s1 : State := { params := [.i64 0, .i64 d], locals := List.replicate 6 (.i64 0) }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, s1, rfl, rfl, heap, 0, s1, rfl, hLeaf⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hHead, -, hk, -, -⟩ := hOwned
    simp only [Nat.zero_add] at hk
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let ps : List Value := [.i64 p, .i64 d]
    let s1 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 0, .i64 0, .i64 0, .i64 0] }
    let s2 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 0, .i64 0, .i64 0] }
    let s3 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 0, .i64 0] }
    let s4 (a : UInt64) : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 0] }
    let s5 (a b : UInt64) : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] }
    let s6 (a b : UInt64) : State :=
      { params := ps, locals := [.i64 p, .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] }
    obtain ⟨hB1, hSep1⟩ := incr_call1 hArg
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap1 : Heap) (a : UInt64), st = s4 a ∧
          heap.Rebuilt initial ((Represent.moves initial [.i64 pl] (Moved.mk l)).map
            (block initial)) heap1 s a (Encode.encode (incrMoved ⟨l⟩))) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih ⟨l⟩ (by simp; omega)) hHeap hB1
          hSep1 hCap (d := d + 1) rfl fun a => by simp [State.setAll, State.set?, s3, s4, ps]
      refine Triple.of_forall fun store1 st ⟨heap1, a, hst, hR1⟩ => ?_
      subst hst
      obtain ⟨hB2, hSep2⟩ := incr_call2 hArg hR1
      refine Stmt.seq_spec (M := fun s st => ∃ (heap2 : Heap) (b : UInt64), st = s5 a b ∧
          heap1.Rebuilt store1 ((Represent.moves store1 [.i64 pr] (Moved.mk r)).map
            (block store1)) heap2 s b (Encode.encode (incrMoved ⟨r⟩))) ?_ ?_
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih ⟨r⟩ (by simp)) hR1.at_ hB2
          hSep2 (memoryCap_le_of_caps hR1.caps hCap) (d := d + 1) rfl
          fun b => by simp [State.setAll, State.set?, s4, s5, ps]
      refine Triple.of_forall fun store2 st ⟨heap2, b, hst, hR2⟩ => ?_
      subst hst
      let w0 := store2.mem.write64 (slotAddress p 0) a
      let w1 := w0.write64 (slotAddress p 1) (k + 1)
      let w2 := w1.write64 (slotAddress p 2) b
      refine Stmt.seq_spec (M := fun s st => s = { store2 with mem := w0 } ∧ st = s5 a b) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w1 } ∧ st = s5 a b) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w2 } ∧ st = s5 a b) ?_ ?_
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, s5 a b, a, s5 a b, rfl, rfl, ?_, ?_⟩
        · rw [h0, hs0]
          have := incr_bound hArg hR1 hR2
          omega
        · rw [h0]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s5 a b, k + 1, s5 a b, rfl, rfl, ?_, ?_⟩
        · rw [h1, hs1]
          have := incr_bound hArg hR1 hR2
          simp only [w0, Wasm.Mem.write64_pages]
          omega
        · rw [h1]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s5 a b, b, s5 a b, rfl, rfl, ?_, ?_⟩
        · rw [h2, hs2]
          have := incr_bound hArg hR1 hR2
          simp only [w1, w0, Wasm.Mem.write64_pages]
          omega
        · rw [h2]
          exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        have hRead0 : w2.read64 (slotAddress p 0) = a := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega),
            Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead1 : w2.read64 (slotAddress p 1) = k + 1 := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead2 : w2.read64 (slotAddress p 2) = b := Memory.read64_write64 _ _ _
        exact ⟨p, s5 a b, s6 a b, rfl, rfl, heap2, p, s6 a b,
          rfl, incr_node hArg hR1 hR2 (writes3 store2 p a (k + 1) b (by omega)) hRead0 hRead1 hRead2⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem incr_implements : Implements treeMoves.module 3 incrMoved :=
  Func.entry_rebuilds treeMoves.funcs 1 treeMoves.incr.ir "incr" rfl incrMoved
    (g := treeMoves.incr.rec.ir.function (2 + 12)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl
    rfl (compile_funcs (i := 12) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, treeMoves.incr.ir, Func.locals]⟩)
    incr_rec

/-- The consumed blocks of a word and a moved tree are the tree's blocks. -/
theorem pair_gone (store : Store Unit) (x q : UInt64) (t : KeyTree) :
    (Represent.moves store [.i64 x, .i64 q] (x, Moved.mk t)).map (block store) =
      Node.blocks store q (encode t) :=
  Node.pointers_blocks store q (encode t)

/-- A word and an owned tree with disjoint blocks are a borrowed pair with separate moves. -/
theorem pair_args {heap : Heap} {store : Store Unit} {x q : UInt64} {t : KeyTree}
    (h : NodeOwned heap store q (encode t))
    (hd : (Node.blocks store q (encode t)).Pairwise regionsDisjoint) :
    Represent.borrowed heap store [.i64 x, .i64 q] (x, Moved.mk t) ∧
      Separate store (Represent.moves store [.i64 x, .i64 q] (x, Moved.mk t))
        (Represent.reads store [.i64 x, .i64 q] (x, Moved.mk t)) := by
  refine ⟨⟨[.i64 x], [.i64 q], rfl, rfl, q, rfl, h, hd⟩, ?_, fun _ h => nomatch h⟩
  rw [pair_gone]
  exact hd

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

/-- A new record holding a null pointer, the word `x`, and a null pointer is the one-node tree
of `x`. -/
theorem newLeafNode {heap heap' : Heap} {initial store : Store Unit} {ptr x : UInt64}
    (hNew : heap.NewRecord initial heap' store ptr [0, x, 0] 5) :
    heap.Built initial heap' store ptr (encode (.node .leaf x .leaf)) := by
  have h0 : store.mem.read64 (slotAddress ptr 0) = 0 := hNew.slots 0 (by simp)
  have h2 : store.mem.read64 (slotAddress ptr 2) = 0 := hNew.slots 2 (by simp)
  have hBlocks : Node.blocks store ptr (encode (.node .leaf x .leaf)) = [block store ptr] := by
    simp [encode, Node.blocks, slotsBlocks]
  refine ⟨hNew.at_, ⟨hNew.header _ rfl rfl, h0, hNew.slots 1 (by simp), h2, trivial⟩,
    by rw [hBlocks]; exact List.pairwise_singleton _ _, fun r hr => ?_, hNew.caps⟩
  obtain ⟨hBytes, hRegion, hApart⟩ := hNew.region r hr
  refine ⟨hBytes, hRegion, fun b hb => ?_⟩
  rw [hBlocks, List.mem_singleton] at hb
  subst hb
  exact hApart

/-- `insert`'s path into the left child: the call's result stored into slot 0. -/
theorem insert_left {heap heap1 : Heap} {initial store1 : Store Unit} {p x k q1 : UInt64}
    {l r : KeyTree} (hOwned : NodeOwned heap initial p (encode (.node l k r)))
    (hDisjoint : (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint)
    (h1 : heap.Rebuilt initial (Node.blocks initial (initial.mem.read64 (slotAddress p 0))
      (encode l)) heap1 store1 q1 (encode (KeyTree.insert x l))) :
    heap.Rebuilt initial (Node.blocks initial p (encode (.node l k r))) heap1
      { store1 with mem := store1.mem.write64 (slotAddress p 0) q1 } p
      (.record [.child (encode (KeyTree.insert x l)), .word k, .child (encode r)]) := by
  obtain ⟨-, -, hr, hPr⟩ := node_children hOwned hDisjoint
  have hRecord := hOwned
  obtain ⟨hHead, -, hk, -, -⟩ := hRecord
  have hBase := hHead.base
  have hRoom := hHead.capacity
  have hAddress := hHead.address
  simp only [List.length_cons, List.length_nil] at hRoom
  have hDisjoint' := hDisjoint
  rw [blocks_node] at hDisjoint'
  obtain ⟨hP0, hPlr⟩ := List.pairwise_cons.mp hDisjoint'
  obtain ⟨-, -, hlr⟩ := List.pairwise_append.mp hPlr
  obtain ⟨hBytesP, -, -⟩ := h1.region _ hHead.region (block_pos initial p)
    fun b hb => hP0 b (List.mem_append_left _ hb)
  obtain ⟨hr1, hrBlocks1, -⟩ := h1.keepNode hr fun b hb g hg => regionsDisjoint_symm (hlr g hg b hb)
  have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
  have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
  have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
  have hKeep : ∀ i, 1 ≤ i → i < 3 → (store1.mem.write64 (slotAddress p 0) q1).read64
      (slotAddress p i) = initial.mem.read64 (slotAddress p i) := fun i h1 h3 => by
    have hsi := slotAddress_toNat (p := p) (i := i) (by omega)
    rw [Memory.read64_write64_disjoint _ _ _ _ (by omega)]
    exact Memory.read64_congr _ fun j hj => hBytesP _ (by simp only [block]; omega)
      (by simp only [block]; omega)
  have hRefl := Heap.Rebuilt.refl h1.at_ hr1 (by rw [hrBlocks1]; exact hPr)
  exact Heap.Rebuilt.node hOwned hDisjoint h1 hRefl
    (Memory.WritesRange.write64 _ _ _ _ _ (by omega) (by omega)) (Memory.read64_write64 _ _ _)
    ((hKeep 1 (by omega) (by omega)).trans hk) (hKeep 2 (by omega) (by omega))

/-- `insert`'s path into the right child: the call's result stored into slot 2. -/
theorem insert_right {heap heap2 : Heap} {initial store2 : Store Unit} {p x k q2 : UInt64}
    {l r : KeyTree} (hHeap : heap.At initial)
    (hOwned : NodeOwned heap initial p (encode (.node l k r)))
    (hDisjoint : (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint)
    (h2 : heap.Rebuilt initial (Node.blocks initial (initial.mem.read64 (slotAddress p 2))
      (encode r)) heap2 store2 q2 (encode (KeyTree.insert x r))) :
    heap.Rebuilt initial (Node.blocks initial p (encode (.node l k r))) heap2
      { store2 with mem := store2.mem.write64 (slotAddress p 2) q2 } p
      (.record [.child (encode l), .word k, .child (encode (KeyTree.insert x r))]) := by
  obtain ⟨hl, hPl, -, -⟩ := node_children hOwned hDisjoint
  have hRecord := hOwned
  obtain ⟨hHead, -, hk, -, -⟩ := hRecord
  have hBase := hHead.base
  have hRoom := hHead.capacity
  have hAddress := hHead.address
  simp only [List.length_cons, List.length_nil] at hRoom
  have hDisjoint' := hDisjoint
  rw [blocks_node] at hDisjoint'
  obtain ⟨hP0, -⟩ := List.pairwise_cons.mp hDisjoint'
  obtain ⟨hBytesP, -, -⟩ := h2.region _ hHead.region (block_pos initial p)
    fun b hb => hP0 b (List.mem_append_right _ hb)
  have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
  have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
  have hKeep : ∀ i, i < 2 → (store2.mem.write64 (slotAddress p 2) q2).read64
      (slotAddress p i) = initial.mem.read64 (slotAddress p i) := fun i h2 => by
    have hsi := slotAddress_toNat (p := p) (i := i) (by omega)
    rw [Memory.read64_write64_disjoint _ _ _ _ (by omega)]
    exact Memory.read64_congr _ fun j hj => hBytesP _ (by simp only [block]; omega)
      (by simp only [block]; omega)
  exact Heap.Rebuilt.node hOwned hDisjoint (Heap.Rebuilt.refl hHeap hl hPl) h2
    (Memory.WritesRange.write64 _ _ _ _ _ (by omega) (by omega)) (hKeep 0 (by omega))
    ((hKeep 1 (by omega)).trans hk) (Memory.read64_write64 _ _ _)

/-- `insert` with its tree consumed. -/
def insertMoved (x : UInt64 × Moved KeyTree) : KeyTree := KeyTree.insert x.1 x.2.val

/-- The internal function of `insert`, at any depth, consumes its tree and returns the tree with
the key, rebuilt in the same records and one new record when the key is new. -/
theorem insert_rec : ∀ x, Rebuilds (compile treeMoves.funcs) (2 + 13) insertMoved x := by
  refine Func.rebuildRecursion treeMoves.funcs 13 treeMoves.insert.rec.ir "insert.rec" rfl
    insertMoved (fun x => sizeOf x.2.val) (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl)
    fun ⟨x, ⟨t⟩⟩ ih heap initial vs d hHeap hArgs _ hCap => ?_
  obtain ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ := hArgs
  rw [show Scalar.values x ++ [Value.i64 p] = [.i64 x, .i64 p] from rfl, pair_gone]
  have hCallee : (compile treeMoves.funcs).funcs[2 + 13 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.insert.rec.ir.function (2 + 13)) := compile_funcs (i := 13) rfl
  have hMemory32 : (compile treeMoves.funcs).memIs64 = false := rfl
  have hImports : (compile treeMoves.funcs).imports = [] := rfl
  have hAlloc : (compile treeMoves.funcs).funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 x, .i64 p, .i64 d], locals := List.replicate 9 (.i64 0) }
  have hStart : treeMoves.insert.rec.ir.state ([.i64 x, .i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 2)) .abort .skip)
      (.ite (.eq (.get 1) (.const 0))
        (.seq (.record 4 [.const 0, .get 0, .const 0] 5) (.assign 3 (.get 4)))
        (.seq (.load .u64 5 (.bin .add (.get 1) (.const 0)))
          (.seq (.load .u64 6 (.bin .add (.get 1) (.const 8)))
            (.seq (.load .u64 7 (.bin .add (.get 1) (.const 16)))
              (.seq (.ite (.ltU (.get 0) (.get 6))
                  (.seq (.call (2 + 13) [⟨.u64, .get 0⟩, ⟨.u64, .get 5⟩,
                      ⟨.u64, .bin .add (.get 2) (.const 1)⟩] [9])
                    (.seq (.store (.bin .add (.get 1) (.const 0)) (.get 9)) (.assign 8 (.get 1))))
                  (.seq (.ite (.ltU (.get 6) (.get 0))
                      (.seq (.call (2 + 13) [⟨.u64, .get 0⟩, ⟨.u64, .get 7⟩,
                          ⟨.u64, .bin .add (.get 2) (.const 1)⟩] [11])
                        (.seq (.store (.bin .add (.get 1) (.const 16)) (.get 11))
                          (.assign 10 (.get 1))))
                      (.assign 10 (.get 1)))
                    (.assign 8 (.get 10))))
                (.assign 3 (.get 8)))))))) 12
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
    ((Stmt.ite_spec (PThen := fun _ _ => True) (PElse := fun s st => s = initial ∧ st = start)
      Stmt.abort_spec (Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h)).mono ?_
        fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    refine ⟨decide ((999 : UInt64) < d), start, by simp [Expr.eval, start, State.get], ?_⟩
    split <;> trivial
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) ?_ Triple.of_false).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (Stmt.record_spec hMemory32 hImports hAlloc (by decide)
        (by simp [start]) hHeap hCap (by decide) (by decide) (words := [0, x, 0]) ?_) ?_
      · refine .cons (fun _ st _ => ⟨st, rfl⟩) (.cons (fun _ st hF => ⟨st, ?_⟩)
          (.cons (fun _ st _ => ⟨st, rfl⟩) .nil))
        have h0 : st.get 0 = some (.i64 x) := (hF.get 0 (by decide) (by decide)).trans rfl
        simp [Expr.eval, h0]
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨ptr, hF, hPtr, hNew⟩
        obtain ⟨next, hSet⟩ := State.exists_set? (state := st) (index := 3) (.i64 ptr)
          (by rw [hF.params, hF.locals]; simp [start])
        exact ⟨ptr, st, next, by simp [Expr.eval, hPtr], hSet, _, ptr, next,
          by simp [treeMoves.insert.rec.ir, Func.scratch, Expr.evalResults, Expr.eval,
            State.get_set?_same hSet],
          (newLeafNode hNew).rebuilt _⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hl, hPl, hr, hPr⟩ := node_children hOwned hDisjoint
    have hRecord := hOwned
    obtain ⟨hHead, -, hk, -, -⟩ := hRecord
    simp only [Nat.zero_add] at hk
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let ps : List Value := [.i64 x, .i64 p, .i64 d]
    let s1 : State :=
      { params := ps
        locals := [.i64 0, .i64 0, .i64 pl, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
    let s2 : State :=
      { params := ps
        locals := [.i64 0, .i64 0, .i64 pl, .i64 k, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
    let sf (r3 r8 a r10 c : UInt64) : State :=
      { params := ps, locals := [.i64 r3, .i64 0, .i64 pl, .i64 k, .i64 pr, .i64 r8, .i64 a,
          .i64 r10, .i64 c] }
    let gone := Node.blocks initial p (encode (.node l k r))
    let goal := Encode.encode (insertMoved (x, ⟨.node l k r⟩))
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = sf 0 0 0 0 0) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap' : Heap) (a b c : UInt64), st = sf 0 p a b c ∧
          heap.Rebuilt initial gone heap' s p goal) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, sf 0 0 0 0 0, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = sf 0 0 0 0 0 ∧ x < k)
          (PElse := fun s st => s = initial ∧ st = sf 0 0 0 0 0 ∧ ¬ x < k) ?_ ?_).mono ?_
            fun _ _ h => h
        · -- The key goes left: the call on `l`, then its result into slot 0.
          refine Triple.of_forall fun s st ⟨hs, hst, hlt⟩ => ?_
          subst s st
          obtain ⟨hB1, hSep1⟩ := pair_args (x := x) hl hPl
          refine Stmt.seq_spec (M := fun s st => ∃ (heap1 : Heap) (a : UInt64),
            st = sf 0 0 a 0 0 ∧ heap.Rebuilt initial
              ((Represent.moves initial [.i64 x, .i64 pl] (x, Moved.mk l)).map (block initial))
              heap1 s a (Encode.encode (insertMoved (x, ⟨l⟩)))) ?_ ?_
          · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih (x, ⟨l⟩) (by simp; omega))
              hHeap hB1 hSep1 hCap (d := d + 1) rfl
              fun a => by simp [State.setAll, State.set?, sf, ps]
          refine Triple.of_forall fun store1 st ⟨heap1, a, hst, hR1⟩ => ?_
          subst hst
          rw [pair_gone] at hR1
          refine Stmt.seq_spec (M := fun s st =>
            s = { store1 with mem := store1.mem.write64 (slotAddress p 0) a } ∧
              st = sf 0 0 a 0 0) ?_ ?_
          · refine Stmt.store_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨p + 0, sf 0 0 a 0 0, a, sf 0 0 a 0 0, rfl, rfl, ?_, ?_⟩
            · rw [h0, hs0]
              have := insertLeft_bound hOwned hDisjoint hR1
              omega
            · rw [h0]
              exact ⟨rfl, rfl⟩
          · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            have hGoal : goal = .record [.child (encode (KeyTree.insert x l)), .word k,
                .child (encode r)] := by
              simp [goal, insertMoved, KeyTree.insert, hlt, encode, Encode.encode]
            exact ⟨p, sf 0 0 a 0 0, sf 0 p a 0 0, rfl, rfl, heap1, a, 0, 0, rfl,
              hGoal ▸ insert_left hOwned hDisjoint hR1⟩
        · refine Triple.of_forall fun s st ⟨hs, hst, hlt⟩ => ?_
          subst s st
          refine Stmt.seq_spec (M := fun s st => ∃ (heap' : Heap) (c : UInt64),
            st = sf 0 0 0 p c ∧ heap.Rebuilt initial gone heap' s p goal) ?_ ?_
          · refine (Stmt.ite_spec
              (PThen := fun s st => s = initial ∧ st = sf 0 0 0 0 0 ∧ k < x)
              (PElse := fun s st => s = initial ∧ st = sf 0 0 0 0 0 ∧ ¬ k < x) ?_ ?_).mono ?_
                fun _ _ h => h
            · -- The key goes right: the call on `r`, then its result into slot 2.
              refine Triple.of_forall fun s st ⟨hs, hst, hgt⟩ => ?_
              subst s st
              obtain ⟨hB2, hSep2⟩ := pair_args (x := x) hr hPr
              refine Stmt.seq_spec (M := fun s st => ∃ (heap2 : Heap) (c : UInt64),
                st = sf 0 0 0 0 c ∧ heap.Rebuilt initial
                  ((Represent.moves initial [.i64 x, .i64 pr] (x, Moved.mk r)).map
                    (block initial)) heap2 s c (Encode.encode (insertMoved (x, ⟨r⟩)))) ?_ ?_
              · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih (x, ⟨r⟩) (by simp))
                  hHeap hB2 hSep2 hCap (d := d + 1) rfl
                  fun c => by simp [State.setAll, State.set?, sf, ps]
              refine Triple.of_forall fun store2 st ⟨heap2, c, hst, hR2⟩ => ?_
              subst hst
              rw [pair_gone] at hR2
              refine Stmt.seq_spec (M := fun s st =>
                s = { store2 with mem := store2.mem.write64 (slotAddress p 2) c } ∧
                  st = sf 0 0 0 0 c) ?_ ?_
              · refine Stmt.store_spec.mono ?_ fun _ _ h => h
                rintro s st ⟨rfl, rfl⟩
                refine ⟨p + 16, sf 0 0 0 0 c, c, sf 0 0 0 0 c, rfl, rfl, ?_, ?_⟩
                · rw [h2, hs2]
                  have := right_bound hOwned hDisjoint hR2
                  omega
                · rw [h2]
                  exact ⟨rfl, rfl⟩
              · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
                rintro s st ⟨rfl, rfl⟩
                have hGoal : goal = .record [.child (encode l), .word k,
                    .child (encode (KeyTree.insert x r))] := by
                  simp [goal, insertMoved, KeyTree.insert, hlt, hgt, encode, Encode.encode]
                exact ⟨p, sf 0 0 0 0 c, sf 0 0 0 p c, rfl, rfl, heap2, c, rfl,
                  hGoal ▸ insert_right hHeap hOwned hDisjoint hR2⟩
            · -- The key is present: the tree as it is.
              refine Stmt.assign_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl, hgt⟩
              have hGoal : goal = encode (.node l k r) := by
                simp [goal, insertMoved, KeyTree.insert, hlt, hgt, Encode.encode]
              exact ⟨p, sf 0 0 0 0 0, sf 0 0 0 p 0, rfl, rfl, heap, 0, rfl,
                hGoal ▸ Heap.Rebuilt.refl hHeap hOwned hDisjoint⟩
            · rintro s st ⟨rfl, rfl, -⟩
              refine ⟨decide (k < x), sf 0 0 0 0 0, by simp [Expr.eval, sf, State.get, ps], ?_⟩
              by_cases h : k < x <;> simp [h]
          · refine Triple.of_forall fun s st ⟨heap', c, hst, hR⟩ => ?_
            subst hst
            refine Stmt.assign_spec.mono ?_ fun _ _ h => h
            rintro s' st ⟨rfl, rfl⟩
            exact ⟨p, sf 0 0 0 p c, sf 0 p 0 p c, rfl, rfl, heap', 0, p, c, rfl, hR⟩
        · rintro s st ⟨rfl, rfl⟩
          refine ⟨decide (x < k), sf 0 0 0 0 0, by simp [Expr.eval, sf, State.get, ps], ?_⟩
          by_cases h : x < k <;> simp [h]
      · refine Triple.of_forall fun s st ⟨heap', a, b, c, hst, hR⟩ => ?_
        subst hst
        refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s' st ⟨rfl, rfl⟩
        exact ⟨p, sf 0 p a b c, sf p p a b c, rfl, rfl, heap', p, sf p p a b c, rfl, hR⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem insert_implements : Implements treeMoves.module 4 insertMoved :=
  Func.entry_rebuilds treeMoves.funcs 2 treeMoves.insert.ir "insert" rfl insertMoved
    (g := treeMoves.insert.rec.ir.function (2 + 13))
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) rfl rfl rfl (compile_funcs (i := 13) rfl) rfl
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩
      simp [Expr.evalResults, Expr.eval, Func.state, State.get, Scalar.values])
    (by
      intro params v hLen
      match params, hLen with
      | [a, b], _ =>
        exact ⟨_, rfl, by simp [State.get, Func.state, treeMoves.insert.ir, Func.locals]⟩)
    insert_rec

/-- `leftChild`'s node case over `KeyTree`: the result `encode l` at the old slot-0 pointer,
rebuilt from the consumed blocks of `node l k r`. -/
theorem leftChild_node {heap heap' : Heap} {initial final : Store Unit} {p k : UInt64}
    {l r : KeyTree} (hHeap : heap.At initial)
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r)))
    (hAt : heap'.At final) (hCaps : final.memoryCaps = initial.memoryCaps)
    (hRegion : ∀ q, heap.Region q → 0 < q.2 →
      (∀ b ∈ Node.blocks { initial with mem := initial.mem.write64 (slotAddress p 0) 0 } p
        (.record [.child .null, .word k, .child (encode r)]), regionsDisjoint q b) →
      (∀ a, q.1 ≤ a → a < q.1 + q.2 → final.mem.bytes a =
        ({ initial with mem := initial.mem.write64 (slotAddress p 0) 0 } : Store Unit).mem.bytes a) ∧
        heap'.Region q) :
    heap.Rebuilt initial
      ((Represent.moves initial [.i64 p] (Moved.mk (KeyTree.node l k r))).map (block initial))
      heap' final (initial.mem.read64 (slotAddress p 0)) (Encode.encode l) := by
  obtain ⟨p', hp, hOwned, hDisjoint⟩ := hArg
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hp
  subst hp
  rw [gone_eq]
  exact Heap.Rebuilt.leftChild hHeap hOwned hDisjoint hAt hCaps hRegion

/-- `dropRight` with its tree consumed. -/
def dropRightMoved (t : Moved KeyTree) : KeyTree := t.val.dropRight

theorem dropRight_implements : Implements treeMoves.module 5 dropRightMoved := by
  refine Func.implements_rebuilt treeMoves.funcs 3 treeMoves.dropRight.ir "dropRight" rfl _
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro ⟨t⟩ heap initial _ hHeap ⟨p, rfl, hOwned, hDisjoint⟩ - -
  rw [gone_eq]
  have hImports : (compile treeMoves.funcs).imports = [] := rfl
  have hRelease : (compile treeMoves.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 p], locals := List.replicate 4 (.i64 0) }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.assign 1 (.const 0))
      (.seq (.load .u64 2 (.bin .add (.get 0) (.const 0)))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 8)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 16)))
            (.seq (.release 4)
              (.seq (.store (.bin .add (.get 0) (.const 16)) (.const 0))
                (.assign 1 (.get 0)))))))) 5
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, start, rfl, rfl, heap, 0, start, rfl, Heap.Rebuilt.null hHeap⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨-, -, hr, hPr⟩ := node_children hOwned hDisjoint
    have hRecord := hOwned
    obtain ⟨hHead, -, hk, -, -⟩ := hRecord
    simp only [Nat.zero_add] at hk
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let s1 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 0, .i64 0] }
    let s2 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 0] }
    let s3 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 pr] }
    let s4 : State := { params := [.i64 p], locals := [.i64 p, .i64 pl, .i64 k, .i64 pr] }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => st = s3 ∧ ∃ heap2 : Heap, heap.Rebuilt initial
          (Node.blocks initial pr (encode r)) heap2 s 0 .null) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · exact Stmt.releaseNode_rebuilt hImports hRelease rfl hHeap hr hPr
      refine Triple.of_forall fun store2 st ⟨hst, heap2, hR2⟩ => ?_
      subst hst
      refine Stmt.seq_spec (M := fun s st =>
        s = { store2 with mem := store2.mem.write64 (slotAddress p 2) 0 } ∧ st = s3) ?_ ?_
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s3, 0, s3, rfl, rfl, ?_, ?_⟩
        · rw [h2, hs2]
          have := right_bound hOwned hDisjoint hR2
          omega
        · rw [h2]
          exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p, s3, s4, rfl, rfl, heap2, p, s4, rfl,
          Heap.Rebuilt.dropRight hHeap hOwned hDisjoint hR2⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `leftChild` with its tree consumed. -/
def leftChildMoved (t : Moved KeyTree) : KeyTree := t.val.leftChild

theorem leftChild_implements : Implements treeMoves.module 6 leftChildMoved := by
  refine Func.implements_rebuilt treeMoves.funcs 4 treeMoves.leftChild.ir "leftChild" rfl _
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro ⟨t⟩ heap initial _ hHeap hArg - -
  have hArg' := hArg
  obtain ⟨p, rfl, hOwned, hDisjoint⟩ := hArg'
  have hImports : (compile treeMoves.funcs).imports = [] := rfl
  have hRelease : (compile treeMoves.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 p], locals := List.replicate 4 (.i64 0) }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.assign 1 (.const 0))
      (.seq (.load .u64 2 (.bin .add (.get 0) (.const 0)))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 8)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 16)))
            (.seq (.assign 1 (.get 2))
              (.seq (.store (.bin .add (.get 0) (.const 0)) (.const 0)) (.release 0))))))) 5
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      refine ⟨0, start, start, rfl, rfl, heap, 0, start, rfl, ?_⟩
      rw [gone_eq]
      exact Heap.Rebuilt.null hHeap
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    have hRecord := hOwned
    obtain ⟨hHead, -, hk, -, -⟩ := hRecord
    simp only [Nat.zero_add] at hk
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let s1 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 0, .i64 0] }
    let s2 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 0] }
    let s3 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 pr] }
    let s4 : State := { params := [.i64 p], locals := [.i64 pl, .i64 pl, .i64 k, .i64 pr] }
    let store1 : Store Unit := { initial with mem := initial.mem.write64 (slotAddress p 0) 0 }
    obtain ⟨-, hAt1, hCleared, -, hClearedDisjoint, -, -⟩ :=
      NodeOwned.clearLeft hHeap hOwned hDisjoint
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s4) ?_ <|
        Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s4) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨pl, s3, s4, rfl, rfl, rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, s4, 0, s4, rfl, rfl, by rw [h0, hs0]; omega, ?_⟩
        rw [h0]
        exact ⟨rfl, rfl⟩
      · refine (Stmt.releaseNode_spec hImports hRelease rfl hAt1 hCleared
          hClearedDisjoint).mono (fun _ _ h => h) ?_
        rintro s st ⟨rfl, heap', hAt, hCaps, hRegion⟩
        exact ⟨heap', pl, s4, rfl, leftChild_node hHeap hArg hAt
          hCaps hRegion⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `keepIf` with its two arguments as one pair, the tree consumed. -/
def keepIfMoved (x : UInt64 × Moved KeyTree) : KeyTree := KeyTree.keepIf x.1 x.2.val

theorem keepIf_implements : Implements treeMoves.module 7 keepIfMoved := by
  refine Func.implements_rebuilt treeMoves.funcs 5 treeMoves.keepIf.ir "keepIf" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨c, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - -
  rw [show Scalar.values c ++ [Value.i64 p] = [.i64 c, .i64 p] from rfl, pair_gone]
  have hImports : (compile treeMoves.funcs).imports = [] := rfl
  have hRelease : (compile treeMoves.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 c, .i64 p], locals := [.i64 0] }
  let sElse : State := { params := [.i64 c, .i64 p], locals := [.i64 0] }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.get 1))
      (.seq (.assign 2 (.const 0)) (.release 1))) 3
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start ∧ c = 0)
    (PElse := fun s st => s = initial ∧ st = start ∧ c ≠ 0) ?_ ?_).mono ?_ fun _ _ h => h
  · -- The tree, kept.
    refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨rfl, rfl, hc⟩
    have hv : keepIfMoved (c, ⟨t⟩) = t := by simp [keepIfMoved, KeyTree.keepIf, hc]
    refine ⟨p, start, { params := [.i64 c, .i64 p], locals := [.i64 p] }, rfl, rfl, heap, p, _,
      rfl, ?_⟩
    rw [hv]
    exact Heap.Rebuilt.refl hHeap hOwned hDisjoint
  · -- A leaf, and the tree released.
    refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = sElse ∧ c ≠ 0) ?_ ?_
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl, hc⟩
      exact ⟨0, start, sElse, rfl, rfl, rfl, rfl, hc⟩
    · apply Triple.of_forall
      rintro s st ⟨rfl, rfl, hc⟩
      refine (Stmt.releaseNode_rebuilt hImports hRelease rfl hHeap hOwned hDisjoint).mono
        (fun _ _ h => h) ?_
      rintro s' st' ⟨rfl, heap', hR⟩
      have hv : keepIfMoved (c, ⟨t⟩) = .leaf := by simp [keepIfMoved, KeyTree.keepIf, hc]
      refine ⟨heap', 0, sElse, rfl, ?_⟩
      rw [hv]
      exact hR
  · rintro s st ⟨rfl, rfl⟩
    by_cases hc : c = 0
    · exact ⟨true, start, by simp [Expr.eval, start, State.get, hc], rfl, rfl, hc⟩
    · exact ⟨false, start, by simp [Expr.eval, start, State.get, hc], rfl, rfl, hc⟩

/-- `trim` with its tree consumed. -/
def trimMoved (t : Moved KeyTree) : KeyTree := t.val.trim

theorem trim_implements : Implements treeMoves.module 8 trimMoved := by
  refine Func.implements_rebuilt treeMoves.funcs 6 treeMoves.trim.ir "trim" rfl _
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro ⟨t⟩ heap initial _ hHeap hArg - -
  have hArg' := hArg
  obtain ⟨p, rfl, hOwned, hDisjoint⟩ := hArg'
  have hImports : (compile treeMoves.funcs).imports = [] := rfl
  have hRelease : (compile treeMoves.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 p], locals := List.replicate 5 (.i64 0) }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.assign 1 (.const 0))
      (.seq (.load .u64 2 (.bin .add (.get 0) (.const 0)))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 8)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 16)))
            (.seq (.ite (.eq (.get 3) (.const 0))
                (.seq (.assign 5 (.get 2))
                  (.seq (.store (.bin .add (.get 0) (.const 0)) (.const 0)) (.release 0)))
                (.seq (.release 4)
                  (.seq (.store (.bin .add (.get 0) (.const 16)) (.const 0)) (.assign 5 (.get 0)))))
              (.assign 1 (.get 5))))))) 6
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      refine ⟨0, start, start, rfl, rfl, heap, 0, start, rfl, ?_⟩
      rw [gone_eq]
      exact Heap.Rebuilt.null hHeap
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨-, -, hr, hPr⟩ := node_children hOwned hDisjoint
    have hRecord := hOwned
    obtain ⟨hHead, -, hk, -, -⟩ := hRecord
    simp only [Nat.zero_add] at hk
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let s1 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 0, .i64 0, .i64 0] }
    let s2 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 0, .i64 0] }
    let s3 : State := { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 0] }
    let sq : UInt64 → State := fun q =>
      { params := [.i64 p], locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 q] }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap' : Heap) (q : UInt64), st = sq q ∧
          heap.Rebuilt initial
            ((Represent.moves initial [.i64 p] (Moved.mk (KeyTree.node l k r))).map (block initial))
            heap' s q (Encode.encode (trimMoved ⟨.node l k r⟩))) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = s3 ∧ k = 0)
          (PElse := fun s st => s = initial ∧ st = s3 ∧ k ≠ 0) ?_ ?_).mono ?_ fun _ _ h => h
        · -- The left subtree: its slot cleared and the record released, as in `leftChild`.
          apply Triple.of_forall
          rintro s0 st0 ⟨hs0', hst0, hk0⟩
          subst s0 st0
          let store1 : Store Unit := { initial with mem := initial.mem.write64 (slotAddress p 0) 0 }
          obtain ⟨-, hAt1, hCleared, -, hClearedDisjoint, -, -⟩ :=
            NodeOwned.clearLeft hHeap hOwned hDisjoint
          refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = sq pl) ?_ <|
            Stmt.seq_spec (M := fun s st => s = store1 ∧ st = sq pl) ?_ ?_
          · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            exact ⟨pl, s3, sq pl, rfl, rfl, rfl, rfl⟩
          · refine Stmt.store_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨p + 0, sq pl, 0, sq pl, rfl, rfl, by rw [h0, hs0]; omega, ?_⟩
            rw [h0]
            exact ⟨rfl, rfl⟩
          · refine (Stmt.releaseNode_spec hImports hRelease rfl hAt1 hCleared
              hClearedDisjoint).mono (fun _ _ h => h) ?_
            rintro s st ⟨rfl, heap', hAt, hCaps, hRegion⟩
            have hv : trimMoved ⟨.node l k r⟩ = l := by simp [trimMoved, KeyTree.trim, hk0]
            refine ⟨heap', pl, rfl, ?_⟩
            rw [hv]
            exact leftChild_node hHeap hArg hAt hCaps
              hRegion
        · -- The right subtree released and its slot cleared, as in `dropRight`.
          apply Triple.of_forall
          rintro s0 st0 ⟨hs0', hst0, hk0⟩
          subst s0 st0
          refine Stmt.seq_spec (M := fun s st => st = s3 ∧ ∃ heap2 : Heap, heap.Rebuilt initial
            (Node.blocks initial pr (encode r)) heap2 s 0 .null)
            (Stmt.releaseNode_rebuilt hImports hRelease rfl hHeap hr hPr) ?_
          refine Triple.of_forall fun store2 st ⟨hst, heap2, hR2⟩ => ?_
          subst hst
          refine Stmt.seq_spec (M := fun s st =>
            s = { store2 with mem := store2.mem.write64 (slotAddress p 2) 0 } ∧ st = s3) ?_ ?_
          · refine Stmt.store_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨p + 16, s3, 0, s3, rfl, rfl, ?_, ?_⟩
            · rw [h2, hs2]
              have := right_bound hOwned hDisjoint hR2
              omega
            · rw [h2]
              exact ⟨rfl, rfl⟩
          · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            have hv : trimMoved ⟨.node l k r⟩ = .node l k .leaf := by
              simp [trimMoved, KeyTree.trim, hk0]
            refine ⟨p, s3, sq p, rfl, rfl, heap2, p, rfl, ?_⟩
            rw [hv, gone_eq]
            exact Heap.Rebuilt.dropRight hHeap hOwned hDisjoint hR2
        · rintro s st ⟨rfl, rfl⟩
          by_cases hk0 : k = 0
          · exact ⟨true, s3, by simp [Expr.eval, s3, State.get, hk0], rfl, rfl, hk0⟩
          · exact ⟨false, s3, by simp [Expr.eval, s3, State.get, hk0], rfl, rfl, hk0⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨heap', q, rfl, hR⟩
        exact ⟨q, sq q,
          { params := [.i64 p], locals := [.i64 q, .i64 pl, .i64 k, .i64 pr, .i64 q] }, rfl, rfl,
          heap', q, _, rfl, hR⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `insertTwo` with its three arguments as one tuple, the tree consumed. -/
def insertTwoMoved (x : UInt64 × UInt64 × Moved KeyTree) : KeyTree :=
  KeyTree.insertTwo x.1 x.2.1 x.2.2.val

/-- `insertTwo` calls `insert` on its tree and then on the first call's result, which the
second call consumes.  `insert`'s `Implements` theorem covers both calls. -/
theorem insertTwo_implements : Implements treeMoves.module 9 insertTwoMoved := by
  refine Func.implements_moves treeMoves.funcs 7 treeMoves.insertTwo.ir "insertTwo" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨a, b, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOwned,
    hDisjoint⟩ - hCap
  have hFunc : (compile treeMoves.funcs).funcs[2 + 2 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.insert.ir.function (2 + 2)) := compile_funcs (i := 2) rfl
  let start : State := { params := [.i64 a, .i64 b, .i64 p], locals := [.i64 0, .i64 0] }
  show Triple _ (.seq (.call (2 + 2) [⟨.u64, .get 0⟩, ⟨.u64, .get 2⟩] [3])
      (.call (2 + 2) [⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩] [4])) 5
    (fun store state => store = initial ∧ state = start) _
  obtain ⟨hB1, hSep1⟩ := pair_args (x := a) hOwned hDisjoint
  refine Stmt.seq_spec (Stmt.callImplements_spec insert_implements rfl hFunc rfl
    (before := start) (results := [3]) (x := (a, Moved.mk t)) rfl hHeap hB1 hSep1 hCap
    (by rintro _ _ _ ⟨q, rfl, -⟩; exact ⟨_, rfl⟩)) ?_
  apply Triple.of_forall
  rintro s1 st1 ⟨heap1, _, hAt1, ⟨q1, rfl, hOwned1, hDisjoint1⟩, hCaps1, hK1, hSet1⟩
  obtain rfl : st1 = { params := [.i64 a, .i64 b, .i64 p], locals := [.i64 q1, .i64 0] } :=
    (Option.some.inj (hSet1.symm.trans rfl))
  obtain ⟨hB2, hSep2⟩ := pair_args (x := b) hOwned1 hDisjoint1
  refine (Stmt.callImplements_spec insert_implements rfl hFunc rfl
    (results := [4]) (x := (b, Moved.mk (KeyTree.insert a t))) rfl hAt1 hB2 hSep2
    (memoryCap_le_of_caps hCaps1 hCap) (by rintro _ _ _ ⟨q, rfl, -⟩; exact ⟨_, rfl⟩)).mono
      (fun _ _ h => h) ?_
  rintro s2 st2 ⟨heap2, _, hAt2, ⟨q2, rfl, hOwned2, hDisjoint2⟩, hCaps2, hK2, hSet2⟩
  obtain rfl : st2 = { params := [.i64 a, .i64 b, .i64 p], locals := [.i64 q1, .i64 q2] } :=
    (Option.some.inj (hSet2.symm.trans rfl))
  -- The second call consumes exactly the first call's result.
  exact ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 q2], _, rfl, ⟨q2, rfl, hOwned2, hDisjoint2⟩,
    hK1.trans hK2 fun _ _ hFresh c hc => hFresh c (by rw [pair_gone] at hc; exact hc)⟩

/-- `addRoot` with its two arguments as one pair, the second tree consumed. -/
def addRootMoved (x : KeyTree × Moved KeyTree) : KeyTree := KeyTree.addRoot x.1 x.2.val

/-- `addRoot` reads the root key of its borrowed tree and writes the sum into the root record
of its consumed tree. -/
theorem addRoot_implements : Implements treeMoves.module 10 addRootMoved := by
  refine Func.implements_moves treeMoves.funcs 8 treeMoves.addRoot.ir "addRoot" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, p, rfl, -⟩; rfl) ?_
  rintro ⟨a, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨pa, rfl, hA⟩, p, rfl, hOwned, hDisjoint⟩ - -
  have hMoves : Represent.moves initial ([.i64 pa] ++ [.i64 p]) (a, Moved.mk t) =
      Node.pointers initial p (encode t) := rfl
  rw [hMoves]
  rw [show [Value.i64 pa] ++ [Value.i64 p] = [.i64 pa, .i64 p] from rfl]
  let start : State := { params := [.i64 pa, .i64 p], locals := List.replicate 8 (.i64 0) }
  show Triple _ (.ite (.eq (.get 1) (.const 0)) (.assign 2 (.const 0))
      (.seq (.load .u64 3 (.bin .add (.get 1) (.const 0)))
        (.seq (.load .u64 4 (.bin .add (.get 1) (.const 8)))
          (.seq (.load .u64 5 (.bin .add (.get 1) (.const 16)))
            (.seq (.ite (.eq (.get 0) (.const 0)) (.assign 6 (.get 1))
                (.seq (.load .u64 7 (.bin .add (.get 0) (.const 0)))
                  (.seq (.load .u64 8 (.bin .add (.get 0) (.const 8)))
                    (.seq (.load .u64 9 (.bin .add (.get 0) (.const 16)))
                      (.seq (.store (.bin .add (.get 1) (.const 8)) (.bin .add (.get 4) (.get 8)))
                        (.assign 6 (.get 1)))))))
              (.assign 2 (.get 6))))))) 10
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      refine ⟨0, start, start, rfl, rfl, heap, hHeap, rfl, [.i64 0], start,
        by simp [treeMoves.addRoot.ir, Func.scratch, Expr.evalResults, Expr.eval, start,
          State.get],
        ⟨0, rfl, rfl, .nil⟩, fun _ hg _ _ => ⟨fun _ _ _ => rfl, hg, fun b hb => ?_⟩⟩
      change b ∈ Node.blocks _ 0 .null at hb
      cases hb
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l key r =>
    let slots : List Slot := [.child (encode l), .word key, .child (encode r)]
    have hRecord : NodeOwned heap initial p (.record slots) := hOwned
    obtain ⟨hHead, -, hKey, -, -⟩ := hRecord
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [slots, List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let ps : List Value := [.i64 pa, .i64 p]
    let z : Value := .i64 0
    let s1 : State := { params := ps, locals := [z, .i64 pl, z, z, z, z, z, z] }
    let s2 : State := { params := ps, locals := [z, .i64 pl, .i64 key, z, z, z, z, z] }
    let s3 : State := { params := ps, locals := [z, .i64 pl, .i64 key, .i64 pr, z, z, z, z] }
    have hRoot : p ∈ Node.pointers initial p (encode (.node l key r)) := by
      simp [encode, Node.pointers]
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, ?_, rfl, rfl⟩
        rw [h0]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hKey]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, ?_, rfl, rfl⟩
        rw [h2]
        rfl
      cases a with
      | leaf =>
        -- The borrowed tree is a leaf: the consumed tree is the result as it is.
        obtain rfl : pa = 0 := hA
        let t4 : State := { params := ps, locals := [z, .i64 pl, .i64 key, .i64 pr, .i64 p, z, z, z] }
        let t5 : State :=
          { params := ps, locals := [.i64 p, .i64 pl, .i64 key, .i64 pr, .i64 p, z, z, z] }
        refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = t4)
          ((Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = s3)
            (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
            Triple.of_false).mono ?_ fun _ _ h => h) ?_
        · rintro s st ⟨rfl, rfl⟩
          exact ⟨p, s3, t4, rfl, rfl, rfl, rfl⟩
        · rintro s st ⟨rfl, rfl⟩
          exact ⟨true, s3, by simp [Expr.eval, s3, State.get, ps], rfl, rfl⟩
        refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p, t4, t5, rfl, rfl, heap, hHeap, rfl, [.i64 p], t5,
          by simp [treeMoves.addRoot.ir, Func.scratch, Expr.evalResults, Expr.eval, State.get, t5,
            ps],
          ⟨p, rfl, hOwned, hDisjoint⟩, fun g hg _ hApart => ⟨fun _ _ _ => rfl, hg, fun b hb => ?_⟩⟩
        exact hApart b (by rw [Node.pointers_blocks]; exact hb)
      | node al ak ar =>
        -- The borrowed tree is a node: its root key goes into the consumed tree's root record.
        obtain ⟨hRecA, -, hAk, -, -⟩ := hA
        simp only [Nat.zero_add] at hAk
        have hNonzeroA := hRecA.nonzero
        have hAddressA := hRecA.address
        have hBelowA := hRecA.below
        simp only [List.length_cons, List.length_nil] at hAddressA hBelowA
        have g0 : (pa + 0).toUInt32 = slotAddress pa 0 := by simp [slotAddress]
        have g1 : (pa + 8).toUInt32 = slotAddress pa 1 := by simp [slotAddress]
        have g2 : (pa + 16).toUInt32 = slotAddress pa 2 := by simp [slotAddress]
        have ga0 := slotAddress_toNat (p := pa) (i := 0) (by omega)
        have ga1 := slotAddress_toNat (p := pa) (i := 1) (by omega)
        have ga2 := slotAddress_toNat (p := pa) (i := 2) (by omega)
        obtain ⟨hWrites, hAt, hOwned', hBlocks⟩ :=
          NodeOwned.writeWord (i := 1) (w := key + ak) hHeap hOwned hDisjoint ⟨key, rfl⟩
        have hResult : Encode.encode (addRootMoved (.node al ak ar, ⟨.node l key r⟩)) =
            .record (slots.set 1 (.word (key + ak))) := rfl
        let final : Store Unit :=
          { initial with mem := initial.mem.write64 (slotAddress p 1) (key + ak) }
        have hKeep : ∀ g : Nat × Nat, regionsDisjoint g (block initial p) →
            ∀ x, g.1 ≤ x → x < g.1 + g.2 → final.mem.bytes x = initial.mem.bytes x :=
          fun g hg x hLow hHigh => hWrites.2.2 x (by
            simp only [regionsDisjoint, block] at hg
            omega)
        let qal := initial.mem.read64 (slotAddress pa 0)
        let qar := initial.mem.read64 (slotAddress pa 2)
        let u1 : State :=
          { params := ps, locals := [z, .i64 pl, .i64 key, .i64 pr, z, .i64 qal, z, z] }
        let u2 : State :=
          { params := ps, locals := [z, .i64 pl, .i64 key, .i64 pr, z, .i64 qal, .i64 ak, z] }
        let u3 : State :=
          { params := ps, locals := [z, .i64 pl, .i64 key, .i64 pr, z, .i64 qal, .i64 ak, .i64 qar] }
        let u4 : State :=
          { params := ps,
            locals := [z, .i64 pl, .i64 key, .i64 pr, .i64 p, .i64 qal, .i64 ak, .i64 qar] }
        let u5 : State :=
          { params := ps,
            locals := [.i64 p, .i64 pl, .i64 key, .i64 pr, .i64 p, .i64 qal, .i64 ak, .i64 qar] }
        refine Stmt.seq_spec (M := fun s st => s = final ∧ st = u4)
          ((Stmt.ite_spec (PThen := fun _ _ => False)
            (PElse := fun s st => s = initial ∧ st = s3) Triple.of_false ?_).mono ?_
              fun _ _ h => h) ?_
        · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = u1) ?_ <|
            Stmt.seq_spec (M := fun s st => s = initial ∧ st = u2) ?_ <|
            Stmt.seq_spec (M := fun s st => s = initial ∧ st = u3) ?_ <|
            Stmt.seq_spec (M := fun s st => s = final ∧ st = u3) ?_ ?_
          · refine Stmt.load_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨pa + 0, s3, u1, rfl, by rw [g0, ga0]; omega, ?_, rfl, rfl⟩
            rw [g0]
            rfl
          · refine Stmt.load_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨pa + 8, u1, u2, rfl, by rw [g1, ga1]; omega, ?_, rfl, rfl⟩
            rw [g1, hAk]
            rfl
          · refine Stmt.load_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨pa + 16, u2, u3, rfl, by rw [g2, ga2]; omega, ?_, rfl, rfl⟩
            rw [g2]
            rfl
          · refine Stmt.store_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            refine ⟨p + 8, u3, key + ak, u3, rfl, rfl, by rw [h1, hs1]; omega, ?_⟩
            rw [h1]
            exact ⟨rfl, rfl⟩
          · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
            rintro s st ⟨rfl, rfl⟩
            exact ⟨p, u3, u4, rfl, rfl, rfl, rfl⟩
        · rintro s st ⟨rfl, rfl⟩
          exact ⟨false, s3, by simp [Expr.eval, s3, State.get, ps, hNonzeroA], rfl, rfl⟩
        refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p, u4, u5, rfl, rfl, heap, hAt, rfl, [.i64 p], u5,
          by simp [treeMoves.addRoot.ir, Func.scratch, Expr.evalResults, Expr.eval, State.get, u5,
            ps],
          ⟨p, rfl, hResult ▸ hOwned', by rw [hResult, hBlocks]; exact hDisjoint⟩,
          fun g hg _ hApart => ⟨hKeep g (hApart _ (List.mem_map_of_mem hRoot)), hg, fun b hb => ?_⟩⟩
        change b ∈ Node.blocks final p (Encode.encode (addRootMoved (.node al ak ar, ⟨.node l key r⟩)))
          at hb
        rw [hResult, hBlocks] at hb
        exact hApart b (by rw [Node.pointers_blocks]; exact hb)
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- The root key of a tree, 0 for a leaf. -/
def rootKeyOf : KeyTree → UInt64
  | .leaf => 0
  | .node _ ak _ => ak

/-- `addAll` with its two arguments as one pair, the second tree consumed. -/
def addAllMoved (x : KeyTree × Moved KeyTree) : KeyTree := KeyTree.addAll x.1 x.2.val

theorem addAll_node (a l r : KeyTree) (k : UInt64) :
    KeyTree.addAll a (.node l k r) =
      .node (KeyTree.addAll a l) (k + rootKeyOf a) (KeyTree.addAll a r) := by
  cases a <;> rfl

/-- A borrowed tree at `pa` and a consumed tree at `q`, whose blocks lie apart from the borrowed
tree's slot regions, are a borrowed pair with separate moves and reads. -/
theorem treePair_args {heap : Heap} {store : Store Unit} {pa q : UInt64} {a t : KeyTree}
    (hA : NodeBorrowed heap store pa (encode a)) (hOwned : NodeOwned heap store q (encode t))
    (hDisjoint : (Node.blocks store q (encode t)).Pairwise regionsDisjoint)
    (hApart : ∀ s ∈ Node.slotRegions store pa (encode a), ∀ c ∈ Node.blocks store q (encode t),
      regionsDisjoint s c) :
    Represent.borrowed heap store [.i64 pa, .i64 q] (a, Moved.mk t) ∧
      Separate store (Represent.moves store [.i64 pa, .i64 q] (a, Moved.mk t))
        (Represent.reads store [.i64 pa, .i64 q] (a, Moved.mk t)) := by
  refine ⟨⟨[.i64 pa], [.i64 q], rfl, ⟨pa, rfl, hA⟩, q, rfl, hOwned, hDisjoint⟩, ?_, ?_⟩
  · show ((Node.pointers store q (encode t)).map (block store)).Pairwise regionsDisjoint
    rw [Node.pointers_blocks]
    exact hDisjoint
  · intro s hs x hx
    have hs' : s ∈ Node.slotRegions store pa (encode a) := by
      have : s ∈ Node.slotRegions store pa (encode a) ++ [] := hs
      simpa using this
    have hx' : x ∈ Node.pointers store q (encode t) := hx
    exact hApart s hs' _ (by
      rw [← Node.pointers_blocks]
      exact List.mem_map_of_mem hx')

/-- The bound at the three stores after a node's two children are rebuilt in turn: the root's
block, kept by both rebuilds, lies inside the memory after them. -/
theorem rebuilt_bound {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {p k q1 q2 : UInt64} {l r ml mr : KeyTree}
    (hOwned : NodeOwned heap initial p (encode (.node l k r)))
    (hDisjoint : (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint)
    (h1 : heap.Rebuilt initial
      (Node.blocks initial (initial.mem.read64 (slotAddress p 0)) (encode l)) heap1 store1 q1
      (encode ml))
    (h2 : heap1.Rebuilt store1
      (Node.blocks store1 (initial.mem.read64 (slotAddress p 2)) (encode r)) heap2 store2 q2
      (encode mr)) :
    p.toNat + 24 ≤ store2.mem.pages * 65536 := by
  obtain ⟨hHead, -, -, hr, -⟩ := hOwned
  simp only [Nat.zero_add, Nat.reduceAdd] at hr
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

/-- The internal function of `addAll`, at any depth, borrows its first tree, consumes its
second, and returns the second with the first's root key added to every key, rebuilt in the
same records. -/
theorem addAll_rec : ∀ x, Rebuilds (compile treeMoves.funcs) (2 + 14) addAllMoved x := by
  refine Func.rebuildRecursion treeMoves.funcs 14 treeMoves.addAll.rec.ir "addAll.rec" rfl
    addAllMoved (fun x => sizeOf x.2.val)
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, rfl, -⟩; rfl)
    fun ⟨a, ⟨t⟩⟩ ih heap initial vs d hHeap hArgs hSep hCap => ?_
  obtain ⟨_, _, rfl, ⟨pa, rfl, hA⟩, p, rfl, hOwned, hDisjoint⟩ := hArgs
  change NodeBorrowed heap initial pa (encode a) at hA
  -- The borrowed tree's slots lie apart from every block of the consumed tree.
  have hApartAll : ∀ s ∈ Node.slotRegions initial pa (encode a),
      ∀ c ∈ Node.blocks initial p (encode t), regionsDisjoint s c := by
    intro s hs c hc
    have h := hSep.2 s (show s ∈ Node.slotRegions initial pa (encode a) ++ [] from
      List.mem_append_left _ hs)
    rw [← Node.pointers_blocks] at hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact h q hq
  have hCallee : (compile treeMoves.funcs).funcs[2 + 14 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.addAll.rec.ir.function (2 + 14)) := compile_funcs (i := 14) rfl
  let z : Value := .i64 0
  let start : State := { params := [.i64 pa, .i64 p, .i64 d], locals := List.replicate 10 z }
  have hStart : treeMoves.addAll.rec.ir.state ([.i64 pa] ++ [.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 2)) .abort .skip)
      (.ite (.eq (.get 1) (.const 0)) (.assign 3 (.const 0))
        (.seq (.load .u64 4 (.bin .add (.get 1) (.const 0)))
          (.seq (.load .u64 5 (.bin .add (.get 1) (.const 8)))
            (.seq (.load .u64 6 (.bin .add (.get 1) (.const 16)))
              (.seq (.call (2 + 14) [⟨.u64, .get 0⟩, ⟨.u64, .get 4⟩,
                  ⟨.u64, .bin .add (.get 2) (.const 1)⟩] [7])
                (.seq (.ite (.eq (.get 0) (.const 0)) (.assign 8 (.const 0))
                    (.seq (.load .u64 9 (.bin .add (.get 0) (.const 0)))
                      (.seq (.load .u64 10 (.bin .add (.get 0) (.const 8)))
                        (.seq (.load .u64 11 (.bin .add (.get 0) (.const 16)))
                          (.assign 8 (.get 10))))))
                  (.seq (.call (2 + 14) [⟨.u64, .get 0⟩, ⟨.u64, .get 6⟩,
                      ⟨.u64, .bin .add (.get 2) (.const 1)⟩] [12])
                    (.seq (.store (.bin .add (.get 1) (.const 0)) (.get 7))
                      (.seq (.store (.bin .add (.get 1) (.const 8)) (.bin .add (.get 5) (.get 8)))
                        (.seq (.store (.bin .add (.get 1) (.const 16)) (.get 12))
                          (.assign 3 (.get 1))))))))))))) 13
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
    ((Stmt.ite_spec (PThen := fun _ _ => True) (PElse := fun s st => s = initial ∧ st = start)
      Stmt.abort_spec (Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h)).mono ?_
        fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    refine ⟨decide ((999 : UInt64) < d), start, by simp [Expr.eval, start, State.get], ?_⟩
    split <;> trivial
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    let s1 : State := { params := [.i64 pa, .i64 0, .i64 d], locals := List.replicate 10 z }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, s1, rfl, rfl, heap, 0, s1, rfl, Heap.Rebuilt.null hHeap⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    have hOwnedN := hOwned
    obtain ⟨hHead, hl, hk, hr, -⟩ := hOwned
    simp only [Nat.zero_add, Nat.reduceAdd] at hk hr
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    have hDisjointN := hDisjoint
    change (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint at hDisjoint
    rw [blocks_node] at hDisjoint
    obtain ⟨hPl, hPr, hlr⟩ := List.pairwise_append.mp (List.pairwise_cons.mp hDisjoint).2
    have hBlocksN : Node.blocks initial p (encode (.node l k r)) = block initial p ::
        (Node.blocks initial pl (encode l) ++ Node.blocks initial pr (encode r)) :=
      blocks_node initial p k l r
    have hApartL : ∀ s ∈ Node.slotRegions initial pa (encode a),
        ∀ c ∈ Node.blocks initial pl (encode l), regionsDisjoint s c := fun s hs c hc =>
      hApartAll s hs c (by rw [hBlocksN]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hc))
    have hApartR : ∀ s ∈ Node.slotRegions initial pa (encode a),
        ∀ c ∈ Node.blocks initial pr (encode r), regionsDisjoint s c := fun s hs c hc =>
      hApartAll s hs c (by rw [hBlocksN]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hc))
    let ps : List Value := [.i64 pa, .i64 p, .i64 d]
    let s1 : State := { params := ps, locals := [z, .i64 pl, z, z, z, z, z, z, z, z] }
    let s2 : State := { params := ps, locals := [z, .i64 pl, .i64 k, z, z, z, z, z, z, z] }
    let s3 : State := { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, z, z, z, z, z, z] }
    let s4 (q1 : UInt64) : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 q1, z, z, z, z, z] }
    let s5 (q1 key x y w : UInt64) : State :=
      { params := ps,
        locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 q1, .i64 key, .i64 x, .i64 y, .i64 w, z] }
    let s6 (q1 key x y w q2 : UInt64) : State :=
      { params := ps,
        locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 q1, .i64 key, .i64 x, .i64 y, .i64 w,
          .i64 q2] }
    let s7 (q1 key x y w q2 : UInt64) : State :=
      { params := ps,
        locals := [.i64 p, .i64 pl, .i64 k, .i64 pr, .i64 q1, .i64 key, .i64 x, .i64 y, .i64 w,
          .i64 q2] }
    obtain ⟨hB1, hSep1⟩ := treePair_args hA hl hPl hApartL
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap1 : Heap) (q1 : UInt64), st = s4 q1 ∧
          heap.Rebuilt initial ((Represent.moves initial [.i64 pa, .i64 pl] (a, Moved.mk l)).map
            (block initial)) heap1 s q1 (Encode.encode (addAllMoved (a, ⟨l⟩)))) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih (a, ⟨l⟩) (by simp; omega)) hHeap
          hB1 hSep1 hCap (d := d + 1) rfl fun q => by simp [State.setAll, State.set?, s3, s4, ps]
      refine Triple.of_forall fun store1 st ⟨heap1, q1, hst, hR1⟩ => ?_
      subst hst
      have hR1' : heap.Rebuilt initial (Node.blocks initial pl (encode l)) heap1 store1 q1
          (encode (KeyTree.addAll a l)) := by
        have h : heap.Rebuilt initial ((Node.pointers initial pl (encode l)).map (block initial))
            heap1 store1 q1 (encode (KeyTree.addAll a l)) := hR1
        rwa [Node.pointers_blocks] at h
      -- The borrowed tree and the right subtree survive the first call.
      obtain ⟨hA1, hSlots1, -⟩ := Heap.Keeps.nodeBorrowed hR1'.region hA (EncodeSlotted.slotRegions_pos a)
        hApartL
      obtain ⟨hr1, hrBlocks1, -⟩ := hR1'.keepNode hr fun b hb g hg =>
        regionsDisjoint_symm (hlr g hg b hb)
      have hPr1 : (Node.blocks store1 pr (encode r)).Pairwise regionsDisjoint := by
        rw [hrBlocks1]; exact hPr
      have hApartR1 : ∀ s ∈ Node.slotRegions store1 pa (encode a),
          ∀ c ∈ Node.blocks store1 pr (encode r), regionsDisjoint s c := by
        rw [hSlots1, hrBlocks1]; exact hApartR
      obtain ⟨hB2, hSep2⟩ := treePair_args hA1 hr1 hPr1 hApartR1
      refine Stmt.seq_spec (M := fun s st => s = store1 ∧ ∃ x y w : UInt64,
          st = s5 q1 (rootKeyOf a) x y w) ?_ ?_
      · -- The borrowed tree's root key, read from its record.
        cases a with
        | leaf =>
          obtain rfl : pa = 0 := hA1
          refine (Stmt.ite_spec (PThen := fun s st => s = store1 ∧ st = s4 q1)
            (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
            Triple.of_false).mono ?_ fun _ _ h => h
          · rintro s st ⟨rfl, rfl⟩
            exact ⟨0, s4 q1, s5 q1 0 0 0 0, rfl, rfl, rfl, 0, 0, 0, rfl⟩
          · rintro s st ⟨rfl, rfl⟩
            exact ⟨true, s4 q1, by simp [Expr.eval, s4, State.get, ps], rfl, rfl⟩
        | node al ak ar =>
          obtain ⟨hRecA, -, hAk, -, -⟩ := hA1
          simp only [Nat.zero_add] at hAk
          have hNonzeroA := hRecA.nonzero
          have hAddressA := hRecA.address
          have hBelowA := hRecA.below
          have hTop1 := hR1'.at_.top
          simp only [List.length_cons, List.length_nil] at hAddressA hBelowA
          have g0 : (pa + 0).toUInt32 = slotAddress pa 0 := by simp [slotAddress]
          have g1 : (pa + 8).toUInt32 = slotAddress pa 1 := by simp [slotAddress]
          have g2 : (pa + 16).toUInt32 = slotAddress pa 2 := by simp [slotAddress]
          have ga0 := slotAddress_toNat (p := pa) (i := 0) (by omega)
          have ga1 := slotAddress_toNat (p := pa) (i := 1) (by omega)
          have ga2 := slotAddress_toNat (p := pa) (i := 2) (by omega)
          let x := store1.mem.read64 (slotAddress pa 0)
          let w := store1.mem.read64 (slotAddress pa 2)
          refine (Stmt.ite_spec (PThen := fun _ _ => False)
            (PElse := fun s st => s = store1 ∧ st = s4 q1) Triple.of_false ?_).mono ?_
              fun _ _ h => h
          · refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s5 q1 0 x 0 0) ?_ <|
              Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s5 q1 0 x ak 0) ?_ <|
              Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s5 q1 0 x ak w) ?_ ?_
            · refine Stmt.load_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              refine ⟨pa + 0, s4 q1, s5 q1 0 x 0 0, rfl, by rw [g0, ga0]; omega, ?_, rfl, rfl⟩
              rw [g0]
              rfl
            · refine Stmt.load_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              refine ⟨pa + 8, s5 q1 0 x 0 0, s5 q1 0 x ak 0, rfl, by rw [g1, ga1]; omega, ?_, rfl,
                rfl⟩
              rw [g1, hAk]
              rfl
            · refine Stmt.load_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              refine ⟨pa + 16, s5 q1 0 x ak 0, s5 q1 0 x ak w, rfl, by rw [g2, ga2]; omega, ?_,
                rfl, rfl⟩
              rw [g2]
              rfl
            · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              exact ⟨ak, s5 q1 0 x ak w, s5 q1 ak x ak w, rfl, rfl, rfl, x, ak, w, rfl⟩
          · rintro s st ⟨rfl, rfl⟩
            exact ⟨false, s4 q1, by simp [Expr.eval, s4, State.get, ps, hNonzeroA], rfl, rfl⟩
      refine Triple.of_forall fun s st ⟨hs, x, y, w, hst⟩ => ?_
      subst s hst
      refine Stmt.seq_spec (M := fun s st => ∃ (heap2 : Heap) (q2 : UInt64),
          st = s6 q1 (rootKeyOf a) x y w q2 ∧
          heap1.Rebuilt store1 ((Represent.moves store1 [.i64 pa, .i64 pr] (a, Moved.mk r)).map
            (block store1)) heap2 s q2 (Encode.encode (addAllMoved (a, ⟨r⟩)))) ?_ ?_
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih (a, ⟨r⟩) (by simp)) hR1'.at_ hB2
          hSep2 (memoryCap_le_of_caps hR1'.caps hCap) (d := d + 1) rfl
          fun q => by simp [State.setAll, State.set?, s5, s6, ps]
      refine Triple.of_forall fun store2 st ⟨heap2, q2, hst, hR2⟩ => ?_
      subst hst
      have hR2' : heap1.Rebuilt store1 (Node.blocks store1 pr (encode r)) heap2 store2 q2
          (encode (KeyTree.addAll a r)) := by
        have h : heap1.Rebuilt store1 ((Node.pointers store1 pr (encode r)).map (block store1))
            heap2 store2 q2 (encode (KeyTree.addAll a r)) := hR2
        rwa [Node.pointers_blocks] at h
      have hBound := rebuilt_bound hOwnedN hDisjointN hR1' (by rwa [hrBlocks1] at hR2')
      let w0 := store2.mem.write64 (slotAddress p 0) q1
      let w1 := w0.write64 (slotAddress p 1) (k + rootKeyOf a)
      let w2 := w1.write64 (slotAddress p 2) q2
      let sv := s6 q1 (rootKeyOf a) x y w q2
      refine Stmt.seq_spec (M := fun s st => s = { store2 with mem := w0 } ∧ st = sv) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w1 } ∧ st = sv) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w2 } ∧ st = sv) ?_ ?_
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, sv, q1, sv, rfl, rfl, by rw [h0, hs0]; omega, ?_⟩
        rw [h0]
        exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, sv, k + rootKeyOf a, sv, rfl, rfl, ?_, ?_⟩
        · rw [h1, hs1]
          simp only [w0, Wasm.Mem.write64_pages]
          omega
        · rw [h1]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, sv, q2, sv, rfl, rfl, ?_, ?_⟩
        · rw [h2, hs2]
          simp only [w1, w0, Wasm.Mem.write64_pages]
          omega
        · rw [h2]
          exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        have hRead0 : w2.read64 (slotAddress p 0) = q1 := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega),
            Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead1 : w2.read64 (slotAddress p 1) = k + rootKeyOf a := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead2 : w2.read64 (slotAddress p 2) = q2 := Memory.read64_write64 _ _ _
        have hNode := Heap.Rebuilt.node (heap := heap) hOwnedN hDisjointN hR1'
          (by rwa [hrBlocks1] at hR2') (writes3 store2 p q1 (k + rootKeyOf a) q2 (by omega))
          hRead0 hRead1 hRead2
        refine ⟨p, sv, s7 q1 (rootKeyOf a) x y w q2, rfl, rfl, heap2, p,
          s7 q1 (rootKeyOf a) x y w q2, rfl, ?_⟩
        have hGone : (Represent.moves initial ([.i64 pa] ++ [.i64 p])
            (a, Moved.mk (KeyTree.node l k r))).map
            (block initial) = Node.blocks initial p (encode (.node l k r)) := by
          show (Node.pointers initial p (encode (.node l k r))).map (block initial) = _
          rw [Node.pointers_blocks]
        rw [hGone]
        show heap.Rebuilt initial _ heap2 _ p (encode (KeyTree.addAll a (.node l k r)))
        rw [addAll_node]
        exact hNode
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem addAll_implements : Implements treeMoves.module 11 addAllMoved :=
  Func.entry_rebuilds treeMoves.funcs 9 treeMoves.addAll.ir "addAll" rfl addAllMoved
    (g := treeMoves.addAll.rec.ir.function (2 + 14))
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, rfl, -⟩; rfl) rfl rfl
    rfl (compile_funcs (i := 14) rfl) rfl
    (by
      rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, rfl, -⟩
      simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a, b], _ =>
        exact ⟨_, rfl, by simp [State.get, Func.state, treeMoves.addAll.ir, Func.locals]⟩)
    addAll_rec

/-- `addLeft` with its tree consumed. -/
def addLeftMoved (t : Moved KeyTree) : KeyTree := t.val.addLeft

/-- `addLeft` lends its left child to `addRoot`, which consumes the right child.  The left
child's slot regions lie inside its blocks, which lie apart from the right child's
(`NodeOwned.slotRegions_apart`), so the call's `Separate` premise holds, and
`Heap.Rebuilt.rightChild` gives the record with the call's result in slot 2. -/
theorem addLeft_implements : Implements treeMoves.module 12 addLeftMoved := by
  refine Func.implements_rebuilt treeMoves.funcs 10 treeMoves.addLeft.ir "addLeft" rfl _
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro ⟨t⟩ heap initial _ hHeap ⟨p, rfl, hOwned, hDisjoint⟩ - hCap
  rw [gone_eq]
  let start : State := { params := [.i64 p], locals := List.replicate 5 (.i64 0) }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.assign 1 (.const 0))
      (.seq (.load .u64 2 (.bin .add (.get 0) (.const 0)))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 8)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 16)))
            (.seq (.call 10 [⟨.u64, .get 2⟩, ⟨.u64, .get 4⟩] [5])
              (.seq (.store (.bin .add (.get 0) (.const 16)) (.get 5))
                (.assign 1 (.get 0)))))))) 6
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, start, rfl, rfl, heap, 0, start, rfl, Heap.Rebuilt.null hHeap⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hl, -, hr, hPr⟩ := node_children hOwned hDisjoint
    have hRecord := hOwned
    obtain ⟨hHead, -, hk, -, -⟩ := hRecord
    simp only [Nat.zero_add] at hk
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have e0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have e1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have e2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let z : Value := .i64 0
    let s1 : State := { params := [.i64 p], locals := [z, .i64 pl, z, z, z] }
    let s2 : State := { params := [.i64 p], locals := [z, .i64 pl, .i64 k, z, z] }
    let s3 : State := { params := [.i64 p], locals := [z, .i64 pl, .i64 k, .i64 pr, z] }
    let s4 (q : UInt64) : State :=
      { params := [.i64 p], locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 q] }
    let s5 (q : UInt64) : State :=
      { params := [.i64 p], locals := [.i64 p, .i64 pl, .i64 k, .i64 pr, .i64 q] }
    -- The left child, lent, and the right child, consumed, by one call.
    have hlr : ∀ b ∈ Node.blocks initial pl (encode l),
        ∀ c ∈ Node.blocks initial pr (encode r), regionsDisjoint b c := by
      have hD := hDisjoint
      change (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint at hD
      rw [blocks_node] at hD
      exact (List.pairwise_append.mp (List.pairwise_cons.mp hD).2).2.2
    obtain ⟨hB, hSep⟩ := treePair_args (NodeOwned.borrowed _ _ hl) hr hPr
      fun s hs c hc => NodeOwned.slotRegions_apart _ _ hl (fun b hb => hlr b hb c hc) s hs
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (Stmt.callImplements_spec addRoot_implements rfl
          (compile_funcs (i := 8) rfl) rfl (before := s3) (results := [5]) (x := (l, Moved.mk r))
          rfl hHeap hB hSep hCap fun _ _ _ ⟨_, hq, _⟩ => by subst hq; exact ⟨_, rfl⟩) ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [e0, hs0]; omega, by rw [e0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [e1, hs1]; omega, ?_, rfl, rfl⟩
        rw [e1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [e2, hs2]; omega, by rw [e2]; rfl, rfl, rfl⟩
      refine Triple.of_forall fun store1 st
        ⟨heap1, values, hAt1, ⟨q, hq, hOwnedQ, hDisjointQ⟩, hCaps1, hK1, hSet1⟩ => ?_
      subst hq
      obtain rfl : st = s4 q := (Option.some.inj (hSet1.symm.trans rfl))
      have hGone : (Represent.moves initial [.i64 pl, .i64 pr] (l, Moved.mk r)).map
          (block initial) = Node.blocks initial pr (encode r) :=
        Node.pointers_blocks initial pr (encode r)
      change heap.Keeps initial ((Represent.moves initial [.i64 pl, .i64 pr]
        (l, Moved.mk r)).map (block initial)) heap1 store1
        (Node.blocks store1 q (encode (KeyTree.addRoot l r))) at hK1
      rw [hGone] at hK1
      have hR2 : heap.Rebuilt initial (Node.blocks initial pr (encode r)) heap1 store1 q
          (encode (KeyTree.addRoot l r)) := ⟨hAt1, hOwnedQ, hDisjointQ, hK1, hCaps1⟩
      refine Stmt.seq_spec (M := fun s st =>
        s = { store1 with mem := store1.mem.write64 (slotAddress p 2) q } ∧ st = s4 q) ?_ ?_
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s4 q, q, s4 q, rfl, rfl, ?_, ?_⟩
        · rw [e2, hs2]
          have := right_bound hOwned hDisjoint hR2
          omega
        · rw [e2]
          exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p, s4 q, s5 q, rfl, rfl, heap1, p, s5 q, rfl,
          Heap.Rebuilt.rightChild hHeap hOwned hDisjoint hR2⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `leftSpine` with its two arguments as one pair, the second tree consumed. -/
def leftSpineMoved (x : KeyTree × Moved KeyTree) : KeyTree := KeyTree.leftSpine x.1 x.2.val

theorem leftSpine_node (g l r : KeyTree) (k : UInt64) :
    KeyTree.leftSpine g (.node l k r) =
      .node (KeyTree.leftSpine r l) (k + rootKeyOf g) .leaf := by
  cases g <;> rfl

/-- The internal function of `leftSpine`, at any depth, borrows its first tree, consumes its
second, and returns the second's left spine rebuilt in the same records.  The recursive call
receives the owned right child at the borrowed position (`NodeOwned.borrowed`), and the right
child, kept by the call, is released after it. -/
theorem leftSpine_rec : ∀ x, Rebuilds (compile treeMoves.funcs) (2 + 15) leftSpineMoved x := by
  refine Func.rebuildRecursion treeMoves.funcs 15 treeMoves.leftSpine.rec.ir "leftSpine.rec" rfl
    leftSpineMoved (fun x => sizeOf x.2.val)
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, rfl, -⟩; rfl)
    fun ⟨g, ⟨t⟩⟩ ih heap initial vs d hHeap hArgs hSep hCap => ?_
  obtain ⟨_, _, rfl, ⟨pa, rfl, hA⟩, p, rfl, hOwned, hDisjoint⟩ := hArgs
  change NodeBorrowed heap initial pa (encode g) at hA
  -- The borrowed tree's slots lie apart from every block of the consumed tree.
  have hApartAll : ∀ s ∈ Node.slotRegions initial pa (encode g),
      ∀ c ∈ Node.blocks initial p (encode t), regionsDisjoint s c := by
    intro s hs c hc
    have h := hSep.2 s (show s ∈ Node.slotRegions initial pa (encode g) ++ [] from
      List.mem_append_left _ hs)
    rw [← Node.pointers_blocks] at hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact h q hq
  have hCallee : (compile treeMoves.funcs).funcs[2 + 15 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.leftSpine.rec.ir.function (2 + 15)) := compile_funcs (i := 15) rfl
  have hImports : (compile treeMoves.funcs).imports = [] := rfl
  have hRelease : (compile treeMoves.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let z : Value := .i64 0
  let start : State := { params := [.i64 pa, .i64 p, .i64 d], locals := List.replicate 9 z }
  have hStart : treeMoves.leftSpine.rec.ir.state ([.i64 pa] ++ [.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 2)) .abort .skip)
      (.ite (.eq (.get 1) (.const 0)) (.assign 3 (.const 0))
        (.seq (.load .u64 4 (.bin .add (.get 1) (.const 0)))
          (.seq (.load .u64 5 (.bin .add (.get 1) (.const 8)))
            (.seq (.load .u64 6 (.bin .add (.get 1) (.const 16)))
              (.seq (.call (2 + 15) [⟨.u64, .get 6⟩, ⟨.u64, .get 4⟩,
                  ⟨.u64, .bin .add (.get 2) (.const 1)⟩] [7])
                (.seq (.ite (.eq (.get 0) (.const 0)) (.assign 8 (.const 0))
                    (.seq (.load .u64 9 (.bin .add (.get 0) (.const 0)))
                      (.seq (.load .u64 10 (.bin .add (.get 0) (.const 8)))
                        (.seq (.load .u64 11 (.bin .add (.get 0) (.const 16)))
                          (.assign 8 (.get 10))))))
                  (.seq (.release 6)
                    (.seq (.store (.bin .add (.get 1) (.const 0)) (.get 7))
                      (.seq (.store (.bin .add (.get 1) (.const 8)) (.bin .add (.get 5) (.get 8)))
                        (.seq (.store (.bin .add (.get 1) (.const 16)) (.const 0))
                          (.assign 3 (.get 1))))))))))))) 12
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
    ((Stmt.ite_spec (PThen := fun _ _ => True) (PElse := fun s st => s = initial ∧ st = start)
      Stmt.abort_spec (Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h)).mono ?_
        fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    refine ⟨decide ((999 : UInt64) < d), start, by simp [Expr.eval, start, State.get], ?_⟩
    split <;> trivial
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    let s1 : State := { params := [.i64 pa, .i64 0, .i64 d], locals := List.replicate 9 z }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, s1, rfl, rfl, heap, 0, s1, rfl, Heap.Rebuilt.null hHeap⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    have hOwnedN := hOwned
    obtain ⟨hHead, hl, hk, hr, -⟩ := hOwned
    simp only [Nat.zero_add, Nat.reduceAdd] at hk hr
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    have hDisjointN := hDisjoint
    change (Node.blocks initial p (encode (.node l k r))).Pairwise regionsDisjoint at hDisjoint
    rw [blocks_node] at hDisjoint
    obtain ⟨hPl, hPr, hlr⟩ := List.pairwise_append.mp (List.pairwise_cons.mp hDisjoint).2
    have hBlocksN : Node.blocks initial p (encode (.node l k r)) = block initial p ::
        (Node.blocks initial pl (encode l) ++ Node.blocks initial pr (encode r)) :=
      blocks_node initial p k l r
    have hApartL : ∀ s ∈ Node.slotRegions initial pa (encode g),
        ∀ c ∈ Node.blocks initial pl (encode l), regionsDisjoint s c := fun s hs c hc =>
      hApartAll s hs c (by rw [hBlocksN]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hc))
    let ps : List Value := [.i64 pa, .i64 p, .i64 d]
    let s1 : State := { params := ps, locals := [z, .i64 pl, z, z, z, z, z, z, z] }
    let s2 : State := { params := ps, locals := [z, .i64 pl, .i64 k, z, z, z, z, z, z] }
    let s3 : State := { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, z, z, z, z, z] }
    let s4 (q1 : UInt64) : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 q1, z, z, z, z] }
    let s5 (q1 key x y w : UInt64) : State :=
      { params := ps,
        locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 q1, .i64 key, .i64 x, .i64 y, .i64 w] }
    let s6 (q1 key x y w : UInt64) : State :=
      { params := ps,
        locals := [.i64 p, .i64 pl, .i64 k, .i64 pr, .i64 q1, .i64 key, .i64 x, .i64 y, .i64 w] }
    -- The right child, lent to the recursive call, and the left child, consumed by it.
    obtain ⟨hB1, hSep1⟩ := treePair_args (NodeOwned.borrowed _ _ hr) hl hPl
      fun s hs c hc => NodeOwned.slotRegions_apart _ _ hr
        (fun b hb => regionsDisjoint_symm (hlr c hc b hb)) s hs
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap1 : Heap) (q1 : UInt64), st = s4 q1 ∧
          heap.Rebuilt initial ((Represent.moves initial [.i64 pr, .i64 pl] (r, Moved.mk l)).map
            (block initial)) heap1 s q1 (Encode.encode (leftSpineMoved (r, ⟨l⟩)))) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl, rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, by rw [h2]; rfl, rfl, rfl⟩
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih (r, ⟨l⟩) (by simp; omega)) hHeap
          hB1 hSep1 hCap (d := d + 1) rfl fun q => by simp [State.setAll, State.set?, s3, s4, ps]
      refine Triple.of_forall fun store1 st ⟨heap1, q1, hst, hR1⟩ => ?_
      subst hst
      have hR1' : heap.Rebuilt initial (Node.blocks initial pl (encode l)) heap1 store1 q1
          (encode (KeyTree.leftSpine r l)) := by
        have h : heap.Rebuilt initial ((Node.pointers initial pl (encode l)).map (block initial))
            heap1 store1 q1 (encode (KeyTree.leftSpine r l)) := hR1
        rwa [Node.pointers_blocks] at h
      -- The borrowed tree and the lent right child survive the call.
      obtain ⟨hA1, -, -⟩ := Heap.Keeps.nodeBorrowed hR1'.region hA
        (EncodeSlotted.slotRegions_pos g) hApartL
      obtain ⟨hr1, hrBlocks1, -⟩ := hR1'.keepNode hr fun b hb c hc =>
        regionsDisjoint_symm (hlr c hc b hb)
      have hPr1 : (Node.blocks store1 pr (encode r)).Pairwise regionsDisjoint := by
        rw [hrBlocks1]; exact hPr
      refine Stmt.seq_spec (M := fun s st => s = store1 ∧ ∃ x y w : UInt64,
          st = s5 q1 (rootKeyOf g) x y w) ?_ ?_
      · -- The borrowed tree's root key, read from its record.
        cases g with
        | leaf =>
          obtain rfl : pa = 0 := hA1
          refine (Stmt.ite_spec (PThen := fun s st => s = store1 ∧ st = s4 q1)
            (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
            Triple.of_false).mono ?_ fun _ _ h => h
          · rintro s st ⟨rfl, rfl⟩
            exact ⟨0, s4 q1, s5 q1 0 0 0 0, rfl, rfl, rfl, 0, 0, 0, rfl⟩
          · rintro s st ⟨rfl, rfl⟩
            exact ⟨true, s4 q1, by simp [Expr.eval, s4, State.get, ps], rfl, rfl⟩
        | node gl gk gr =>
          obtain ⟨hRecG, -, hGk, -, -⟩ := hA1
          simp only [Nat.zero_add] at hGk
          have hNonzeroG := hRecG.nonzero
          have hAddressG := hRecG.address
          have hBelowG := hRecG.below
          have hTop1 := hR1'.at_.top
          simp only [List.length_cons, List.length_nil] at hAddressG hBelowG
          have g0 : (pa + 0).toUInt32 = slotAddress pa 0 := by simp [slotAddress]
          have g1 : (pa + 8).toUInt32 = slotAddress pa 1 := by simp [slotAddress]
          have g2 : (pa + 16).toUInt32 = slotAddress pa 2 := by simp [slotAddress]
          have ga0 := slotAddress_toNat (p := pa) (i := 0) (by omega)
          have ga1 := slotAddress_toNat (p := pa) (i := 1) (by omega)
          have ga2 := slotAddress_toNat (p := pa) (i := 2) (by omega)
          let x := store1.mem.read64 (slotAddress pa 0)
          let w := store1.mem.read64 (slotAddress pa 2)
          refine (Stmt.ite_spec (PThen := fun _ _ => False)
            (PElse := fun s st => s = store1 ∧ st = s4 q1) Triple.of_false ?_).mono ?_
              fun _ _ h => h
          · refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s5 q1 0 x 0 0) ?_ <|
              Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s5 q1 0 x gk 0) ?_ <|
              Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s5 q1 0 x gk w) ?_ ?_
            · refine Stmt.load_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              refine ⟨pa + 0, s4 q1, s5 q1 0 x 0 0, rfl, by rw [g0, ga0]; omega, ?_, rfl, rfl⟩
              rw [g0]
              rfl
            · refine Stmt.load_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              refine ⟨pa + 8, s5 q1 0 x 0 0, s5 q1 0 x gk 0, rfl, by rw [g1, ga1]; omega, ?_, rfl,
                rfl⟩
              rw [g1, hGk]
              rfl
            · refine Stmt.load_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              refine ⟨pa + 16, s5 q1 0 x gk 0, s5 q1 0 x gk w, rfl, by rw [g2, ga2]; omega, ?_,
                rfl, rfl⟩
              rw [g2]
              rfl
            · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
              rintro s st ⟨rfl, rfl⟩
              exact ⟨gk, s5 q1 0 x gk w, s5 q1 gk x gk w, rfl, rfl, rfl, x, gk, w, rfl⟩
          · rintro s st ⟨rfl, rfl⟩
            exact ⟨false, s4 q1, by simp [Expr.eval, s4, State.get, ps, hNonzeroG], rfl, rfl⟩
      refine Triple.of_forall fun s st ⟨hs, x, y, w, hst⟩ => ?_
      subst s hst
      -- The lent right child, released.
      refine Stmt.seq_spec (M := fun s st => st = s5 q1 (rootKeyOf g) x y w ∧ ∃ heap2 : Heap,
          heap1.Rebuilt store1 (Node.blocks store1 pr (encode r)) heap2 s 0 .null)
        (Stmt.releaseNode_rebuilt hImports hRelease rfl hR1'.at_ hr1 hPr1) ?_
      refine Triple.of_forall fun store2 st ⟨hst, heap2, hR2⟩ => ?_
      subst hst
      have hBound := rebuilt_bound (mr := .leaf) hOwnedN hDisjointN hR1' hR2
      let w0 := store2.mem.write64 (slotAddress p 0) q1
      let w1 := w0.write64 (slotAddress p 1) (k + rootKeyOf g)
      let w2 := w1.write64 (slotAddress p 2) 0
      let sv := s5 q1 (rootKeyOf g) x y w
      refine Stmt.seq_spec (M := fun s st => s = { store2 with mem := w0 } ∧ st = sv) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w1 } ∧ st = sv) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w2 } ∧ st = sv) ?_ ?_
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, sv, q1, sv, rfl, rfl, by rw [h0, hs0]; omega, ?_⟩
        rw [h0]
        exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, sv, k + rootKeyOf g, sv, rfl, rfl, ?_, ?_⟩
        · rw [h1, hs1]
          simp only [w0, Wasm.Mem.write64_pages]
          omega
        · rw [h1]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, sv, 0, sv, rfl, rfl, ?_, ?_⟩
        · rw [h2, hs2]
          simp only [w1, w0, Wasm.Mem.write64_pages]
          omega
        · rw [h2]
          exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        have hRead0 : w2.read64 (slotAddress p 0) = q1 := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega),
            Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead1 : w2.read64 (slotAddress p 1) = k + rootKeyOf g := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead2 : w2.read64 (slotAddress p 2) = 0 := Memory.read64_write64 _ _ _
        have hNode := Heap.Rebuilt.node (heap := heap) hOwnedN hDisjointN hR1' hR2
          (writes3 store2 p q1 (k + rootKeyOf g) 0 (by omega)) hRead0 hRead1 hRead2
        refine ⟨p, sv, s6 q1 (rootKeyOf g) x y w, rfl, rfl, heap2, p,
          s6 q1 (rootKeyOf g) x y w, rfl, ?_⟩
        have hGone : (Represent.moves initial ([.i64 pa] ++ [.i64 p])
            (g, Moved.mk (KeyTree.node l k r))).map
            (block initial) = Node.blocks initial p (encode (.node l k r)) := by
          show (Node.pointers initial p (encode (.node l k r))).map (block initial) = _
          rw [Node.pointers_blocks]
        rw [hGone]
        show heap.Rebuilt initial _ heap2 _ p (encode (KeyTree.leftSpine g (.node l k r)))
        rw [leftSpine_node]
        exact hNode
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem leftSpine_implements : Implements treeMoves.module 13 leftSpineMoved :=
  Func.entry_rebuilds treeMoves.funcs 11 treeMoves.leftSpine.ir "leftSpine" rfl leftSpineMoved
    (g := treeMoves.leftSpine.rec.ir.function (2 + 15))
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, rfl, -⟩; rfl) rfl rfl
    rfl (compile_funcs (i := 15) rfl) rfl
    (by
      rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, rfl, -⟩
      simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a, b], _ =>
        exact ⟨_, rfl, by simp [State.get, Func.state, treeMoves.leftSpine.ir, Func.locals]⟩)
    leftSpine_rec

/-- `encode` succeeds on `treeMoves.module`, and its bytes decode to a module that computes
`KeyTree.setKey`, `KeyTree.incr`, `KeyTree.insert`, `KeyTree.dropRight`, `KeyTree.leftChild`,
`KeyTree.keepIf`, `KeyTree.trim`, `KeyTree.insertTwo`, `KeyTree.addRoot`, `KeyTree.addAll`,
`KeyTree.addLeft`, and `KeyTree.leftSpine` on a consumed tree exactly. -/
theorem treeMoves_bytes : ∃ bytes, Wasm.Encoding.encode treeMoves.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 setKeyMoved ∧
      Implements m 3 incrMoved ∧ Implements m 4 insertMoved ∧ Implements m 5 dropRightMoved ∧
      Implements m 6 leftChildMoved ∧ Implements m 7 keepIfMoved ∧ Implements m 8 trimMoved ∧
      Implements m 9 insertTwoMoved ∧ Implements m 10 addRootMoved ∧
      Implements m 11 addAllMoved ∧ Implements m 12 addLeftMoved ∧
      Implements m 13 leftSpineMoved := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip treeMoves.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, treeMoves.module, decoded, setKey_implements, incr_implements,
    insert_implements, dropRight_implements, leftChild_implements, keepIf_implements,
    trim_implements, insertTwo_implements, addRoot_implements, addAll_implements,
    addLeft_implements, leftSpine_implements⟩

#print axioms treeMoves_bytes

end Project.Trees
