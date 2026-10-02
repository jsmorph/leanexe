import Project.Trees.Moves
import Project.Trees.Encode
import Project.IR.Recursion
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
      refine ⟨0, start, start, rfl, rfl, heap, hHeap, rfl, fun _ _ h _ => h,
        fun _ _ h _ => ⟨h, rfl⟩, [.i64 0], start,
        by simp [treeMoves.setKey.ir, Func.scratch, Expr.evalResults, Expr.eval, start, State.get],
        ⟨0, rfl, rfl, .nil⟩, fun _ _ _ _ b hb => ?_, fun _ _ _ _ b hb => ?_⟩
      · change b ∈ Node.blocks _ 0 .null at hb
        cases hb
      · change b ∈ Node.blocks _ 0 .null at hb
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
        refine ⟨p, s3, s4, rfl, rfl, heap, hAt, rfl, fun q ws hq hApart => ?_,
          fun q ws hq hApart => ?_, [.i64 p], s4,
          by simp [treeMoves.setKey.ir, Func.scratch, Expr.evalResults, Expr.eval, State.get, s4, ps],
          ⟨p, rfl, hResult ▸ hOwned', by rw [hResult, hBlocks]; exact hDisjoint⟩,
          fun q ws hq hApart b hb => ?_, fun q ws hq hApart b hb => ?_⟩
        · exact hq.keep (le_of_eq hWrites.2.1.symm) (hKeep _ (hApart p hRoot)) hq.region
        · exact hq.keep (le_of_eq hWrites.2.1.symm) (hKeep _ (hApart p hRoot)) hq.region
        · change b ∈ Node.blocks final p (Encode.encode (setKeyMoved (k, ⟨.node l key r⟩))) at hb
          rw [hResult, hBlocks] at hb
          exact apart_pointers.mp hApart b hb
        · change b ∈ Node.blocks final p (Encode.encode (setKeyMoved (k, ⟨.node l key r⟩))) at hb
          rw [hResult, hBlocks] at hb
          exact apart_pointers.mp hApart b hb
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

/-- The premises of the first self-call, from the internal function's own premises. -/
theorem incr_call1 {heap : Heap} {initial : Store Unit} {p k : UInt64} {l r : KeyTree}
    (hArg : Represent.borrowed heap initial [.i64 p] (Moved.mk (KeyTree.node l k r))) :
    Represent.borrowed heap initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l) ∧
      Separate initial
        (Represent.moves initial [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l))
        (Represent.reads [.i64 (initial.mem.read64 (slotAddress p 0))] (Moved.mk l)) := by
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
        (Represent.reads [.i64 (initial.mem.read64 (slotAddress p 2))] (Moved.mk r)) := by
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
theorem incr_rec : ∀ t, Rebuilds (compile treeMoves.funcs) (2 + 3) incrMoved t := by
  refine Func.rebuildRecursion treeMoves.funcs 3 treeMoves.incr.rec.ir "incr.rec" rfl incrMoved
    (fun t => sizeOf t.val) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl)
    fun ⟨t⟩ ih heap initial vs d hHeap hArgs _ hCap => ?_
  have hArg := hArgs
  obtain ⟨p, rfl, hOwned, -⟩ := hArgs
  have hCallee : (compile treeMoves.funcs).funcs[2 + 3 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.incr.rec.ir.function (2 + 3)) := compile_funcs (i := 3) rfl
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 6 (.i64 0) }
  have hStart : treeMoves.incr.rec.ir.state ([.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + 3) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call (2 + 3) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [7])
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
          have := hR2.pages
          have := hR1.pages
          omega
        · rw [h0]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s5 a b, k + 1, s5 a b, rfl, rfl, ?_, ?_⟩
        · rw [h1, hs1]
          have := hR2.pages
          have := hR1.pages
          simp only [w0, Wasm.Mem.write64_pages]
          omega
        · rw [h1]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s5 a b, b, s5 a b, rfl, rfl, ?_, ?_⟩
        · rw [h2, hs2]
          have := hR2.pages
          have := hR1.pages
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
    (g := treeMoves.incr.rec.ir.function (2 + 3)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl
    rfl (compile_funcs (i := 3) rfl) rfl
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
        (Represent.reads [.i64 x, .i64 q] (x, Moved.mk t)) := by
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
    by rw [hBlocks]; exact List.pairwise_singleton _ _, fun r hr => ?_, hNew.pages, hNew.caps⟩
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
theorem insert_rec : ∀ x, Rebuilds (compile treeMoves.funcs) (2 + 4) insertMoved x := by
  refine Func.rebuildRecursion treeMoves.funcs 4 treeMoves.insert.rec.ir "insert.rec" rfl
    insertMoved (fun x => sizeOf x.2.val) (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl)
    fun ⟨x, ⟨t⟩⟩ ih heap initial vs d hHeap hArgs _ hCap => ?_
  obtain ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ := hArgs
  rw [show Scalar.values x ++ [Value.i64 p] = [.i64 x, .i64 p] from rfl, pair_gone]
  have hCallee : (compile treeMoves.funcs).funcs[2 + 4 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.insert.rec.ir.function (2 + 4)) := compile_funcs (i := 4) rfl
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
                  (.seq (.call (2 + 4) [⟨.u64, .get 0⟩, ⟨.u64, .get 5⟩,
                      ⟨.u64, .bin .add (.get 2) (.const 1)⟩] [9])
                    (.seq (.store (.bin .add (.get 1) (.const 0)) (.get 9)) (.assign 8 (.get 1))))
                  (.seq (.ite (.ltU (.get 6) (.get 0))
                      (.seq (.call (2 + 4) [⟨.u64, .get 0⟩, ⟨.u64, .get 7⟩,
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
              have := hR1.pages
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
                  have := hR2.pages
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
    (g := treeMoves.insert.rec.ir.function (2 + 4))
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) rfl rfl rfl (compile_funcs (i := 4) rfl) rfl
    (by
      rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩
      simp [Expr.evalResults, Expr.eval, Func.state, State.get, Scalar.values])
    (by
      intro params v hLen
      match params, hLen with
      | [a, b], _ =>
        exact ⟨_, rfl, by simp [State.get, Func.state, treeMoves.insert.ir, Func.locals]⟩)
    insert_rec

/-- `encode` succeeds on `treeMoves.module`, and its bytes decode to a module that computes
`KeyTree.setKey`, `KeyTree.incr`, and `KeyTree.insert` on a consumed tree exactly. -/
theorem treeMoves_bytes : ∃ bytes, Wasm.Encoding.encode treeMoves.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 setKeyMoved ∧
      Implements m 3 incrMoved ∧ Implements m 4 insertMoved := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip treeMoves.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, treeMoves.module, decoded, setKey_implements, incr_implements,
    insert_implements⟩

#print axioms treeMoves_bytes

end Project.Trees
