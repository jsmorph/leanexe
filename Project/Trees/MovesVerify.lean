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
theorem incr_rec : ∀ t, Rebuilds (compile treeMoves.funcs) (2 + 2) incrMoved t := by
  refine Func.rebuildRecursion treeMoves.funcs 2 treeMoves.incr.rec.ir "incr.rec" rfl incrMoved
    (fun t => sizeOf t.val) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl)
    fun ⟨t⟩ ih heap initial vs d hHeap hArgs _ hCap => ?_
  have hArg := hArgs
  obtain ⟨p, rfl, hOwned, -⟩ := hArgs
  have hCallee : (compile treeMoves.funcs).funcs[2 + 2 - (compile treeMoves.funcs).imports.length]? =
      some (treeMoves.incr.rec.ir.function (2 + 2)) := compile_funcs (i := 2) rfl
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 6 (.i64 0) }
  have hStart : treeMoves.incr.rec.ir.state ([.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + 2) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call (2 + 2) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [7])
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
    (g := treeMoves.incr.rec.ir.function (2 + 2)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl
    rfl (compile_funcs (i := 2) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, treeMoves.incr.ir, Func.locals]⟩)
    incr_rec

/-- `encode` succeeds on `treeMoves.module`, and its bytes decode to a module that computes
`KeyTree.setKey` and `KeyTree.incr` on a consumed tree exactly. -/
theorem treeMoves_bytes : ∃ bytes, Wasm.Encoding.encode treeMoves.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 setKeyMoved ∧
      Implements m 3 incrMoved := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip treeMoves.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, treeMoves.module, decoded, setKey_implements, incr_implements⟩

#print axioms treeMoves_bytes

end Project.Trees
