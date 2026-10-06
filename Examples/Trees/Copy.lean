import Examples.Trees.Encode
import Project.IR.Copy
import Project.IR.Recursion
import Project.IR.Record

/-! `KeyTree`'s copy function, which the compiler generates as `Func.copy [true, false, true]`
for a module that copies a tree, rebuilds a borrowed tree in new records. -/

namespace Examples.Trees

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Trees

/-- `KeyTree`'s copy function, at any index of any module: at any depth, a call on a borrowed
tree aborts or returns a pointer to an equal tree in new records, and keeps every region of the
heap. -/
theorem copy_rec (funcs : List (Func × String)) (i : Nat) (name : String)
    (hFunc : funcs[i]? = some (Func.copy [true, false, true] (2 + i), name)) :
    ∀ t : KeyTree, Rebuilds (compile funcs) (2 + i) (fun t : KeyTree => t) t := by
  have hCallee : (compile funcs).funcs[2 + i - (compile funcs).imports.length]? =
      some ((Func.copy [true, false, true] (2 + i)).function (2 + i)) := compile_funcs hFunc
  have hMemory32 : (compile funcs).memIs64 = false := rfl
  have hImports : (compile funcs).imports = [] := rfl
  have hAlloc : (compile funcs).funcs[0]? = some (allocFunction 0) := rfl
  refine Func.rebuildRecursion funcs i (Func.copy [true, false, true] (2 + i)) name hFunc
    (fun t => t) (fun t => sizeOf t) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl)
    fun t ih heap initial vs d hHeap hArgs _ hCap => ?_
  obtain ⟨p, rfl, hNode⟩ := hArgs
  have hGone : (Represent.moves initial [Value.i64 p] t).map (block initial) = [] := rfl
  rw [hGone]
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 7 (.i64 0) }
  have hStart : (Func.copy [true, false, true] (2 + i)).state ([.i64 p] ++ [.i64 d]) = start :=
    rfl
  have hScratch : (Func.copy [true, false, true] (2 + i)).scratch = 9 := rfl
  have hResults : (Func.copy [true, false, true] (2 + i)).results = [⟨.u64, .get 2⟩] := rfl
  rw [hStart, hScratch, hResults]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + i) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call (2 + i) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                    [7])
                  (.seq (Stmt.record 8 [.get 6, .get 4, .get 7] 5) (.assign 2 (.get 8)))))))))) 9
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
    obtain rfl : p = 0 := hNode
    let s1 : State := { params := [.i64 0, .i64 d], locals := .i64 0 :: List.replicate 6 (.i64 0) }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, start, rfl, rfl, heap, 0, start,
        by simp [Expr.evalResults, Expr.eval, start, State.get],
        Heap.Rebuilt.null hHeap⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hSlots, hl, hk, hr, -⟩ := hNode
    simp only [Nat.zero_add, Nat.reduceAdd] at hk hr
    have hNonzero := hSlots.nonzero
    have hAddress := hSlots.address
    have hBelow := hSlots.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hAddress hBelow
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let ps : List Value := [.i64 p, .i64 d]
    let sf (a b c x y z : UInt64) : State :=
      { params := ps, locals := [.i64 0, .i64 a, .i64 b, .i64 c, .i64 x, .i64 y, .i64 z] }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = sf pl 0 0 0 0 0) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = sf pl k 0 0 0 0) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = sf pl k pr 0 0 0) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap1 : Heap) (q1 : UInt64),
          st = sf pl k pr q1 0 0 ∧ heap.Rebuilt initial [] heap1 s q1 (encode l)) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 0, start, sf pl 0 0 0 0 0, rfl, by rw [h0, hs0]; omega, by rw [h0]; rfl, rfl,
          rfl⟩
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, sf pl 0 0 0 0 0, sf pl k 0 0 0 0, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hk]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 16, sf pl k 0 0 0 0, sf pl k pr 0 0 0, rfl, by rw [h2, hs2]; omega,
          by rw [h2]; rfl, rfl, rfl⟩
      · exact Stmt.selfCall_rebuilds rfl hCallee rfl (ih l (by simp; omega)) hHeap ⟨pl, rfl, hl⟩
          Separate.nil hCap (d := d + 1) rfl fun q => by simp [State.setAll, State.set?, sf, ps]
      refine Triple.of_forall fun store1 st ⟨heap1, q1, hst, hR1⟩ => ?_
      subst hst
      have hB2 : NodeBorrowed heap1 store1 pr (encode r) :=
        (Heap.Keeps.nodeBorrowed hR1.region hr (EncodeSlotted.slotRegions_pos r)
          fun _ _ _ hg => nomatch hg).1
      have hCap1 := memoryCap_le_of_caps hR1.caps hCap
      refine Stmt.seq_spec (M := fun s st => ∃ (heap2 : Heap) (q2 : UInt64),
          st = sf pl k pr q1 q2 0 ∧ heap1.Rebuilt store1 [] heap2 s q2 (encode r)) ?_ ?_
      · exact Stmt.selfCall_rebuilds rfl hCallee rfl (ih r (by simp)) hR1.at_ ⟨pr, rfl, hB2⟩
          Separate.nil hCap1 (d := d + 1) rfl fun q => by simp [State.setAll, State.set?, sf, ps]
      refine Triple.of_forall fun store2 st ⟨heap2, q2, hst, hR2⟩ => ?_
      subst hst
      refine Stmt.seq_spec (Stmt.record_spec hMemory32 hImports hAlloc (by decide)
        (by simp [sf, ps]) hR2.at_ (memoryCap_le_of_caps hR2.caps hCap1) (by decide) (by decide)
        (words := [q1, k, q2]) ?_) ?_
      · refine .cons (fun _ st hF => ⟨st, ?_⟩) (.cons (fun _ st hF => ⟨st, ?_⟩)
          (.cons (fun _ st hF => ⟨st, ?_⟩) .nil))
        · have : st.get 6 = some (.i64 q1) := (hF.get 6 (by decide) (by decide)).trans rfl
          simp [Expr.eval, this]
        · have : st.get 4 = some (.i64 k) := (hF.get 4 (by decide) (by decide)).trans rfl
          simp [Expr.eval, this]
        · have : st.get 7 = some (.i64 q2) := (hF.get 7 (by decide) (by decide)).trans rfl
          simp [Expr.eval, this]
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨ptr, hF, hPtr, hNew⟩
        obtain ⟨next, hSet⟩ := State.exists_set? (state := st) (index := 2) (.i64 ptr)
          (by rw [hF.params, hF.locals]; simp [sf, ps])
        exact ⟨ptr, st, next, by simp [Expr.eval, hPtr], hSet, _, ptr, next,
          by simp [Expr.evalResults, Expr.eval, State.get_set?_same hSet],
          hR1.newNode hR2 hNew⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

end Examples.Trees
