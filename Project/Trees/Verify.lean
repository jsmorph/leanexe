import Project.Trees.Module
import Project.Trees.Encode
import Project.IR.Recursion
import Project.IR.Call
import Project.IR.Update
import Project.IR.Live
import Project.Pipeline.Records
import Project.Encoding.RoundTrip

/-! The compiled functions over `KeyTree` compute their Lean definitions exactly.  Each is an
entry function and an internal function that recurses with a depth parameter. -/

namespace Project.Trees

open Wasm Project.Pipeline Project.IR Project.ProofKit Project.Runtime LeanExe.Examples.Trees

/-- The internal function of a recursion over `KeyTree` whose body is the depth guard and a
match: a leaf assigns `c` to the result, and a node loads its fields, calls the function on
both subtrees into locals 6 and 7, and runs `combine`, which leaves `g (f l) k (f r)` in the
result.  At any depth, a call aborts or keeps the store and returns `f t`. -/
theorem treeRec {i : Nat} {func : Func} {name : String} (hFunc : trees.funcs[i]? = some (func, name))
    (f : KeyTree → UInt64) (c : UInt64) (g : UInt64 → UInt64 → UInt64 → UInt64)
    (hLeaf : f .leaf = c) (hNode : ∀ l k r, f (.node l k r) = g (f l) k (f r))
    (extra : Nat) (combine : Stmt)
    (hBody : func.body = .seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const c))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + i) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call (2 + i) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                  [7]) combine)))))))
    (hParams : func.params = [.u64, .u64]) (hVars : func.vars = List.replicate (6 + extra) .u64)
    (hWidth : func.width = 0) (hResults : func.results = [⟨.u64, .get 2⟩])
    (hCombine : ∀ (initial : Store Unit) (p d pl k pr a b : UInt64),
      Triple (compile trees.funcs) combine (8 + extra)
        (fun store state => store = initial ∧ state =
          { params := [.i64 p, .i64 d]
            locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] ++
              List.replicate extra (.i64 0) })
        (fun store state => store = initial ∧ ∃ next,
          Expr.evalResults store.mem (8 + extra) [⟨.u64, .get 2⟩] state =
            some ([.i64 (g a k b)], next))) :
    ∀ t, Keeps (compile trees.funcs) (2 + i) f t := by
  have hScratch : func.scratch = 8 + extra := by
    simp only [Func.scratch, hParams, hVars, List.length_cons, List.length_nil,
      List.length_replicate]
    omega
  refine Func.recursion trees.funcs i func name hFunc f (fun t => sizeOf t)
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [hParams]) fun t ih heap initial vs d hHeap hB => ?_
  obtain ⟨p, rfl, hNode'⟩ := hB
  have hCallee : (compile trees.funcs).funcs[2 + i - (compile trees.funcs).imports.length]? =
      some (func.function (2 + i)) := compile_funcs hFunc
  let zeros := List.replicate extra (Value.i64 0)
  let start : State :=
    { params := [.i64 p, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] ++ zeros }
  have hStart : func.state ([.i64 p] ++ [.i64 d]) = start := by
    simp [Func.state, Func.locals, hVars, hWidth, start, zeros, List.replicate_add,
      ScalarType.valueType, ValueType.zero]
  rw [hStart, hBody, hResults, hScratch]
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
    ((Stmt.ite_spec (PThen := fun _ _ => True) (PElse := fun s st => s = initial ∧ st = start)
      Stmt.abort_spec (Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h)).mono ?_
        fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    refine ⟨decide ((999 : UInt64) < d), start, by simp [Expr.eval, start, State.get], ?_⟩
    split <;> trivial
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hNode'
    let s1 : State :=
      { params := [.i64 0, .i64 d]
        locals := [.i64 c, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] ++ zeros }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨c, start, s1, rfl, rfl, rfl, s1,
        by simp [Expr.evalResults, Expr.eval, s1, State.get, hLeaf]⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hSlots, hl, hk, hr, -⟩ := hNode'
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
    let s1 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 0, .i64 0, .i64 0, .i64 0] ++ zeros }
    let s2 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 0, .i64 0, .i64 0] ++ zeros }
    let s3 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 0, .i64 0] ++ zeros }
    let s4 : State :=
      { params := ps
        locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 (f l), .i64 0] ++ zeros }
    let s5 : State :=
      { params := ps
        locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 (f l), .i64 (f r)] ++ zeros }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s4) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s5) ?_ ?_
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
      · exact Stmt.selfCall_spec rfl hCallee (by simp [Func.function, Func.type,
          Function.numParams, hParams]) (ih l (by simp; omega)) hHeap ⟨pl, rfl, hl⟩
          (d := d + 1) rfl (by simp [State.setAll, State.set?, s3, s4, ps, zeros]; omega)
      · exact Stmt.selfCall_spec rfl hCallee (by simp [Func.function, Func.type,
          Function.numParams, hParams]) (ih r (by simp)) hHeap ⟨pr, rfl, hr⟩
          (d := d + 1) rfl (by simp [State.setAll, State.set?, s4, s5, ps, zeros]; omega)
      · refine (hCombine initial p d pl k pr (f l) (f r)).mono (fun _ _ h => h) ?_
        rintro s st ⟨rfl, next, hEval⟩
        exact ⟨rfl, next, by rw [hNode]; exact hEval⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem size_rec : ∀ t, Keeps (compile trees.funcs) (2 + 6) KeyTree.size t :=
  treeRec (i := 6) rfl KeyTree.size 0 (fun a _ b => a + 1 + b) rfl (fun _ _ _ => rfl) 0 _ rfl
    rfl rfl rfl rfl fun initial p d pl k pr a b => by
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      let next : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 (a + 1 + b), .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] }
      exact ⟨a + 1 + b, _, next, rfl, rfl, rfl, next,
        by simp [Expr.evalResults, Expr.eval, State.get, next]⟩

theorem sum_rec : ∀ t, Keeps (compile trees.funcs) (2 + 7) KeyTree.sum t :=
  treeRec (i := 7) rfl KeyTree.sum 0 (fun a k b => a + k + b) rfl (fun _ _ _ => rfl) 0 _ rfl
    rfl rfl rfl rfl fun initial p d pl k pr a b => by
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      let next : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 (a + k + b), .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] }
      exact ⟨a + k + b, _, next, rfl, rfl, rfl, next,
        by simp [Expr.evalResults, Expr.eval, State.get, next]⟩

theorem height_rec : ∀ t, Keeps (compile trees.funcs) (2 + 8) KeyTree.height t :=
  treeRec (i := 8) rfl KeyTree.height 0 (fun a _ b => max a b + 1) rfl (fun _ _ _ => rfl) 2 _
    rfl rfl rfl rfl rfl fun initial p d pl k pr a b => by
      let s1 : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b, .i64 a, .i64 0] }
      let s2 : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b, .i64 a, .i64 b] }
      let s3 : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 (max a b + 1), .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b, .i64 a,
            .i64 b] }
      refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ ?_
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨a, _, s1, rfl, rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨b, s1, s2, rfl, rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨max a b + 1, s2, s3, ?_, rfl, rfl, s3,
          by simp [Expr.evalResults, Expr.eval, State.get, s3]⟩
        simp only [Expr.eval, State.get, s2, U64Op.apply]
        rw [show max a b = if a ≤ b then b else a from rfl]
        by_cases h : a ≤ b <;> simp [h]

theorem size_implements : Implements trees.module 2 KeyTree.size :=
  Func.entry_implements trees.funcs 0 trees.size.ir "size" rfl KeyTree.size
    (g := trees.size.rec.ir.function (2 + 6)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 6) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.size.ir, Func.locals]⟩)
    size_rec

theorem sum_implements : Implements trees.module 3 KeyTree.sum :=
  Func.entry_implements trees.funcs 1 trees.sum.ir "sum" rfl KeyTree.sum
    (g := trees.sum.rec.ir.function (2 + 7)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 7) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.sum.ir, Func.locals]⟩)
    sum_rec

theorem height_implements : Implements trees.module 4 KeyTree.height :=
  Func.entry_implements trees.funcs 2 trees.height.ir "height" rfl KeyTree.height
    (g := trees.height.rec.ir.function (2 + 8)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 8) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.height.ir, Func.locals]⟩)
    height_rec

/-- `sizeSum` calls `size` and then `sum` on its borrowed tree.  `size`'s `Implements` theorem
keeps the tree for the second call (`Heap.Keeps.nodeBorrowed`). -/
theorem sizeSum_implements : Implements trees.module 5 KeyTree.sizeSum := by
  refine Func.implements_heap trees.funcs 3 trees.sizeSum.ir "sizeSum" rfl KeyTree.sizeSum
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro t heap initial _ hHeap hB hCap
  obtain ⟨p, rfl, hNode⟩ := id hB
  let start : State := { params := [.i64 p], locals := [.i64 0, .i64 0] }
  show Triple _ (.seq (.call (2 + 0) [⟨.u64, .get 0⟩] [1]) (.call (2 + 1) [⟨.u64, .get 0⟩] [2])) 3
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.callImplements_spec size_implements rfl (compile_funcs (i := 0) rfl)
    rfl (before := start) (results := [1]) (x := t) rfl hHeap hB Separate.nil hCap
    (fun _ _ _ h => by rw [show _ = _ from h]; exact ⟨_, rfl⟩)) ?_
  apply Triple.of_forall
  rintro s1 st1 ⟨heap1, values1, hAt1, hOwned1, hCaps1, hK1, hSet1⟩
  obtain rfl : values1 = [.i64 t.size] := hOwned1
  obtain rfl : st1 = { params := [.i64 p], locals := [.i64 t.size, .i64 0] } :=
    (Option.some.inj (hSet1.symm.trans rfl))
  have hB1 : NodeBorrowed heap1 s1 p (encode t) :=
    (hK1.nodeBorrowed hNode (EncodeSlotted.slotRegions_pos t) fun _ _ _ hg => nomatch hg).1
  refine (Stmt.callImplements_spec sum_implements rfl (compile_funcs (i := 1) rfl) rfl
    (results := [2]) (x := t) rfl hAt1 ⟨p, rfl, hB1⟩ Separate.nil
    (memoryCap_le_of_caps hCaps1 hCap)
    (fun _ _ _ h => by rw [show _ = _ from h]; exact ⟨_, rfl⟩)).mono (fun _ _ h => h) ?_
  rintro s2 st2 ⟨heap2, values2, hAt2, hOwned2, hCaps2, hK2, hSet2⟩
  obtain rfl : values2 = [.i64 t.sum] := hOwned2
  obtain rfl : st2 = { params := [.i64 p], locals := [.i64 t.size, .i64 t.sum] } :=
    (Option.some.inj (hSet2.symm.trans rfl))
  exact ⟨heap2, hAt2, hCaps2.trans hCaps1, _, _, rfl, rfl,
    hK1.trans hK2 fun _ _ _ _ hb => nomatch hb⟩

/-- `pushSum` with its two arguments as one pair, the array handed over. -/
def pushSumMoved (x : Moved (Array UInt64) × KeyTree) : Array UInt64 × UInt64 :=
  KeyTree.pushSum x.1.val x.2

/-- `pushSum` pushes onto its array in place and then calls `sum` on its borrowed tree.  The
premise of `Implements` keeps the tree's record slots apart from the array's block, so the
push's frame keeps the tree for the call. -/
theorem pushSum_implements : Implements trees.module 6 pushSumMoved := by
  refine Func.implements_moves trees.funcs 4 trees.pushSum.ir "pushSum" rfl pushSumMoved
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨⟨xs⟩, t⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨p, rfl, hOwned⟩, ⟨q, rfl, hNode⟩⟩ hSep hCap
  change heap.Owned initial p xs at hOwned
  have hApart : ∀ b ∈ Node.slotRegions initial q (encode t), regionsDisjoint b (block initial p) :=
    fun b hb => hSep.2 b hb p (List.mem_singleton_self _)
  have hMemory32 : (compile trees.funcs).memIs64 = false := rfl
  have hImports : (compile trees.funcs).imports = [] := rfl
  have hAlloc : (compile trees.funcs).funcs[0]? = some (allocFunction 0) := rfl
  have hRelease : (compile trees.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 p, .i64 q], locals := List.replicate 8 (.i64 0) }
  let s1 : State := { params := [.i64 p, .i64 q], locals := .i64 1 :: List.replicate 7 (.i64 0) }
  have hStart : trees.pushSum.ir.state ([.i64 p] ++ [.i64 q]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.assign 2 (.const 1))
    (.seq (Stmt.pushInPlace 0 3 2 4 5 6 7) (.call (2 + 1) [⟨.u64, .get 1⟩] [8]))) 9 _ _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1)
    (Stmt.assign_spec.mono ?_ fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    exact ⟨1, start, s1, rfl, rfl, rfl, rfl⟩
  have hL0 : Live heap initial [p] heap initial [(p, xs)] :=
    Live.start_moved hHeap (temps := [(p, xs)])
      (fun u hu => by rw [List.mem_singleton.mp hu]; exact hOwned) (List.pairwise_singleton _ _)
  refine Stmt.seq_spec ((Stmt.pushInPlace_spec (before := s1) (vw := 1) hMemory32 hImports
    hAlloc hRelease (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [s1]) rfl rfl hHeap hCap hOwned).mono (fun _ _ h => h)
      fun _ _ h => Live.appendPost (pre := []) (t := (p, xs)) (post := []) hL0 h) ?_
  apply Triple.of_forall
  rintro s2 st2 ⟨heap1, p1, hL1, hF1, g20⟩
  -- The tree is kept through the push: its slot regions lie apart from the consumed block.
  have hB1 : NodeBorrowed heap1 s2 q (encode t) :=
    (hL1.keeps.nodeBorrowed hNode (EncodeSlotted.slotRegions_pos t) fun b hb g hg => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hg
      subst hg
      exact hApart b hb).1
  have g21 : st2.get 1 = some (.i64 q) := by
    rw [hF1.get 1 (by decide) (by decide)]; rfl
  have hLen2 : st2.params.length + st2.locals.length = 10 := by
    rw [hF1.params, hF1.locals]; rfl
  refine (Stmt.callImplements_spec sum_implements rfl (compile_funcs (i := 1) rfl) rfl
    (results := [8]) (x := t) (vals := [.i64 q]) (afterArgs := st2) (before := st2)
    (by simp [Expr.evalResults, Expr.eval, g21]) hL1.at_ ⟨q, rfl, hB1⟩ Separate.nil
    (hL1.cap hCap) (fun _ _ values h => ?_)).mono (fun _ _ h => h) ?_
  · rw [show values = [.i64 t.sum] from h]
    exact ⟨st2.update 8 (.i64 t.sum), by
      simp [State.setAll, State.set?_eq_update _ (show 8 < st2.params.length + st2.locals.length
        by omega)]⟩
  rintro s3 st3 ⟨heap2, values, hAt2, hOwned2, hCaps2, hK2, hSet⟩
  obtain rfl : values = [.i64 t.sum] := hOwned2
  have hSt3 : st3 = st2.update 8 (.i64 t.sum) := by
    simp [State.setAll, State.set?_eq_update _ (show 8 < st2.params.length + st2.locals.length
      by omega)] at hSet
    exact hSet.symm
  have hL2 : Live heap initial [p] heap2 s3 ([] ++ [(p1, xs.push 1)]) :=
    Live.step (consumed := []) (news := []) hL1 hAt2 hCaps2
      (hK2.mono (fun b hb => nomatch hb) fun _ hb => nomatch hb) (fun _ h => nomatch h) .nil
  rw [List.nil_append] at hL2
  have g30 : st3.get 0 = some (.i64 p1) := by
    rw [hSt3, State.get_update_ne (by decide)]; exact g20
  have g38 : st3.get 8 = some (.i64 t.sum) := by
    rw [hSt3]; exact State.get_update_same (by omega)
  refine ⟨heap2, hL2.at_, hL2.caps, [.i64 p1, .i64 t.sum], st3,
    Expr.evalResults_get g30 (Expr.evalResults_get g38 rfl),
    ⟨[.i64 p1], [.i64 t.sum], rfl, ⟨p1, rfl, hL2.tempsOwned _ List.mem_cons_self⟩, rfl,
      fun _ _ _ h => nomatch h⟩, ?_⟩
  exact hL2.keeps.mono (fun _ h => h) fun b hb => by
    simpa [Represent.blocks, Represent.width] using hb

/-- `dropSmall` with its two arguments as one pair, the tree consumed. -/
def dropSmallMoved (x : UInt64 × Moved KeyTree) : KeyTree := KeyTree.dropSmall x.1 x.2.val

/-- `dropSmall` lends its owned tree to `size` (`NodeOwned.borrowed`), takes it back owned from
`size`'s frame (`Heap.Keeps.node`), and then releases or returns it. -/
theorem dropSmall_implements : Implements trees.module 7 dropSmallMoved := by
  refine Func.implements_rebuilt trees.funcs 5 trees.dropSmall.ir "dropSmall" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  have hGone : (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
      (block initial) = Node.blocks initial p (encode t) := Node.pointers_blocks initial p (encode t)
  rw [hGone]
  have hImports : (compile trees.funcs).imports = [] := rfl
  have hRelease : (compile trees.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 0] }
  let s1 : State := { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 t.size] }
  let sThen : State := { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 t.size] }
  let sElse : State := { params := [.i64 n, .i64 p], locals := [.i64 p, .i64 t.size] }
  have hStart : trees.dropSmall.ir.state (Scalar.values n ++ [.i64 p]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.call (2 + 0) [⟨.u64, .get 1⟩] [3])
      (.ite (.ltU (.get 3) (.get 0)) (.seq (.assign 2 (.const 0)) (.release 1))
        (.assign 2 (.get 1)))) 4
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.callImplements_spec size_implements rfl (compile_funcs (i := 0) rfl)
    rfl (before := start) (results := [3]) (x := t) rfl hHeap
    ⟨p, rfl, NodeOwned.borrowed p _ hOwned⟩ Separate.nil hCap
    (fun _ _ _ h => by rw [show _ = _ from h]; exact ⟨_, rfl⟩)) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, values1, hAt1, hOwned1, hCaps1, hK1, hSet1⟩ => ?_
  obtain rfl : values1 = [.i64 t.size] := hOwned1
  obtain rfl : st = s1 := (Option.some.inj (hSet1.symm.trans rfl))
  -- The tree comes back owned with the same blocks, since `size` consumes nothing.
  obtain ⟨hOwnedT, hBlocks, -⟩ := Heap.Keeps.node hK1 hOwned fun _ _ _ hg => nomatch hg
  have hDisjoint1 : (Node.blocks store1 p (encode t)).Pairwise regionsDisjoint := by
    rw [hBlocks]; exact hDisjoint
  have hK : heap.Keeps initial (Node.blocks initial p (encode t)) heap1 store1 [] :=
    hK1.mono (fun _ hb => nomatch hb) fun _ hb => nomatch hb
  have hAfter : ∀ r, (∀ b ∈ Node.blocks initial p (encode t), regionsDisjoint r b) →
      (∀ b ∈ ([] : List (Nat × Nat)), regionsDisjoint r b) →
      ∀ b ∈ Node.blocks store1 p (encode t), regionsDisjoint r b := fun _ hr _ b hb =>
    hr b (by rwa [hBlocks] at hb)
  refine (Stmt.ite_spec (PThen := fun s st => s = store1 ∧ st = s1 ∧ t.size < n)
    (PElse := fun s st => s = store1 ∧ st = s1 ∧ ¬ t.size < n) ?_ ?_).mono ?_ fun _ _ h => h
  · -- A leaf, and the tree released.
    refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = sThen ∧ t.size < n) ?_ ?_
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, rfl, hc⟩
      exact ⟨0, s1, sThen, rfl, rfl, hs, rfl, hc⟩
    · refine Triple.of_forall fun s st ⟨hs, hst, hc⟩ => ?_
      subst s hst
      refine (Stmt.releaseNode_rebuilt hImports hRelease rfl hAt1 hOwnedT hDisjoint1).mono
        (fun _ _ h => h) ?_
      rintro s' st' ⟨rfl, heap', hR⟩
      have hv : dropSmallMoved (n, ⟨t⟩) = .leaf := by simp [dropSmallMoved, KeyTree.dropSmall, hc]
      refine ⟨heap', 0, sThen, rfl, ?_⟩
      rw [hv]
      exact Heap.Keeps.rebuilt hK hCaps1 hR hAfter
  · -- The tree, returned.
    refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro s st ⟨hs, rfl, hc⟩
    subst s
    have hv : dropSmallMoved (n, ⟨t⟩) = t := by simp [dropSmallMoved, KeyTree.dropSmall, hc]
    refine ⟨p, s1, sElse, rfl, rfl, heap1, p, sElse, rfl, ?_⟩
    rw [hv]
    exact Heap.Keeps.rebuilt hK hCaps1 (Heap.Rebuilt.refl hAt1 hOwnedT hDisjoint1) hAfter
  · rintro s st ⟨rfl, rfl⟩
    by_cases hc : t.size < n
    · exact ⟨true, s1, by simp [Expr.eval, s1, State.get, hc], rfl, rfl, hc⟩
    · exact ⟨false, s1, by simp [Expr.eval, s1, State.get, hc], rfl, rfl, hc⟩

/-- `encode` succeeds on `trees.module`, and its bytes decode to a module that computes
`KeyTree.size`, `KeyTree.sum`, `KeyTree.height`, `KeyTree.sizeSum`, `KeyTree.pushSum`, and
`KeyTree.dropSmall` exactly. -/
theorem trees_bytes : ∃ bytes, Wasm.Encoding.encode trees.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 KeyTree.size ∧
      Implements m 3 KeyTree.sum ∧ Implements m 4 KeyTree.height ∧
      Implements m 5 KeyTree.sizeSum ∧ Implements m 6 pushSumMoved ∧
      Implements m 7 dropSmallMoved := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip trees.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, trees.module, decoded, size_implements, sum_implements,
    height_implements, sizeSum_implements, pushSum_implements, dropSmall_implements⟩

#print axioms trees_bytes

end Project.Trees
