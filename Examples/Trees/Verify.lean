import Examples.Trees.Module
import Examples.Trees.Encode
import Examples.Trees.Node
import LeanExe.IR.Recursion
import LeanExe.IR.Call
import LeanExe.IR.Update
import LeanExe.IR.Live
import LeanExe.Pipeline.Records
import LeanExe.Encoding.RoundTrip

/-! The compiled functions over `KeyTree` compute their Lean definitions exactly.  Each is an
entry function and an internal function that recurses with a depth parameter. -/

namespace Examples.Trees

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.ProofKit LeanExe.Runtime Examples.Trees

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

theorem size_rec : ∀ t, Keeps (compile trees.funcs) (2 + 17) KeyTree.size t :=
  treeRec (i := 17) rfl KeyTree.size 0 (fun a _ b => a + 1 + b) rfl (fun _ _ _ => rfl) 0 _ rfl
    rfl rfl rfl rfl fun initial p d pl k pr a b => by
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      let next : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 (a + 1 + b), .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] }
      exact ⟨a + 1 + b, _, next, rfl, rfl, rfl, next,
        by simp [Expr.evalResults, Expr.eval, State.get, next]⟩

theorem sum_rec : ∀ t, Keeps (compile trees.funcs) (2 + 18) KeyTree.sum t :=
  treeRec (i := 18) rfl KeyTree.sum 0 (fun a k b => a + k + b) rfl (fun _ _ _ => rfl) 0 _ rfl
    rfl rfl rfl rfl fun initial p d pl k pr a b => by
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      let next : State :=
        { params := [.i64 p, .i64 d]
          locals := [.i64 (a + k + b), .i64 pl, .i64 k, .i64 pr, .i64 a, .i64 b] }
      exact ⟨a + k + b, _, next, rfl, rfl, rfl, next,
        by simp [Expr.evalResults, Expr.eval, State.get, next]⟩

theorem height_rec : ∀ t, Keeps (compile trees.funcs) (2 + 19) KeyTree.height t :=
  treeRec (i := 19) rfl KeyTree.height 0 (fun a _ b => max a b + 1) rfl (fun _ _ _ => rfl) 2 _
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
    (g := trees.size.rec.ir.function (2 + 17)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 17) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.size.ir, Func.locals]⟩)
    size_rec

theorem sum_implements : Implements trees.module 3 KeyTree.sum :=
  Func.entry_implements trees.funcs 1 trees.sum.ir "sum" rfl KeyTree.sum
    (g := trees.sum.rec.ir.function (2 + 18)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 18) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.sum.ir, Func.locals]⟩)
    sum_rec

theorem height_implements : Implements trees.module 4 KeyTree.height :=
  Func.entry_implements trees.funcs 2 trees.height.ir "height" rfl KeyTree.height
    (g := trees.height.rec.ir.function (2 + 19)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 19) rfl) rfl
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

/-- `sizeDrop` with its two arguments as one pair, the tree consumed. -/
def sizeDropMoved (x : UInt64 × Moved KeyTree) : UInt64 × KeyTree := KeyTree.sizeDrop x.1 x.2.val

/-- `sizeDrop` lends its tree to `size` through a word `let`, then releases it on the path whose
pair holds a leaf and returns it in the pair on the other. -/
theorem sizeDrop_implements : Implements trees.module 8 sizeDropMoved := by
  refine Func.implements_moves trees.funcs 6 trees.sizeDrop.ir "sizeDrop" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  have hGone : (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
      (block initial) = Node.blocks initial p (encode t) := Node.pointers_blocks initial p (encode t)
  rw [hGone]
  have hImports : (compile trees.funcs).imports = [] := rfl
  have hRelease : (compile trees.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let z : Value := .i64 0
  let c := t.size
  let ps : List Value := [.i64 n, .i64 p]
  let start : State := { params := ps, locals := [z, z, z, z] }
  let s1 : State := { params := ps, locals := [.i64 c, z, z, z] }
  let s2 : State := { params := ps, locals := [.i64 c, .i64 c, z, z] }
  let s3 : State := { params := ps, locals := [.i64 c, .i64 c, .i64 c, z] }
  let sElse : State := { params := ps, locals := [.i64 c, .i64 c, .i64 c, .i64 p] }
  have hStart : trees.sizeDrop.ir.state (Scalar.values n ++ [.i64 p]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.call (2 + 0) [⟨.u64, .get 1⟩] [2])
      (.seq (.assign 3 (.get 2))
        (.ite (.ltU (.get 3) (.get 0))
          (.seq (.assign 4 (.get 3)) (.seq (.assign 5 (.const 0)) (.release 1)))
          (.seq (.assign 4 (.get 3)) (.assign 5 (.get 1)))))) 6
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.callImplements_spec size_implements rfl (compile_funcs (i := 0) rfl)
    rfl (before := start) (results := [2]) (x := t) rfl hHeap
    ⟨p, rfl, NodeOwned.borrowed p _ hOwned⟩ Separate.nil hCap
    (fun _ _ _ h => by rw [show _ = _ from h]; exact ⟨_, rfl⟩)) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, values1, hAt1, hOwned1, hCaps1, hK1, hSet1⟩ => ?_
  obtain rfl : values1 = [.i64 c] := hOwned1
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
  refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s2)
    (Stmt.assign_spec.mono (fun s st ⟨hs, hst⟩ => ⟨c, s1, s2, by rw [hst]; rfl, rfl, hs, rfl⟩)
      fun _ _ h => h) ?_
  refine (Stmt.ite_spec (PThen := fun s st => s = store1 ∧ st = s2 ∧ c < n)
    (PElse := fun s st => s = store1 ∧ st = s2 ∧ ¬ c < n) ?_ ?_).mono ?_ fun _ _ h => h
  · -- A leaf in the pair, and the tree released.
    refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s3 ∧ c < n) ?_ <|
      Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s3 ∧ c < n) ?_ ?_
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, rfl, hc⟩
      exact ⟨c, s2, s3, rfl, rfl, hs, rfl, hc⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, rfl, hc⟩
      exact ⟨0, s3, s3, rfl, rfl, hs, rfl, hc⟩
    · refine Triple.of_forall fun s st ⟨hs, hst, hc⟩ => ?_
      subst s hst
      refine (Stmt.releaseNode_rebuilt hImports hRelease rfl hAt1 hOwnedT hDisjoint1).mono
        (fun _ _ h => h) ?_
      rintro s' st' ⟨rfl, heap', hR⟩
      have hv : sizeDropMoved (n, ⟨t⟩) = (c, .leaf) := by
        simp [sizeDropMoved, KeyTree.sizeDrop, c, hc]
      have hR' := Heap.Keeps.rebuilt hK hCaps1 hR hAfter
      obtain ⟨hOwnedP, hKP⟩ := Heap.Rebuilt.wordPair (w := c) (u := .leaf) hR'
      refine ⟨heap', hR'.at_, hR'.caps, [.i64 c, .i64 0], s3, rfl, ?_⟩
      rw [hv]
      exact ⟨hOwnedP, hKP⟩
  · -- The tree, returned in the pair.
    refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s3 ∧ ¬ c < n) ?_ ?_
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, rfl, hc⟩
      exact ⟨c, s2, s3, rfl, rfl, hs, rfl, hc⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨hs, rfl, hc⟩
      subst s
      have hv : sizeDropMoved (n, ⟨t⟩) = (c, t) := by
        simp [sizeDropMoved, KeyTree.sizeDrop, c, hc]
      have hR' := Heap.Keeps.rebuilt hK hCaps1 (Heap.Rebuilt.refl hAt1 hOwnedT hDisjoint1) hAfter
      obtain ⟨hOwnedP, hKP⟩ := Heap.Rebuilt.wordPair (w := c) (u := t) hR'
      refine ⟨p, s3, sElse, rfl, rfl, heap1, hR'.at_, hR'.caps, [.i64 c, .i64 p], sElse, rfl, ?_⟩
      rw [hv]
      exact ⟨hOwnedP, hKP⟩
  · rintro s st ⟨rfl, rfl⟩
    by_cases hc : c < n
    · exact ⟨true, s2, by simp [Expr.eval, s2, ps, State.get, hc], rfl, rfl, hc⟩
    · exact ⟨false, s2, by simp [Expr.eval, s2, ps, State.get, hc], rfl, rfl, hc⟩

/-- The call of `sizeDrop` at the top of a caller whose parameters are a word `n` and a consumed
tree at `p`: the word result lands in local 2 and the tree, owned, in local 3. -/
theorem sizeDrop_call {heap : Heap} {initial : Store Unit} {n p : UInt64} {t : KeyTree}
    {scratch : Nat} {rest : List Value} (hHeap : heap.At initial)
    (hOwned : NodeOwned heap initial p (encode t))
    (hDisjoint : (Node.blocks initial p (encode t)).Pairwise regionsDisjoint)
    (hCap : initial.memoryCap (compile trees.funcs) 0 ≤ 65535) :
    Triple (compile trees.funcs) (.call 8 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3]) scratch
      (fun store state => store = initial ∧ state = ⟨[.i64 n, .i64 p], [.i64 0, .i64 0] ++ rest⟩)
      (fun store state => ∃ (heap' : Heap) (q : UInt64), heap'.At store ∧
        store.memoryCaps = initial.memoryCaps ∧
        NodeOwned heap' store q (encode (t.sizeDrop n).2) ∧
        (Node.blocks store q (encode (t.sizeDrop n).2)).Pairwise regionsDisjoint ∧
        heap.Keeps initial (Node.blocks initial p (encode t)) heap' store
          (Node.blocks store q (encode (t.sizeDrop n).2)) ∧
        state = ⟨[.i64 n, .i64 p], [.i64 (t.sizeDrop n).1, .i64 q] ++ rest⟩) := by
  have hGone : (Represent.moves initial [.i64 n, .i64 p] (n, Moved.mk t)).map (block initial) =
      Node.blocks initial p (encode t) := Node.pointers_blocks initial p (encode t)
  -- Locals 2 and 3 are the first two locals, before `rest`.
  have h2 : 2 < 2 + (rest.length + 1 + 1) := by omega
  have h3 : 3 < 2 + (rest.length + 1 + 1) := by omega
  have hSetAll : ∀ a q : UInt64,
      State.setAll ⟨[.i64 n, .i64 p], [.i64 0, .i64 0] ++ rest⟩ [3, 2] [.i64 q, .i64 a] =
        some ⟨[.i64 n, .i64 p], [.i64 a, .i64 q] ++ rest⟩ := fun a q => by
    simp [State.setAll, State.set?, h2, h3]
  refine (Stmt.callImplements_spec sizeDrop_implements rfl (compile_funcs (i := 6) rfl) rfl
    (before := ⟨[.i64 n, .i64 p], [.i64 0, .i64 0] ++ rest⟩)
    (afterArgs := ⟨[.i64 n, .i64 p], [.i64 0, .i64 0] ++ rest⟩)
    (results := [2, 3]) (x := (n, Moved.mk t)) (vals := [.i64 n, .i64 p])
    (by simp [Expr.evalResults, Expr.eval, State.get]) hHeap
    ⟨[.i64 n], [.i64 p], rfl, rfl, p, rfl, hOwned, hDisjoint⟩
    ⟨by rw [hGone]; exact hDisjoint, fun _ h => by simp [Represent.reads] at h⟩ hCap ?_).mono
    (fun _ _ h => h) ?_
  · rintro _ _ _ ⟨first, second, rfl, hFirst, ⟨q, rfl, -⟩, -⟩
    obtain rfl : first = [.i64 (t.sizeDrop n).1] := hFirst
    exact ⟨_, hSetAll _ _⟩
  rintro store state ⟨heap', values, hAt, ⟨first, second, rfl, hFirst, ⟨q, rfl, hQ, hDQ⟩, -⟩,
    hCaps, hK, hSet⟩
  obtain rfl : first = [.i64 (t.sizeDrop n).1] := hFirst
  rw [hGone] at hK
  exact ⟨heap', q, hAt, hCaps, hQ, hDQ, hK.mono (fun _ h => h) fun _ hb => hb,
    (Option.some.inj ((hSetAll _ _).symm.trans hSet)).symm⟩

/-- `sizeDropNext` with its two arguments as one pair, the tree consumed. -/
def sizeDropNextMoved (x : UInt64 × Moved KeyTree) : UInt64 × KeyTree :=
  KeyTree.sizeDropNext x.1 x.2.val

/-- `sizeDropNext` passes the tree component of `sizeDrop`'s result through to its own. -/
theorem sizeDropNext_implements : Implements trees.module 9 sizeDropNextMoved := by
  refine Func.implements_moves trees.funcs 7 trees.sizeDropNext.ir "sizeDropNext" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  rw [show (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
    (block initial) = Node.blocks initial p (encode t) from Node.pointers_blocks initial p (encode t)]
  show Triple _ (.call 8 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3]) 4
    (fun store state => store = initial ∧
      state = { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 0] ++ [] }) _
  refine (sizeDrop_call hHeap hOwned hDisjoint hCap).mono (fun _ _ h => h) ?_
  rintro store state ⟨heap', q, hAt, hCaps, hQ, hDQ, hK, rfl⟩
  have hv : sizeDropNextMoved (n, ⟨t⟩) = ((t.sizeDrop n).1 + 1, (t.sizeDrop n).2) := by
    simp only [sizeDropNextMoved, KeyTree.sizeDropNext]
  refine ⟨heap', hAt, hCaps, [.i64 ((t.sizeDrop n).1 + 1), .i64 q], _, rfl, ?_⟩
  rw [hv]
  exact ⟨⟨[.i64 _], [.i64 q], rfl, rfl, ⟨q, rfl, hQ, hDQ⟩, fun _ hb => nomatch hb⟩,
    hK.mono (fun _ h => h) fun b hb => by
      simp [Represent.blocks, Represent.width, Scalar.values] at hb
      exact hb⟩

/-- `sizeAfterDrop` with its two arguments as one pair, the tree consumed. -/
def sizeAfterDropMoved (x : UInt64 × Moved KeyTree) : UInt64 := KeyTree.sizeAfterDrop x.1 x.2.val

/-- `sizeAfterDrop` releases the tree component of `sizeDrop`'s result at its end. -/
theorem sizeAfterDrop_implements : Implements trees.module 10 sizeAfterDropMoved := by
  refine Func.implements_moves trees.funcs 8 trees.sizeAfterDrop.ir "sizeAfterDrop" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  rw [show (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
    (block initial) = Node.blocks initial p (encode t) from Node.pointers_blocks initial p (encode t)]
  have hImports : (compile trees.funcs).imports = [] := rfl
  have hRelease : (compile trees.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let c := (t.sizeDrop n).1
  show Triple _ (.seq (.call 8 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3])
      (.seq (.assign 4 (.get 2)) (.release 3))) 5
    (fun store state => store = initial ∧
      state = { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 0] ++ [.i64 0] }) _
  refine Stmt.seq_spec (sizeDrop_call hHeap hOwned hDisjoint hCap) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, q, hAt1, hCaps1, hQ, hDQ, hK1, hst⟩ => ?_
  subst hst
  let s1 : State := ⟨[.i64 n, .i64 p], [.i64 c, .i64 q] ++ [.i64 0]⟩
  let s2 : State := ⟨[.i64 n, .i64 p], [.i64 c, .i64 q, .i64 c]⟩
  refine Stmt.seq_spec (M := fun s st => s = store1 ∧ st = s2)
    (Stmt.assign_spec.mono (fun s st ⟨hs, hst⟩ => ⟨c, s1, s2, by rw [hst]; rfl, rfl, hs, rfl⟩)
      fun _ _ h => h) ?_
  refine (Stmt.releaseNode_keeps hImports hRelease rfl hAt1 hQ hDQ).mono
    (fun _ _ h => h) ?_
  rintro store2 st2 ⟨rfl, heap2, hAt2, hCaps2, hK2⟩
  refine ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 c], s2, rfl, rfl,
    (hK1.trans hK2 fun _ _ hFresh => hFresh).mono (fun _ h => h) fun _ hb => nomatch hb⟩

/-- `sizeDropSmall` with its two arguments as one pair, the tree consumed. -/
def sizeDropSmallMoved (x : UInt64 × Moved KeyTree) : KeyTree := KeyTree.sizeDropSmall x.1 x.2.val

/-- `sizeDropSmall` passes the tree component of `sizeDrop`'s result to `dropSmall`, which
consumes it. -/
theorem sizeDropSmall_implements : Implements trees.module 11 sizeDropSmallMoved := by
  refine Func.implements_moves trees.funcs 9 trees.sizeDropSmall.ir "sizeDropSmall" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  rw [show (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
    (block initial) = Node.blocks initial p (encode t) from Node.pointers_blocks initial p (encode t)]
  let c := (t.sizeDrop n).1
  let u := (t.sizeDrop n).2
  show Triple _ (.seq (.call 8 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3])
      (.call 7 [⟨.u64, .bin .add (.get 2) (.const 1)⟩, ⟨.u64, .get 3⟩] [4])) 5
    (fun store state => store = initial ∧
      state = { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 0] ++ [.i64 0] }) _
  refine Stmt.seq_spec (sizeDrop_call hHeap hOwned hDisjoint hCap) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, q, hAt1, hCaps1, hQ, hDQ, hK1, hst⟩ => ?_
  subst hst
  have hGone1 : (Represent.moves store1 [.i64 (c + 1), .i64 q] (c + 1, Moved.mk u)).map
      (block store1) = Node.blocks store1 q (encode u) := Node.pointers_blocks store1 q (encode u)
  refine (Stmt.callImplements_spec dropSmall_implements rfl (compile_funcs (i := 5) rfl) rfl
    (before := ⟨[.i64 n, .i64 p], [.i64 c, .i64 q] ++ [.i64 0]⟩)
    (afterArgs := ⟨[.i64 n, .i64 p], [.i64 c, .i64 q] ++ [.i64 0]⟩)
    (results := [4]) (x := (c + 1, Moved.mk u)) (vals := [.i64 (c + 1), .i64 q])
    (by simp [Expr.evalResults, Expr.eval, State.get, U64Op.apply]) hAt1
    ⟨[.i64 (c + 1)], [.i64 q], rfl, rfl, q, rfl, hQ, hDQ⟩
    ⟨by rw [hGone1]; exact hDQ, fun _ h => by simp [Represent.reads] at h⟩
    (memoryCap_le_of_caps hCaps1 hCap)
    fun _ _ _ ⟨q2, hq2, _⟩ => by subst hq2; exact ⟨_, rfl⟩).mono (fun _ _ h => h) ?_
  rintro store2 st2 ⟨heap2, values, hAt2, ⟨q2, rfl, hQ2, hDQ2⟩, hCaps2, hK2, hSet2⟩
  obtain rfl : st2 = ⟨[.i64 n, .i64 p], [.i64 c, .i64 q, .i64 q2]⟩ :=
    (Option.some.inj (hSet2.symm.trans rfl))
  rw [hGone1] at hK2
  have hv : sizeDropSmallMoved (n, ⟨t⟩) = dropSmallMoved (c + 1, ⟨u⟩) := by
    simp only [sizeDropSmallMoved, KeyTree.sizeDropSmall, dropSmallMoved, c, u]
  refine ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 q2], _, rfl, ?_⟩
  rw [hv]
  exact ⟨⟨q2, rfl, hQ2, hDQ2⟩, hK1.trans hK2 fun _ _ hFresh => hFresh⟩

/-- `sizeFirst` with its two arguments as one pair, the tree consumed. -/
def sizeFirstMoved (x : UInt64 × Moved KeyTree) : UInt64 := KeyTree.sizeFirst x.1 x.2.val

/-- `sizeFirst` projects the word component of `sizeDrop`'s result and releases the tree
component right after the call. -/
theorem sizeFirst_implements : Implements trees.module 12 sizeFirstMoved := by
  refine Func.implements_moves trees.funcs 10 trees.sizeFirst.ir "sizeFirst" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  rw [show (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
    (block initial) = Node.blocks initial p (encode t) from Node.pointers_blocks initial p (encode t)]
  have hImports : (compile trees.funcs).imports = [] := rfl
  have hRelease : (compile trees.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let c := (t.sizeDrop n).1
  show Triple _ (.seq (.call 8 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2, 3]) (.release 3)) 4
    (fun store state => store = initial ∧
      state = { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 0] ++ [] }) _
  refine Stmt.seq_spec (sizeDrop_call hHeap hOwned hDisjoint hCap) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, q, hAt1, hCaps1, hQ, hDQ, hK1, hst⟩ => ?_
  subst hst
  refine (Stmt.releaseNode_keeps hImports hRelease rfl hAt1 hQ hDQ).mono
    (fun _ _ h => h) ?_
  rintro store2 st2 ⟨rfl, heap2, hAt2, hCaps2, hK2⟩
  refine ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 c], _, rfl, rfl,
    (hK1.trans hK2 fun _ _ hFresh => hFresh).mono (fun _ h => h) fun _ hb => nomatch hb⟩

/-- The call of `dropSmall` at the top of a caller whose parameters are a word `n` and a consumed
tree at `p`: the result, owned, lands in local 2. -/
theorem dropSmall_call {heap : Heap} {initial : Store Unit} {n p : UInt64} {t : KeyTree}
    {scratch : Nat} {rest : List Value} (hHeap : heap.At initial)
    (hOwned : NodeOwned heap initial p (encode t))
    (hDisjoint : (Node.blocks initial p (encode t)).Pairwise regionsDisjoint)
    (hCap : initial.memoryCap (compile trees.funcs) 0 ≤ 65535) :
    Triple (compile trees.funcs) (.call 7 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2]) scratch
      (fun store state => store = initial ∧ state = ⟨[.i64 n, .i64 p], .i64 0 :: rest⟩)
      (fun store state => ∃ (heap' : Heap) (q : UInt64), heap'.At store ∧
        store.memoryCaps = initial.memoryCaps ∧
        NodeOwned heap' store q (encode (t.dropSmall n)) ∧
        (Node.blocks store q (encode (t.dropSmall n))).Pairwise regionsDisjoint ∧
        heap.Keeps initial (Node.blocks initial p (encode t)) heap' store
          (Node.blocks store q (encode (t.dropSmall n))) ∧
        state = ⟨[.i64 n, .i64 p], .i64 q :: rest⟩) := by
  have hGone : (Represent.moves initial [.i64 n, .i64 p] (n, Moved.mk t)).map (block initial) =
      Node.blocks initial p (encode t) := Node.pointers_blocks initial p (encode t)
  have h2 : 2 < 2 + (rest.length + 1) := by omega
  have hSetAll : ∀ q : UInt64,
      State.setAll ⟨[.i64 n, .i64 p], .i64 0 :: rest⟩ [2] [.i64 q] =
        some ⟨[.i64 n, .i64 p], .i64 q :: rest⟩ := fun q => by
    simp [State.setAll, State.set?, h2]
  refine (Stmt.callImplements_spec dropSmall_implements rfl (compile_funcs (i := 5) rfl) rfl
    (before := ⟨[.i64 n, .i64 p], .i64 0 :: rest⟩)
    (afterArgs := ⟨[.i64 n, .i64 p], .i64 0 :: rest⟩)
    (results := [2]) (x := (n, Moved.mk t)) (vals := [.i64 n, .i64 p])
    (by simp [Expr.evalResults, Expr.eval, State.get]) hHeap
    ⟨[.i64 n], [.i64 p], rfl, rfl, p, rfl, hOwned, hDisjoint⟩
    ⟨by rw [hGone]; exact hDisjoint, fun _ h => by simp [Represent.reads] at h⟩ hCap ?_).mono
    (fun _ _ h => h) ?_
  · rintro _ _ _ ⟨q, rfl, -⟩
    exact ⟨_, hSetAll q⟩
  rintro store state ⟨heap', values, hAt, ⟨q, rfl, hQ, hDQ⟩, hCaps, hK, hSet⟩
  rw [hGone] at hK
  exact ⟨heap', q, hAt, hCaps, hQ, hDQ, hK.mono (fun _ h => h) fun _ hb => hb,
    (Option.some.inj ((hSetAll q).symm.trans hSet)).symm⟩

/-- `droppedSize` with its two arguments as one pair, the tree consumed. -/
def droppedSizeMoved (x : UInt64 × Moved KeyTree) : UInt64 := KeyTree.droppedSize x.1 x.2.val

/-- `droppedSize` binds `dropSmall`'s result with `let`, lends it to `size`, and releases it. -/
theorem droppedSize_implements : Implements trees.module 13 droppedSizeMoved := by
  refine Func.implements_moves trees.funcs 11 trees.droppedSize.ir "droppedSize" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  rw [show (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
    (block initial) = Node.blocks initial p (encode t) from Node.pointers_blocks initial p (encode t)]
  have hImports : (compile trees.funcs).imports = [] := rfl
  have hRelease : (compile trees.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  let u := t.dropSmall n
  show Triple _ (.seq (.call 7 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2])
      (.seq (.call 2 [⟨.u64, .get 2⟩] [3]) (.seq (.assign 4 (.get 3)) (.release 2)))) 5
    (fun store state => store = initial ∧ state = ⟨[.i64 n, .i64 p], .i64 0 :: [.i64 0, .i64 0]⟩) _
  refine Stmt.seq_spec (dropSmall_call hHeap hOwned hDisjoint hCap) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, q, hAt1, hCaps1, hQ, hDQ, hK1, hst⟩ => ?_
  subst hst
  -- The result, lent to `size`.
  refine Stmt.seq_spec (Stmt.callImplements_spec size_implements rfl (compile_funcs (i := 0) rfl)
    rfl (before := ⟨[.i64 n, .i64 p], .i64 q :: [.i64 0, .i64 0]⟩) (results := [3]) (x := u) rfl
    hAt1 ⟨q, rfl, NodeOwned.borrowed q _ hQ⟩ Separate.nil (memoryCap_le_of_caps hCaps1 hCap)
    (fun _ _ _ h => by rw [show _ = _ from h]; exact ⟨_, rfl⟩)) ?_
  refine Triple.of_forall fun store2 st ⟨heap2, values2, hAt2, hOwned2, hCaps2, hK2, hSet2⟩ => ?_
  obtain rfl : values2 = [.i64 u.size] := hOwned2
  let s2 : State := ⟨[.i64 n, .i64 p], [.i64 q, .i64 u.size, .i64 0]⟩
  let s3 : State := ⟨[.i64 n, .i64 p], [.i64 q, .i64 u.size, .i64 u.size]⟩
  obtain rfl : st = s2 := (Option.some.inj (hSet2.symm.trans rfl))
  obtain ⟨hQ2, hBlocks2, -⟩ := Heap.Keeps.node hK2 hQ fun _ _ _ hg => nomatch hg
  have hDQ2 : (Node.blocks store2 q (encode u)).Pairwise regionsDisjoint := by
    rw [hBlocks2]; exact hDQ
  refine Stmt.seq_spec (M := fun s st => s = store2 ∧ st = s3)
    (Stmt.assign_spec.mono (fun s st ⟨hs, hst⟩ => ⟨u.size, s2, s3, by rw [hst]; rfl, rfl, hs, rfl⟩)
      fun _ _ h => h) ?_
  -- The result, released.
  refine (Stmt.releaseNode_keeps hImports hRelease rfl hAt2 hQ2 hDQ2).mono
    (fun _ _ h => h) ?_
  rintro store3 st3 ⟨rfl, heap3, hAt3, hCaps3, hK3⟩
  have hK12 := hK1.transBoth hK2 fun _ _ _ _ hb => nomatch hb
  refine ⟨heap3, hAt3, hCaps3.trans (hCaps2.trans hCaps1), [.i64 u.size], s3, rfl, rfl,
    (hK12.trans hK3 fun _ _ hFresh b hb => hFresh b (List.mem_append_left _ ?_)).mono
      (fun _ h => h) fun _ hb => nomatch hb⟩
  rwa [hBlocks2] at hb

/-- `dropWithSize` with its two arguments as one pair, the tree consumed. -/
def dropWithSizeMoved (x : UInt64 × Moved KeyTree) : UInt64 × KeyTree :=
  KeyTree.dropWithSize x.1 x.2.val

/-- `dropWithSize` binds `dropSmall`'s result with `let`, lends it to `size`, and returns it. -/
theorem dropWithSize_implements : Implements trees.module 14 dropWithSizeMoved := by
  refine Func.implements_moves trees.funcs 12 trees.dropWithSize.ir "dropWithSize" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - hCap
  change NodeOwned heap initial p (encode t) at hOwned
  change (Node.blocks initial p (encode t)).Pairwise regionsDisjoint at hDisjoint
  rw [show (Represent.moves initial (Scalar.values n ++ [.i64 p]) (n, Moved.mk t)).map
    (block initial) = Node.blocks initial p (encode t) from Node.pointers_blocks initial p (encode t)]
  let u := t.dropSmall n
  show Triple _ (.seq (.call 7 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩] [2])
      (.call 2 [⟨.u64, .get 2⟩] [3])) 4
    (fun store state => store = initial ∧ state = ⟨[.i64 n, .i64 p], .i64 0 :: [.i64 0]⟩) _
  refine Stmt.seq_spec (dropSmall_call hHeap hOwned hDisjoint hCap) ?_
  refine Triple.of_forall fun store1 st ⟨heap1, q, hAt1, hCaps1, hQ, hDQ, hK1, hst⟩ => ?_
  subst hst
  refine (Stmt.callImplements_spec size_implements rfl (compile_funcs (i := 0) rfl)
    rfl (before := ⟨[.i64 n, .i64 p], .i64 q :: [.i64 0]⟩) (results := [3]) (x := u) rfl
    hAt1 ⟨q, rfl, NodeOwned.borrowed q _ hQ⟩ Separate.nil (memoryCap_le_of_caps hCaps1 hCap)
    (fun _ _ _ h => by rw [show _ = _ from h]; exact ⟨_, rfl⟩)).mono (fun _ _ h => h) ?_
  rintro store2 st ⟨heap2, values2, hAt2, hOwned2, hCaps2, hK2, hSet2⟩
  obtain rfl : values2 = [.i64 u.size] := hOwned2
  obtain rfl : st = ⟨[.i64 n, .i64 p], [.i64 q, .i64 u.size]⟩ :=
    (Option.some.inj (hSet2.symm.trans rfl))
  obtain ⟨hQ2, hBlocks2, -⟩ := Heap.Keeps.node hK2 hQ fun _ _ _ hg => nomatch hg
  have hDQ2 : (Node.blocks store2 q (encode u)).Pairwise regionsDisjoint := by
    rw [hBlocks2]; exact hDQ
  refine ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 u.size, .i64 q], _, rfl,
    ⟨[.i64 u.size], [.i64 q], rfl, rfl, ⟨q, rfl, hQ2, hDQ2⟩, fun _ hb => nomatch hb⟩,
    (hK1.transBoth hK2 fun _ _ _ _ hb => nomatch hb).mono (fun _ h => h) fun b hb => ?_⟩
  have hb' : b ∈ Node.blocks store2 q (encode u) := hb
  rw [hBlocks2] at hb'
  exact List.mem_append_left _ hb'

/-- `size`'s entry keeps the store: one call of its internal function, which keeps it. -/
theorem size_keeps : ∀ t, KeepsEntry (compile trees.funcs) (2 + 0) KeyTree.size t :=
  Func.entry_keeps trees.funcs 0 trees.size.ir "size" rfl KeyTree.size
    (g := trees.size.rec.ir.function (2 + 17)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 17) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.size.ir, Func.locals]⟩)
    size_rec

/-- `leftSizes` with its tree consumed. -/
def leftSizesMoved (t : Moved KeyTree) : KeyTree := t.val.leftSizes

/-- The internal function of `leftSizes`, at any depth, consumes its tree and rewrites each
record in place.  A record branch lends its left child to `size`'s internal function at the
depth plus one, which keeps the store, before the two self-calls. -/
theorem leftSizes_rec : ∀ t, Rebuilds (compile trees.funcs) (2 + 20) leftSizesMoved t := by
  refine Func.rebuildRecursion trees.funcs 20 trees.leftSizes.rec.ir "leftSizes.rec" rfl
    leftSizesMoved (fun t => sizeOf t.val) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl)
    fun ⟨t⟩ ih heap initial vs d hHeap hArgs _ hCap => ?_
  have hArg := hArgs
  obtain ⟨p, rfl, hOwned, -⟩ := hArgs
  have hCallee : (compile trees.funcs).funcs[2 + 20 - (compile trees.funcs).imports.length]? =
      some (trees.leftSizes.rec.ir.function (2 + 20)) := compile_funcs (i := 20) rfl
  have hSize : (compile trees.funcs).funcs[2 + 17 - (compile trees.funcs).imports.length]? =
      some (trees.size.rec.ir.function (2 + 17)) := compile_funcs (i := 17) rfl
  let z : Value := .i64 0
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 8 z }
  have hStart : trees.leftSizes.rec.ir.state ([.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + 17) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.assign 7 (.get 6))
                  (.seq (.call (2 + 20) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                      [8])
                    (.seq (.call (2 + 20) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                        [9])
                      (.seq (.store (.bin .add (.get 0) (.const 0)) (.get 8))
                        (.seq (.store (.bin .add (.get 0) (.const 8)) (.get 7))
                          (.seq (.store (.bin .add (.get 0) (.const 16)) (.get 9))
                            (.assign 2 (.get 0)))))))))))))) 10
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
    let s1 : State := { params := [.i64 0, .i64 d], locals := List.replicate 8 z }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, s1, rfl, rfl, heap, 0, s1, rfl, Heap.Rebuilt.null hHeap⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hHead, hl, hk, -, -⟩ := hOwned
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
    let c := KeyTree.size l
    let s1 : State := { params := ps, locals := [z, .i64 pl, z, z, z, z, z, z] }
    let s2 : State := { params := ps, locals := [z, .i64 pl, .i64 k, z, z, z, z, z] }
    let s3 : State := { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, z, z, z, z] }
    let s4 : State := { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 c, z, z, z] }
    let s5 : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 c, .i64 c, z, z] }
    let s6 (a : UInt64) : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 c, .i64 c, .i64 a, z] }
    let s7 (a b : UInt64) : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 c, .i64 c, .i64 a, .i64 b] }
    let s8 (a b : UInt64) : State :=
      { params := ps
        locals := [.i64 p, .i64 pl, .i64 k, .i64 pr, .i64 c, .i64 c, .i64 a, .i64 b] }
    obtain ⟨hB1, hSep1⟩ := node_call1 hArg
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s4) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s5) ?_ <|
        Stmt.seq_spec (M := fun s st => ∃ (heap1 : Heap) (a : UInt64), st = s6 a ∧
          heap.Rebuilt initial ((Represent.moves initial [.i64 pl] (Moved.mk l)).map
            (block initial)) heap1 s a (Encode.encode (leftSizesMoved ⟨l⟩))) ?_ ?_
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
      · -- The left child, lent to `size`'s internal function.
        exact Stmt.selfCall_spec rfl hSize (by rfl) (size_rec l) hHeap
          ⟨pl, rfl, NodeOwned.borrowed _ _ hl⟩ (d := d + 1) rfl
          (by simp [State.setAll, State.set?, s3, s4, ps, c])
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨c, s4, s5, rfl, rfl, rfl, rfl⟩
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih ⟨l⟩ (by simp; omega)) hHeap hB1
          hSep1 hCap (d := d + 1) rfl fun a => by simp [State.setAll, State.set?, s5, s6, ps]
      refine Triple.of_forall fun store1 st ⟨heap1, a, hst, hR1⟩ => ?_
      subst hst
      obtain ⟨hB2, hSep2⟩ := node_call2 hArg hR1
      refine Stmt.seq_spec (M := fun s st => ∃ (heap2 : Heap) (b : UInt64), st = s7 a b ∧
          heap1.Rebuilt store1 ((Represent.moves store1 [.i64 pr] (Moved.mk r)).map
            (block store1)) heap2 s b (Encode.encode (leftSizesMoved ⟨r⟩))) ?_ ?_
      · exact Stmt.selfCall_rebuilds rfl hCallee (by rfl) (ih ⟨r⟩ (by simp)) hR1.at_ hB2
          hSep2 (memoryCap_le_of_caps hR1.caps hCap) (d := d + 1) rfl
          fun b => by simp [State.setAll, State.set?, s6, s7, ps]
      refine Triple.of_forall fun store2 st ⟨heap2, b, hst, hR2⟩ => ?_
      subst hst
      let w0 := store2.mem.write64 (slotAddress p 0) a
      let w1 := w0.write64 (slotAddress p 1) c
      let w2 := w1.write64 (slotAddress p 2) b
      refine Stmt.seq_spec (M := fun s st => s = { store2 with mem := w0 } ∧ st = s7 a b) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w1 } ∧ st = s7 a b) ?_ <|
        Stmt.seq_spec (M := fun s st => s = { store2 with mem := w2 } ∧ st = s7 a b) ?_ ?_
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, s7 a b, a, s7 a b, rfl, rfl, ?_, ?_⟩
        · rw [h0, hs0]
          have := node_bound hArg hR1 hR2
          omega
        · rw [h0]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s7 a b, c, s7 a b, rfl, rfl, ?_, ?_⟩
        · rw [h1, hs1]
          have := node_bound hArg hR1 hR2
          simp only [w0, Wasm.Mem.write64_pages]
          omega
        · rw [h1]
          exact ⟨rfl, rfl⟩
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s7 a b, b, s7 a b, rfl, rfl, ?_, ?_⟩
        · rw [h2, hs2]
          have := node_bound hArg hR1 hR2
          simp only [w1, w0, Wasm.Mem.write64_pages]
          omega
        · rw [h2]
          exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        have hRead0 : w2.read64 (slotAddress p 0) = a := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega),
            Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead1 : w2.read64 (slotAddress p 1) = c := by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
        have hRead2 : w2.read64 (slotAddress p 2) = b := Memory.read64_write64 _ _ _
        exact ⟨p, s7 a b, s8 a b, rfl, rfl, heap2, p, s8 a b, rfl,
          node_rebuilt hArg hR1 hR2 (writes3 store2 p a c b (by omega)) hRead0 hRead1 hRead2⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem leftSizes_implements : Implements trees.module 15 leftSizesMoved :=
  Func.entry_rebuilds trees.funcs 13 trees.leftSizes.ir "leftSizes" rfl leftSizesMoved
    (g := trees.leftSizes.rec.ir.function (2 + 20)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl
    rfl (compile_funcs (i := 20) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.leftSizes.ir, Func.locals]⟩)
    leftSizes_rec

/-- The internal function of `leftHeavy`, at any depth, keeps the store.  A record branch calls
`size`'s internal function on both children at the depth plus one, which keeps the store, and
then itself on both. -/
theorem leftHeavy_rec : ∀ t, Keeps (compile trees.funcs) (2 + 21) KeyTree.leftHeavy t := by
  refine Func.recursion trees.funcs 21 trees.leftHeavy.rec.ir "leftHeavy.rec" rfl
    KeyTree.leftHeavy (fun t => sizeOf t) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl)
    fun t ih heap initial vs d hHeap hB => ?_
  obtain ⟨p, rfl, hNode'⟩ := hB
  have hCallee : (compile trees.funcs).funcs[2 + 21 - (compile trees.funcs).imports.length]? =
      some (trees.leftHeavy.rec.ir.function (2 + 21)) := compile_funcs (i := 21) rfl
  have hSize : (compile trees.funcs).funcs[2 + 17 - (compile trees.funcs).imports.length]? =
      some (trees.size.rec.ir.function (2 + 17)) := compile_funcs (i := 17) rfl
  let z : Value := .i64 0
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 8 z }
  have hStart : trees.leftHeavy.rec.ir.state ([.i64 p] ++ [.i64 d]) = start := rfl
  rw [hStart]
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call (2 + 17) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call (2 + 17) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                    [7])
                  (.seq (.call (2 + 21) [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                      [8])
                    (.seq (.call (2 + 21) [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
                        [9])
                      (.assign 2 (.bin .add (.bin .add
                        (.ite (.ltU (.get 6) (.get 7)) (.const 1) (.const 0)) (.get 8)) (.get 9)))))))))))) 10
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
    obtain rfl : p = 0 := hNode'
    let s1 : State := { params := [.i64 0, .i64 d], locals := List.replicate 8 z }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, s1, rfl, rfl, rfl, s1, rfl⟩
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
    let sl := KeyTree.size l
    let sr := KeyTree.size r
    let hl' := KeyTree.leftHeavy l
    let hr' := KeyTree.leftHeavy r
    let s1 : State := { params := ps, locals := [z, .i64 pl, z, z, z, z, z, z] }
    let s2 : State := { params := ps, locals := [z, .i64 pl, .i64 k, z, z, z, z, z] }
    let s3 : State := { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, z, z, z, z] }
    let s4 : State := { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 sr, z, z, z] }
    let s5 : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 sr, .i64 sl, z, z] }
    let s6 : State :=
      { params := ps, locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 sr, .i64 sl, .i64 hl', z] }
    let s7 : State :=
      { params := ps
        locals := [z, .i64 pl, .i64 k, .i64 pr, .i64 sr, .i64 sl, .i64 hl', .i64 hr'] }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s4) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s5) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s6) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s7) ?_ ?_
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
      · exact Stmt.selfCall_spec rfl hSize (by rfl) (size_rec r) hHeap ⟨pr, rfl, hr⟩
          (d := d + 1) rfl (by simp [State.setAll, State.set?, s3, s4, ps, sr])
      · exact Stmt.selfCall_spec rfl hSize (by rfl) (size_rec l) hHeap ⟨pl, rfl, hl⟩
          (d := d + 1) rfl (by simp [State.setAll, State.set?, s4, s5, ps, sl])
      · exact Stmt.selfCall_spec rfl hCallee (by rfl) (ih l (by simp; omega)) hHeap ⟨pl, rfl, hl⟩
          (d := d + 1) rfl (by simp [State.setAll, State.set?, s5, s6, ps, hl'])
      · exact Stmt.selfCall_spec rfl hCallee (by rfl) (ih r (by simp)) hHeap ⟨pr, rfl, hr⟩
          (d := d + 1) rfl (by simp [State.setAll, State.set?, s6, s7, ps, hr'])
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        let v := (if sr < sl then 1 else 0) + hl' + hr'
        let s8 : State :=
          { params := ps
            locals := [.i64 v, .i64 pl, .i64 k, .i64 pr, .i64 sr, .i64 sl, .i64 hl', .i64 hr'] }
        refine ⟨v, s7, s8, ?_, rfl, rfl, s8, rfl⟩
        by_cases hc : sr < sl
        · simp [Expr.eval, s7, ps, State.get, U64Op.apply, v, hc]
        · simp [Expr.eval, s7, ps, State.get, U64Op.apply, v, hc]
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem leftHeavy_implements : Implements trees.module 16 KeyTree.leftHeavy :=
  Func.entry_implements trees.funcs 14 trees.leftHeavy.ir "leftHeavy" rfl KeyTree.leftHeavy
    (g := trees.leftHeavy.rec.ir.function (2 + 21)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 21) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.leftHeavy.ir, Func.locals]⟩)
    leftHeavy_rec

/-- `sumSizes` with its two arguments as one pair. -/
def sumSizesPair (x : UInt64 × KeyTree) : UInt64 := KeyTree.sumSizes x.1 x.2

/-- `sumSizes` lends its tree to `size` in every iteration of its loop.  `size`'s entry keeps
the store (`size_keeps`), so the loop body keeps it, and `Stmt.loop_spec` applies with no
invariant beyond the state. -/
theorem sumSizes_implements : Implements trees.module 17 sumSizesPair := by
  refine Func.implements trees.funcs 15 trees.sumSizes.ir "sumSizes" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨n, t⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hNode⟩
  let start : State :=
    { params := [.i64 n, .i64 p], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.seq (.assign 2 (.const 0)) (.loop 3 4 (.get 0)
      (.seq (.call 2 [⟨.u64, .get 1⟩] [5]) (.seq (.assign 6 (.bin .add (.get 2) (.get 5)))
        (.assign 2 (.get 6)))))) 7
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 2 := rfl
  have hLocals : start.locals.length = 5 := rfl
  let s1 := start.update 2 (.i64 0)
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1]
  have hS1 : s1.params.length = 2 ∧ s1.locals.length = 5 := by simp [s1, hParams, hLocals]
  refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5, 6]) (init := (0 : UInt64)) (n := n)
    (fun _ acc => acc + KeyTree.size t) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [hS1.1, hS1.2]) ⟨s1, by simp [Expr.eval, s1, start]; rfl⟩
    (by simp [State.Holds, Scalar.values, s1, hParams, hLocals]) ?_).mono (fun _ _ h => h) ?_
  · intro k acc state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 2 ∧ state.locals.length = 5 :=
      ⟨hFrame.params.trans hS1.1, hFrame.locals.trans hS1.2⟩
    have g1 : state.get 1 = some (.i64 p) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s1, start]; rfl)
    have g2 : state.get 2 = some (.i64 acc) := by
      simpa [State.Holds, Scalar.values] using hHolds
    let a := state.update 5 (.i64 (KeyTree.size t))
    let b := a.update 6 (.i64 (acc + KeyTree.size t))
    let c := b.update 2 (.i64 (acc + KeyTree.size t))
    -- The call keeps the store: `t` is borrowed in `initial` in every iteration.
    refine Stmt.seq_spec (Stmt.callKeeps_spec (before := state) (afterArgs := state) (next := a)
      rfl (compile_funcs (i := 0) rfl) rfl (size_keeps t) hHeap ⟨p, rfl, hNode⟩
      (by simp [Expr.evalResults, Expr.eval, g1])
      (by simp [State.setAll, State.set?_eq_update, a, hState.1, hState.2])) ?_
    refine (Stmt.run_spec (final := c) ?_).mono (fun _ _ h => h) ?_
    · simp [Stmt.run, Expr.eval, State.set?_eq_update, a, b, c, g2, hState.1, hState.2,
        U64Op.apply]
    rintro s st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, by simp [State.Holds, Scalar.values, c, b, a, hState.1, hState.2]⟩
    simp only [c, b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  rintro s st ⟨rfl, -, hHolds⟩
  refine ⟨rfl, [.i64 (sumSizesPair (n, t))], st, ?_, rfl⟩
  have g2 : st.get 2 = some (.i64 (sumSizesPair (n, t))) := by
    simpa [State.Holds, Scalar.values, sumSizesPair, KeyTree.sumSizes] using hHolds
  show Expr.evalResults _ 7 [⟨.u64, .get 2⟩] st = _
  simp [Expr.evalResults, Expr.eval, g2]

/-- `keyPair` reads its borrowed tree in a pair-valued match. -/
theorem keyPair_implements : Implements trees.module 18 KeyTree.keyPair := by
  refine Func.implements trees.funcs 16 trees.keyPair.ir "keyPair" rfl _
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro t heap initial _ hHeap ⟨p, rfl, hB⟩
  let z : Value := .i64 0
  let start : State := { params := [.i64 p], locals := List.replicate 5 z }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.seq (.assign 1 (.const 0)) (.assign 2 (.const 0)))
      (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
        (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
          (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
            (.seq (.assign 1 (.get 4)) (.assign 2 (.bin .add (.get 4) (.const 1)))))))) 6
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hB
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
        (Stmt.assign_spec.mono ?_ fun _ _ h => h) (Stmt.assign_spec.mono ?_ fun _ _ h => h))
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, start, rfl, rfl, rfl, [.i64 0, .i64 0], start, rfl, rfl⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l k r =>
    obtain ⟨hRec, -, hk, -, -⟩ := hB
    simp only [Nat.zero_add] at hk
    have hNonzero := hRec.nonzero
    have hAddress := hRec.address
    have hBelow := hRec.below
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
    let ps : List Value := [.i64 p]
    let s1 : State := { params := ps, locals := [z, z, .i64 pl, z, z] }
    let s2 : State := { params := ps, locals := [z, z, .i64 pl, .i64 k, z] }
    let s3 : State := { params := ps, locals := [z, z, .i64 pl, .i64 k, .i64 pr] }
    let s4 : State := { params := ps, locals := [.i64 k, z, .i64 pl, .i64 k, .i64 pr] }
    let s5 : State := { params := ps, locals := [.i64 k, .i64 (k + 1), .i64 pl, .i64 k, .i64 pr] }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s4) ?_ ?_
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
        exact ⟨k, s3, s4, rfl, rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨k + 1, s4, s5, rfl, rfl, rfl, [.i64 k, .i64 (k + 1)], s5, rfl, rfl⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `encode` succeeds on `trees.module`, and its bytes decode to a module that computes
`KeyTree.size`, `KeyTree.sum`, `KeyTree.height`, `KeyTree.sizeSum`, `KeyTree.pushSum`,
`KeyTree.dropSmall`, `KeyTree.sizeDrop` and its four callers, `KeyTree.droppedSize`,
`KeyTree.dropWithSize`, `KeyTree.leftSizes`, `KeyTree.leftHeavy`, `KeyTree.sumSizes`, and
`KeyTree.keyPair` exactly. -/
theorem trees_bytes : ∃ bytes, Wasm.Encoding.encode trees.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 KeyTree.size ∧
      Implements m 3 KeyTree.sum ∧ Implements m 4 KeyTree.height ∧
      Implements m 5 KeyTree.sizeSum ∧ Implements m 6 pushSumMoved ∧
      Implements m 7 dropSmallMoved ∧ Implements m 8 sizeDropMoved ∧
      Implements m 9 sizeDropNextMoved ∧ Implements m 10 sizeAfterDropMoved ∧
      Implements m 11 sizeDropSmallMoved ∧ Implements m 12 sizeFirstMoved ∧
      Implements m 13 droppedSizeMoved ∧ Implements m 14 dropWithSizeMoved ∧
      Implements m 15 leftSizesMoved ∧ Implements m 16 KeyTree.leftHeavy ∧
      Implements m 17 sumSizesPair ∧ Implements m 18 KeyTree.keyPair := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip trees.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, trees.module, decoded, size_implements, sum_implements,
    height_implements, sizeSum_implements, pushSum_implements, dropSmall_implements,
    sizeDrop_implements, sizeDropNext_implements, sizeAfterDrop_implements,
    sizeDropSmall_implements, sizeFirst_implements, droppedSize_implements,
    dropWithSize_implements, leftSizes_implements, leftHeavy_implements,
    sumSizes_implements, keyPair_implements⟩

#print axioms trees_bytes

end Examples.Trees
