import Project.Trees.Module
import Project.Trees.Encode
import Project.IR.Recursion
import Project.Pipeline.Records
import Project.Encoding.RoundTrip

/-! The compiled functions over `Tree` compute their Lean definitions exactly.  Each is an
entry function and an internal function that recurses with a depth parameter. -/

namespace Project.Trees

open Wasm Project.Pipeline Project.IR LeanExe.Examples.Trees

/-- The internal function of `size`, at any depth, aborts or returns the size and keeps the
store. -/
theorem size_rec : ∀ t, Keeps (compile trees.funcs) (2 + 1) Tree.size t :=
  Func.recursion trees.funcs 1 trees.size.rec.ir "size.rec" rfl Tree.size (fun t => sizeOf t)
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) fun t ih heap initial vs d hHeap hB => by
  obtain ⟨p, rfl, hNode⟩ := hB
  let start : State := { params := [.i64 p, .i64 d], locals := List.replicate 6 (.i64 0) }
  show Triple _ (.seq (.ite (.ltU (.const 999) (.get 1)) .abort .skip)
      (.ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 0)))
          (.seq (.load .u64 4 (.bin .add (.get 0) (.const 8)))
            (.seq (.load .u64 5 (.bin .add (.get 0) (.const 16)))
              (.seq (.call 3 [⟨.u64, .get 3⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [6])
                (.seq (.call 3 [⟨.u64, .get 5⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩] [7])
                  (.assign 2 (.bin .add (.bin .add (.get 6) (.const 1)) (.get 7)))))))))) 8
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = start)
    ((Stmt.ite_spec (PThen := fun _ _ => True) (PElse := fun s st => s = initial ∧ st = start)
      Stmt.abort_spec (Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h)).mono ?_
        fun _ _ h => h) ?_
  · rintro s st ⟨rfl, rfl⟩
    refine ⟨decide ((999 : UInt64) < d), start, by simp [Expr.eval, start, State.get], ?_⟩
    split <;> trivial
  have hCallee : (compile trees.funcs).funcs[3 - (compile trees.funcs).imports.length]? =
      some (trees.size.rec.ir.function (2 + 1)) := compile_funcs (i := 1) rfl
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hNode
    let s1 : State := { params := [.i64 0, .i64 d], locals := List.replicate 6 (.i64 0) }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, s1, rfl, rfl, rfl, s1,
        by simp [trees.size.rec.ir, Func.scratch, Expr.evalResults, Expr.eval, s1, State.get,
          Tree.size]⟩
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
    let s1 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 0, .i64 0, .i64 0, .i64 0] }
    let s2 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 0, .i64 0, .i64 0] }
    let s3 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 0, .i64 0] }
    let s4 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 l.size, .i64 0] }
    let s5 : State :=
      { params := ps, locals := [.i64 0, .i64 pl, .i64 k, .i64 pr, .i64 l.size, .i64 r.size] }
    let s6 : State :=
      { params := ps
        locals := [.i64 (l.size + 1 + r.size), .i64 pl, .i64 k, .i64 pr, .i64 l.size,
          .i64 r.size] }
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
      · exact Stmt.selfCall_spec rfl hCallee rfl (ih l (by simp; omega)) hHeap ⟨pl, rfl, hl⟩
          (d := d + 1) rfl rfl
      · exact Stmt.selfCall_spec rfl hCallee rfl (ih r (by simp)) hHeap ⟨pr, rfl, hr⟩
          (d := d + 1) rfl rfl
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨l.size + 1 + r.size, s5, s6, rfl, rfl, rfl, s6,
          by simp [trees.size.rec.ir, Func.scratch, Expr.evalResults, Expr.eval, s6, ps,
            State.get, Tree.size]⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

theorem size_implements : Implements trees.module 2 Tree.size :=
  Func.entry_implements trees.funcs 0 trees.size.ir "size" rfl Tree.size
    (g := trees.size.rec.ir.function (2 + 1)) (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) rfl rfl rfl
    (compile_funcs (i := 1) rfl) rfl
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; simp [Expr.evalResults, Expr.eval, Func.state, State.get])
    (by
      intro params v hLen
      match params, hLen with
      | [a], _ => exact ⟨_, rfl, by simp [State.get, Func.state, trees.size.ir, Func.locals]⟩)
    size_rec

/-- `encode` succeeds on `trees.module`, and its bytes decode to a module that computes
`Tree.size` exactly. -/
theorem trees_bytes : ∃ bytes, Wasm.Encoding.encode trees.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 Tree.size := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip trees.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, trees.module, decoded, size_implements⟩

#print axioms trees_bytes

end Project.Trees
