import Project.Lists.Module
import Project.IR.Correct
import Project.IR.ListFold
import Project.IR.Loop
import Project.IR.Record
import Project.Encoding.RoundTrip

/-! The list module's compiled functions compute their Lean definitions exactly. -/

namespace Project.Lists

open Wasm Project.Pipeline Project.IR Project.Runtime

theorem listSum_implements :
    Implements lists.module 2 LeanExe.Examples.Lists.listSum := by
  refine Func.implements lists.funcs 0 lists.listSum.ir "listSum" rfl _
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨ptr, rfl, hBorrowed⟩
  let start : State := { params := [.i64 ptr], locals := List.replicate 3 (.i64 0) }
  show Triple _ (.seq (.assign 1 (.const 0)) (.listFold 0 1 2 3 (.bin .add (.get 1) (.get 3)))) 4
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_
    ((Stmt.listFold_spec (initial := initial) (before := start) (ptr := ptr) (start := 0) (· + ·)
      (by decide) (by decide) (by simp [start]) (NodeBorrowed.listAt hHeap hBorrowed) rfl rfl
      fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, U64Op.apply]⟩).mono
        (fun _ _ h => h) ?_)
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  · rintro store state ⟨hStore, -, hAcc⟩
    exact ⟨hStore, [.i64 (xs.foldl (· + ·) 0)], state, by
      simp [lists.listSum.ir, Func.scratch, Expr.evalResults, Expr.eval, hAcc], rfl⟩

theorem listRange_implements :
    Implements lists.module 3 LeanExe.Examples.Lists.listRange := by
  refine Func.implements_heap lists.funcs 1 lists.listRange.ir "listRange" rfl _
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap rfl hCap
  have hMemory32 : (compile lists.funcs).memIs64 = false := rfl
  have hImports : (compile lists.funcs).imports = [] := rfl
  have hAlloc : (compile lists.funcs).funcs[0]? = some (allocFunction 0) := rfl
  let f : UInt64 → List UInt64 → List UInt64 := fun i xs => (n - 1 - i) :: xs
  let start : State := { params := [.i64 n], locals := List.replicate 4 (.i64 0) }
  let Inv : Nat → Store Unit → List Value → Prop := fun k store vals =>
    ∃ heap' p, vals = [.i64 p] ∧ heap.Built initial heap' store p (encodeList (loopPrefix f [] k))
  show Triple _ (.seq (.assign 1 (.const 0)) (.loop 2 3 (.get 0)
      (.seq (.record 4 [.bin .sub (.bin .sub (.get 0) (.const 1)) (.get 3), .get 1] 2)
        (.assign 1 (.get 4))))) 5 (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_
    ((Stmt.loop_inv (vars := [1]) (writes := [1, 4]) (n := n) (vals0 := [.i64 0]) Inv
      (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [start])
      ⟨start, by simp [Expr.eval, start, State.get]⟩ (.cons (by simp [start, State.get]) .nil)
      ⟨heap, 0, rfl, Heap.Built.null hHeap⟩ ?_).mono (fun _ _ h => h) ?_)
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  · rintro k store vals state - ⟨heap1, p, rfl, hBuilt⟩ hFrame hHolds hIndex -
    have hP : state.get 1 = some (.i64 p) := by cases hHolds; assumption
    have hN : state.get 0 = some (.i64 n) := (hFrame.get 0 (by decide) (by decide)).trans rfl
    have hRoom : 5 ≤ state.params.length + state.locals.length := by
      rw [hFrame.params, hFrame.locals]; simp [start]
    refine Stmt.seq_spec (Stmt.record_spec hMemory32 hImports hAlloc (by decide) hRoom
      hBuilt.at_ (memoryCap_le_of_caps hBuilt.caps hCap) (by decide) (by decide)
      (words := [n - 1 - UInt64.ofNat k, p]) ?_) ?_
    · refine .cons (fun _ st hF => ⟨st, ?_⟩) (.cons (fun _ st hF => ⟨st, ?_⟩) .nil)
      · have h0 : st.get 0 = some (.i64 n) := (hF.get 0 (by decide) (by decide)).trans hN
        have h3 : st.get 3 = some (.i64 (UInt64.ofNat k)) :=
          (hF.get 3 (by decide) (by decide)).trans hIndex
        simp [Expr.eval, h0, h3, U64Op.apply]
      · have h1 : st.get 1 = some (.i64 p) := (hF.get 1 (by decide) (by decide)).trans hP
        simp [Expr.eval, h1]
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨ptr, hF, hPtr, hNew⟩
      obtain ⟨next, hSet⟩ := State.exists_set? (state := st) (index := 1) (.i64 ptr)
        (by rw [hF.params, hF.locals]; omega)
      refine ⟨ptr, st, next, by simp [Expr.eval, hPtr], hSet,
        (hF.weaken (by simp)).set? hSet (by simp), [.i64 ptr],
        .cons (State.get_set?_same hSet) .nil, heap1.allocate (UInt64.ofNat (8 * 2)), ptr, rfl,
        ?_⟩
      rw [loopPrefix_succ]
      exact hBuilt.cell hNew
  · rintro store state ⟨-, vals, hHolds, heap', p, rfl, hBuilt⟩
    have hP : state.get 1 = some (.i64 p) := by cases hHolds; assumption
    have hLoop : loopPrefix f [] n.toNat = LeanExe.Examples.Lists.listRange n := rfl
    rw [hLoop] at hBuilt
    exact ⟨heap', hBuilt.at_, hBuilt.caps, fun q ws hq => (hBuilt.keepBorrowed hq).1,
      fun q ws hq => (hBuilt.keepOwned hq).1, [.i64 p], state,
      by simp [lists.listRange.ir, Func.scratch, Expr.evalResults, Expr.eval, hP],
      ⟨p, rfl, hBuilt.owned, hBuilt.disjoint⟩, fun q ws hq => (hBuilt.keepBorrowed hq).2,
      fun q ws hq => (hBuilt.keepOwned hq).2⟩

/-- `encode` succeeds on `lists.module`, and its bytes decode to a module that computes
`listSum` and `listRange` exactly. -/
theorem lists_bytes : ∃ bytes, Wasm.Encoding.encode lists.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 LeanExe.Examples.Lists.listSum ∧
      Implements m 3 LeanExe.Examples.Lists.listRange := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip lists.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, lists.module, decoded, listSum_implements, listRange_implements⟩

#print axioms lists_bytes

end Project.Lists
