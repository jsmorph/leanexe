import Project.PairSum.Module
import Project.IR.Correct
import Project.Encoding.RoundTrip

namespace Project.PairSum

open Wasm Project.Pipeline Project.IR Project.Runtime

/-- `pairSum` with its two arguments as one pair. -/
def pairTuple (x : UInt64 × UInt64) : UInt64 := LeanExe.Examples.PairSum.pairSum x.1 x.2

theorem pairSum_implements : Implements pairSum.module 2 pairTuple := by
  refine Func.implements_heap [(pairSum.ir, "pairSum")] 0 pairSum.ir "pairSum" rfl pairTuple
    (fun _ _ _ x h => by rw [Scalar.borrowed.mp h]; rfl) ?_
  rintro ⟨a, b⟩ heap initial params hHeap hArgs hCap
  obtain rfl := Scalar.borrowed.mp hArgs
  have hMemory32 : (compile [(pairSum.ir, "pairSum")]).memIs64 = false := rfl
  have hImports : (compile [(pairSum.ir, "pairSum")]).imports = [] := rfl
  have hAlloc : (compile [(pairSum.ir, "pairSum")]).funcs[0]? = some (allocFunction 0) := rfl
  have hRelease : (compile [(pairSum.ir, "pairSum")]).funcs[1]? = some (releaseFunction 1) := rfl
  let start : State := { params := [.i64 a, .i64 b], locals := List.replicate 5 (.i64 0) }
  show Triple _ (.seq (.arrayLiteral 2 [.get 0, .get 1]) (.seq (.assign 3 (.const 0))
    (.seq (.fold .u64 2 3 4 5 6 (.bin .add (.get 3) (.get 6))) (.release 2)))) 7
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.arrayLiteral_spec (words := [a, b]) hMemory32 hImports hAlloc
    (by decide) (by simp [start]) hHeap hCap (by decide) ?_) ?_
  · refine .cons (fun _ state hFrame => ⟨state, ?_⟩) (.cons (fun _ state hFrame => ⟨state, ?_⟩) .nil)
    · have hGet : state.get 0 = some (.i64 a) :=
        (hFrame.get 0 (by decide) (by decide)).trans (by simp [start, State.get])
      simp [Expr.eval, hGet]
    · have hGet : state.get 1 = some (.i64 b) :=
        (hFrame.get 1 (by decide) (by decide)).trans (by simp [start, State.get])
      simp [Expr.eval, hGet]
  apply Triple.of_forall
  rintro store state ⟨ptr, hFrame, hPtr, hNew⟩
  have hAt := hNew.at_
  have hOwned := hNew.owned
  have hLength : state.params.length + state.locals.length = 7 := by
    rw [hFrame.params, hFrame.locals]; simp [start]
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := state) (index := 3) (.i64 0) (by omega)
  have hFrame1 := (State.Frame.refl 7 [3, 4, 5, 6] state).set? hSet1 (Or.inl (by simp))
  refine Stmt.seq_spec (M := fun store' state' => store' = store ∧ state' = s1) ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store' state' ⟨hs, ht⟩
    subst store' state'
    exact ⟨0, state, s1, rfl, hSet1, rfl, rfl⟩
  apply Triple.of_forall
  rintro store' state' ⟨hs, ht⟩
  subst store' state'
  refine Stmt.seq_spec ((Stmt.fold_spec (initial := store) (before := s1) (ptr := ptr)
    (start := 0) (· + ·) (by decide) (by decide)
    (by rw [hFrame1.params, hFrame1.locals]; omega) hOwned.values
    (by rw [State.get_set?_ne (by decide) hSet1, hPtr]) (State.get_set?_same hSet1)
    fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, U64Op.apply]⟩).mono
      (fun _ _ h => h) (R' := fun store' state' => store' = store ∧
        State.Frame 7 [3, 4, 5, 6] s1 state' ∧
        state'.get 3 = some (.i64 (#[a, b].foldl (· + ·) 0))) fun _ _ h => h) ?_
  apply Triple.of_forall
  rintro store' s2 ⟨hs, hFrame2, hAcc⟩
  subst store'
  have hPtr2 : s2.get 2 = some (.i64 ptr) := by
    rw [hFrame2.get 2 (by decide) (by decide), State.get_set?_ne (by decide) hSet1, hPtr]
  refine (Stmt.release_spec hImports hRelease hPtr2 hAt hOwned).mono (fun _ _ h => h) ?_
  rintro store' state' ⟨hs, ht⟩
  subst store' state'
  refine ⟨_, hAt.release hOwned, rfl, hNew.caps, fun p ws h =>
      (hNew.borrowed p ws h).release hAt hOwned (hNew.borrowedApart p ws h), fun p ws h => ?_,
    _, s2, ?_, rfl, fun _ _ _ => trivial, fun _ _ _ => trivial⟩
  · obtain ⟨hKept, hCapacity⟩ := hNew.ownedKeep p ws h
    obtain ⟨hReleased, hCapacity'⟩ :=
      hKept.release hAt hOwned (by rw [hCapacity]; exact hNew.ownedApart p ws h)
    exact ⟨hReleased, hCapacity'.trans hCapacity⟩
  · simp [pairSum.ir, Func.scratch, Expr.evalResults, Expr.eval, hAcc, pairTuple,
      LeanExe.Examples.PairSum.pairSum, Scalar.values]

/-- `encode` succeeds on `pairSum.module`, and its bytes decode to a module that
computes `pairSum` exactly. -/
theorem pairSum_bytes : ∃ bytes, Wasm.Encoding.encode pairSum.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 pairTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip pairSum.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, pairSum.module, decoded, pairSum_implements⟩

end Project.PairSum
