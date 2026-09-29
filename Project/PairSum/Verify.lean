import Project.PairSum.Module
import Project.IR.Correct
import Project.Encoding.RoundTrip

namespace Project.PairSum

open Wasm Project.Pipeline Project.IR Project.Runtime

/-- `pairSum` with its two arguments as one pair. -/
def pairTuple (x : UInt64 × UInt64) : UInt64 := LeanExe.Examples.PairSum.pairSum x.1 x.2

theorem pairSum_implements : Implements pairSum.module 0 pairTuple (fun _ => 72) := by
  refine Func.implements_heap pairSum.ir "pairSum" pairTuple (fun _ => 72)
    (fun _ _ _ x h => by rw [Scalar.borrowed.mp h]; rfl) ?_
  rintro ⟨a, b⟩ heap initial params hHeap hArgs hRoom
  obtain rfl := Scalar.borrowed.mp hArgs
  have hMemory32 : (compile pairSum.ir "pairSum").memIs64 = false := rfl
  have hImports : (compile pairSum.ir "pairSum").imports = [] := rfl
  have hAlloc : (compile pairSum.ir "pairSum").funcs[1]? = some (allocFunction 1) := rfl
  have hRelease : (compile pairSum.ir "pairSum").funcs[3]? = some (releaseFunction 2) := rfl
  let start : State := { params := [.i64 a, .i64 b], locals := List.replicate 5 (.i64 0) }
  show Triple _ (.seq (.arrayLiteral 2 [.get 0, .get 1]) (.seq (.assign 3 (.const 0))
    (.seq (.fold .u64 2 3 4 5 6 (.bin .add (.get 3) (.get 6))) (.release 2)))) 7
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.arrayLiteral_spec (words := [a, b]) hMemory32 hImports hAlloc
    (by decide) (by simp [start]) hHeap hRoom ?_) ?_
  · refine .cons (fun state hFrame => ⟨state, ?_⟩) (.cons (fun state hFrame => ⟨state, ?_⟩) .nil)
    · have hGet : state.get 0 = some (.i64 a) :=
        (hFrame.get 0 (by decide) (by decide)).trans (by simp [start, State.get])
      simp [Expr.eval, hGet]
    · have hGet : state.get 1 = some (.i64 b) :=
        (hFrame.get 1 (by decide) (by decide)).trans (by simp [start, State.get])
      simp [Expr.eval, hGet]
  apply Triple.of_forall
  rintro store state ⟨ptr, hFrame, hPtr, hAt, hOwned, hTop, hPages, -⟩
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
  refine ⟨_, hAt.release hOwned, rfl, hTop, ?_, _, s2, ?_, rfl⟩
  · simpa [Heap.releaseStore] using hPages
  · simp [pairSum.ir, Func.scratch, Expr.eval, hAcc, pairTuple, LeanExe.Examples.PairSum.pairSum]

/-- The bytes `encode` produces for `pairSum.module` decode to a module that
computes `pairSum` exactly, allocating at most 72 bytes. -/
theorem pairSum_bytes (bytes : ByteArray)
    (success : Wasm.Encoding.encode pairSum.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 0 pairTuple (fun _ => 72) :=
  ⟨pairSum.module, Wasm.Encoding.decode_encode pairSum.module bytes (by decide) success,
    pairSum_implements⟩

end Project.PairSum
