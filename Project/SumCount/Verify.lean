import Project.SumCount.Module
import Project.IR.Correct
import Project.Encoding.RoundTrip

namespace Project.SumCount

open Wasm Project.Pipeline Project.IR Project.Runtime

theorem sumCount_implements :
    Implements sumCount.module 0 LeanExe.Examples.SumCount.sumCount (fun _ => 72) := by
  refine Func.implements_heap sumCount.ir "sumCount" _ (fun _ => 72)
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨ptr, rfl, hBorrowed⟩ hRoom
  have hMemory32 : (compile sumCount.ir "sumCount").memIs64 = false := rfl
  have hImports : (compile sumCount.ir "sumCount").imports = [] := rfl
  have hAlloc : (compile sumCount.ir "sumCount").funcs[1]? = some (allocFunction 1) := rfl
  let start : State := { params := [.i64 ptr], locals := List.replicate 6 (.i64 0) }
  show Triple _ (.seq (.assign 1 (.const 0)) (.seq (.fold .u64 0 1 2 3 4 (.bin .add (.get 1) (.get 4)))
    (.seq (.arraySize 5 0) (.arrayLiteral 6 [.get 1, .get 5])))) 7
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  refine Stmt.seq_spec ((Stmt.fold_spec (initial := initial) (before := start) (ptr := ptr)
    (start := 0) (· + ·) (by decide) (by decide) (by simp [start]) hBorrowed.values rfl rfl
    fun state a e _ hA hE => ⟨state, by simp [Expr.eval, hA, hE, U64Op.apply]⟩).mono
      (fun _ _ h => h) (R' := fun store state => store = initial ∧
        State.Frame 7 [1, 2, 3, 4] start state ∧
        state.get 1 = some (.i64 (xs.foldl (· + ·) 0))) fun _ _ h => h) ?_
  apply Triple.of_forall
  rintro store s2 ⟨hStore, hFrame2, hAcc⟩
  subst store
  have hPtr2 : s2.get 0 = some (.i64 ptr) := (hFrame2.get 0 (by decide) (by decide)).trans rfl
  have hLength2 : s2.params.length + s2.locals.length = 7 := by
    rw [hFrame2.params, hFrame2.locals]; simp [start]
  obtain ⟨s3, hSet3⟩ := State.exists_set? (state := s2) (index := 5)
    (.i64 (UInt64.ofNat xs.size)) (by omega)
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s3)
    ((Stmt.arraySize_spec hBorrowed.values hPtr2 (by omega)).mono (fun _ _ h => h) ?_) ?_
  · rintro store state ⟨hStore, hSet⟩
    exact ⟨hStore, Option.some.inj (hSet.symm.trans hSet3)⟩
  apply Triple.of_forall
  rintro store s3' ⟨hStore, hState⟩
  subst store s3'
  have hFrame3 := (State.Frame.refl 7 [5] s2).set? hSet3 (Or.inl (by simp))
  refine (Stmt.arrayLiteral_spec (values := [.get 1, .get 5])
    (words := [xs.foldl (· + ·) 0, UInt64.ofNat xs.size]) hMemory32 hImports hAlloc (by decide)
    (by rw [hFrame3.params, hFrame3.locals]; omega) hHeap hRoom ?_).mono
      (fun _ _ h => h) ?_
  · refine .cons (fun state hFrame => ⟨state, ?_⟩) (.cons (fun state hFrame => ⟨state, ?_⟩) .nil)
    · have hGet : state.get 1 = some (.i64 (xs.foldl (· + ·) 0)) := by
        rw [hFrame.get 1 (by decide) (by decide), State.get_set?_ne (by decide) hSet3, hAcc]
      simp [Expr.eval, hGet]
    · have hGet : state.get 5 = some (.i64 (UInt64.ofNat xs.size)) := by
        rw [hFrame.get 5 (by decide) (by decide), State.get_set?_same hSet3]
      simp [Expr.eval, hGet]
  · rintro store state ⟨result, -, hResult, hAt, hOwned, hTop, hPages, hKeep⟩
    refine ⟨_, hAt, ⟨ptr, rfl, hKeep ptr xs hBorrowed⟩, hTop, hPages, result, state,
      by simp [sumCount.ir, Func.scratch, Expr.eval, hResult], result, rfl, ?_⟩
    simpa [LeanExe.Examples.SumCount.sumCount] using hOwned

/-- The bytes `encode` produces for `sumCount.module` decode to a module that
computes `sumCount` exactly, returning an array the caller owns. -/
theorem sumCount_bytes (bytes : ByteArray)
    (success : Wasm.Encoding.encode sumCount.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 0 LeanExe.Examples.SumCount.sumCount (fun _ => 72) :=
  ⟨sumCount.module, Wasm.Encoding.decode_encode sumCount.module bytes (by decide) success,
    sumCount_implements⟩

end Project.SumCount
