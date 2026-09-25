import LeanExe.IR.ScalarRangeSlots
import LeanExe.IR.ScalarIterationExit

namespace LeanExe.IR

/-- The exit flag is staged before updating the accumulator, so both step
projections observe the same source accumulator. It is not a source binding. -/
def rangeExitStore (saved : ScalarStore) (value : UInt64) (index : Nat)
    (stop flag : UInt64) : ScalarStore := saved ++ [value, UInt64.ofNat index, stop, flag]

@[simp] theorem rangeExitStore_length (saved : ScalarStore) (value : UInt64)
    (index : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag).length = saved.length + 4 := by simp [rangeExitStore]

@[simp] theorem rangeExitStore_value (saved : ScalarStore) (value : UInt64)
    (index : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag)[saved.length]? = some value := by
  simpa [rangeExitStore] using read_suffix saved [value, UInt64.ofNat index, stop, flag] 0

@[simp] theorem rangeExitStore_index (saved : ScalarStore) (value : UInt64)
    (index : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag)[saved.length + 1]? = some (UInt64.ofNat index) := by
  simp [rangeExitStore]

@[simp] theorem rangeExitStore_stop (saved : ScalarStore) (value : UInt64)
    (index : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag)[saved.length + 2]? = some stop := by simp [rangeExitStore]

@[simp] theorem rangeExitStore_flag (saved : ScalarStore) (value : UInt64)
    (index : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag)[saved.length + 3]? = some flag := by simp [rangeExitStore]

@[simp] theorem rangeExitStore_write_value (saved : ScalarStore) (value result : UInt64)
    (index : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag).write saved.length result =
      some (rangeExitStore saved result index stop flag) := by
  simpa [rangeExitStore] using write_suffix saved [value, UInt64.ofNat index, stop, flag] 0 result (by simp)

@[simp] theorem rangeExitStore_write_index (saved : ScalarStore) (value : UInt64)
    (index next : Nat) (stop flag : UInt64) :
    (rangeExitStore saved value index stop flag).write (saved.length + 1) (UInt64.ofNat next) =
      some (rangeExitStore saved value next stop flag) := by
  simpa [rangeExitStore] using write_suffix saved [value, UInt64.ofNat index, stop, flag] 1 (UInt64.ofNat next) (by simp)

@[simp] theorem rangeExitStore_write_flag (saved : ScalarStore) (value : UInt64)
    (index : Nat) (stop flag next : UInt64) :
    (rangeExitStore saved value index stop flag).write (saved.length + 3) next =
      some (rangeExitStore saved value index stop next) := by
  simpa [rangeExitStore] using write_suffix saved [value, UInt64.ofNat index, stop, flag] 3 next (by simp)

def rangeExitFlag (outcome : ForInStep UInt64) : UInt64 :=
  if LeanExe.Source.Scalar.Range.Exit.isDone outcome then 1 else 0

def rangeExitNextIndex (index : Nat) (stop : UInt64) (outcome : ForInStep UInt64) : Nat :=
  if LeanExe.Source.Scalar.Range.Exit.isDone outcome then stop.toNat else index + 1

def rangeExitIndex (slot : Nat) : Expr :=
  .ite (.eqU64 (.local (slot + 3)) (.u64 0))
    (.u64Bin .add (.local (slot + 1)) (.u64 1)) (.local (slot + 2))

def rangeExitBody (slot : Nat) (step done : Expr) : Stmt :=
  .seq (.assign (slot + 3) done)
    (.seq (.assign slot step) (.assign (slot + 1) (rangeExitIndex slot)))

theorem rangeExitIndex_eval (saved : ScalarStore) (value : UInt64) (index : Nat)
    (stop : UInt64) (outcome : ForInStep UInt64) :
    (rangeExitIndex saved.length).ScalarEval
      (rangeExitStore saved value index stop (rangeExitFlag outcome))
      (UInt64.ofNat (rangeExitNextIndex index stop outcome))
      (rangeExitStore saved value index stop (rangeExitFlag outcome)) := by
  cases outcome with
  | done result =>
    simp only [rangeExitFlag, rangeExitNextIndex, LeanExe.Source.Scalar.Range.Exit.isDone, ite_true]
    apply Expr.ScalarEval.iteFalse
    · simpa using Cond.ScalarEval.eq
        (Expr.ScalarEval.local (rangeExitStore_flag saved value index stop 1)) (Expr.ScalarEval.const (n := 0))
    · simpa using Expr.ScalarEval.local (rangeExitStore_stop saved value index stop 1)
  | yield result =>
    simp only [rangeExitFlag, rangeExitNextIndex, LeanExe.Source.Scalar.Range.Exit.isDone, Bool.false_eq_true, ite_false]
    apply Expr.ScalarEval.iteTrue
    · simpa using Cond.ScalarEval.eq
        (Expr.ScalarEval.local (rangeExitStore_flag saved value index stop 0)) (Expr.ScalarEval.const (n := 0))
    · exact .bin (.local (rangeExitStore_index saved value index stop 0)) .const
        (by simp [U64Op.evalScalar])

theorem rangeExitBody_step (saved : ScalarStore) (value : UInt64) (index : Nat)
    (stop flag : UInt64) (step done : Expr) (outcome : ForInStep UInt64)
    (doneEval : done.ScalarEval (rangeExitStore saved value index stop flag) (rangeExitFlag outcome)
      (rangeExitStore saved value index stop flag))
    (valueEval : step.ScalarEval (rangeExitStore saved value index stop (rangeExitFlag outcome))
      (LeanExe.Source.Scalar.Range.Exit.value outcome)
      (rangeExitStore saved value index stop (rangeExitFlag outcome))) :
    (rangeExitBody saved.length step done).ScalarEval (rangeExitStore saved value index stop flag)
      (rangeExitStore saved (LeanExe.Source.Scalar.Range.Exit.value outcome)
        (rangeExitNextIndex index stop outcome) stop (rangeExitFlag outcome)) := by
  apply Stmt.ScalarEval.seq
  · exact .assign doneEval (rangeExitStore_write_flag saved value index stop flag (rangeExitFlag outcome))
  · apply Stmt.ScalarEval.seq
    · exact .assign valueEval (rangeExitStore_write_value saved value
        (LeanExe.Source.Scalar.Range.Exit.value outcome) index stop (rangeExitFlag outcome))
    · exact .assign (rangeExitIndex_eval saved (LeanExe.Source.Scalar.Range.Exit.value outcome) index stop outcome)
        (rangeExitStore_write_index saved (LeanExe.Source.Scalar.Range.Exit.value outcome) index
          (rangeExitNextIndex index stop outcome) stop (rangeExitFlag outcome))

/-- The concrete four-local loop implements bounded native early-exit
iteration. Both projections are read-only and may be evaluated with any flag. -/
theorem rangeExit_while_execution (saved : ScalarStore) (initial stop initialFlag : UInt64)
    (step done : Expr) (meaning : Nat → UInt64 → ForInStep UInt64)
    (doneEval : ∀ index, index < stop.toNat → ∀ value flag,
      done.ScalarEval (rangeExitStore saved value index stop flag) (rangeExitFlag (meaning index value))
        (rangeExitStore saved value index stop flag))
    (valueEval : ∀ index, index < stop.toNat → ∀ value flag,
      step.ScalarEval (rangeExitStore saved value index stop flag)
        (LeanExe.Source.Scalar.Range.Exit.value (meaning index value))
        (rangeExitStore saved value index stop flag)) :
    ∃ finalFlag,
      (Stmt.while (rangeCondition saved.length) (rangeExitBody saved.length step done)).ScalarEval
        (rangeExitStore saved initial 0 stop initialFlag)
        (rangeExitStore saved (LeanExe.Source.Scalar.Range.Exit.iterate meaning stop.toNat 0 initial)
          stop.toNat stop finalFlag) := by
  let Inv := fun index value store => ∃ flag, store = rangeExitStore saved value index stop flag
  have finish : ∀ value store, Inv stop.toNat value store →
      (rangeCondition saved.length).ScalarEval store false store := by
    intro value store invariant
    obtain ⟨flag, rfl⟩ := invariant
    have tested := Cond.ScalarEval.lt (Expr.ScalarEval.local (rangeExitStore_index saved value stop.toNat stop flag))
      (Expr.ScalarEval.local (rangeExitStore_stop saved value stop.toNat stop flag))
    simpa [rangeCondition] using tested
  have advance : ∀ index, index < stop.toNat → ∀ value store, Inv index value store →
      ∃ afterCondition afterBody,
        (rangeCondition saved.length).ScalarEval store true afterCondition ∧
        (rangeExitBody saved.length step done).ScalarEval afterCondition afterBody ∧
        match meaning index value with
        | .done next => Inv stop.toNat next afterBody
        | .yield next => Inv (index + 1) next afterBody := by
    intro index below value store invariant
    obtain ⟨flag, rfl⟩ := invariant
    have less : UInt64.ofNat index < stop :=
      (LeanExe.Source.Scalar.Range.index_lt_stop (by omega)).mpr below
    refine ⟨rangeExitStore saved value index stop flag,
      rangeExitStore saved (LeanExe.Source.Scalar.Range.Exit.value (meaning index value))
        (rangeExitNextIndex index stop (meaning index value)) stop (rangeExitFlag (meaning index value)), ?_,
      rangeExitBody_step saved value index stop flag step done (meaning index value)
        (doneEval index below value flag) (valueEval index below value (rangeExitFlag (meaning index value))), ?_⟩
    · have tested := Cond.ScalarEval.lt (Expr.ScalarEval.local (rangeExitStore_index saved value index stop flag))
        (Expr.ScalarEval.local (rangeExitStore_stop saved value index stop flag))
      simpa [rangeCondition, less] using tested
    · cases meaning index value with
      | done next => exact ⟨1, rfl⟩
      | yield next => exact ⟨0, rfl⟩
  obtain ⟨finalStore, executed, finalFlag, rfl⟩ := bounded_while_exit_execution
    (rangeCondition saved.length) (rangeExitBody saved.length step done) meaning stop.toNat Inv finish advance
    stop.toNat 0 (by simp) initial (rangeExitStore saved initial 0 stop initialFlag) ⟨initialFlag, rfl⟩
  exact ⟨finalFlag, executed⟩

end LeanExe.IR
