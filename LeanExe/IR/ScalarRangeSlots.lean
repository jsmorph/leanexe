import LeanExe.IR.ScalarIteration

namespace LeanExe.IR

/-- The three fresh range locals follow all captured parameter slots. -/
def rangeStore (saved : ScalarStore) (value : UInt64) (index : Nat) (stop : UInt64) : ScalarStore :=
  saved ++ [value, UInt64.ofNat index, stop]

theorem read_suffix (saved suffix : ScalarStore) (index : Nat) :
    (saved ++ suffix)[saved.length + index]? = suffix[index]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem write_suffix (saved suffix : ScalarStore) (index : Nat) (value : UInt64)
    (bound : index < suffix.length) :
    ScalarStore.write (saved ++ suffix) (saved.length + index) value =
      some (saved ++ suffix.set index value) := by
  simp [ScalarStore.write, List.set_append_right, bound]

@[simp] theorem rangeStore_length (saved : ScalarStore) (value : UInt64) (index : Nat) (stop : UInt64) :
    (rangeStore saved value index stop).length = saved.length + 3 := by simp [rangeStore]

@[simp] theorem rangeStore_value (saved : ScalarStore) (value : UInt64) (index : Nat) (stop : UInt64) :
    (rangeStore saved value index stop)[saved.length]? = some value := by
  simpa [rangeStore] using read_suffix saved [value, UInt64.ofNat index, stop] 0

@[simp] theorem rangeStore_index (saved : ScalarStore) (value : UInt64) (index : Nat) (stop : UInt64) :
    (rangeStore saved value index stop)[saved.length + 1]? = some (UInt64.ofNat index) := by
  simp [rangeStore, read_suffix]

@[simp] theorem rangeStore_stop (saved : ScalarStore) (value : UInt64) (index : Nat) (stop : UInt64) :
    (rangeStore saved value index stop)[saved.length + 2]? = some stop := by
  simp [rangeStore, read_suffix]

@[simp] theorem rangeStore_write_value (saved : ScalarStore) (value result : UInt64) (index : Nat) (stop : UInt64) :
    (rangeStore saved value index stop).write saved.length result =
      some (rangeStore saved result index stop) := by
  simpa [rangeStore] using write_suffix saved [value, UInt64.ofNat index, stop] 0 result (by simp)

@[simp] theorem rangeStore_write_index (saved : ScalarStore) (value : UInt64) (index next : Nat) (stop : UInt64) :
    (rangeStore saved value index stop).write (saved.length + 1) (UInt64.ofNat next) =
      some (rangeStore saved value next stop) := by
  simpa [rangeStore] using write_suffix saved [value, UInt64.ofNat index, stop] 1 (UInt64.ofNat next) (by simp)

/-- The loop body emitted by the range extractor updates the accumulator before
advancing its index. Both writes remain in the three fresh local slots. -/
def rangeBody (slot : Nat) (step : Expr) : Stmt :=
  .seq (.assign slot step)
    (.assign (slot + 1) (.u64Bin .add (.local (slot + 1)) (.u64 1)))

def rangeCondition (slot : Nat) : Cond :=
  .ltU64 (.local (slot + 1)) (.local (slot + 2))

theorem rangeBody_step (saved : ScalarStore) (value result : UInt64) (index : Nat) (stop : UInt64)
    (step : Expr)
    (evaluated : step.ScalarEval (rangeStore saved value index stop) result
      (rangeStore saved value index stop)) :
    (rangeBody saved.length step).ScalarEval (rangeStore saved value index stop)
      (rangeStore saved result (index + 1) stop) := by
  apply Stmt.ScalarEval.seq
  · exact .assign evaluated (rangeStore_write_value saved value result index stop)
  · apply Stmt.ScalarEval.assign (v := UInt64.ofNat (index + 1))
    · exact .bin (.local (rangeStore_index saved result index stop)) .const
        (by simp [U64Op.evalScalar])
    · exact rangeStore_write_index saved result index (index + 1) stop

/-- A complete emitted range loop agrees with native ascending iteration.
The stop is a UInt64, so every index through the final test is represented exactly. -/
theorem range_while_execution (saved : ScalarStore) (value : UInt64) (stop : UInt64)
    (step : Expr) (meaning : Nat → UInt64 → UInt64)
    (evaluated : ∀ index, index < stop.toNat → ∀ value,
      step.ScalarEval (rangeStore saved value index stop) (meaning index value)
        (rangeStore saved value index stop)) :
    (Stmt.while (rangeCondition saved.length) (rangeBody saved.length step)).ScalarEval
      (rangeStore saved value 0 stop)
      (rangeStore saved (LeanExe.Source.Scalar.Range.iterate meaning stop.toNat 0 value) stop.toNat stop) := by
  let Inv := fun index value store => store = rangeStore saved value index stop
  have finish : ∀ value store, Inv stop.toNat value store →
      (rangeCondition saved.length).ScalarEval store false store := by
    intro value store same
    subst store
    have tested := Cond.ScalarEval.lt (Expr.ScalarEval.local (rangeStore_index saved value stop.toNat stop))
      (Expr.ScalarEval.local (rangeStore_stop saved value stop.toNat stop))
    simpa [rangeCondition] using tested
  have advance : ∀ index, index < stop.toNat → ∀ value store, Inv index value store →
      ∃ afterCondition afterBody,
        (rangeCondition saved.length).ScalarEval store true afterCondition ∧
        (rangeBody saved.length step).ScalarEval afterCondition afterBody ∧
        Inv (index + 1) (meaning index value) afterBody := by
    intro index below value store same
    subst store
    have less : UInt64.ofNat index < stop :=
      (LeanExe.Source.Scalar.Range.index_lt_stop (by omega)).mpr below
    refine ⟨rangeStore saved value index stop, rangeStore saved (meaning index value) (index + 1) stop, ?_,
      rangeBody_step saved value (meaning index value) index stop step (evaluated index below value), rfl⟩
    have tested := Cond.ScalarEval.lt (Expr.ScalarEval.local (rangeStore_index saved value index stop))
      (Expr.ScalarEval.local (rangeStore_stop saved value index stop))
    simpa [rangeCondition, less] using tested
  obtain ⟨finalStore, executed, finalShape⟩ := bounded_while_execution
    (rangeCondition saved.length) (rangeBody saved.length step) meaning stop.toNat Inv finish advance
    stop.toNat 0 (by simp) value (rangeStore saved value 0 stop) rfl
  exact finalShape ▸ executed

end LeanExe.IR
