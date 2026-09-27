import Project.Beck.ExecutionComputePrepare

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure ComputeInitialLocals (locals : List Value) (input : Input)
    (inputOwner inputRoot pointOwner pointRoot : UInt64) : Prop extends ComputeInputLocals locals input inputOwner inputRoot where
  fuel : locals[15]? = some (.i64 input.jobs.toUInt64)
  inputStatus : locals[16]? = some (.i64 input.status)
  inputJobs : locals[17]? = some (.i64 input.jobs.toUInt64)
  inputCategories : locals[18]? = some (.i64 input.categories.toUInt64)
  inputOverlap : locals[19]? = some (.i64 input.overlap.toUInt64)
  inputOwner : locals[20]? = some (.i64 inputOwner)
  inputPointer : locals[21]? = some (.i64 inputRoot)
  denominator : locals[24]? = some (.i64 1)
  pointOwner : locals[25]? = some (.i64 pointOwner)
  pointPointer : locals[26]? = some (.i64 pointRoot)

theorem computeInitial_state {before after : List Value} {input : Input} {inputOwner inputRoot pointOwner pointRoot : UInt64}
    (state : ComputeInputLocals before input inputOwner inputRoot) (size : after.length = 79) (typed : WordLocals after)
    (keeps : ∀ k, k < 22 ∨ k = 24 → after[k]? = (computePreparedLocals before input inputOwner inputRoot)[k]?)
    (ownerRead : after[25]? = some (.i64 pointOwner)) (pointerRead : after[26]? = some (.i64 pointRoot)) :
    ComputeInitialLocals after input inputOwner inputRoot pointOwner pointRoot := by
  have prepared := computePrepared_update state.words input inputOwner inputRoot
  have low : ∀ k, k < 14 → after[k]? = before[k]? := by
    intro k bound
    exact (keeps k (Or.inl (by omega))).trans (prepared.keeps k (Or.inl bound))
  refine ⟨⟨size, typed, (low 8 (by decide)).trans state.status, (low 9 (by decide)).trans state.jobs,
    (low 10 (by decide)).trans state.categories, (low 11 (by decide)).trans state.overlap,
    (low 12 (by decide)).trans state.owner, (low 13 (by decide)).trans state.pointer⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ownerRead, pointerRead⟩
  all_goals
    rw [keeps _ (by omega)]
    simp [computePreparedLocals, List.getElem?_set, state.size]

#print axioms computeInitial_state

end Project.Beck.Execution
