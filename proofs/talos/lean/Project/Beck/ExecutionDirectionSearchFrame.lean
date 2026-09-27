import Project.Beck.ExecutionDirectionFirstRead
import Project.Beck.ExecutionWordWindow

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem DirectionSeed.preserved {original before after : Heap} {initial final : Store Unit} {ro rp co cp : FreeNode}
    (seed : DirectionSeed original before initial ro rp co cp) (frame : before.Frame initial after final) (valid : after.At final) :
    DirectionSeed original after final ro rp co cp :=
  { seed with
    rowOwner := frame.ownsWords valid seed.rowOwner
    rowPointer := frame.ownsWords valid seed.rowPointer
    columnOwner := frame.ownsWords valid seed.columnOwner
    columnPointer := frame.ownsWords valid seed.columnPointer }

structure DirectionSearchLocals (locals : List Value) (matrix srOwner srPointer scOwner scPointer : UInt64)
    (basis : Basis) (ro rp co cp : UInt64) : Prop where
  size : locals.length = 112
  matrixOriginal : locals[9]? = some (.i64 matrix)
  matrixOwner : locals[11]? = some (.i64 matrix)
  matrixPointer : locals[12]? = some (.i64 matrix)
  seedRowOwner : locals[19]? = some (.i64 srOwner)
  seedRowPointer : locals[20]? = some (.i64 srPointer)
  seedColumnOwner : locals[21]? = some (.i64 scOwner)
  seedColumnPointer : locals[22]? = some (.i64 scPointer)
  rowOwner : locals[29]? = some (.i64 ro)
  rowPointer : locals[30]? = some (.i64 rp)
  columnOwner : locals[31]? = some (.i64 co)
  columnPointer : locals[32]? = some (.i64 cp)
  determinant : locals[33]? = some (.i64 basis.determinant)
  words : WordLocals locals

structure DirectionSeedLocals (locals : List Value) (jobs : Nat) (matrix ro rp co cp : UInt64) : Prop
    extends DirectionBasisLocals locals jobs matrix ro rp co cp where
  matrixOriginal : locals[9]? = some (.i64 matrix)
  originalOwner : locals[11]? = some (.i64 matrix)
  originalPointer : locals[12]? = some (.i64 matrix)
  words : WordLocals locals

theorem directionInitialLocals_words (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer matrix : UInt64) :
    WordLocals (directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer matrix) := by
  unfold directionInitialLocals directionMatrixLocals directionPreparedLocals
  repeat' apply WordLocals.set
  exact WordLocals.replicate 112 0

theorem directionSeedSaved_words {saved : List Value} (typed : WordLocals saved) (ro rp co cp : UInt64) :
    WordLocals (directionSeedSaved saved ro rp co cp) := by
  unfold directionSeedSaved directionEmptySaved
  repeat' apply WordLocals.set
  exact typed

theorem directionSeedFrame_words (params locals : List Value) (typed : WordLocals locals)
    (ro rp co cp previous current capacity afterNode : UInt64) :
    WordLocals (FixedArraySearch.frame params (directionSeedSaved (locals.take 93) ro rp co cp) (locals.drop 99)
      8 previous current capacity afterNode cp).locals :=
  (directionSeedSaved_words (typed.take 93) ro rp co cp).searchFrame (typed.drop 99) params 8 previous current capacity afterNode cp

theorem directionSeed_state (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer matrix ro rp co cp : UInt64)
    (previous current capacity afterNode : UInt64) :
    let initial := directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer matrix
    let seeded := (FixedArraySearch.frame (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
      (directionSeedSaved (initial.take 93) ro rp co cp) (initial.drop 99) 8 previous current capacity afterNode cp).locals
    DirectionSeedLocals seeded input.jobs matrix ro rp co cp := by
  dsimp only
  refine ⟨direction_seed_basis_state input point inputOwner inputPointer pointOwner pointPointer matrix ro rp co cp previous current capacity afterNode, ?_, ?_, ?_, ?_⟩
  case refine_1 | refine_2 | refine_3 => simp [FixedArraySearch.frame, directionSeedSaved, directionEmptySaved,
      directionInitialLocals, directionMatrixLocals, directionPreparedLocals]
  exact directionSeedFrame_words (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
    (directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer matrix)
    (directionInitialLocals_words input point inputOwner inputPointer pointOwner pointPointer matrix)
    ro rp co cp previous current capacity afterNode

theorem directionSearch_state (input : Input) (point : Point) (basis : Basis)
    (inputOwner inputPointer pointOwner pointPointer matrix srOwner srPointer scOwner scPointer ro rp co cp : UInt64)
    (locals : List Value) (state : DirectionSeedLocals locals input.jobs matrix srOwner srPointer scOwner scPointer) :
    DirectionSearchLocals (directionFreeLocals (locals.set 23 (.i64 1)) input point basis inputOwner inputPointer pointOwner pointPointer ro rp co cp)
      matrix srOwner srPointer scOwner scPointer basis ro rp co cp := by
  constructor
  all_goals first
    | (solve | simp only [directionFreeLocals, List.length_set, List.getElem?_set,
    state.size, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, state.matrixOriginal, state.originalOwner, state.originalPointer,
    state.rowOwner, state.rowPointer, state.columnOwner, state.columnPointer])
    | skip
  unfold directionFreeLocals
  repeat' apply WordLocals.set
  exact state.words

#print axioms directionSearch_state

end Project.Beck.Execution
