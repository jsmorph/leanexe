import Project.Beck.ExecutionRound
import Project.Beck.ExecutionPreviousRelease
import Project.Beck.Loop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsParams (fuel : Nat) (input : Input) (point : Point) (inputRoot pointOwner pointRoot : UInt64) : List Value :=
  .i64 fuel.toUInt64 :: matrixParams input point inputRoot inputRoot pointOwner pointRoot

def roundsBody : Wasm.Program := match (func34[6]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def roundsAdvancing : Wasm.Program := match (roundsBody[25]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def roundsContinue : Wasm.Program := match (roundsAdvancing[47]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def roundsFinish : Wasm.Program := match (func34[10]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

structure RoundsLocals (locals : List Value) (stopped : Bool) (point : Point) (pointOwner root internal : UInt64) : Prop where
  size : locals.length = 61
  owner : locals[0]? = some (.i64 internal)
  extra : locals[1]? = some (.i64 0)
  flag : locals[5]? = some (.i64 (if stopped then 1 else 0))
  result : stopped = true → locals[2]? = some (.i64 point.denominator) ∧
    locals[3]? = some (.i64 pointOwner) ∧ locals[4]? = some (.i64 root)

theorem RoundsLocals.preserved {before after : List Value} {stopped : Bool} {point : Point} {pointOwner root internal : UInt64}
    (state : RoundsLocals before stopped point pointOwner root internal) (size : after.length = before.length)
    (keeps : ∀ k, k < 6 → after[k]? = before[k]?) : RoundsLocals after stopped point pointOwner root internal := by
  refine ⟨size.trans state.size, (keeps 0 (by omega)).trans state.owner,
    (keeps 1 (by omega)).trans state.extra, (keeps 5 (by omega)).trans state.flag, ?_⟩
  intro stopped
  obtain ⟨den, owner, pointer⟩ := state.result stopped
  exact ⟨(keeps 2 (by omega)).trans den, (keeps 3 (by omega)).trans owner, (keeps 4 (by omega)).trans pointer⟩

theorem roundsEntry_state (point : Point) (pointOwner root : UInt64) :
    RoundsLocals (List.replicate 61 (.i64 0)) false point pointOwner root 0 := by
  constructor <;> simp

set_option maxRecDepth 4096 in
theorem roundsEntry_exact (env : HostEnv Unit) (initial : Store Unit) (params : List Value)
    (size : params.length = 10) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := List.replicate 61 (.i64 0) })) :
    wp Project.Beck.«module» (func34.take 6) Q initial
      { params := params, locals := List.replicate 61 (.i64 0) } env := by
  simp only [func34, List.take]
  wp_run [size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, List.set]
  exact next

#print axioms roundsEntry_exact

end Project.Beck.Execution
