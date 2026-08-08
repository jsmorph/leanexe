import Project.ProofKit.ScalarTransition

namespace Project.ProofKit.ScalarTransition

open Wasm

structure U64State where
  params : List UInt64
  locals : List UInt64
  deriving Repr

@[simp]
theorem u64_one_beq_zero : (((1 : UInt64) == (0 : UInt64)) = false) := by
  decide

@[simp]
theorem u64_zero_beq_one : (((0 : UInt64) == (1 : UInt64)) = false) := by
  decide

def U64State.toState (state : U64State) : State :=
  { params := state.params.map Value.i64
    locals := state.locals.map Value.i64 }

def U64State.get (state : U64State) (index : Nat) : Option UInt64 :=
  if index < state.params.length then state.params[index]?
  else if index < state.params.length + state.locals.length then
    state.locals[index - state.params.length]?
  else none

def U64State.set? (state : U64State) (index : Nat) (value : UInt64) : Option U64State :=
  if index < state.params.length then
    some { state with params := state.params.set index value }
  else if index < state.params.length + state.locals.length then
    some { state with locals := state.locals.set (index - state.params.length) value }
  else none

@[simp]
theorem U64State.toState_get (state : U64State) (index : Nat) :
    state.toState.get index = (state.get index).map Value.i64 := by
  by_cases hParam : index < state.params.length
  · simp [State.get, U64State.get, U64State.toState, hParam]
  · by_cases hLocal : index < state.params.length + state.locals.length
    · simp [State.get, U64State.get, U64State.toState, hParam, hLocal]
    · simp [State.get, U64State.get, U64State.toState, hParam, hLocal]

@[simp]
theorem U64State.toState_set? (state : U64State) (index : Nat) (value : UInt64) :
    state.toState.set? index (.i64 value) =
      (state.set? index value).map U64State.toState := by
  by_cases hParam : index < state.params.length
  · simp [State.set?, U64State.set?, U64State.toState, hParam]
  · by_cases hLocal : index < state.params.length + state.locals.length
    · simp [State.set?, U64State.set?, U64State.toState, hParam, hLocal,
        List.map_set]
    · simp [State.set?, U64State.set?, U64State.toState, hParam, hLocal]

mutual

  def Expr.evalU64 : {type : ScalarType} →
      Expr type → Nat → U64State → Option (type.denote × U64State)
    | .u64, .get index, _, state => do
        let value ← state.get index
        pure (value, state)
    | .u64, .const value, _, state => pure (value, state)
    | .bool, .bconst value, _, state => pure (value, state)
    | .u64, .bin operation left right, scratch, state => do
        let childScratch :=
          if operation = .divU ∨ operation = .remU then scratch + 2 else scratch
        let (leftValue, afterLeft) ← left.evalU64 childScratch state
        let afterLeft ←
          if operation = .divU ∨ operation = .remU then
            afterLeft.set? scratch leftValue
          else some afterLeft
        let (rightValue, afterRight) ← right.evalU64 childScratch afterLeft
        let afterRight ←
          if operation = .divU ∨ operation = .remU then
            afterRight.set? (scratch + 1) rightValue
          else some afterRight
        pure (operation.apply leftValue rightValue, afterRight)
    | .bool, .eq left right, scratch, state => do
        let (leftValue, afterLeft) ← left.evalU64 scratch state
        let (rightValue, afterRight) ← right.evalU64 scratch afterLeft
        pure (leftValue == rightValue, afterRight)
    | .bool, .ne left right, scratch, state => do
        let (leftValue, afterLeft) ← left.evalU64 scratch state
        let (rightValue, afterRight) ← right.evalU64 scratch afterLeft
        pure (leftValue != rightValue, afterRight)
    | .bool, .ltU left right, scratch, state => do
        let (leftValue, afterLeft) ← left.evalU64 scratch state
        let (rightValue, afterRight) ← right.evalU64 scratch afterLeft
        pure (decide (leftValue < rightValue), afterRight)
    | .bool, .leU left right, scratch, state => do
        let (leftValue, afterLeft) ← left.evalU64 scratch state
        let (rightValue, afterRight) ← right.evalU64 scratch afterLeft
        pure (decide (leftValue ≤ rightValue), afterRight)
    | .bool, .not condition, scratch, state => do
        let (value, next) ← condition.evalU64 scratch state
        pure (!value, next)
    | .bool, .and left right, scratch, state => do
        let (leftValue, afterLeft) ← left.evalU64 scratch state
        if leftValue then right.evalU64 scratch afterLeft else pure (false, afterLeft)
    | .bool, .or left right, scratch, state => do
        let (leftValue, afterLeft) ← left.evalU64 scratch state
        if leftValue then pure (true, afterLeft) else right.evalU64 scratch afterLeft
    | .u64, .ite condition thenValue elseValue, scratch, state => do
        let (conditionValue, afterCondition) ← condition.evalU64 scratch state
        if conditionValue then
          thenValue.evalU64 scratch afterCondition
        else
          elseValue.evalU64 scratch afterCondition

end

def Stmt.evalU64 : Stmt → Nat → U64State → Option U64State
  | .skip, _, state => some state
  | .assign index value, scratch, state => do
      let (result, afterValue) ← value.evalU64 scratch state
      afterValue.set? index result
  | .seq first second, scratch, state => do
      let afterFirst ← first.evalU64 scratch state
      second.evalU64 scratch afterFirst
  | .ite condition thenStmt elseStmt, scratch, state => do
      let (result, afterCondition) ← condition.evalU64 scratch state
      if result then
        thenStmt.evalU64 scratch afterCondition
      else
        elseStmt.evalU64 scratch afterCondition

set_option maxHeartbeats 2000000 in
theorem Expr.eval_toState
    {type : ScalarType} (expression : Expr type) (scratch : Nat) (state : U64State) :
    expression.eval scratch state.toState =
      (expression.evalU64 scratch state).map fun result =>
        (result.1, result.2.toState) := by
  induction expression generalizing scratch state with
  | get index =>
      simp [Expr.eval, Expr.evalU64, Option.bind_map]
  | const | bconst =>
      rfl
  | bin operation left right leftProof rightProof =>
      cases operation <;>
        simp [Expr.eval, Expr.evalU64, leftProof, rightProof, Option.bind_map]
  | eq left right leftProof rightProof
  | ne left right leftProof rightProof
  | ltU left right leftProof rightProof
  | leU left right leftProof rightProof =>
      simp [Expr.eval, Expr.evalU64, leftProof, rightProof, Option.bind_map]
  | not condition proof =>
      simp [Expr.eval, Expr.evalU64, proof, Option.bind_map]
  | and left right leftProof rightProof
  | or left right leftProof rightProof =>
      rcases hLeft : left.evalU64 scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [Expr.eval, Expr.evalU64, leftProof, hLeft]
      · cases leftValue <;>
          simp [Expr.eval, Expr.evalU64, leftProof, rightProof, hLeft]
  | ite condition thenValue elseValue conditionProof thenProof elseProof =>
      rcases hCondition : condition.evalU64 scratch state with
        _ | ⟨conditionValue, afterCondition⟩
      · simp [Expr.eval, Expr.evalU64, conditionProof, hCondition]
      · cases conditionValue <;>
          simp [Expr.eval, Expr.evalU64, conditionProof, thenProof, elseProof,
            hCondition]

set_option maxHeartbeats 2000000 in
theorem Stmt.eval_toState (statement : Stmt) (scratch : Nat) (state : U64State) :
    statement.eval scratch state.toState =
      (statement.evalU64 scratch state).map U64State.toState := by
  induction statement generalizing state with
  | skip =>
      rfl
  | assign index value =>
      simp [Stmt.eval, Stmt.evalU64, Expr.eval_toState, Option.bind_map]
  | seq first second firstProof secondProof =>
      simp [Stmt.eval, Stmt.evalU64, firstProof, secondProof, Option.bind_map]
  | ite condition thenStmt elseStmt thenProof elseProof =>
      rcases hCondition : condition.evalU64 scratch state with
        _ | ⟨conditionValue, afterCondition⟩
      · simp [Stmt.eval, Stmt.evalU64, Expr.eval_toState, hCondition]
      · cases conditionValue <;>
          simp [Stmt.eval, Stmt.evalU64, Expr.eval_toState, thenProof, elseProof,
            hCondition]

end Project.ProofKit.ScalarTransition
