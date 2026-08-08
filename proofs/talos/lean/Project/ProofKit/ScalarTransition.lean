import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.ScalarTransition

open Wasm

inductive ScalarType where
  | u64
  | bool

abbrev ScalarType.denote : ScalarType → Type
  | .u64 => UInt64
  | .bool => Bool

@[simp]
def ScalarType.value : {type : ScalarType} → type.denote → Value
  | .u64, value => .i64 value
  | .bool, value => .i32 (if value then 1 else 0)

structure State where
  params : List Value
  locals : List Value
  deriving Repr

def State.ofLocals (locals : Locals) : State :=
  { params := locals.params, locals := locals.locals }

@[simp]
def State.toLocals (state : State) (values : List Value := []) : Locals :=
  { params := state.params, locals := state.locals, values }

def State.get (state : State) (index : Nat) : Option Value :=
  if index < state.params.length then state.params[index]?
  else if index < state.params.length + state.locals.length then
    state.locals[index - state.params.length]?
  else none

def State.set? (state : State) (index : Nat) (value : Value) : Option State :=
  if index < state.params.length then
    some { state with params := state.params.set index value }
  else if index < state.params.length + state.locals.length then
    some { state with locals := state.locals.set (index - state.params.length) value }
  else none

@[simp]
theorem State.toLocals_get (state : State) (values : List Value) (index : Nat) :
    (state.toLocals values).get index = state.get index := by
  rfl

@[simp]
theorem State.toLocals_set? (state : State) (values : List Value)
    (index : Nat) (value : Value) :
    (state.toLocals values).set? index value =
      (state.set? index value).map (fun next => next.toLocals values) := by
  by_cases hParam : index < state.params.length
  · simp [State.set?, State.toLocals, Wasm.Locals.set?, hParam]
  · by_cases hLocal : index < state.params.length + state.locals.length
    · simp [State.set?, State.toLocals, Wasm.Locals.set?, hParam, hLocal]
    · simp [State.set?, State.toLocals, Wasm.Locals.set?, hParam, hLocal]

theorem State.get_set?_same {state next : State} {index : Nat} {value : Value}
    (hSet : state.set? index value = some next) :
    next.get index = some value := by
  unfold State.set? at hSet
  split at hSet
  · simp only [Option.some.injEq] at hSet
    subst next
    simp [State.get, *]
  · split at hSet
    · simp only [Option.some.injEq] at hSet
      subst next
      have hLocal : index - state.params.length < state.locals.length := by omega
      simp [State.get, *]
    · contradiction

theorem State.get_set?_ne {state next : State} {writeIndex readIndex : Nat}
    {value : Value} (hNe : readIndex ≠ writeIndex)
    (hSet : state.set? writeIndex value = some next) :
    next.get readIndex = state.get readIndex := by
  unfold State.set? at hSet
  split at hSet
  · simp only [Option.some.injEq] at hSet
    subst next
    by_cases hRead : readIndex < state.params.length
    · simp only [State.get, List.length_set, if_pos hRead]
      rw [List.getElem?_set]
      simp [hNe.symm]
    · simp [State.get, hRead]
  · split at hSet
    · simp only [Option.some.injEq] at hSet
      subst next
      by_cases hReadParam : readIndex < state.params.length
      · simp [State.get, hReadParam]
      · by_cases hRead : readIndex < state.params.length + state.locals.length
        · have hLocalNe :
              readIndex - state.params.length ≠
                writeIndex - state.params.length := by omega
          simp only [State.get, List.length_set, hReadParam, hRead,
            if_false, if_true]
          rw [List.getElem?_set]
          simp [hLocalNe.symm]
        · simp [State.get, hReadParam, hRead]
    · contradiction

theorem localSet_spec
    {state next : State} {index : Nat} {value : Value}
    {values : List Value} {module_ : Module} {env : HostEnv α}
    {store : Store α} {rest : Program} {Q : Assertion α}
    (hSet : state.set? index value = some next)
    (hNext : wp module_ rest Q store (next.toLocals values) env) :
    wp module_ (.localSet index :: rest) Q store
      (state.toLocals (value :: values)) env := by
  unfold State.set? at hSet
  split at hSet
  · simp only [Option.some.injEq] at hSet
    subst next
    simpa [wp_simp, State.toLocals, Wasm.Locals.set?, *] using hNext
  · split at hSet
    · simp only [Option.some.injEq] at hSet
      subst next
      simpa [wp_simp, State.toLocals, Wasm.Locals.set?, *] using hNext
    · contradiction

theorem localGet_spec
    {state : State} {index : Nat} {value : Value}
    {values : List Value} {module_ : Module} {env : HostEnv α}
    {store : Store α} {rest : Program} {Q : Assertion α}
    (hGet : state.get index = some value)
    (hNext : wp module_ rest Q store (state.toLocals (value :: values)) env) :
    wp module_ (.localGet index :: rest) Q store (state.toLocals values) env := by
  rw [Wasm.wp_localGet_cons]
  change (match state.get index with
    | some found => wp module_ rest Q store (state.toLocals (found :: values)) env
    | none => Q (.Invalid "localGet index out of bounds"))
  rw [hGet]
  exact hNext

inductive U64Op where
  | add
  | sub
  | mul
  | divU
  | remU
  | bitAnd
  | bitOr
  | bitXor
  | shiftLeft
  | shiftRight
  deriving Repr, DecidableEq

def U64Op.apply : U64Op → UInt64 → UInt64 → UInt64
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .mul, left, right => left * right
  | .divU, left, right => if right = 0 then 0 else left / right
  | .remU, left, right => if right = 0 then left else left % right
  | .bitAnd, left, right => left &&& right
  | .bitOr, left, right => left ||| right
  | .bitXor, left, right => left ^^^ right
  | .shiftLeft, left, right => left <<< (right % 64)
  | .shiftRight, left, right => left >>> (right % 64)

def U64Op.instruction : U64Op → Instruction
  | .add => .addI64
  | .sub => .subI64
  | .mul => .mulI64
  | .divU => .divUI64
  | .remU => .remUI64
  | .bitAnd => .andI64
  | .bitOr => .orI64
  | .bitXor => .xorI64
  | .shiftLeft => .shlI64
  | .shiftRight => .shrUI64

inductive Expr : ScalarType → Type where
  | get (index : Nat) : Expr .u64
  | const (value : UInt64) : Expr .u64
  | bconst (value : Bool) : Expr .bool
  | bin (op : U64Op) (left right : Expr .u64) : Expr .u64
  | eq (left right : Expr .u64) : Expr .bool
  | ltU (left right : Expr .u64) : Expr .bool
  | leU (left right : Expr .u64) : Expr .bool
  | not (condition : Expr .bool) : Expr .bool
  | and (left right : Expr .bool) : Expr .bool
  | or (left right : Expr .bool) : Expr .bool
  | ite (condition : Expr .bool) (thenValue elseValue : Expr .u64) : Expr .u64
  deriving Repr

mutual

  def Expr.eval : {type : ScalarType} →
      Expr type → Nat → State → Option (type.denote × State)
    | .u64, .get index, _, state => do
        let .i64 value ← state.get index | none
        pure (value, state)
    | .u64, .const value, _, state => pure (value, state)
    | .bool, .bconst value, _, state => pure (value, state)
    | .u64, .bin op left right, scratch, state => do
        let childScratch := if op = .divU ∨ op = .remU then scratch + 2 else scratch
        let (leftValue, afterLeft) ← left.eval childScratch state
        let afterLeft ←
          if op = .divU ∨ op = .remU then
            afterLeft.set? scratch (.i64 leftValue)
          else some afterLeft
        let (rightValue, afterRight) ← right.eval childScratch afterLeft
        let afterRight ←
          if op = .divU ∨ op = .remU then
            afterRight.set? (scratch + 1) (.i64 rightValue)
          else some afterRight
        pure (op.apply leftValue rightValue, afterRight)
    | .bool, .eq left right, scratch, state => do
        let (leftValue, afterLeft) ← left.eval scratch state
        let (rightValue, afterRight) ← right.eval scratch afterLeft
        pure (leftValue == rightValue, afterRight)
    | .bool, .ltU left right, scratch, state => do
        let (leftValue, afterLeft) ← left.eval scratch state
        let (rightValue, afterRight) ← right.eval scratch afterLeft
        pure (decide (leftValue < rightValue), afterRight)
    | .bool, .leU left right, scratch, state => do
        let (leftValue, afterLeft) ← left.eval scratch state
        let (rightValue, afterRight) ← right.eval scratch afterLeft
        pure (decide (leftValue ≤ rightValue), afterRight)
    | .bool, .not condition, scratch, state => do
        let (value, next) ← condition.eval scratch state
        pure (!value, next)
    | .bool, .and left right, scratch, state => do
        let (leftValue, afterLeft) ← left.eval scratch state
        if leftValue then right.eval scratch afterLeft else pure (false, afterLeft)
    | .bool, .or left right, scratch, state => do
        let (leftValue, afterLeft) ← left.eval scratch state
        if leftValue then pure (true, afterLeft) else right.eval scratch afterLeft
    | .u64, .ite condition thenValue elseValue, scratch, state => do
        let (conditionValue, afterCondition) ← condition.eval scratch state
        if conditionValue then
          thenValue.eval scratch afterCondition
        else
          elseValue.eval scratch afterCondition

  def Expr.program : {type : ScalarType} → Expr type → Nat → Program
    | .u64, .get index, _ => [.localGet index]
    | .u64, .const value, _ => [.constI64 value]
    | .bool, .bconst value, _ => [.const (if value then 1 else 0)]
    | .u64, .bin op left right, scratch =>
        if op = .divU ∨ op = .remU then
          let childScratch := scratch + 2
          let zeroValue := if op = .divU then [.constI64 0] else [.localGet scratch]
          left.program childScratch ++ [.localSet scratch] ++
            right.program childScratch ++ [.localSet (scratch + 1)] ++
            [.localGet (scratch + 1), .constI64 0, .eqI64,
              .iff 0 1 zeroValue
                [.localGet scratch, .localGet (scratch + 1), op.instruction]]
        else
          left.program scratch ++ right.program scratch ++ [op.instruction]
    | .bool, .eq left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.eqI64]
    | .bool, .ltU left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.ltUI64]
    | .bool, .leU left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.leUI64]
    | .bool, .not condition, scratch => condition.program scratch ++ [.eqz]
    | .bool, .and left right, scratch =>
        left.program scratch ++ [.iff 0 1 (right.program scratch) [.const 0]]
    | .bool, .or left right, scratch =>
        left.program scratch ++ [.iff 0 1 [.const 1] (right.program scratch)]
    | .u64, .ite condition thenValue elseValue, scratch =>
        condition.program scratch ++
          [.iff 0 1 (thenValue.program scratch) (elseValue.program scratch)]

end

inductive Stmt where
  | skip
  | assign (index : Nat) (value : Expr .u64)
  | seq (first second : Stmt)
  | ite (condition : Expr .bool) (thenStmt elseStmt : Stmt)
  deriving Repr

def Stmt.eval : Stmt → Nat → State → Option State
  | .skip, _, state => some state
  | .assign index value, scratch, state => do
      let (result, afterValue) ← value.eval scratch state
      afterValue.set? index (.i64 result)
  | .seq first second, scratch, state => do
      let afterFirst ← first.eval scratch state
      second.eval scratch afterFirst
  | .ite condition thenStmt elseStmt, scratch, state => do
      let (result, afterCondition) ← condition.eval scratch state
      if result then
        thenStmt.eval scratch afterCondition
      else
        elseStmt.eval scratch afterCondition

def Stmt.program : Stmt → Nat → Program
  | .skip, _ => []
  | .assign index value, scratch => value.program scratch ++ [.localSet index]
  | .seq first second, scratch => first.program scratch ++ second.program scratch
  | .ite condition thenStmt elseStmt, scratch =>
      condition.program scratch ++
        [.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch)]

def whileProgram (scratch : Nat) (condition : Expr .bool) (body : Stmt) : Program :=
  [.block 0 0 [.loop 0 0
    (condition.program scratch ++ [.eqz, .br_if 1] ++
      body.program scratch ++ [.br 0])]]

theorem Expr.eval_preserves_below
    {type : ScalarType} (expression : Expr type) (scratch : Nat)
    (state next : State) (result : type.denote) (index : Nat)
    (hEval : expression.eval scratch state = some (result, next))
    (hIndex : index < scratch) :
    next.get index = state.get index := by
  induction expression generalizing scratch state next index with
  | get localIndex =>
      unfold Expr.eval at hEval
      cases hGet : state.get localIndex with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case i64 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            rfl
  | const value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      rfl
  | bconst value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      rfl
  | bin op left right leftPreserves rightPreserves =>
      cases op with
      | add | sub | mul | bitAnd | bitOr | bitXor | shiftLeft | shiftRight =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact (rightPreserves scratch afterLeft afterRight rightValue index
            hRight hIndex).trans
              (leftPreserves scratch state afterLeft leftValue index hLeft hIndex)
      | divU | remU =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hSetLeft, hRight] at hEval
          rcases hSetRight : afterRight.set? (scratch + 1) (.i64 rightValue) with _ | savedRight
          · simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          calc
            savedRight.get index = afterRight.get index :=
              State.get_set?_ne (by omega) hSetRight
            _ = savedLeft.get index :=
              rightPreserves (scratch + 2) savedLeft afterRight rightValue
                index hRight (by omega)
            _ = afterLeft.get index := State.get_set?_ne (by omega) hSetLeft
            _ = state.get index :=
              leftPreserves (scratch + 2) state afterLeft leftValue index
                hLeft (by omega)
  | eq left right leftPreserves rightPreserves
  | ltU left right leftPreserves rightPreserves
  | leU left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact (rightPreserves scratch afterLeft afterRight rightValue index
        hRight hIndex).trans
          (leftPreserves scratch state afterLeft leftValue index hLeft hIndex)
  | not condition conditionPreserves =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval scratch state with _ | ⟨value, afterCondition⟩
      · simp [hCondition] at hEval
      have hPreserves := conditionPreserves scratch state afterCondition value
        index hCondition hIndex
      simp [hCondition] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hPreserves
  | and left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact leftPreserves scratch state afterLeft false index hLeft hIndex
      · rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (rightPreserves scratch afterLeft afterRight rightValue index
          hRight hIndex).trans
            (leftPreserves scratch state afterLeft true index hLeft hIndex)
  | or left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (rightPreserves scratch afterLeft afterRight rightValue index
          hRight hIndex).trans
            (leftPreserves scratch state afterLeft false index hLeft hIndex)
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact leftPreserves scratch state afterLeft true index hLeft hIndex
  | ite condition thenValue elseValue conditionPreserves thenPreserves elsePreserves =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (elsePreserves scratch afterCondition afterValue value index
          hElse hIndex).trans
            (conditionPreserves scratch state afterCondition false index
              hCondition hIndex)
      · rcases hThen : thenValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (thenPreserves scratch afterCondition afterValue value index
          hThen hIndex).trans
            (conditionPreserves scratch state afterCondition true index
              hCondition hIndex)

set_option maxHeartbeats 1000000 in
theorem Expr.program_spec
    {type : ScalarType} (expression : Expr type) (scratch : Nat)
    (state next : State) (result : type.denote) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α)
    (rest : Program) (Q : Assertion α)
    (hEval : expression.eval scratch state = some (result, next))
    (hNext : wp module_ rest Q store
      (next.toLocals (type.value result :: values)) env) :
    wp module_ (expression.program scratch ++ rest) Q store
      (state.toLocals values) env := by
  induction expression generalizing scratch state next values rest Q with
  | get index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case i64 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [Expr.program, List.cons_append, List.nil_append,
              Wasm.wp_localGet_cons, State.toLocals_get, hGet]
            exact hNext
  | const value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      simp only [Expr.program, List.cons_append, List.nil_append,
        Wasm.wp_constI64_cons]
      exact hNext
  | bconst value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      cases value <;>
        simpa [Expr.program, ScalarType.value, wp_simp] using hNext
  | bin op left right leftSpec rightSpec =>
      cases op with
      | add =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.program, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
      | sub =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.program, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
      | mul =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.program, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
      | divU =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.program, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hSetLeft, hRight] at hEval
          rcases hSetRight : afterRight.set? (scratch + 1) (.i64 rightValue) with _ | savedRight
          · simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch + 2) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          simp only [ScalarType.value]
          apply localSet_spec hSetLeft
          apply rightSpec (scratch := scratch + 2) (state := savedLeft)
            (next := afterRight) (result := rightValue) (values := values)
            (rest := _) (Q := _) hRight
          simp only [ScalarType.value]
          apply localSet_spec hSetRight
          have hRightSlot : savedRight.get (scratch + 1) = some (.i64 rightValue) :=
            State.get_set?_same hSetRight
          have hLeftSlot : savedRight.get scratch = some (.i64 leftValue) := by
            calc
              savedRight.get scratch = afterRight.get scratch :=
                State.get_set?_ne (by omega) hSetRight
              _ = savedLeft.get scratch :=
                Expr.eval_preserves_below right (scratch + 2) savedLeft
                  afterRight rightValue scratch hRight (by omega)
              _ = some (.i64 leftValue) := State.get_set?_same hSetLeft
          simp only [Wasm.wp_localGet_cons, State.toLocals_get, hRightSlot,
            Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
          refine Wasm.wp_iff_cons rfl ?_
          by_cases hZero : rightValue = 0
          · rw [if_pos (by simp [hZero])]
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
          · rw [if_neg (by simp [hZero])]
            apply localGet_spec hLeftSlot
            apply localGet_spec hRightSlot
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
      | remU =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.program, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hSetLeft, hRight] at hEval
          rcases hSetRight : afterRight.set? (scratch + 1) (.i64 rightValue) with _ | savedRight
          · simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch + 2) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          simp only [ScalarType.value]
          apply localSet_spec hSetLeft
          apply rightSpec (scratch := scratch + 2) (state := savedLeft)
            (next := afterRight) (result := rightValue) (values := values)
            (rest := _) (Q := _) hRight
          simp only [ScalarType.value]
          apply localSet_spec hSetRight
          have hRightSlot : savedRight.get (scratch + 1) = some (.i64 rightValue) :=
            State.get_set?_same hSetRight
          have hLeftSlot : savedRight.get scratch = some (.i64 leftValue) := by
            calc
              savedRight.get scratch = afterRight.get scratch :=
                State.get_set?_ne (by omega) hSetRight
              _ = savedLeft.get scratch :=
                Expr.eval_preserves_below right (scratch + 2) savedLeft
                  afterRight rightValue scratch hRight (by omega)
              _ = some (.i64 leftValue) := State.get_set?_same hSetLeft
          simp only [Wasm.wp_localGet_cons, State.toLocals_get, hRightSlot,
            Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
          refine Wasm.wp_iff_cons rfl ?_
          by_cases hZero : rightValue = 0
          · rw [if_pos (by simp [hZero])]
            apply localGet_spec hLeftSlot
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
          · rw [if_neg (by simp [hZero])]
            apply localGet_spec hLeftSlot
            apply localGet_spec hRightSlot
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
      | bitAnd | bitOr | bitXor | shiftLeft | shiftRight =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.program, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
  | eq left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.program, ScalarType.value, wp_simp] using hNext
  | ltU left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.program, ScalarType.value, wp_simp] using hNext
  | leU left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.program, ScalarType.value, wp_simp] using hNext
  | not condition conditionSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hCondition : condition.eval scratch state with _ | ⟨value, afterCondition⟩
      · simp [hCondition] at hEval
      cases value with
      | false =>
          simp [hCondition] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply conditionSpec (scratch := scratch) (state := state)
            (next := afterCondition) (result := false) (values := values)
            (rest := _) (Q := _) hCondition
          simpa [Expr.program, ScalarType.value, wp_simp] using hNext
      | true =>
          simp [hCondition] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply conditionSpec (scratch := scratch) (state := state)
            (next := afterCondition) (result := true) (values := values)
            (rest := _) (Q := _) hCondition
          simpa [Expr.program, ScalarType.value, wp_simp] using hNext
  | and left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := false) (values := values)
          (rest := _) (Q := _) hLeft
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        simpa [wp_simp, ScalarType.value] using hNext
      · rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := true) (values := values)
          (rest := _) (Q := _) hLeft
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        rw [← List.append_nil (right.program scratch)]
        apply rightSpec (scratch := scratch) (state := afterLeft)
          (next := afterRight) (result := rightValue) (values := values)
          (rest := []) (Q := _) hRight
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
  | or left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := false) (values := values)
          (rest := _) (Q := _) hLeft
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        rw [← List.append_nil (right.program scratch)]
        apply rightSpec (scratch := scratch) (state := afterLeft)
          (next := afterRight) (result := rightValue) (values := values)
          (rest := []) (Q := _) hRight
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := true) (values := values)
          (rest := _) (Q := _) hLeft
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        simpa [wp_simp, ScalarType.value] using hNext
  | ite condition thenValue elseValue conditionSpec thenSpec elseSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hCondition : condition.eval scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := false) (values := values)
          (rest := _) (Q := _) hCondition
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        rw [← List.append_nil (elseValue.program scratch)]
        apply elseSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hElse
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · rcases hThen : thenValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := true) (values := values)
          (rest := _) (Q := _) hCondition
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        rw [← List.append_nil (thenValue.program scratch)]
        apply thenSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hThen
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext

set_option maxHeartbeats 1000000 in
theorem Stmt.program_spec
    (statement : Stmt) (scratch : Nat) (state next : State)
    (values : List Value) (module_ : Module) (env : HostEnv α)
    (store : Store α) (rest : Program) (Q : Assertion α)
    (hEval : statement.eval scratch state = some next)
    (hNext : wp module_ rest Q store (next.toLocals values) env) :
    wp module_ (statement.program scratch ++ rest) Q store
      (state.toLocals values) env := by
  induction statement generalizing state next values rest Q with
  | skip =>
      obtain rfl := Option.some.inj hEval
      simpa [Stmt.program] using hNext
  | assign index expression =>
      simp only [Stmt.eval] at hEval
      rcases hExpression : expression.eval scratch state with
        _ | ⟨result, afterExpression⟩
      · simp [hExpression] at hEval
      rcases hSet : afterExpression.set? index (.i64 result) with _ | afterSet
      · simp [hExpression, hSet] at hEval
      simp [hExpression, hSet] at hEval
      subst next
      simp only [Stmt.program, List.append_assoc]
      apply Expr.program_spec expression scratch state afterExpression result values
        module_ env store (.localSet index :: rest) Q hExpression
      apply localSet_spec hSet
      exact hNext
  | seq first second firstSpec secondSpec =>
      simp only [Stmt.eval] at hEval
      rcases hFirst : first.eval scratch state with _ | afterFirst
      · simp [hFirst] at hEval
      have hSecond : second.eval scratch afterFirst = some next := by
        simpa [hFirst] using hEval
      simp only [Stmt.program, List.append_assoc]
      apply firstSpec (state := state) (next := afterFirst) (values := values)
        (rest := second.program scratch ++ rest) (Q := Q) hFirst
      exact secondSpec (state := afterFirst) (next := next) (values := values)
        (rest := rest) (Q := Q) hSecond hNext
  | ite condition thenStmt elseStmt thenSpec elseSpec =>
      simp only [Stmt.eval] at hEval
      rcases hCondition : condition.eval scratch state with
        _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      simp only [Stmt.program, List.append_assoc]
      cases conditionValue
      · have hElse : elseStmt.eval scratch afterCondition = some next := by
          simpa [hCondition] using hEval
        apply Expr.program_spec condition scratch state afterCondition false values
          module_ env store
          (.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch) :: rest)
          Q hCondition
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        rw [← List.append_nil (elseStmt.program scratch)]
        apply elseSpec (state := afterCondition) (next := next) (values := values)
          (rest := []) (Q := _) hElse
        simpa [wp_simp, State.toLocals] using hNext
      · have hThen : thenStmt.eval scratch afterCondition = some next := by
          simpa [hCondition] using hEval
        apply Expr.program_spec condition scratch state afterCondition true values
          module_ env store
          (.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch) :: rest)
          Q hCondition
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        rw [← List.append_nil (thenStmt.program scratch)]
        apply thenSpec (state := afterCondition) (next := next) (values := values)
          (rest := []) (Q := _) hThen
        simpa [wp_simp, State.toLocals] using hNext

set_option maxHeartbeats 1000000 in
theorem whileProgram_spec
    (condition : Expr .bool) (body : Stmt) (scratch : Nat)
    (initial : State) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α)
    (rest : Program) (Q : Assertion α)
    (Inv : State → Prop) (measure : State → Nat)
    (hInit : Inv initial)
    (hStep : ∀ current, Inv current →
      ∃ result afterCondition,
        condition.eval scratch current = some (result, afterCondition) ∧
        if result then
          ∃ afterBody,
            body.eval scratch afterCondition = some afterBody ∧
            Inv afterBody ∧ measure afterBody < measure current
        else
          wp module_ rest Q store (afterCondition.toLocals values) env) :
    wp module_ (whileProgram scratch condition body ++ rest) Q store
      (initial.toLocals values) env := by
  let loopInv : AssertionF α := fun currentStore locals =>
    currentStore = store ∧
      ∃ current, locals = current.toLocals values ∧ Inv current
  let loopMeasure : Store α → Locals → Nat := fun _ locals =>
    measure (State.ofLocals locals)
  simp only [whileProgram, List.singleton_append]
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons (Inv := loopInv) (μ := loopMeasure)
  · exact ⟨rfl, initial, rfl, hInit⟩
  · intro currentStore locals hInv
    rcases hInv with ⟨hStore, current, hLocals, hCurrent⟩
    subst currentStore
    subst locals
    rcases hStep current hCurrent with
      ⟨result, afterCondition, hCondition, hResult⟩
    simp only [List.append_assoc]
    refine Expr.program_spec (expression := condition) (scratch := scratch)
      (state := current) (next := afterCondition) (result := result)
      (values := values) (module_ := module_) (env := env) (store := store)
      (rest := [Instruction.eqz, Instruction.br_if 1] ++
        (body.program scratch ++ [Instruction.br 0]))
      (Q := _) hCondition ?_
    cases result
    · simpa [wp_simp, State.toLocals, ScalarType.value] using hResult
    · rcases hResult with ⟨afterBody, hBody, hBodyInv, hDecrease⟩
      simp only [List.cons_append, List.nil_append, Wasm.wp_eqz_cons,
        Wasm.wp_br_if_cons, ScalarType.value]
      apply Stmt.program_spec body scratch afterCondition afterBody values
        module_ env store [.br 0] _ hBody
      simp only [Wasm.wp_br_cons]
      constructor
      · exact ⟨rfl, afterBody, rfl, hBodyInv⟩
      · simpa [loopMeasure, State.ofLocals, State.toLocals] using hDecrease

end Project.ProofKit.ScalarTransition
