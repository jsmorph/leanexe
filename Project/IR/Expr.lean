import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Tactic
import Project.TalosCompat

/-!
IR expressions over 64-bit words, Booleans, and binary64 and binary32 floats, the IR state of
locals, and the expression rule `Expr.program_spec`: evaluating an expression
with `Expr.eval` predicts what its compiled code pushes and which locals it
changes.
-/

namespace Project.IR

open Wasm

/-- The types of IR values.  A float value is its bit pattern. -/
inductive ScalarType where
  | u64
  | bool
  | f64
  | f32
  deriving Repr, DecidableEq

abbrev ScalarType.denote : ScalarType → Type
  | .u64 => UInt64
  | .bool => Bool
  | .f64 => UInt64
  | .f32 => UInt32

@[simp]
def ScalarType.value : {type : ScalarType} → type.denote → Value
  | .u64, value => .i64 value
  | .bool, value => .i32 (if value then 1 else 0)
  | .f64, value => .f64 value
  | .f32, value => .f32 value

/-- The value that a 64-bit word read from memory becomes in a local of this
type: an `f64` keeps the word's bits, and an `f32` its low 32 bits. -/
@[simp]
def ScalarType.ofBits : ScalarType → UInt64 → Value
  | .u64, word => .i64 word
  | .bool, word => .i64 word
  | .f64, word => .f64 word
  | .f32, word => .f32 word.toUInt32

/-- The instructions that turn a loaded 64-bit word into a value of this type. -/
def ScalarType.fromBits : ScalarType → Program
  | .u64 => []
  | .bool => []
  | .f64 => [.f64ReinterpretI64]
  | .f32 => [.wrapI64, .f32ReinterpretI32]

def ScalarType.valueType : ScalarType → ValueType
  | .u64 => .i64
  | .bool => .i32
  | .f64 => .f64
  | .f32 => .f32

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

/-- Binary64 arithmetic in the WebAssembly deterministic profile. -/
inductive F64Op where
  | add
  | sub
  | mul
  | div
  deriving Repr, DecidableEq

def F64Op.apply : F64Op → UInt64 → UInt64 → UInt64
  | .add, left, right => IEEE64.add left right
  | .sub, left, right => IEEE64.sub left right
  | .mul, left, right => IEEE64.mul left right
  | .div, left, right => IEEE64.div left right

def F64Op.instruction : F64Op → Instruction
  | .add => .f64Add
  | .sub => .f64Sub
  | .mul => .f64Mul
  | .div => .f64Div

inductive F64UnOp where
  | sqrt
  | abs
  deriving Repr, DecidableEq

def F64UnOp.apply : F64UnOp → UInt64 → UInt64
  | .sqrt, value => IEEE64.sqrt value
  | .abs, value => IEEE64.abs value

def F64UnOp.instruction : F64UnOp → Instruction
  | .sqrt => .f64Sqrt
  | .abs => .f64Abs

/-- Binary32 arithmetic in the WebAssembly deterministic profile. -/
inductive F32Op where
  | add
  | sub
  | mul
  | div
  deriving Repr, DecidableEq

def F32Op.apply : F32Op → UInt32 → UInt32 → UInt32
  | .add, left, right => IEEE32.add left right
  | .sub, left, right => IEEE32.sub left right
  | .mul, left, right => IEEE32.mul left right
  | .div, left, right => IEEE32.div left right

def F32Op.instruction : F32Op → Instruction
  | .add => .f32Add
  | .sub => .f32Sub
  | .mul => .f32Mul
  | .div => .f32Div

inductive F32UnOp where
  | sqrt
  deriving Repr, DecidableEq

def F32UnOp.apply : F32UnOp → UInt32 → UInt32
  | .sqrt, value => IEEE32.sqrt value

def F32UnOp.instruction : F32UnOp → Instruction
  | .sqrt => .f32Sqrt

inductive Expr : ScalarType → Type where
  | get (index : Nat) : Expr .u64
  | const (value : UInt64) : Expr .u64
  | bconst (value : Bool) : Expr .bool
  | bin (op : U64Op) (left right : Expr .u64) : Expr .u64
  | eq (left right : Expr .u64) : Expr .bool
  | ne (left right : Expr .u64) : Expr .bool
  | ltU (left right : Expr .u64) : Expr .bool
  | leU (left right : Expr .u64) : Expr .bool
  | not (condition : Expr .bool) : Expr .bool
  | and (left right : Expr .bool) : Expr .bool
  | or (left right : Expr .bool) : Expr .bool
  | ite (condition : Expr .bool) (thenValue elseValue : Expr .u64) : Expr .u64
  | getF (index : Nat) : Expr .f64
  | binF (op : F64Op) (left right : Expr .f64) : Expr .f64
  | unF (op : F64UnOp) (operand : Expr .f64) : Expr .f64
  | constF (bits : UInt64) : Expr .f64
  | iteF (condition : Expr .bool) (thenValue elseValue : Expr .f64) : Expr .f64
  | eqF (left right : Expr .f64) : Expr .bool
  | ltF (left right : Expr .f64) : Expr .bool
  | leF (left right : Expr .f64) : Expr .bool
  /-- The float nearest the unsigned word, as `f64.convert_i64_u`. -/
  | convertU (operand : Expr .u64) : Expr .f64
  /-- The float truncated toward zero and clamped to an unsigned word, as
  `i64.trunc_sat_f64_u`. -/
  | truncSatU (operand : Expr .f64) : Expr .u64
  /-- The float whose bit pattern is the word, as `f64.reinterpret_i64`. -/
  | ofBits (operand : Expr .u64) : Expr .f64
  /-- The bit pattern of the float, as `i64.reinterpret_f64`. -/
  | toBits (operand : Expr .f64) : Expr .u64
  /-- Element `position` of the array whose pointer local `array` holds, or 0 when
  `position` is not below the array's length.  Scratch local `scratch` holds the
  position. -/
  | read (array : Nat) (position : Expr .u64) : Expr .u64
  | getF32 (index : Nat) : Expr .f32
  | binF32 (op : F32Op) (left right : Expr .f32) : Expr .f32
  | unF32 (op : F32UnOp) (operand : Expr .f32) : Expr .f32
  deriving Repr

/-- Element `k` of the array whose pointer local `array` holds, or 0 when `k` is
not below the array's length word; `none` when a load would leave memory. -/
def Expr.readValue (mem : Mem) (array : Nat) (k : UInt64) (state : State) :
    Option (UInt64 × State) := do
  let .i64 ptr ← state.get array | none
  if ptr.toUInt32.toNat + 8 ≤ mem.pages * 65536 then
    if k < mem.read64 ptr.toUInt32 then
      if (ptr + (k + 1) * 8).toUInt32.toNat + 8 ≤ mem.pages * 65536 then
        pure (mem.read64 (ptr + (k + 1) * 8).toUInt32, state)
      else none
    else pure (0, state)
  else none

mutual

  def Expr.eval : {type : ScalarType} →
      Expr type → Mem → Nat → State → Option (type.denote × State)
    | .u64, .get index, _, _, state => do
        let .i64 value ← state.get index | none
        pure (value, state)
    | .u64, .const value, _, _, state => pure (value, state)
    | .bool, .bconst value, _, _, state => pure (value, state)
    | .f64, .getF index, _, _, state => do
        let .f64 value ← state.get index | none
        pure (value, state)
    | .f64, .binF op left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (op.apply leftValue rightValue, afterRight)
    | .f64, .unF op operand, mem, scratch, state => do
        let (value, next) ← operand.eval mem scratch state
        pure (op.apply value, next)
    | .f32, .getF32 index, _, _, state => do
        let .f32 value ← state.get index | none
        pure (value, state)
    | .f32, .binF32 op left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (op.apply leftValue rightValue, afterRight)
    | .f32, .unF32 op operand, mem, scratch, state => do
        let (value, next) ← operand.eval mem scratch state
        pure (op.apply value, next)
    | .f64, .convertU operand, mem, scratch, state => do
        let (value, next) ← operand.eval mem scratch state
        pure (IEEE64.convertI64U value, next)
    | .u64, .truncSatU operand, mem, scratch, state => do
        let (value, next) ← operand.eval mem scratch state
        pure (IEEE64.truncSatI64U value, next)
    | .f64, .ofBits operand, mem, scratch, state => do
        let (value, next) ← operand.eval mem scratch state
        pure (value, next)
    | .u64, .toBits operand, mem, scratch, state => do
        let (value, next) ← operand.eval mem scratch state
        pure (value, next)
    | .u64, .read array position, mem, scratch, state => do
        let (k, afterPosition) ← position.eval mem (scratch + 1) state
        Expr.readValue mem array k (← afterPosition.set? scratch (.i64 k))
    | .f64, .constF bits, _, _, state => pure (bits, state)
    | .f64, .iteF condition thenValue elseValue, mem, scratch, state => do
        let (conditionValue, afterCondition) ← condition.eval mem scratch state
        if conditionValue then
          thenValue.eval mem scratch afterCondition
        else
          elseValue.eval mem scratch afterCondition
    | .bool, .eqF left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (IEEE64.eq leftValue rightValue, afterRight)
    | .bool, .ltF left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (IEEE64.lt leftValue rightValue, afterRight)
    | .bool, .leF left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (IEEE64.le leftValue rightValue, afterRight)
    | .u64, .bin op left right, mem, scratch, state => do
        let childScratch := if op = .divU ∨ op = .remU then scratch + 2 else scratch
        let (leftValue, afterLeft) ← left.eval mem childScratch state
        let afterLeft ←
          if op = .divU ∨ op = .remU then
            afterLeft.set? scratch (.i64 leftValue)
          else some afterLeft
        let (rightValue, afterRight) ← right.eval mem childScratch afterLeft
        let afterRight ←
          if op = .divU ∨ op = .remU then
            afterRight.set? (scratch + 1) (.i64 rightValue)
          else some afterRight
        pure (op.apply leftValue rightValue, afterRight)
    | .bool, .eq left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (leftValue == rightValue, afterRight)
    | .bool, .ne left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (leftValue != rightValue, afterRight)
    | .bool, .ltU left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (decide (leftValue < rightValue), afterRight)
    | .bool, .leU left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        let (rightValue, afterRight) ← right.eval mem scratch afterLeft
        pure (decide (leftValue ≤ rightValue), afterRight)
    | .bool, .not condition, mem, scratch, state => do
        let (value, next) ← condition.eval mem scratch state
        pure (!value, next)
    | .bool, .and left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        if leftValue then right.eval mem scratch afterLeft else pure (false, afterLeft)
    | .bool, .or left right, mem, scratch, state => do
        let (leftValue, afterLeft) ← left.eval mem scratch state
        if leftValue then pure (true, afterLeft) else right.eval mem scratch afterLeft
    | .u64, .ite condition thenValue elseValue, mem, scratch, state => do
        let (conditionValue, afterCondition) ← condition.eval mem scratch state
        if conditionValue then
          thenValue.eval mem scratch afterCondition
        else
          elseValue.eval mem scratch afterCondition

  def Expr.program : {type : ScalarType} → Expr type → Nat → Program
    | .u64, .get index, _ => [.localGet index]
    | .u64, .const value, _ => [.constI64 value]
    | .f64, .getF index, _ => [.localGet index]
    | .f64, .binF op left right, scratch =>
        left.program scratch ++ right.program scratch ++ [op.instruction]
    | .f64, .unF op operand, scratch => operand.program scratch ++ [op.instruction]
    | .f32, .getF32 index, _ => [.localGet index]
    | .f32, .binF32 op left right, scratch =>
        left.program scratch ++ right.program scratch ++ [op.instruction]
    | .f32, .unF32 op operand, scratch => operand.program scratch ++ [op.instruction]
    | .f64, .convertU operand, scratch => operand.program scratch ++ [.f64ConvertI64U]
    | .u64, .truncSatU operand, scratch => operand.program scratch ++ [.i64TruncSatF64U]
    | .f64, .ofBits operand, scratch => operand.program scratch ++ [.f64ReinterpretI64]
    | .u64, .toBits operand, scratch => operand.program scratch ++ [.i64ReinterpretF64]
    | .u64, .read array position, scratch =>
        position.program (scratch + 1) ++
          [.localSet scratch, .localGet scratch, .localGet array, .wrapI64, .load64 0, .ltUI64,
            .iff 0 1 [.localGet array, .localGet scratch, .constI64 1, .addI64, .constI64 8,
              .mulI64, .addI64, .wrapI64, .load64 0] [.constI64 0] [] [.i64]]
    | .f64, .constF bits, _ => [.f64Const bits]
    | .f64, .iteF condition thenValue elseValue, scratch =>
        condition.program scratch ++
          [.iff 0 1 (thenValue.program scratch) (elseValue.program scratch) [] [.f64]]
    | .bool, .eqF left right, scratch => left.program scratch ++ right.program scratch ++ [.f64Eq]
    | .bool, .ltF left right, scratch => left.program scratch ++ right.program scratch ++ [.f64Lt]
    | .bool, .leF left right, scratch => left.program scratch ++ right.program scratch ++ [.f64Le]
    | .bool, .bconst value, _ => [.const (if value then 1 else 0)]
    | .u64, .bin op left right, scratch =>
        if op = .divU ∨ op = .remU then
          let childScratch := scratch + 2
          let zeroValue := if op = .divU then [.constI64 0] else [.localGet scratch]
          left.program childScratch ++ [.localSet scratch] ++
            right.program childScratch ++ [.localSet (scratch + 1)] ++
            [.localGet (scratch + 1), .constI64 0, .eqI64,
              .iff 0 1 zeroValue
                [.localGet scratch, .localGet (scratch + 1), op.instruction] [] [.i64]]
        else
          left.program scratch ++ right.program scratch ++ [op.instruction]
    | .bool, .eq left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.eqI64]
    | .bool, .ne left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.neI64]
    | .bool, .ltU left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.ltUI64]
    | .bool, .leU left right, scratch =>
        left.program scratch ++ right.program scratch ++ [.leUI64]
    | .bool, .not condition, scratch => condition.program scratch ++ [.eqz]
    | .bool, .and left right, scratch =>
        left.program scratch ++ [.iff 0 1 (right.program scratch) [.const 0] [] [.i32]]
    | .bool, .or left right, scratch =>
        left.program scratch ++ [.iff 0 1 [.const 1] (right.program scratch) [] [.i32]]
    | .u64, .ite condition thenValue elseValue, scratch =>
        condition.program scratch ++
          [.iff 0 1 (thenValue.program scratch) (elseValue.program scratch) [] [.i64]]

end

def Expr.scratchWidth : {type : ScalarType} → Expr type → Nat
  | _, .get _ | _, .const _ | _, .bconst _ | _, .getF _ | _, .constF _ | _, .getF32 _ => 0
  | _, .binF _ left right | _, .binF32 _ left right => max left.scratchWidth right.scratchWidth
  | _, .unF _ operand | _, .convertU operand | _, .truncSatU operand | _, .ofBits operand
  | _, .toBits operand | _, .unF32 _ operand =>
      operand.scratchWidth
  | _, .eqF left right | _, .ltF left right | _, .leF left right =>
      max left.scratchWidth right.scratchWidth
  | _, .iteF condition thenValue elseValue =>
      max condition.scratchWidth (max thenValue.scratchWidth elseValue.scratchWidth)
  | _, .bin operation left right =>
      let childWidth := max left.scratchWidth right.scratchWidth
      if operation = .divU ∨ operation = .remU then childWidth + 2 else childWidth
  | _, .eq left right | _, .ne left right | _, .ltU left right | _, .leU left right
  | _, .and left right | _, .or left right =>
      max left.scratchWidth right.scratchWidth
  | _, .not condition => condition.scratchWidth
  | _, .read _ position => position.scratchWidth + 1
  | _, .ite condition thenValue elseValue =>
      max condition.scratchWidth (max thenValue.scratchWidth elseValue.scratchWidth)

/-- Binding the result of a conditional binds each branch; evaluation of
`iteF` and `ite` produces this shape. -/
theorem ite_bind {α β : Type} {c : Prop} [Decidable c] (a b : Option α) (f : α → Option β) :
    (if c then a else b).bind f = if c then a.bind f else b.bind f := by
  split <;> rfl

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

/-- `wrap_toUInt32` with the modulus as `simp` writes it. -/
theorem ofNat_mod_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 4294967296) = a.toUInt32 :=
  wrap_toUInt32 a

/-- A read changes the state only by evaluating its position and saving the
position in its scratch local. -/
theorem Expr.read_state {mem : Mem} {array scratch : Nat} {position : Expr .u64}
    {state next : State} {result : UInt64}
    (hEval : (Expr.read array position).eval mem scratch state = some (result, next)) :
    ∃ k afterPosition, position.eval mem (scratch + 1) state = some (k, afterPosition) ∧
      afterPosition.set? scratch (.i64 k) = some next := by
  simp only [Expr.eval] at hEval
  rcases hPosition : position.eval mem (scratch + 1) state with _ | ⟨k, afterPosition⟩
  · simp [hPosition] at hEval
  rcases hSet : afterPosition.set? scratch (.i64 k) with _ | saved
  · simp [hPosition, hSet] at hEval
  refine ⟨k, afterPosition, rfl, ?_⟩
  simp only [hPosition, hSet, Option.bind_eq_bind, Option.bind_some, Expr.readValue] at hEval
  rcases hPtr : saved.get array with _ | v
  · simp [hPtr] at hEval
  cases v <;> simp only [hPtr, Option.bind_some, reduceCtorEq] at hEval
  split_ifs at hEval <;> simp_all

theorem Expr.eval_preserves_below
    {type : ScalarType} (expression : Expr type) (mem : Mem) (scratch : Nat)
    (state next : State) (result : type.denote) (index : Nat)
    (hEval : expression.eval mem scratch state = some (result, next))
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
  | const value | constF value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      rfl
  | bconst value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      rfl
  | bin op left right leftPreserves rightPreserves =>
      cases op with
      | add | sub | mul | bitAnd | bitOr | bitXor | shiftLeft | shiftRight =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact (rightPreserves scratch afterLeft afterRight rightValue index
            hRight hIndex).trans
              (leftPreserves scratch state afterLeft leftValue index hLeft hIndex)
      | divU | remU =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval mem (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval mem (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
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
  | read array position positionPreserves =>
      obtain ⟨k, afterPosition, hPosition, hSet⟩ := Expr.read_state hEval
      calc
        next.get index = afterPosition.get index := State.get_set?_ne (by omega) hSet
        _ = state.get index :=
          positionPreserves (scratch + 1) state afterPosition k index hPosition (by omega)
  | eq left right leftPreserves rightPreserves
  | ne left right leftPreserves rightPreserves
  | ltU left right leftPreserves rightPreserves
  | leU left right leftPreserves rightPreserves
  | eqF left right leftPreserves rightPreserves
  | ltF left right leftPreserves rightPreserves
  | leF left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact (rightPreserves scratch afterLeft afterRight rightValue index
        hRight hIndex).trans
          (leftPreserves scratch state afterLeft leftValue index hLeft hIndex)
  | not condition conditionPreserves =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval mem scratch state with _ | ⟨value, afterCondition⟩
      · simp [hCondition] at hEval
      have hPreserves := conditionPreserves scratch state afterCondition value
        index hCondition hIndex
      simp [hCondition] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hPreserves
  | and left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact leftPreserves scratch state afterLeft false index hLeft hIndex
      · rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (rightPreserves scratch afterLeft afterRight rightValue index
          hRight hIndex).trans
            (leftPreserves scratch state afterLeft true index hLeft hIndex)
  | or left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
      rcases hCondition : condition.eval mem scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (elsePreserves scratch afterCondition afterValue value index
          hElse hIndex).trans
            (conditionPreserves scratch state afterCondition false index
              hCondition hIndex)
      · rcases hThen : thenValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (thenPreserves scratch afterCondition afterValue value index
          hThen hIndex).trans
            (conditionPreserves scratch state afterCondition true index
              hCondition hIndex)

  | iteF condition thenValue elseValue conditionPreserves thenPreserves elsePreserves =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval mem scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (elsePreserves scratch afterCondition afterValue value index
          hElse hIndex).trans
            (conditionPreserves scratch state afterCondition false index
              hCondition hIndex)
      · rcases hThen : thenValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (thenPreserves scratch afterCondition afterValue value index
          hThen hIndex).trans
            (conditionPreserves scratch state afterCondition true index
              hCondition hIndex)
  | getF localIndex =>
      unfold Expr.eval at hEval
      cases hGet : state.get localIndex with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case f64 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            rfl
  | getF32 localIndex =>
      unfold Expr.eval at hEval
      cases hGet : state.get localIndex with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case f32 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            rfl
  | binF op left right leftPreserves rightPreserves
  | binF32 op left right leftPreserves rightPreserves =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact (rightPreserves scratch afterLeft afterRight rightValue index hRight hIndex).trans
        (leftPreserves scratch state afterLeft leftValue index hLeft hIndex)
  | unF _ operand operandPreserves | convertU operand operandPreserves
  | truncSatU operand operandPreserves | ofBits operand operandPreserves
  | toBits operand operandPreserves | unF32 _ operand operandPreserves =>
      simp only [Expr.eval] at hEval
      rcases hOperand : operand.eval mem scratch state with _ | ⟨value, afterOperand⟩
      · simp [hOperand] at hEval
      simp [hOperand] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact operandPreserves scratch state afterOperand value index hOperand hIndex

set_option maxHeartbeats 1000000 in
theorem Expr.program_spec
    {type : ScalarType} (expression : Expr type) (scratch : Nat)
    (state next : State) (result : type.denote) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α)
    (rest : Program) (Q : Assertion α)
    (hEval : expression.eval store.mem scratch state = some (result, next))
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
          rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
          rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
          rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
          rcases hLeft : left.eval store.mem (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval store.mem (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
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
                Expr.eval_preserves_below right store.mem (scratch + 2) savedLeft
                  afterRight rightValue scratch hRight (by omega)
              _ = some (.i64 leftValue) := State.get_set?_same hSetLeft
          simp only [Wasm.wp_localGet_cons, State.toLocals_get, hRightSlot,
            Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
          try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
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
          rcases hLeft : left.eval store.mem (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval store.mem (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
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
                Expr.eval_preserves_below right store.mem (scratch + 2) savedLeft
                  afterRight rightValue scratch hRight (by omega)
              _ = some (.i64 leftValue) := State.get_set?_same hSetLeft
          simp only [Wasm.wp_localGet_cons, State.toLocals_get, hRightSlot,
            Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
          try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
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
          rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
  | ne left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
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
      rcases hCondition : condition.eval store.mem scratch state with _ | ⟨value, afterCondition⟩
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
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := false) (values := values)
          (rest := _) (Q := _) hLeft
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        simpa [wp_simp, ScalarType.value] using hNext
      · rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := true) (values := values)
          (rest := _) (Q := _) hLeft
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
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
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := false) (values := values)
          (rest := _) (Q := _) hLeft
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
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
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        simpa [wp_simp, ScalarType.value] using hNext
  | ite condition thenValue elseValue conditionSpec thenSpec elseSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hCondition : condition.eval store.mem scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval store.mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := false) (values := values)
          (rest := _) (Q := _) hCondition
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        rw [← List.append_nil (elseValue.program scratch)]
        apply elseSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hElse
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · rcases hThen : thenValue.eval store.mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := true) (values := values)
          (rest := _) (Q := _) hCondition
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        rw [← List.append_nil (thenValue.program scratch)]
        apply thenSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hThen
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext

  | iteF condition thenValue elseValue conditionSpec thenSpec elseSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hCondition : condition.eval store.mem scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval store.mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := false) (values := values)
          (rest := _) (Q := _) hCondition
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        rw [← List.append_nil (elseValue.program scratch)]
        apply elseSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hElse
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · rcases hThen : thenValue.eval store.mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := true) (values := values)
          (rest := _) (Q := _) hCondition
        try simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        rw [← List.append_nil (thenValue.program scratch)]
        apply thenSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hThen
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
  | eqF left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .f64 leftValue :: values) (rest := _) (Q := _) hRight
      simp only [List.cons_append, List.nil_append, Wasm.wp_f64Eq_cons, Wasm.wp_f64Lt_cons,
        Wasm.wp_f64Le_cons, State.toLocals]
      exact hNext
  | ltF left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .f64 leftValue :: values) (rest := _) (Q := _) hRight
      simp only [List.cons_append, List.nil_append, Wasm.wp_f64Eq_cons, Wasm.wp_f64Lt_cons,
        Wasm.wp_f64Le_cons, State.toLocals]
      exact hNext
  | leF left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .f64 leftValue :: values) (rest := _) (Q := _) hRight
      simp only [List.cons_append, List.nil_append, Wasm.wp_f64Eq_cons, Wasm.wp_f64Lt_cons,
        Wasm.wp_f64Le_cons, State.toLocals]
      exact hNext
  | constF bits =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      simp only [Expr.program, List.cons_append, List.nil_append, Wasm.wp_f64Const_cons]
      exact hNext
  | getF index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case f64 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [Expr.program, List.cons_append, List.nil_append,
              Wasm.wp_localGet_cons, State.toLocals_get, hGet]
            exact hNext
  | binF op left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .f64 leftValue :: values) (rest := _) (Q := _) hRight
      cases op <;>
        simpa [F64Op.instruction, F64Op.apply, wp_simp, Wasm.f64Add, Wasm.f64Sub, Wasm.f64Mul,
          Wasm.f64Div] using hNext
  | unF op operand operandSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hOperand : operand.eval store.mem scratch state with _ | ⟨value, afterOperand⟩
      · simp [hOperand] at hEval
      simp [hOperand] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply operandSpec (scratch := scratch) (state := state)
        (next := afterOperand) (result := value) (values := values)
        (rest := _) (Q := _) hOperand
      cases op <;>
        simpa [F64UnOp.instruction, F64UnOp.apply, wp_simp, Wasm.f64Sqrt, Wasm.f64Abs] using hNext
  | getF32 index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case f32 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [Expr.program, List.cons_append, List.nil_append,
              Wasm.wp_localGet_cons, State.toLocals_get, hGet]
            exact hNext
  | binF32 op left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hLeft : left.eval store.mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval store.mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .f32 leftValue :: values) (rest := _) (Q := _) hRight
      cases op <;>
        simpa [F32Op.instruction, F32Op.apply, wp_simp, Wasm.f32Add, Wasm.f32Sub, Wasm.f32Mul,
          Wasm.f32Div] using hNext
  | unF32 op operand operandSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hOperand : operand.eval store.mem scratch state with _ | ⟨value, afterOperand⟩
      · simp [hOperand] at hEval
      simp [hOperand] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply operandSpec (scratch := scratch) (state := state)
        (next := afterOperand) (result := value) (values := values)
        (rest := _) (Q := _) hOperand
      cases op
      simpa [F32UnOp.instruction, F32UnOp.apply, wp_simp, Wasm.f32Sqrt] using hNext
  | convertU operand operandSpec | truncSatU operand operandSpec | ofBits operand operandSpec
  | toBits operand operandSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.program, List.append_assoc]
      rcases hOperand : operand.eval store.mem scratch state with _ | ⟨value, afterOperand⟩
      · simp [hOperand] at hEval
      simp [hOperand] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply operandSpec (scratch := scratch) (state := state)
        (next := afterOperand) (result := value) (values := values)
        (rest := _) (Q := _) hOperand
      simpa [wp_simp, Wasm.f64ConvertI64U, Wasm.i64TruncSatF64U] using hNext
  | read array position positionSpec =>
      have hState := Expr.read_state hEval
      obtain ⟨k, afterPosition, hPosition, hSet⟩ := hState
      simp only [Expr.eval, hPosition, hSet, Option.bind_eq_bind, Option.bind_some,
        Expr.readValue] at hEval
      rcases hPtr : next.get array with _ | v
      · simp [hPtr] at hEval
      cases v <;> simp only [hPtr, Option.bind_some, reduceCtorEq] at hEval
      rename_i ptr
      simp only [Expr.program, List.append_assoc, List.cons_append, List.nil_append]
      apply positionSpec (scratch := scratch + 1) (state := state) (next := afterPosition)
        (result := k) (values := values) (rest := _) (Q := _) hPosition
      simp only [ScalarType.value]
      apply localSet_spec hSet
      apply localGet_spec (State.get_set?_same hSet)
      apply localGet_spec hPtr
      simp only [Wasm.wp_wrapI64_cons, Wasm.wp_load64_cons, State.toLocals, wrap_toUInt32,
        UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
      by_cases hLength : ptr.toUInt32.toNat + 8 ≤ store.mem.pages * 65536
      · rw [if_pos hLength] at hEval
        rw [ite_eq_right (by omega)]
        simp only [Wasm.wp_ltUI64_cons]
        try simp only [Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        by_cases hk : k < store.mem.read64 ptr.toUInt32
        · rw [if_pos hk] at hEval
          by_cases hElement : (ptr + (k + 1) * 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536
          · rw [if_pos hElement] at hEval
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hEval)
            rw [if_pos (by simp [hk])]
            apply localGet_spec hPtr
            apply localGet_spec (State.get_set?_same hSet)
            simp only [Wasm.wp_constI64_cons, Wasm.wp_addI64_cons, Wasm.wp_mulI64_cons,
              Wasm.wp_wrapI64_cons, Wasm.wp_load64_cons, State.toLocals, wrap_toUInt32,
              UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
            rw [ite_eq_right (by omega)]
            simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
          · rw [if_neg hElement] at hEval
            cases hEval
        · rw [if_neg hk] at hEval
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hEval)
          rw [if_neg (by simp [hk])]
          simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · rw [if_neg hLength] at hEval
        cases hEval

/-- `after` has as many parameters and locals as `before` and agrees with it at
every local below `scratch` outside `writes`. -/
structure State.Frame (scratch : Nat) (writes : List Nat) (before after : State) : Prop where
  params : after.params.length = before.params.length
  locals : after.locals.length = before.locals.length
  get : ∀ index, index < scratch → index ∉ writes → after.get index = before.get index

theorem State.Frame.refl (scratch : Nat) (writes : List Nat) (state : State) :
    State.Frame scratch writes state state :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem State.Frame.trans {scratch : Nat} {writes : List Nat} {a b c : State}
    (hFirst : State.Frame scratch writes a b) (hSecond : State.Frame scratch writes b c) :
    State.Frame scratch writes a c :=
  ⟨hSecond.params.trans hFirst.params, hSecond.locals.trans hFirst.locals,
    fun index hIndex hWrite => (hSecond.get index hIndex hWrite).trans (hFirst.get index hIndex hWrite)⟩

theorem State.Frame.weaken {scratch : Nat} {writes writes' : List Nat} {before after : State}
    (h : State.Frame scratch writes before after) (hSub : ∀ j ∈ writes, j ∈ writes') :
    State.Frame scratch writes' before after :=
  ⟨h.params, h.locals, fun index hIndex hWrite =>
    h.get index hIndex fun hIn => hWrite (hSub index hIn)⟩

theorem State.Frame.mono {scratch scratch' : Nat} {writes : List Nat} {before after : State}
    (h : State.Frame scratch writes before after) (hScratch : scratch' ≤ scratch) :
    State.Frame scratch' writes before after :=
  ⟨h.params, h.locals, fun index hIndex hWrite => h.get index (by omega) hWrite⟩

theorem State.exists_set? {state : State} {index : Nat} (value : Value)
    (hIndex : index < state.params.length + state.locals.length) :
    ∃ next, state.set? index value = some next := by
  unfold State.set?
  split <;> simp

theorem State.Frame.set? {scratch index : Nat} {writes : List Nat} {before state next : State}
    {value : Value} (hFrame : State.Frame scratch writes before state)
    (hSet : state.set? index value = some next) (hIndex : index ∈ writes ∨ scratch ≤ index) :
    State.Frame scratch writes before next := by
  have hLengths : next.params.length = state.params.length ∧
      next.locals.length = state.locals.length := by
    unfold State.set? at hSet
    split at hSet
    · cases hSet; simp
    · split at hSet
      · cases hSet; simp
      · contradiction
  refine ⟨hLengths.1.trans hFrame.params, hLengths.2.trans hFrame.locals,
    fun j hj hWrite => ?_⟩
  have hNe : j ≠ index := by
    rintro rfl
    rcases hIndex with hIndex | hIndex
    · exact hWrite hIndex
    · omega
  rw [State.get_set?_ne hNe hSet]
  exact hFrame.get j hj hWrite

/-- Evaluating an expression changes only scratch locals. -/
theorem Expr.eval_frame (writes : List Nat) {type : ScalarType} (expression : Expr type)
    (mem : Mem) (scratch : Nat) (state next : State) (result : type.denote)
    (hEval : expression.eval mem scratch state = some (result, next)) :
    State.Frame scratch writes state next := by
  induction expression generalizing scratch state next with
  | get index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact .refl _ _ _
  | const value | bconst value | constF value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      exact .refl _ _ _
  | bin op left right hLeftFrame hRightFrame =>
      cases op with
      | add | sub | mul | bitAnd | bitOr | bitXor | shiftLeft | shiftRight =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight)
      | divU | remU =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval mem (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval mem (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hSetLeft, hRight] at hEval
          rcases hSetRight : afterRight.set? (scratch + 1) (.i64 rightValue) with _ | savedRight
          · simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact ((((hLeftFrame _ _ _ _ hLeft).mono (by omega)).set? hSetLeft
            (Or.inr (by omega))).trans ((hRightFrame _ _ _ _ hRight).mono (by omega))).set?
              hSetRight (Or.inr (by omega))
  | read array position hPositionFrame =>
      obtain ⟨k, afterPosition, hPosition, hSet⟩ := Expr.read_state hEval
      exact ((hPositionFrame _ _ _ _ hPosition).mono (by omega)).set? hSet (Or.inr (by omega))
  | eq left right hLeftFrame hRightFrame
  | ne left right hLeftFrame hRightFrame
  | ltU left right hLeftFrame hRightFrame
  | leU left right hLeftFrame hRightFrame
  | eqF left right hLeftFrame hRightFrame
  | ltF left right hLeftFrame hRightFrame
  | leF left right hLeftFrame hRightFrame =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight)
  | not condition hConditionFrame =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval mem scratch state with _ | ⟨value, afterCondition⟩
      · simp [hCondition] at hEval
      simp [hCondition] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hConditionFrame _ _ _ _ hCondition
  | and left right hLeftFrame hRightFrame | or left right hLeftFrame hRightFrame =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      all_goals
        first
        | (simp [hLeft] at hEval
           obtain ⟨rfl, rfl⟩ := hEval
           exact hLeftFrame _ _ _ _ hLeft)
        | (rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
           · simp [hLeft, hRight] at hEval
           simp [hLeft, hRight] at hEval
           obtain ⟨rfl, rfl⟩ := hEval
           exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight))
  | ite condition thenValue elseValue hConditionFrame hThenFrame hElseFrame =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval mem scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (hConditionFrame _ _ _ _ hCondition).trans (hElseFrame _ _ _ _ hElse)
      · rcases hThen : thenValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (hConditionFrame _ _ _ _ hCondition).trans (hThenFrame _ _ _ _ hThen)
  | iteF condition thenValue elseValue hConditionFrame hThenFrame hElseFrame =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval mem scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (hConditionFrame _ _ _ _ hCondition).trans (hElseFrame _ _ _ _ hElse)
      · rcases hThen : thenValue.eval mem scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (hConditionFrame _ _ _ _ hCondition).trans (hThenFrame _ _ _ _ hThen)
  | getF index | getF32 index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact .refl _ _ _
  | binF op left right hLeftFrame hRightFrame | binF32 op left right hLeftFrame hRightFrame =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval mem scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval mem scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight)
  | unF _ operand hOperandFrame | convertU operand hOperandFrame
  | truncSatU operand hOperandFrame | ofBits operand hOperandFrame
  | toBits operand hOperandFrame | unF32 _ operand hOperandFrame =>
      simp only [Expr.eval] at hEval
      rcases hOperand : operand.eval mem scratch state with _ | ⟨value, afterOperand⟩
      · simp [hOperand] at hEval
      simp [hOperand] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hOperandFrame _ _ _ _ hOperand

end Project.IR
