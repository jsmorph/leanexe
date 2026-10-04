import Project.WGSL.Syntax
import Interpreter.Wasm.IEEE32

/-!
The meaning of a kernel under the device model of 2026-10-04.  Binary32 operations compute Talos's
`IEEE32` results.  An invocation runs the body with the read-only buffers and records its stores
to the read-write buffer, which it may not read.  A dispatch runs invocations `0` to `count - 1`
on the initial buffers and applies each invocation's stores to the output in order; when the
stores of distinct invocations go to distinct words (`Module.RaceFree`), the order does not
matter, and WGSL's memory model gives the same result for the concurrent execution.  Every error
here, an ill-typed operation, an access outside a buffer, or a read of the output, makes the
result `none`.
-/

namespace Project.WGSL

inductive Value where
  | u32 (value : UInt32)
  | f32 (bits : UInt32)
  | bool (value : Bool)
  | vec2 (low high : UInt32)
  deriving Repr, DecidableEq

/-- Whether two values have the same type. -/
def Value.sameType : Value → Value → Bool
  | .u32 _, .u32 _ | .f32 _, .f32 _ | .bool _, .bool _ | .vec2 _ _, .vec2 _ _ => true
  | _, _ => false

def Ty.holds : Ty → Value → Bool
  | .u32, .u32 _ | .f32, .f32 _ | .bool, .bool _ | .vec2u, .vec2 _ _ => true
  | _, _ => false

/-- The variables in scope, innermost first, each with its value and whether it is a `var`. -/
abbrev Env := List (Nat × Value × Bool)

def Env.find (env : Env) (index : Nat) : Option (Value × Bool) :=
  (env.find? (·.1 = index)).map (·.2)

def Env.set (env : Env) (index : Nat) (value : Value) : Env :=
  env.map fun b => if b.1 = index then (b.1, value, b.2.2) else b

/-- What an invocation sees: its index, the read-only buffers, and the size of the output. -/
structure Context where
  gid : UInt32
  inputs : List (Array UInt32)
  outputSize : Nat

def BinOp.apply : BinOp → Value → Value → Option Value
  | .add, .u32 a, .u32 b => some (.u32 (a + b))
  | .sub, .u32 a, .u32 b => some (.u32 (a - b))
  | .mul, .u32 a, .u32 b => some (.u32 (a * b))
  | .div, .u32 a, .u32 b => some (.u32 (if b = 0 then a else a / b))
  | .lt, .u32 a, .u32 b => some (.bool (decide (a < b)))
  | .le, .u32 a, .u32 b => some (.bool (decide (a ≤ b)))
  | .eq, .u32 a, .u32 b => some (.bool (a == b))
  | .add, .f32 a, .f32 b => some (.f32 (Wasm.IEEE32.add a b))
  | .sub, .f32 a, .f32 b => some (.f32 (Wasm.IEEE32.sub a b))
  | .mul, .f32 a, .f32 b => some (.f32 (Wasm.IEEE32.mul a b))
  | .div, .f32 a, .f32 b => some (.f32 (Wasm.IEEE32.div a b))
  | .lt, .f32 a, .f32 b => some (.bool (Wasm.IEEE32.lt a b))
  | .le, .f32 a, .f32 b => some (.bool (Wasm.IEEE32.le a b))
  | .eq, .f32 a, .f32 b => some (.bool (Wasm.IEEE32.eq a b))
  | .eq, .bool a, .bool b => some (.bool (a == b))
  | _, _, _ => none

/-- The value of an expression.  `&&` and `||` evaluate their right operand only when it decides
the result, and `select` evaluates all three arguments, as WGSL does. -/
def Expr.eval (ctx : Context) (env : Env) : Expr → Option Value
  | .lit v => some (.u32 v)
  | .bool b => some (.bool b)
  | .var n => (env.find n).map (·.1)
  | .gidX => some (.u32 ctx.gid)
  | .fst n => match env.find n with
    | some (.vec2 low _, _) => some (.u32 low)
    | _ => none
  | .snd n => match env.find n with
    | some (.vec2 _ high, _) => some (.u32 high)
    | _ => none
  | .vec2 a b => match a.eval ctx env, b.eval ctx env with
    | some (.u32 low), some (.u32 high) => some (.vec2 low high)
    | _, _ => none
  | .bin .and a b => match a.eval ctx env with
    | some (.bool true) => match b.eval ctx env with
      | some (.bool v) => some (.bool v)
      | _ => none
    | some (.bool false) => some (.bool false)
    | _ => none
  | .bin .or a b => match a.eval ctx env with
    | some (.bool false) => match b.eval ctx env with
      | some (.bool v) => some (.bool v)
      | _ => none
    | some (.bool true) => some (.bool true)
    | _ => none
  | .bin op a b => do op.apply (← a.eval ctx env) (← b.eval ctx env)
  | .not a => match a.eval ctx env with
    | some (.bool v) => some (.bool !v)
    | _ => none
  | .toF32 a => match a.eval ctx env with
    | some (.u32 v) => some (.f32 v)
    | _ => none
  | .toU32 a => match a.eval ctx env with
    | some (.f32 v) => some (.u32 v)
    | _ => none
  | .sqrt a => match a.eval ctx env with
    | some (.f32 v) => some (.f32 (Wasm.IEEE32.sqrt v))
    | _ => none
  | .abs a => match a.eval ctx env with
    | some (.f32 v) => some (.f32 (Wasm.IEEE32.abs v))
    | _ => none
  | .select f t c => match f.eval ctx env, t.eval ctx env, c.eval ctx env with
    | some fv, some tv, some (.bool cv) =>
        if fv.sameType tv then some (if cv then tv else fv) else none
    | _, _, _ => none
  | .min a b => match a.eval ctx env, b.eval ctx env with
    | some (.u32 x), some (.u32 y) => some (.u32 (if x ≤ y then x else y))
    | _, _ => none
  | .length b => (ctx.inputs[b]?).map fun buffer => .u32 (UInt32.ofNat buffer.size)
  | .index b p => match ctx.inputs[b]?, p.eval ctx env with
    | some buffer, some (.u32 i) => (buffer[i.toNat]?).map .u32
    | _, _ => none

/-- An invocation's state: the variables in scope, its stores to the output in order, and
whether it has returned. -/
structure Run where
  env : Env
  writes : List (Nat × UInt32)
  returned : Bool

mutual
  /-- One statement. -/
  def Stmt.exec (ctx : Context) (run : Run) : Stmt → Option Run
    | .let_ n ty e => do
        let v ← e.eval ctx run.env
        if ty.holds v && (run.env.find n).isNone then
          some { run with env := (n, v, false) :: run.env } else none
    | .var n ty e => do
        let v ← e.eval ctx run.env
        if ty.holds v && (run.env.find n).isNone then
          some { run with env := (n, v, true) :: run.env } else none
    | .assign n e => do
        let v ← e.eval ctx run.env
        let (old, true) ← run.env.find n | none
        if old.sameType v then some { run with env := run.env.set n v } else none
    | .store b p e => do
        let .u32 i ← p.eval ctx run.env | none
        let .u32 v ← e.eval ctx run.env | none
        if b = ctx.inputs.length ∧ i.toNat < ctx.outputSize then
          some { run with writes := run.writes ++ [(i.toNat, v)] } else none
    | .ite c ts es => do
        let .bool cv ← c.eval ctx run.env | none
        let inner ← if cv then Stmt.execList ctx run ts else Stmt.execList ctx run es
        -- Declarations inside the block go out of scope; assignments to outer variables stay.
        some { inner with env := inner.env.drop (inner.env.length - run.env.length) }
    | .ret => some { run with returned := true }

  /-- Statements in order; those after a `return` do nothing. -/
  def Stmt.execList (ctx : Context) (run : Run) : List Stmt → Option Run
    | [] => some run
    | s :: rest =>
        if run.returned then some run else do Stmt.execList ctx (← Stmt.exec ctx run s) rest
end

/-- The stores of invocation `gid`, or `none` when it fails. -/
def Module.invoke (m : Module) (inputs : List (Array UInt32)) (outputSize : Nat) (gid : UInt32) :
    Option (List (Nat × UInt32)) :=
  if inputs.length = m.inputs then
    (Stmt.execList { gid, inputs, outputSize } { env := [], writes := [], returned := false }
      m.body).map (·.writes)
  else none

def applyWrites (output : Array UInt32) (writes : List (Nat × UInt32)) : Array UInt32 :=
  writes.foldl (fun out w => out.setIfInBounds w.1 w.2) output

/-- The output after invocations `0` to `count - 1`, each run on the initial buffers. -/
def Module.dispatch (m : Module) (inputs : List (Array UInt32)) (output : Array UInt32)
    (count : Nat) : Option (Array UInt32) :=
  (List.range count).foldlM (fun out g => do
    let w ← m.invoke inputs output.size (UInt32.ofNat g)
    pure (applyWrites out w)) output

/-- Distinct invocations store to distinct words. -/
def Module.RaceFree (m : Module) (inputs : List (Array UInt32)) (outputSize count : Nat) : Prop :=
  ∀ g h, g < count → h < count → g ≠ h → ∀ wg wh,
    m.invoke inputs outputSize (UInt32.ofNat g) = some wg →
    m.invoke inputs outputSize (UInt32.ofNat h) = some wh →
    ∀ a ∈ wg, ∀ b ∈ wh, a.1 ≠ b.1

end Project.WGSL
