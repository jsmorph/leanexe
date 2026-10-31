import Interpreter.Wasm.Syntax
import Interpreter.Wasm.IEEE64

/-!
The source language of the WGSL translation: scalar types and their values, the word, binary64,
and binary32 operators, and the expressions and statements whose denotation
`LeanExe.WGSL.SourceDenote` gives.  The verified compiler states each kernel body in this language,
and `LeanExe.WGSL.Translate` and `LeanExe.WGSL.TranslateStmt` translate it to WGSL.
-/

namespace LeanExe.WGSL.Source

open Wasm

/-- The types of source values.  A float value is its bit pattern. -/
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

inductive F64UnOp where
  | sqrt
  | abs
  deriving Repr, DecidableEq

def F64UnOp.apply : F64UnOp → UInt64 → UInt64
  | .sqrt, value => IEEE64.sqrt value
  | .abs, value => IEEE64.abs value

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

inductive F32UnOp where
  | sqrt
  | abs
  | nearest
  deriving Repr, DecidableEq

def F32UnOp.apply : F32UnOp → UInt32 → UInt32
  | .sqrt, value => IEEE32.sqrt value
  | .abs, value => IEEE32.abs value
  | .nearest, value => IEEE32.nearest value

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
  | constF32 (bits : UInt32) : Expr .f32
  /-- The binary32 float whose bit pattern is the word's low 32 bits, as `i32.wrap_i64` and
  `f32.reinterpret_i32`. -/
  | ofBits32 (operand : Expr .u64) : Expr .f32
  /-- The binary32 float's bit pattern as a word, as `i32.reinterpret_f32` and
  `i64.extend_i32_u`. -/
  | toBits32 (operand : Expr .f32) : Expr .u64
  | iteF32 (condition : Expr .bool) (thenValue elseValue : Expr .f32) : Expr .f32
  | eqF32 (left right : Expr .f32) : Expr .bool
  | ltF32 (left right : Expr .f32) : Expr .bool
  | leF32 (left right : Expr .f32) : Expr .bool
  deriving Repr

/-- Source statements.  `while` is the only loop; its body runs while the condition holds.
`load`, `store`, `call`, and `abort` have no denotation. -/
inductive Stmt where
  | skip
  | assign {type : ScalarType} (index : Nat) (value : Expr type)
  | seq (first second : Stmt)
  | ite (condition : Expr .bool) (thenStmt elseStmt : Stmt)
  | while (condition : Expr .bool) (body : Stmt)
  /-- Local `index` receives the 64-bit word at `address`, wrapped to 32 bits, as a value of
  `type`. -/
  | load (type : ScalarType) (index : Nat) (address : Expr .u64)
  /-- The 64-bit word at `address`, wrapped to 32 bits, receives `value`. -/
  | store (address value : Expr .u64)
  /-- Calls function `func` with the values of `args`, and puts its result in
  local `index` when `result` is `some index`. -/
  | call (func : Nat) (args : List ((type : ScalarType) × Expr type)) (results : List Nat)
  /-- Traps at `unreachable`. -/
  | abort
  deriving Repr

end LeanExe.WGSL.Source
