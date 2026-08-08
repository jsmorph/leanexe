import LeanExe.IR.Core
import LeanExe.Wasm.Instr
import Lean.Data.Json.Printer

namespace LeanExe.Wasm.ScalarDescriptor

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
  deriving Repr, BEq

def U64Op.ofIR : LeanExe.IR.U64Op → Option U64Op
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .divU => some .divU
  | .modU => some .remU
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor
  | .shiftLeft => some .shiftLeft
  | .shiftRight => some .shiftRight
  | .natAdd | .natSub | .natMul => none

def U64Op.instruction : U64Op → Instr
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

mutual

  inductive Expr where
    | get (index : Nat)
    | const (value : Nat)
    | bin (op : U64Op) (left right : Expr)
    | ite (condition : Cond) (thenValue elseValue : Expr)
    deriving Repr, BEq

  inductive Cond where
    | true
    | false
    | eq (left right : Expr)
    | ltU (left right : Expr)
    | leU (left right : Expr)
    | not (condition : Cond)
    | and (left right : Cond)
    | or (left right : Cond)
    deriving Repr, BEq

end

inductive Stmt where
  | skip
  | assign (index : Nat) (value : Expr)
  | seq (first second : Stmt)
  | ite (condition : Cond) (thenStmt elseStmt : Stmt)
  deriving Repr, BEq

structure While where
  condition : Cond
  body : Stmt
  deriving Repr, BEq

mutual

  def Expr.reads : Expr → List Nat
    | .get index => [index]
    | .const _ => []
    | .bin _ left right => left.reads ++ right.reads
    | .ite condition thenValue elseValue =>
        condition.reads ++ thenValue.reads ++ elseValue.reads

  def Cond.reads : Cond → List Nat
    | .true | .false => []
    | .eq left right | .ltU left right | .leU left right =>
        left.reads ++ right.reads
    | .not condition => condition.reads
    | .and left right | .or left right => left.reads ++ right.reads

end

mutual

  def Expr.scratchWidth : Expr → Nat
    | .get _ | .const _ => 0
    | .bin operation left right =>
        let childWidth := max left.scratchWidth right.scratchWidth
        if operation == .divU || operation == .remU then childWidth + 2 else childWidth
    | .ite condition thenValue elseValue =>
        max condition.scratchWidth (max thenValue.scratchWidth elseValue.scratchWidth)

  def Cond.scratchWidth : Cond → Nat
    | .true | .false => 0
    | .eq left right | .ltU left right | .leU left right =>
        max left.scratchWidth right.scratchWidth
    | .not condition => condition.scratchWidth
    | .and left right | .or left right =>
        max left.scratchWidth right.scratchWidth

end


def Stmt.reads : Stmt → List Nat
  | .skip => []
  | .assign _ value => value.reads
  | .seq first second => first.reads ++ second.reads
  | .ite condition thenStmt elseStmt =>
      condition.reads ++ thenStmt.reads ++ elseStmt.reads

def Stmt.writes : Stmt → List Nat
  | .skip => []
  | .assign index _ => [index]
  | .seq first second => first.writes ++ second.writes
  | .ite _ thenStmt elseStmt => thenStmt.writes ++ elseStmt.writes

def Stmt.scratchWidth : Stmt → Nat
  | .skip => 0
  | .assign _ value => value.scratchWidth
  | .seq first second => max first.scratchWidth second.scratchWidth
  | .ite condition thenStmt elseStmt =>
      max condition.scratchWidth (max thenStmt.scratchWidth elseStmt.scratchWidth)

def While.reads (descriptor : While) : List Nat :=
  descriptor.condition.reads ++ descriptor.body.reads

def While.writes (descriptor : While) : List Nat := descriptor.body.writes

def While.scratchWidth (descriptor : While) : Nat :=
  max descriptor.condition.scratchWidth descriptor.body.scratchWidth

mutual

  def Expr.ofIR : LeanExe.IR.Expr → Option Expr
    | .local index => some (.get index)
    | .u64 value => some (.const value)
    | .u64Bin op left right => do
        let descriptorOp ← U64Op.ofIR op
        let descriptorLeft ← Expr.ofIR left
        let descriptorRight ← Expr.ofIR right
        pure (.bin descriptorOp descriptorLeft descriptorRight)
    | .ite condition thenValue elseValue => do
        let descriptorCondition ← Cond.ofIR condition
        let descriptorThen ← Expr.ofIR thenValue
        let descriptorElse ← Expr.ofIR elseValue
        pure (.ite descriptorCondition descriptorThen descriptorElse)
    | _ => none

  def Cond.ofIR : LeanExe.IR.Cond → Option Cond
    | .true => some .true
    | .false => some .false
    | .eqU64 left right => do
        let descriptorLeft ← Expr.ofIR left
        let descriptorRight ← Expr.ofIR right
        pure (.eq descriptorLeft descriptorRight)
    | .ltU64 left right => do
        let descriptorLeft ← Expr.ofIR left
        let descriptorRight ← Expr.ofIR right
        pure (.ltU descriptorLeft descriptorRight)
    | .leU64 left right => do
        let descriptorLeft ← Expr.ofIR left
        let descriptorRight ← Expr.ofIR right
        pure (.leU descriptorLeft descriptorRight)
    | .not condition => return .not (← Cond.ofIR condition)
    | .and left right => return .and (← Cond.ofIR left) (← Cond.ofIR right)
    | .or left right => return .or (← Cond.ofIR left) (← Cond.ofIR right)

end

def Stmt.ofIR : LeanExe.IR.Stmt → Option Stmt
  | .skip => some .skip
  | .assign index value => return .assign index (← Expr.ofIR value)
  | .seq first second => return .seq (← Stmt.ofIR first) (← Stmt.ofIR second)
  | .ite condition thenStmt elseStmt =>
      return .ite (← Cond.ofIR condition) (← Stmt.ofIR thenStmt)
        (← Stmt.ofIR elseStmt)
  | _ => none

def While.ofIR : LeanExe.IR.Stmt → Option While
  | .while condition body => return ⟨← Cond.ofIR condition, ← Stmt.ofIR body⟩
  | _ => none

mutual

  def Expr.emit : Expr → Nat → List Instr
    | .get index, _ => [.localGet index]
    | .const value, _ => [.constI64 value]
    | .bin op left right, scratch =>
        if op == .divU || op == .remU then
          let childScratch := scratch + 2
          let zeroValue := if op == .divU then [.constI64 0] else [.localGet scratch]
          left.emit childScratch ++ [.localSet scratch] ++
            right.emit childScratch ++ [.localSet (scratch + 1)] ++
            [.localGet (scratch + 1), .constI64 0, .eqI64,
              .iff true zeroValue
                (some [.localGet scratch, .localGet (scratch + 1), op.instruction])]
        else
          left.emit scratch ++ right.emit scratch ++ [op.instruction]
    | .ite condition thenValue elseValue, scratch =>
        condition.emit scratch ++
          [.iff true (thenValue.emit scratch) (some (elseValue.emit scratch))]

  def Cond.emit : Cond → Nat → List Instr
    | .true, _ => [.constI32 1]
    | .false, _ => [.constI32 0]
    | .eq left right, scratch => left.emit scratch ++ right.emit scratch ++ [.eqI64]
    | .ltU left right, scratch => left.emit scratch ++ right.emit scratch ++ [.ltUI64]
    | .leU left right, scratch => left.emit scratch ++ right.emit scratch ++ [.leUI64]
    | .not condition, scratch => condition.emit scratch ++ [.eqzI32]
    | .and left right, scratch =>
        left.emit scratch ++ [.iffI32 (right.emit scratch) (some [.constI32 0])]
    | .or left right, scratch =>
        left.emit scratch ++ [.iffI32 [.constI32 1] (some (right.emit scratch))]

end

def Stmt.emit : Stmt → Nat → List Instr
  | .skip, _ => []
  | .assign index value, scratch => value.emit scratch ++ [.localSet index]
  | .seq first second, scratch => first.emit scratch ++ second.emit scratch
  | .ite condition thenStmt elseStmt, scratch =>
      condition.emit scratch ++
        [.iff false (thenStmt.emit scratch) (some (elseStmt.emit scratch))]

def While.emit (descriptor : While) (scratch : Nat) : List Instr :=
  [.block [.loop
    (descriptor.condition.emit scratch ++ [.eqzI32, .brIf 1] ++
      descriptor.body.emit scratch ++ [.br 0])]]

def U64Op.toJson : U64Op → Lean.Json
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .divU => "div-u"
  | .remU => "rem-u"
  | .bitAnd => "bit-and"
  | .bitOr => "bit-or"
  | .bitXor => "bit-xor"
  | .shiftLeft => "shift-left"
  | .shiftRight => "shift-right"

instance : Lean.ToJson U64Op where
  toJson := U64Op.toJson

mutual

  def Expr.toJson : Expr → Lean.Json
    | .get index => Lean.Json.mkObj [
        ("kind", "get"), ("index", Lean.toJson index)]
    | .const value => Lean.Json.mkObj [
        ("kind", "const"), ("value", toString value)]
    | .bin operation left right => Lean.Json.mkObj [
        ("kind", "bin"), ("operation", operation.toJson),
        ("left", left.toJson), ("right", right.toJson)]
    | .ite condition thenValue elseValue => Lean.Json.mkObj [
        ("kind", "ite"), ("condition", condition.toJson),
        ("then", thenValue.toJson), ("else", elseValue.toJson)]

  def Cond.toJson : Cond → Lean.Json
    | .true => Lean.Json.mkObj [("kind", "true")]
    | .false => Lean.Json.mkObj [("kind", "false")]
    | .eq left right => Lean.Json.mkObj [
        ("kind", "eq"), ("left", left.toJson), ("right", right.toJson)]
    | .ltU left right => Lean.Json.mkObj [
        ("kind", "lt-u"), ("left", left.toJson), ("right", right.toJson)]
    | .leU left right => Lean.Json.mkObj [
        ("kind", "le-u"), ("left", left.toJson), ("right", right.toJson)]
    | .not condition => Lean.Json.mkObj [
        ("kind", "not"), ("condition", condition.toJson)]
    | .and left right => Lean.Json.mkObj [
        ("kind", "and"), ("left", left.toJson), ("right", right.toJson)]
    | .or left right => Lean.Json.mkObj [
        ("kind", "or"), ("left", left.toJson), ("right", right.toJson)]

end

instance : Lean.ToJson Expr where
  toJson := Expr.toJson

instance : Lean.ToJson Cond where
  toJson := Cond.toJson

def Stmt.toJson : Stmt → Lean.Json
  | .skip => Lean.Json.mkObj [("kind", "skip")]
  | .assign index value => Lean.Json.mkObj [
      ("kind", "assign"), ("index", Lean.toJson index), ("value", value.toJson)]
  | .seq first second => Lean.Json.mkObj [
      ("kind", "seq"), ("first", first.toJson), ("second", second.toJson)]
  | .ite condition thenStmt elseStmt => Lean.Json.mkObj [
      ("kind", "ite"), ("condition", condition.toJson),
      ("then", thenStmt.toJson), ("else", elseStmt.toJson)]

instance : Lean.ToJson Stmt where
  toJson := Stmt.toJson

instance : Lean.ToJson While where
  toJson descriptor := Lean.Json.mkObj [
    ("condition", descriptor.condition.toJson), ("body", descriptor.body.toJson)]

end LeanExe.Wasm.ScalarDescriptor
