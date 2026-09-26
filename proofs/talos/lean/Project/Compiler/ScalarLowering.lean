import Project.ProofKit.ScalarTransition
import LeanExe.Wasm.ScalarSemantics

namespace Project.Compiler.ScalarLowering


/-! Interpretation of the production structured instruction syntax in Talos.
Unsupported instructions fail explicitly. This is a semantic translation, not
an alternative code generator; the input is the actual emitter's instruction list.
-/

mutual
  def instruction : LeanExe.Wasm.Instr → Option Wasm.Instruction
    | .constI64 n => some (.constI64 (UInt64.ofNat n))
    | .constI32 n => some (.const (UInt32.ofNat n))
    | .localGet n => some (.localGet n)
    | .localSet n => some (.localSet n)
    | .localTee n => some (.localTee n)
    | .call n => some (.call n)
    | .addI64 => some .addI64
    | .subI64 => some .subI64
    | .mulI64 => some .mulI64
    | .divUI64 => some .divUI64
    | .remUI64 => some .remUI64
    | .andI64 => some .andI64
    | .orI64 => some .orI64
    | .xorI64 => some .xorI64
    | .shlI64 => some .shlI64
    | .shrUI64 => some .shrUI64
    | .eqI64 => some .eqI64
    | .neI64 => some .neI64
    | .ltUI64 => some .ltUI64
    | .leUI64 => some .leUI64
    | .eqzI32 => some .eqz
    | .block body => return .block 0 0 (← program body)
    | .loop body => return .loop 0 0 (← program body)
    | .iff result thenBody elseBody =>
        return .iff 0 (if result then 1 else 0) (← program thenBody)
          (← program (elseBody.getD [])) [] (if result then [.i64] else [])
    | .iffI32 thenBody elseBody =>
        return .iff 0 1 (← program thenBody) (← program (elseBody.getD [])) [] [.i32]
    | .br depth => some (.br depth)
    | .brIf depth => some (.br_if depth)
    | _ => none
  termination_by item => sizeOf item
  decreasing_by
    all_goals first
      | decreasing_tactic
      | cases elseBody <;> simp_all [Option.getD] <;> omega

  def program : List LeanExe.Wasm.Instr → Option Wasm.Program
    | [] => some []
    | head :: tail => return (← instruction head) :: (← program tail)
  termination_by items => sizeOf items
end

@[simp] theorem program_append (a b : List LeanExe.Wasm.Instr) :
    program (a ++ b) = (do
      let x ← program a
      let y ← program b
      pure (x ++ y)) := by
  induction a with
  | nil => simp [program]
  | cons head tail ih =>
    simp only [List.cons_append, program, ih]
    cases instruction head <;> cases program tail <;> cases program b <;> rfl

def operation : LeanExe.Wasm.ScalarDescriptor.U64Op → Project.ProofKit.ScalarTransition.U64Op
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .divU => .divU
  | .remU => .remU
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor
  | .shiftLeft => .shiftLeft
  | .shiftRight => .shiftRight

mutual
  def expression : LeanExe.Wasm.ScalarDescriptor.Expr → Project.ProofKit.ScalarTransition.Expr .u64
    | .get index => .get index
    | .const value => .const (UInt64.ofNat value)
    | .bin op left right => .bin (operation op) (expression left) (expression right)
    | .ite c left right => .ite (condition c) (expression left) (expression right)

  def condition : LeanExe.Wasm.ScalarDescriptor.Cond → Project.ProofKit.ScalarTransition.Expr .bool
    | .true => .bconst true
    | .false => .bconst false
    | .eq left right => .eq (expression left) (expression right)
    | .ne left right => .ne (expression left) (expression right)
    | .ltU left right => .ltU (expression left) (expression right)
    | .leU left right => .leU (expression left) (expression right)
    | .not c => .not (condition c)
    | .and left right => .and (condition left) (condition right)
    | .or left right => .or (condition left) (condition right)
end

@[simp] theorem operation_instruction (op : LeanExe.Wasm.ScalarDescriptor.U64Op) :
    instruction op.instruction = some (operation op).instruction := by
  cases op <;> simp [instruction, LeanExe.Wasm.ScalarDescriptor.U64Op.instruction, operation, Project.ProofKit.ScalarTransition.U64Op.instruction]

mutual
  theorem expression_program (e : LeanExe.Wasm.ScalarDescriptor.Expr) (scratch : Nat) :
      program (e.emit scratch) = some ((expression e).program scratch) := by
    cases e with
    | get i | const i =>
      simp [LeanExe.Wasm.ScalarDescriptor.Expr.emit, expression,
        Project.ProofKit.ScalarTransition.Expr.program, program, instruction]
    | bin op a b =>
      cases op <;>
        simp [LeanExe.Wasm.ScalarDescriptor.U64Op.ctorIdx, LeanExe.Wasm.ScalarDescriptor.instBEqU64Op.beq, BEq.beq, LeanExe.Wasm.ScalarDescriptor.instBEqU64Op,LeanExe.Wasm.ScalarDescriptor.Expr.emit, expression, operation,
          Project.ProofKit.ScalarTransition.Expr.program,
          LeanExe.Wasm.ScalarDescriptor.U64Op.instruction,
          Project.ProofKit.ScalarTransition.U64Op.instruction,
          program_append, program, instruction, expression_program a, expression_program b]
    | ite c a b =>
      simp [LeanExe.Wasm.ScalarDescriptor.Expr.emit, expression,
        Project.ProofKit.ScalarTransition.Expr.program, program_append, program,
        instruction, condition_program c, expression_program a, expression_program b]
  termination_by sizeOf e

  theorem condition_program (c : LeanExe.Wasm.ScalarDescriptor.Cond) (scratch : Nat) :
      program (c.emit scratch) = some ((condition c).program scratch) := by
    cases c with
    | true | false =>
      simp [LeanExe.Wasm.ScalarDescriptor.Cond.emit, condition,
        Project.ProofKit.ScalarTransition.Expr.program, program, instruction]
    | eq a b | ne a b | ltU a b | leU a b =>
      simp [LeanExe.Wasm.ScalarDescriptor.Cond.emit, condition,
        Project.ProofKit.ScalarTransition.Expr.program, program_append, program,
        instruction, expression_program a, expression_program b]
    | not c =>
      simp [LeanExe.Wasm.ScalarDescriptor.Cond.emit, condition,
        Project.ProofKit.ScalarTransition.Expr.program, program_append, program,
        instruction, condition_program c]
    | and a b | or a b =>
      simp [LeanExe.Wasm.ScalarDescriptor.Cond.emit, condition,
        Project.ProofKit.ScalarTransition.Expr.program, program_append, program,
        instruction, condition_program a, condition_program b]
  termination_by sizeOf c
end

end Project.Compiler.ScalarLowering
