import Project.Artifact.Binary.Evaluate

namespace Wasm.Binary
open Parser

attribute [cbv_opaque] instruction

@[cbv_opaque] def instructionAt (fuel : Nat) (cursor : Cursor) : Except Error (Instr × Cursor) :=
  instruction fuel cursor

@[cbv_eval] theorem instruction_eta (fuel : Nat) :
    instruction fuel = fun cursor => instructionAt fuel cursor := rfl

/-- A single instruction equation; recursive bodies retain the original parser. -/
def instructionStep : Nat → Parser Instr
  | 0 => fail (.malformed "instruction nesting exceeds body size")
  | fuel + 1 => do
      let opcodeByte ← readByte
      match classify opcodeByte with
      | none => fail (.unsupportedOpcode opcodeByte)
      | some opcode =>
        match opcode with
        | .unreachable => pure .unreachable
        | .block =>
          let type ← blockType
          let (body, terminator) ← instructionSequence fuel false
          match terminator with
          | .end => pure (.block type body)
          | .otherwise => fail (.malformed "else terminates a block")
        | .loop =>
          let type ← blockType
          let (body, terminator) ← instructionSequence fuel false
          match terminator with
          | .end => pure (.loop type body)
          | .otherwise => fail (.malformed "else terminates a loop")
        | .iff =>
          let type ← blockType
          let (thenBody, terminator) ← instructionSequence fuel true
          match terminator with
          | .end => pure (.iff type thenBody none)
          | .otherwise =>
              let (elseBody, elseTerminator) ← instructionSequence fuel false
              match elseTerminator with
              | .end => pure (.iff type thenBody (some elseBody))
              | .otherwise => fail (.malformed "second else in if")
        | .br => pure (.br (← Leb.u32))
        | .brIf => pure (.brIf (← Leb.u32))
        | .ret => pure .ret
        | .call => pure (.call (← Leb.u32))
        | .drop => pure .drop
        | .localGet => pure (.localGet (← Leb.u32))
        | .localSet => pure (.localSet (← Leb.u32))
        | .localTee => pure (.localTee (← Leb.u32))
        | .globalGet => pure (.globalGet (← Leb.u32))
        | .globalSet => pure (.globalSet (← Leb.u32))
        | .i32Load => pure (.i32Load (← memArg))
        | .i64Load => pure (.i64Load (← memArg))
        | .i32Load8U => pure (.i32Load8U (← memArg))
        | .i32Store => pure (.i32Store (← memArg))
        | .i64Store => pure (.i64Store (← memArg))
        | .i32Store8 => pure (.i32Store8 (← memArg))
        | .memorySize => pure (.memorySize (← Leb.u32))
        | .memoryGrow => pure (.memoryGrow (← Leb.u32))
        | .i32Const => pure (.i32Const (← Leb.s32))
        | .i64Const => pure (.i64Const (← Leb.s64))
        | .i32Eqz => pure .i32Eqz
        | .i32Eq => pure .i32Eq
        | .i64Eqz => pure .i64Eqz
        | .i64Eq => pure .i64Eq
        | .i64Ne => pure .i64Ne
        | .i64LtU => pure .i64LtU
        | .i64LeU => pure .i64LeU
        | .i64GeU => pure .i64GeU
        | .i32And => pure .i32And
        | .i64Add => pure .i64Add
        | .i64Sub => pure .i64Sub
        | .i64Mul => pure .i64Mul
        | .i64DivU => pure .i64DivU
        | .i64RemU => pure .i64RemU
        | .i64And => pure .i64And
        | .i64Or => pure .i64Or
        | .i64Xor => pure .i64Xor
        | .i64Shl => pure .i64Shl
        | .i64ShrU => pure .i64ShrU
        | .f64Add => pure .f64Add
        | .f64Mul => pure .f64Mul
        | .f64Sub => pure .f64Sub
        | .f64Div => pure .f64Div
        | .f64Sqrt => pure .f64Sqrt
        | .i32WrapI64 => pure .i32WrapI64
        | .i64ExtendI32U => pure .i64ExtendI32U
        | .i64ReinterpretF64 => pure .i64ReinterpretF64
        | .f64ReinterpretI64 => pure .f64ReinterpretI64

/-- Expose one certified step without unfolding the mutual recursion's
fuel-indexed implementation. -/
@[cbv_eval] theorem instructionAt_apply (fuel : Nat) (cursor : Cursor) :
    instructionAt fuel cursor = instructionStep fuel cursor := by
  cases fuel <;> rfl

#print axioms instructionAt_apply
end Wasm.Binary
