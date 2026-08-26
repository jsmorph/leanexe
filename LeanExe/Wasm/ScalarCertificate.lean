import LeanExe.Wasm.Binary
import LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Wasm.ScalarDescriptor

open LeanExe.IR

theorem U64Op.ofIR_instruction
    {operation : LeanExe.IR.U64Op} {descriptor : U64Op}
    (hReify : U64Op.ofIR operation = some descriptor) :
    Binary.CoreWasm.emitU64Op operation = [descriptor.instruction] := by
  cases operation <;> simp [U64Op.ofIR] at hReify <;> subst descriptor <;> rfl

theorem Expr.ofIR_emitWithRelease
    (releaseIndex scratch : Nat) (expression : LeanExe.IR.Expr)
    (descriptor : Expr)
    (hReify : Expr.ofIR expression = some descriptor) :
    Binary.CoreWasm.emitExprWithRelease releaseIndex scratch expression =
      descriptor.emit scratch := by
  unfold Binary.CoreWasm.emitExprWithRelease
  rw [hReify]

theorem Cond.ofIR_emitWithRelease
    (releaseIndex scratch : Nat) (condition : LeanExe.IR.Cond)
    (descriptor : Cond)
    (hReify : Cond.ofIR condition = some descriptor) :
    Binary.CoreWasm.emitCondWithRelease releaseIndex scratch condition =
      descriptor.emit scratch := by
  unfold Binary.CoreWasm.emitCondWithRelease
  rw [hReify]

theorem Stmt.ofIR_emit
    (releaseIndex scratch : Nat) (statement : LeanExe.IR.Stmt)
    (descriptor : Stmt)
    (hReify : Stmt.ofIR statement = some descriptor) :
    Binary.CoreWasm.emitStmt releaseIndex scratch statement =
      descriptor.emit scratch := by
  have hWhile : While.ofIR statement = none := by
    cases statement <;> simp_all [Stmt.ofIR, While.ofIR]
  unfold Binary.CoreWasm.emitStmt
  rw [hWhile, hReify]

theorem While.ofIR_emit
    (releaseIndex scratch : Nat) (statement : LeanExe.IR.Stmt)
    (descriptor : While)
    (hReify : While.ofIR statement = some descriptor) :
    Binary.CoreWasm.emitStmt releaseIndex scratch statement =
      descriptor.emit scratch := by
  unfold Binary.CoreWasm.emitStmt
  rw [hReify]

theorem EncodedIndex.ofIR_emit
    (releaseIndex scratch : Nat) (statement : LeanExe.IR.Stmt)
    (descriptor : EncodedIndex)
    (hReify : EncodedIndex.ofIR statement = some descriptor) :
    Binary.CoreWasm.emitStmt releaseIndex scratch statement =
      descriptor.emit scratch := by
  have hAssign : ∃ decodedLocal expression,
      statement = .assign decodedLocal expression := by
    cases statement <;> simp_all [EncodedIndex.ofIR]
  obtain ⟨decodedLocal, expression, rfl⟩ := hAssign
  unfold EncodedIndex.ofIR EncodedIndex.ofExpr at hReify
  split at hReify
  · rename_i _ decodedLocal' expression' hStatement
    injection hStatement with hDecoded hExpression
    subst decodedLocal'
    subst expression'
    split at hReify
    · split at hReify
      · simp at hReify
        subst_vars
        unfold Binary.CoreWasm.emitStmt
        simp [While.ofIR, Stmt.ofIR, Expr.ofIR, Cond.ofIR, U64Op.ofIR,
          EncodedIndex.ofIR, EncodedIndex.ofExpr]
      · cases hReify
    · cases hReify
  · rename_i _ hNoAssignment
    exact False.elim (hNoAssignment decodedLocal expression rfl)

theorem EncodedIndex.ofProgramPrefix_emit
    (program : List Instr) (descriptor : EncodedIndex) (scratch : Nat)
    (hRecognize : EncodedIndex.ofProgramPrefix program = some (descriptor, scratch)) :
    ∃ suffix, program = descriptor.emit scratch ++ suffix := by
  cases descriptor
  unfold EncodedIndex.ofProgramPrefix at hRecognize
  split at hRecognize <;>
    simp_all [EncodedIndex.emit, EncodedIndex.emitValue, Bool.and_eq_true]

end LeanExe.Wasm.ScalarDescriptor
