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

end LeanExe.Wasm.ScalarDescriptor
