import LeanExe.Wasm.ScalarCertificate
import LeanExe.Extract.ScalarFunc

namespace LeanExe.Wasm.ScalarDescriptor

/-- Exact instructions produced by the normal function emitter for the scalar
declaration case, including its result-slot ABI. -/
theorem scalarFunc_emit (releaseIndex arity : Nat) (name : Lean.Name)
    (exportName : Option String) (expression : LeanExe.IR.Expr) (descriptor : Expr)
    (recognized : Expr.ofIR expression = some descriptor) :
    Binary.CoreWasm.emitFuncInstrs releaseIndex
      (LeanExe.Extract.Core.scalarFunc name exportName arity expression) =
      descriptor.emit (arity + 1) ++ [.localSet arity, .localGet arity] := by
  change Binary.CoreWasm.emitStmt releaseIndex (arity + 1) (.assign arity expression) ++
    Binary.CoreWasm.emitExprWithRelease releaseIndex (arity + 1) (.local arity) = _
  rw [Stmt.ofIR_emit releaseIndex (arity + 1) (.assign arity expression)
    (.assign arity descriptor) (by simp [Stmt.ofIR, recognized])]
  simp [Stmt.emit, Binary.CoreWasm.emitExprWithRelease, Expr.ofIR, Expr.emit, List.append_assoc]

end LeanExe.Wasm.ScalarDescriptor
