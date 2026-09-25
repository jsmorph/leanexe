import LeanExe.Wasm.ScalarCertificate

namespace LeanExe.Wasm.ScalarDescriptor

/-- Annotation data does not change the instructions of a scalar assignment. -/
theorem annotated_assign (releaseIndex scratch index : Nat) (value : LeanExe.IR.Expr) :
    (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch (.assign index value)).code =
      Binary.CoreWasm.emitStmt releaseIndex scratch (.assign index value) := by
  rfl

/-- Sequence annotations may add facts about the combined statement, while its
instructions remain the concatenation of the two emitted child sequences. -/
theorem annotated_seq (releaseIndex scratch : Nat) (first second : LeanExe.IR.Stmt) :
    (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch (.seq first second)).code =
      (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch first).code ++
        (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch second).code := by
  simp only [Binary.CoreWasm.emitStmtAnnotated]
  split <;> rfl

theorem annotated_while (releaseIndex scratch : Nat) (condition : LeanExe.IR.Cond)
    (body : LeanExe.IR.Stmt) (descriptor : Cond)
    (matched : Cond.ofIR condition = some descriptor) :
    (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch (.while condition body)).code =
      [.block [.loop (descriptor.emit scratch ++ [.eqzI32, .brIf 1] ++
        (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch body).code ++ [.br 0])]] := by
  simp only [Binary.CoreWasm.emitStmtAnnotated, matched]

end LeanExe.Wasm.ScalarDescriptor
