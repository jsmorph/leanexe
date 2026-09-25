import LeanExe.Extract.ScalarRange
import LeanExe.Wasm.ScalarScratch
import LeanExe.Wasm.ScalarAnnotatedCertificate

namespace LeanExe.Wasm.ScalarDescriptor

/-- The four pure expressions in one extracted range function. -/
structure Range where
  count : Expr
  initial : Expr
  step : Expr
  result : Expr

def Range.Matches (descriptor : Range) (plan : LeanExe.Extract.Core.ScalarRangePlan) : Prop :=
  Expr.ofIR plan.count = some descriptor.count ∧
  Expr.ofIR plan.initial = some descriptor.initial ∧
  Expr.ofIR plan.step = some descriptor.step ∧
  Expr.ofIR plan.result = some descriptor.result

def Range.setup (descriptor : Range) (slot : Nat) : Stmt :=
  .seq (.assign (slot + 2) descriptor.count)
    (.seq (.assign slot descriptor.initial) (.assign (slot + 1) (.const 0)))

def Range.loop (descriptor : Range) (slot : Nat) : While :=
  { condition := .ltU (.get (slot + 1)) (.get (slot + 2))
    body := .seq (.assign slot descriptor.step)
      (.assign (slot + 1) (.bin .add (.get (slot + 1)) (.const 1))) }

def Range.program (descriptor : Range) (slot : Nat) : Program :=
  .seq (.scalar (.assign (slot + 2) descriptor.count))
    (.seq (.scalar (.assign slot descriptor.initial))
      (.seq (.scalar (.assign (slot + 1) (.const 0)))
        (.seq (.loop (descriptor.loop slot)) (.scalar (.assign slot descriptor.result)))))

def Range.scratchWidth (descriptor : Range) : Nat :=
  max descriptor.count.scratchWidth
    (max descriptor.initial.scratchWidth (max descriptor.step.scratchWidth descriptor.result.scratchWidth))

theorem Range.ofIR_program {descriptor : Range} {plan : LeanExe.Extract.Core.ScalarRangePlan}
    (matched : descriptor.Matches plan) (slot : Nat) :
    Program.ofIR (plan.body slot) = some (descriptor.program slot) := by
  obtain ⟨hc, hi, hs, hr⟩ := matched
  simp [LeanExe.Extract.Core.ScalarRangePlan.body, Program.ofIR.eq_def,
    While.ofIR, Stmt.ofIR, Expr.ofIR, Cond.ofIR, U64Op.ofIR,
    hc, hi, hs, hr, Range.program, Range.loop]

theorem Range.func_emit {descriptor : Range} {plan : LeanExe.Extract.Core.ScalarRangePlan}
    (matched : descriptor.Matches plan) (releaseIndex arity : Nat) (name : Lean.Name)
    (exportName : Option String) :
    Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName arity) =
      (descriptor.setup arity).emit (arity + 3) ++ (descriptor.loop arity).emit (arity + 3) ++
        descriptor.result.emit (arity + 3) ++ [.localSet arity, .localGet arity] := by
  obtain ⟨hc, hi, hs, hr⟩ := matched
  change (Binary.CoreWasm.emitStmtAnnotated releaseIndex (arity + 3) (plan.body arity)).code ++
    Binary.CoreWasm.emitExprWithRelease releaseIndex (arity + 3) (.local arity) = _
  have assign (index : Nat) (value : LeanExe.IR.Expr) (d : Expr)
      (h : Expr.ofIR value = some d) :
      Binary.CoreWasm.emitStmt releaseIndex (arity + 3) (.assign index value) =
        d.emit (arity + 3) ++ [.localSet index] :=
    Stmt.ofIR_emit releaseIndex (arity + 3) _ (.assign index d) (by simp [Stmt.ofIR, h])
  simp only [LeanExe.Extract.Core.ScalarRangePlan.body, annotated_seq]
  rw [annotated_while releaseIndex (arity + 3) _ _ (.ltU (.get (arity + 1)) (.get (arity + 2)))
    (by simp [Cond.ofIR, Expr.ofIR])]
  simp only [annotated_seq, annotated_assign]
  rw [assign _ _ _ hc, assign _ _ _ hi, assign _ _ (.const 0) rfl,
    assign _ _ _ hs, assign _ _ (.bin .add (.get (arity + 1)) (.const 1)) rfl, assign _ _ _ hr]
  simp [Range.setup, Range.loop, While.emit, Stmt.emit,
    Binary.CoreWasm.emitExprWithRelease, Expr.ofIR, Expr.emit, List.append_assoc]

theorem Range.func_scratch {descriptor : Range} {plan : LeanExe.Extract.Core.ScalarRangePlan}
    (matched : descriptor.Matches plan) (arity : Nat) (name : Lean.Name) (exportName : Option String) :
    Binary.CoreWasm.funcScratch (plan.func name exportName arity) = descriptor.scratchWidth := by
  obtain ⟨hc, hi, hs, hr⟩ := matched
  simp [LeanExe.Extract.Core.ScalarRangePlan.func, LeanExe.Extract.Core.ScalarRangePlan.body,
    Binary.CoreWasm.funcScratch, Binary.CoreWasm.stmtScratch, Binary.CoreWasm.exprScratch,
    Binary.CoreWasm.condScratch, Expr.ofIR_scratch hc, Expr.ofIR_scratch hi,
    Expr.ofIR_scratch hs, Expr.ofIR_scratch hr, Range.scratchWidth]

end LeanExe.Wasm.ScalarDescriptor
