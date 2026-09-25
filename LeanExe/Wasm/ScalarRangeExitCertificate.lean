import LeanExe.Extract.ScalarRangeExit
import LeanExe.Wasm.ScalarScratch
import LeanExe.Wasm.ScalarAnnotatedCertificate

namespace LeanExe.Wasm.ScalarDescriptor

/-- The five pure expressions in one extracted range function. -/
structure RangeExit where
  count : Expr
  initial : Expr
  step : Expr
  done : Expr
  result : Expr

def RangeExit.Matches (descriptor : RangeExit) (plan : LeanExe.Extract.Core.ScalarRangeExitPlan) : Prop :=
  Expr.ofIR plan.count = some descriptor.count ∧
  Expr.ofIR plan.initial = some descriptor.initial ∧
  Expr.ofIR plan.step = some descriptor.step ∧
  Expr.ofIR plan.done = some descriptor.done ∧
  Expr.ofIR plan.result = some descriptor.result

def RangeExit.setup (descriptor : RangeExit) (slot : Nat) : Stmt :=
  .seq (.assign (slot + 2) descriptor.count)
    (.seq (.assign slot descriptor.initial)
      (.seq (.assign (slot + 1) (.const 0)) (.assign (slot + 3) (.const 0))))

def RangeExit.index (slot : Nat) : Expr :=
  .ite (.eq (.get (slot + 3)) (.const 0))
    (.bin .add (.get (slot + 1)) (.const 1)) (.get (slot + 2))

def RangeExit.loop (descriptor : RangeExit) (slot : Nat) : While :=
  { condition := .ltU (.get (slot + 1)) (.get (slot + 2))
    body := .seq (.assign (slot + 3) descriptor.done)
      (.seq (.assign slot descriptor.step) (.assign (slot + 1) (RangeExit.index slot))) }

def RangeExit.program (descriptor : RangeExit) (slot : Nat) : Program :=
  .seq (.scalar (.assign (slot + 2) descriptor.count))
    (.seq (.scalar (.assign slot descriptor.initial))
      (.seq (.scalar (.assign (slot + 1) (.const 0)))
        (.seq (.scalar (.assign (slot + 3) (.const 0)))
          (.seq (.loop (descriptor.loop slot)) (.scalar (.assign slot descriptor.result))))))

def RangeExit.scratchWidth (descriptor : RangeExit) : Nat :=
  max descriptor.count.scratchWidth
    (max descriptor.initial.scratchWidth (max descriptor.done.scratchWidth (max descriptor.step.scratchWidth descriptor.result.scratchWidth)))

theorem RangeExit.ofIR_program {descriptor : RangeExit} {plan : LeanExe.Extract.Core.ScalarRangeExitPlan}
    (matched : descriptor.Matches plan) (slot : Nat) :
    Program.ofIR (plan.body slot) = some (descriptor.program slot) := by
  obtain ⟨hc, hi, hs, hd, hr⟩ := matched
  simp [LeanExe.Extract.Core.ScalarRangeExitPlan.body, Program.ofIR.eq_def,
    While.ofIR, Stmt.ofIR, Expr.ofIR, Cond.ofIR, U64Op.ofIR,
    hc, hi, hs, hd, hr, RangeExit.program, RangeExit.loop, RangeExit.index,
    LeanExe.IR.rangeExitBody, LeanExe.IR.rangeExitIndex, LeanExe.IR.rangeCondition]

theorem RangeExit.func_emit {descriptor : RangeExit} {plan : LeanExe.Extract.Core.ScalarRangeExitPlan}
    (matched : descriptor.Matches plan) (releaseIndex arity : Nat) (name : Lean.Name)
    (exportName : Option String) :
    Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName arity) =
      (descriptor.setup arity).emit (arity + 4) ++ (descriptor.loop arity).emit (arity + 4) ++
        descriptor.result.emit (arity + 4) ++ [.localSet arity, .localGet arity] := by
  obtain ⟨hc, hi, hs, hd, hr⟩ := matched
  change (Binary.CoreWasm.emitStmtAnnotated releaseIndex (arity + 4) (plan.body arity)).code ++
    Binary.CoreWasm.emitExprWithRelease releaseIndex (arity + 4) (.local arity) = _
  have assign (index : Nat) (value : LeanExe.IR.Expr) (d : Expr)
      (h : Expr.ofIR value = some d) :
      Binary.CoreWasm.emitStmt releaseIndex (arity + 4) (.assign index value) =
        d.emit (arity + 4) ++ [.localSet index] :=
    Stmt.ofIR_emit releaseIndex (arity + 4) _ (.assign index d) (by simp [Stmt.ofIR, h])
  simp only [LeanExe.Extract.Core.ScalarRangeExitPlan.body, annotated_seq]
  rw [annotated_while releaseIndex (arity + 4) _ _ (.ltU (.get (arity + 1)) (.get (arity + 2)))
    (by simp [LeanExe.IR.rangeCondition, Cond.ofIR, Expr.ofIR])]
  simp only [LeanExe.IR.rangeExitBody, annotated_seq, annotated_assign]
  rw [assign _ _ _ hc, assign _ _ _ hi, assign _ _ (.const 0) rfl,
    assign _ _ (.const 0) rfl, assign _ _ _ hd, assign _ _ _ hs,
    assign _ _ (RangeExit.index arity) rfl, assign _ _ _ hr]
  simp [RangeExit.setup, RangeExit.loop, RangeExit.index, While.emit, Stmt.emit,
    Binary.CoreWasm.emitExprWithRelease, Expr.ofIR, Expr.emit, List.append_assoc]

theorem RangeExit.func_scratch {descriptor : RangeExit} {plan : LeanExe.Extract.Core.ScalarRangeExitPlan}
    (matched : descriptor.Matches plan) (arity : Nat) (name : Lean.Name) (exportName : Option String) :
    Binary.CoreWasm.funcScratch (plan.func name exportName arity) = descriptor.scratchWidth := by
  obtain ⟨hc, hi, hs, hd, hr⟩ := matched
  simp [LeanExe.Extract.Core.ScalarRangeExitPlan.func, LeanExe.Extract.Core.ScalarRangeExitPlan.body,
    Binary.CoreWasm.funcScratch, Binary.CoreWasm.stmtScratch, Binary.CoreWasm.exprScratch,
    Binary.CoreWasm.condScratch, Expr.ofIR_scratch hc, Expr.ofIR_scratch hi,
    Expr.ofIR_scratch hs, Expr.ofIR_scratch hd, Expr.ofIR_scratch hr, RangeExit.scratchWidth,
    LeanExe.IR.rangeExitBody, LeanExe.IR.rangeExitIndex, LeanExe.IR.rangeCondition, Nat.max_assoc]

end LeanExe.Wasm.ScalarDescriptor
