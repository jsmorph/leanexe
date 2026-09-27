import LeanExe.Wasm.ScalarRangeExitCertificate
import LeanExe.Extract.ScalarSequencePlan

namespace LeanExe.Wasm.ScalarDescriptor

/-- Descriptors for consecutive loops using the existing scalar instruction forms. -/
inductive LoopSequence where
  | leaf (descriptor : RangeExit)
  | bind (first second : LoopSequence)

namespace LoopSequence

def width : LoopSequence → Nat
  | .leaf _ => 4
  | .bind first second => first.width + second.width

def scratchWidth : LoopSequence → Nat
  | .leaf descriptor => descriptor.scratchWidth
  | .bind first second => max first.scratchWidth second.scratchWidth

def program : LoopSequence → Nat → Program
  | .leaf descriptor, slot => descriptor.program slot
  | .bind first second, slot => .seq (first.program slot) (second.program (slot + first.width))

inductive Matches : LoopSequence → LeanExe.Extract.Core.ScalarSequencePlan → Prop where
  | leaf (matched : descriptor.Matches plan) : Matches (.leaf descriptor) (.leaf plan)
  | bind (first : Matches a x) (second : Matches b y) : Matches (.bind a b) (.bind x y)

theorem Matches.width {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) : descriptor.width = plan.width := by
  induction matched with
  | leaf => rfl
  | bind first second ih₁ ih₂ => simp [LoopSequence.width, LeanExe.Extract.Core.ScalarSequencePlan.width, ih₁, ih₂]

private theorem body_not_scalar (plan : LeanExe.Extract.Core.ScalarSequencePlan) (slot : Nat) :
    Stmt.ofIR (plan.body slot) = none := by
  induction plan generalizing slot with
  | leaf plan =>
    simp [LeanExe.Extract.Core.ScalarSequencePlan.body, LeanExe.Extract.Core.ScalarRangeExitPlan.body,
      Stmt.ofIR, Bind.bind]
  | bind first second firstIH secondIH =>
    simp [LeanExe.Extract.Core.ScalarSequencePlan.body, Stmt.ofIR, Bind.bind, firstIH]

theorem Matches.ofIR_program {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) (slot : Nat) :
    Program.ofIR (plan.body slot) = some (descriptor.program slot) := by
  induction matched generalizing slot with
  | leaf matched => exact RangeExit.ofIR_program matched slot
  | bind first second firstIH secondIH =>
    rw [LeanExe.Extract.Core.ScalarSequencePlan.body, Program.ofIR.eq_def]
    simp only [While.ofIR, Stmt.ofIR, body_not_scalar, Bind.bind, Option.bind_none]
    simp only [firstIH, secondIH, program, first.width, pure, Option.bind_some]

end LoopSequence

/-- Range body emission is independent of the surrounding function's local count. -/
theorem RangeExit.body_emit {descriptor : RangeExit} {plan : LeanExe.Extract.Core.ScalarRangeExitPlan}
    (matched : descriptor.Matches plan) (releaseIndex scratch slot : Nat) :
    (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch (plan.body slot)).code =
      (descriptor.program slot).emit scratch := by
  obtain ⟨hc, hi, hs, hd, hr⟩ := matched
  have assign (index : Nat) (value : LeanExe.IR.Expr) (d : Expr)
      (h : Expr.ofIR value = some d) :
      Binary.CoreWasm.emitStmt releaseIndex scratch (.assign index value) =
        d.emit scratch ++ [.localSet index] :=
    Stmt.ofIR_emit releaseIndex scratch _ (.assign index d) (by simp [Stmt.ofIR, h])
  simp only [LeanExe.Extract.Core.ScalarRangeExitPlan.body, annotated_seq]
  rw [annotated_while releaseIndex scratch _ _ (.ltU (.get (slot + 1)) (.get (slot + 2)))
    (by simp [LeanExe.IR.rangeCondition, Cond.ofIR, Expr.ofIR])]
  simp only [LeanExe.IR.rangeExitBody, annotated_seq, annotated_assign]
  rw [assign _ _ _ hc, assign _ _ _ hi, assign _ _ (.const 0) rfl,
    assign _ _ (.const 0) rfl, assign _ _ _ hd, assign _ _ _ hs,
    assign _ _ (RangeExit.index slot) rfl, assign _ _ _ hr]
  simp [RangeExit.program, Program.emit, RangeExit.loop, RangeExit.index, While.emit, Stmt.emit,
    List.append_assoc]

theorem RangeExit.body_scratch {descriptor : RangeExit} {plan : LeanExe.Extract.Core.ScalarRangeExitPlan}
    (matched : descriptor.Matches plan) (slot : Nat) :
    Binary.CoreWasm.stmtScratch (plan.body slot) = descriptor.scratchWidth := by
  obtain ⟨hc, hi, hs, hd, hr⟩ := matched
  simp [LeanExe.Extract.Core.ScalarRangeExitPlan.body,
    Binary.CoreWasm.stmtScratch, Binary.CoreWasm.exprScratch, Binary.CoreWasm.condScratch,
    Expr.ofIR_scratch hc, Expr.ofIR_scratch hi, Expr.ofIR_scratch hs, Expr.ofIR_scratch hd,
    Expr.ofIR_scratch hr, RangeExit.scratchWidth, LeanExe.IR.rangeExitBody,
    LeanExe.IR.rangeExitIndex, LeanExe.IR.rangeCondition, Nat.max_assoc]

namespace LoopSequence

theorem Matches.body_emit {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) (releaseIndex scratch slot : Nat) :
    (Binary.CoreWasm.emitStmtAnnotated releaseIndex scratch (plan.body slot)).code =
      (descriptor.program slot).emit scratch := by
  induction matched generalizing slot with
  | leaf matched => exact RangeExit.body_emit matched releaseIndex scratch slot
  | bind first second firstIH secondIH =>
    simp only [LeanExe.Extract.Core.ScalarSequencePlan.body, annotated_seq, firstIH, secondIH,
      program, Program.emit, first.width]

theorem Matches.body_scratch {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) (slot : Nat) :
    Binary.CoreWasm.stmtScratch (plan.body slot) = descriptor.scratchWidth := by
  induction matched generalizing slot with
  | leaf matched => exact RangeExit.body_scratch matched slot
  | bind first second firstIH secondIH =>
    simp only [LeanExe.Extract.Core.ScalarSequencePlan.body, Binary.CoreWasm.stmtScratch,
      firstIH, secondIH, scratchWidth]

theorem Matches.func_emit {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) (releaseIndex arity : Nat) (name : Lean.Name)
    (exportName : Option String) :
    Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName arity) =
      (descriptor.program arity).emit (arity + plan.width) ++
        [.localGet (plan.resultSlot arity), .localSet arity, .localGet arity] := by
  change (Binary.CoreWasm.emitStmtAnnotated releaseIndex (arity + plan.width)
    (.seq (plan.body arity) (.assign arity (.local (plan.resultSlot arity))))).code ++
    Binary.CoreWasm.emitExprWithRelease releaseIndex (arity + plan.width) (.local arity) = _
  rw [annotated_seq, matched.body_emit]
  simp [annotated_assign, Binary.CoreWasm.emitStmt, Binary.CoreWasm.emitExprWithRelease,
    While.ofIR, Stmt.ofIR, Expr.ofIR, Stmt.emit, Expr.emit, List.append_assoc]

theorem Matches.func_scratch {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) (arity : Nat) (name : Lean.Name) (exportName : Option String) :
    Binary.CoreWasm.funcScratch (plan.func name exportName arity) = descriptor.scratchWidth := by
  simp [LeanExe.Extract.Core.ScalarSequencePlan.func, Binary.CoreWasm.funcScratch,
    Binary.CoreWasm.stmtScratch, Binary.CoreWasm.exprScratch, matched.body_scratch]

end LoopSequence
end LeanExe.Wasm.ScalarDescriptor
