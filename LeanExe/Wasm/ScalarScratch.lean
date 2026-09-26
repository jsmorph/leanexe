import LeanExe.Wasm.ScalarFunctionCertificate

namespace LeanExe.Wasm.ScalarDescriptor

mutual
  theorem Expr.ofIR_scratch {e : LeanExe.IR.Expr} {d : Expr}
      (recognized : Expr.ofIR e = some d) :
      Binary.CoreWasm.exprScratch e = d.scratchWidth := by
    cases e <;>
      simp only [Expr.ofIR, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq, reduceCtorEq] at recognized
    case «local» index =>
      subst d
      simp [Binary.CoreWasm.exprScratch, Expr.scratchWidth]
    case u64 value =>
      subst d
      simp [Binary.CoreWasm.exprScratch, Expr.scratchWidth]
    case u64Bin op a b =>
      obtain ⟨dop, hop, da, ha, db, hb, rfl⟩ := recognized
      have ia := Expr.ofIR_scratch ha
      have ib := Expr.ofIR_scratch hb
      cases op <;> simp [U64Op.ofIR] at hop <;> subst dop <;>
        simp [Binary.CoreWasm.exprScratch, Expr.scratchWidth, ia, ib,
          BEq.beq, instBEqU64Op, instBEqU64Op.beq, U64Op.ctorIdx, Nat.add_comm]
    case ite c a b =>
      obtain ⟨dc, hc, da, ha, db, hb, rfl⟩ := recognized
      simp [Binary.CoreWasm.exprScratch, Expr.scratchWidth,
        Cond.ofIR_scratch hc, Expr.ofIR_scratch ha, Expr.ofIR_scratch hb]
  termination_by sizeOf e

  theorem Cond.ofIR_scratch {c : LeanExe.IR.Cond} {d : Cond}
      (recognized : Cond.ofIR c = some d) :
      Binary.CoreWasm.condScratch c = d.scratchWidth := by
    cases c with
    | true | false =>
      simp only [Cond.ofIR, Option.some.injEq] at recognized
      subst d
      simp [Binary.CoreWasm.condScratch, Cond.scratchWidth]
    | eqU64 a b | ltU64 a b | leU64 a b =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨da, ha, db, hb, rfl⟩ := recognized
      simp [Binary.CoreWasm.condScratch, Cond.scratchWidth, Expr.ofIR_scratch ha, Expr.ofIR_scratch hb]
    | not c =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨dc, hc, rfl⟩ := recognized
      simpa [Binary.CoreWasm.condScratch, Cond.scratchWidth] using Cond.ofIR_scratch hc
    | and a b | or a b =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨da, ha, db, hb, rfl⟩ := recognized
      simp [Binary.CoreWasm.condScratch, Cond.scratchWidth, Cond.ofIR_scratch ha, Cond.ofIR_scratch hb]
  termination_by sizeOf c
end

theorem scalarFunc_scratch (arity : Nat) (name : Lean.Name) (exportName : Option String)
    {expression : LeanExe.IR.Expr} {descriptor : Expr}
    (recognized : Expr.ofIR expression = some descriptor) :
    Binary.CoreWasm.funcScratch
      (LeanExe.Extract.Core.scalarFunc name exportName arity expression) = descriptor.scratchWidth := by
  simp [LeanExe.Extract.Core.scalarFunc, Binary.CoreWasm.funcScratch,
    Binary.CoreWasm.stmtScratch, Binary.CoreWasm.exprScratch, Expr.ofIR_scratch recognized]

end LeanExe.Wasm.ScalarDescriptor
