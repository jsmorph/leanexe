import LeanExe.Wasm.ScalarScratch

namespace LeanExe.Wasm.ScalarDescriptor

def Program.scratchWidth : Program → Nat
  | .scalar statement => statement.scratchWidth
  | .loop descriptor => descriptor.scratchWidth
  | .seq first second => max first.scratchWidth second.scratchWidth

theorem Stmt.ofIR_scratch {statement : LeanExe.IR.Stmt} {descriptor : Stmt}
    (recognized : Stmt.ofIR statement = some descriptor) :
    Binary.CoreWasm.stmtScratch statement = descriptor.scratchWidth := by
  fun_induction Stmt.ofIR statement generalizing descriptor with
  | case1 => cases recognized; rfl
  | case2 index value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨expression, matched, rfl⟩ := recognized
    exact Expr.ofIR_scratch matched
  | case3 first second firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨a, ma, b, mb, rfl⟩ := recognized
    simp [Binary.CoreWasm.stmtScratch, Stmt.scratchWidth, firstIH ma, secondIH mb]
  | case4 condition yes no yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨c, mc, a, ma, b, mb, rfl⟩ := recognized
    simp [Binary.CoreWasm.stmtScratch, Stmt.scratchWidth, Cond.ofIR_scratch mc, yesIH ma, noIH mb]
  | case5 => contradiction

theorem While.ofIR_scratch {statement : LeanExe.IR.Stmt} {descriptor : While}
    (recognized : While.ofIR statement = some descriptor) :
    Binary.CoreWasm.stmtScratch statement = descriptor.scratchWidth := by
  cases statement <;> simp only [While.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at recognized
  obtain ⟨condition, mc, body, mb, rfl⟩ := recognized
  simp [Binary.CoreWasm.stmtScratch, While.scratchWidth, Cond.ofIR_scratch mc, Stmt.ofIR_scratch mb]

theorem Program.ofIR_scratch {statement : LeanExe.IR.Stmt} {descriptor : Program}
    (recognized : Program.ofIR statement = some descriptor) :
    Binary.CoreWasm.stmtScratch statement = descriptor.scratchWidth := by
  fun_induction Program.ofIR statement generalizing descriptor with
  | case1 statement loop matched => cases recognized; exact While.ofIR_scratch matched
  | case2 statement noLoop scalar matched => cases recognized; exact Stmt.ofIR_scratch matched
  | case3 first second noLoop noScalar firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨a, ma, b, mb, rfl⟩ := recognized
    simp [Binary.CoreWasm.stmtScratch, Program.scratchWidth, firstIH ma, secondIH mb]
  | case4 => contradiction

end LeanExe.Wasm.ScalarDescriptor
