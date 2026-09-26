import LeanExe.Wasm.ScalarSemantics

namespace LeanExe.Wasm.ScalarDescriptor

/-- Loop-free scalar statements use finite, checked local reads and writes. -/
def Stmt.eval (store : LeanExe.IR.ScalarStore) : Stmt → Option LeanExe.IR.ScalarStore
  | .skip => some store
  | .assign index value => do
      let result ← value.eval store
      store.write index result
  | .seq first second => do
      let middle ← first.eval store
      second.eval middle
  | .ite condition yes no => do
      let result ← condition.eval store
      if result then yes.eval store else no.eval store

theorem Stmt.eval_length {statement : Stmt} {store next : LeanExe.IR.ScalarStore}
    (evaluated : statement.eval store = some next) : next.length = store.length := by
  induction statement generalizing store next with
  | skip => cases evaluated; rfl
  | assign index value =>
    simp only [Stmt.eval, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨result, _, written⟩ := evaluated
    exact LeanExe.IR.ScalarStore.write_length written
  | seq first second ihFirst ihSecond =>
    simp only [Stmt.eval, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨middle, firstEval, secondEval⟩ := evaluated
    exact (ihSecond secondEval).trans (ihFirst firstEval)
  | ite condition yes no ihYes ihNo =>
    simp only [Stmt.eval, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨result, _, branch⟩ := evaluated
    cases result
    · exact ihNo branch
    · exact ihYes branch

theorem Stmt.ofIR_eval {statement : LeanExe.IR.Stmt} {store next : LeanExe.IR.ScalarStore}
    (semantics : statement.ScalarEval store next) {descriptor : Stmt}
    (recognized : Stmt.ofIR statement = some descriptor) : descriptor.eval store = some next := by
  induction semantics generalizing descriptor with
  | skip =>
    simp only [Stmt.ofIR, Option.some.injEq] at recognized
    subst descriptor
    rfl
  | assign value written =>
    simp only [Stmt.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨e, he, rfl⟩ := recognized
    obtain ⟨evaluated, rfl⟩ := Expr.ofIR_eval value he
    simp [Stmt.eval, evaluated, written]
  | seq first second ihFirst ihSecond =>
    simp only [Stmt.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨a, ha, b, hb, rfl⟩ := recognized
    simp [Stmt.eval, ihFirst ha, ihSecond hb]
  | iteTrue condition branch ih | iteFalse condition branch ih =>
    simp only [Stmt.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := recognized
    obtain ⟨evaluated, rfl⟩ := Cond.ofIR_eval condition hc
    first
    | simpa [Stmt.eval, evaluated] using ih ha
    | simpa [Stmt.eval, evaluated] using ih hb
  | whileFalse | whileTrue => simp [Stmt.ofIR] at recognized

end LeanExe.Wasm.ScalarDescriptor
