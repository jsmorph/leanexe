import LeanExe.Wasm.ScalarAdmission
import LeanExe.Wasm.ScalarSemantics

namespace LeanExe.Wasm.ScalarDescriptor

inductive Expr.Arithmetic : Expr → Prop where
  | get : Arithmetic (.get index)
  | const : Arithmetic (.const value)
  | bin (left : Arithmetic a) (right : Arithmetic b) : Arithmetic (.bin op a b)

theorem Expr.Arithmetic.reads_bound {e : Expr} (arithmetic : e.Arithmetic)
    {store : LeanExe.IR.ScalarStore} {value : UInt64} (evaluation : e.eval store = some value) :
    ∀ index ∈ e.reads, index < store.length := by
  induction arithmetic generalizing value with
  | get =>
    intro index member
    simp only [Expr.reads, List.mem_singleton] at member
    subst index
    exact (List.getElem?_eq_some_iff.mp evaluation).1
  | const => simp [Expr.reads]
  | bin left right ihl ihr =>
    simp only [Expr.eval, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evaluation
    obtain ⟨x, hx, y, hy, _⟩ := evaluation
    intro index member
    simp only [Expr.reads, List.mem_append] at member
    exact member.elim (ihl hx index) (ihr hy index)

end LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core

theorem extractScalarExpr_arithmetic {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    ∃ descriptor, LeanExe.Wasm.ScalarDescriptor.Expr.ofIR target = some descriptor ∧ descriptor.Arithmetic := by
  have supported := extractScalarExpr_supported compiled
  generalize hlen : locals.length = arity at supported
  induction supported generalizing target with
  | var hi =>
    simp only [extractScalarExpr, Option.map_eq_some_iff] at compiled
    obtain ⟨slot, hs, rfl⟩ := compiled
    exact ⟨_, rfl, .get⟩
  | literal =>
    cases compiled
    exact ⟨_, rfl, .const⟩
  | ofNat =>
    simp only [extractScalarExpr_literalExpr, Option.some.injEq] at compiled
    subst target
    exact ⟨_, rfl, .const⟩
  | binary op _ _ ihl ihr =>
    rw [extractScalarExpr_binary op] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := compiled
    obtain ⟨da, hda, aa⟩ := ihl ha hlen
    obtain ⟨db, hdb, ab⟩ := ihr hb hlen
    obtain ⟨dop, hop⟩ := p.descriptor
    exact ⟨.bin dop da db, by simp [ScalarPrimitive.lower,
      LeanExe.Wasm.ScalarDescriptor.Expr.ofIR, hop, hda, hdb], .bin aa ab⟩
  | metadata _ ih => exact ih compiled hlen

end LeanExe.Extract.Core
