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
  refine extractScalarExprWith_invariant
    (fun expression => ∃ descriptor,
      LeanExe.Wasm.ScalarDescriptor.Expr.ofIR expression = some descriptor ∧ descriptor.Arithmetic)
    (fun _ => ⟨_, rfl, .const⟩) ?_ compiled ?_
  · intro p a b ha hb
    obtain ⟨da, hda, aa⟩ := ha
    obtain ⟨db, hdb, ab⟩ := hb
    obtain ⟨dop, hop⟩ := p.descriptor
    exact ⟨.bin dop da db, by simp [ScalarPrimitive.lower,
      LeanExe.Wasm.ScalarDescriptor.Expr.ofIR, hop, hda, hdb], .bin aa ab⟩
  · intro expression member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    exact ⟨_, rfl, .get⟩

end LeanExe.Extract.Core
