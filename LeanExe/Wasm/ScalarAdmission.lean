import LeanExe.Extract.ScalarFunc
import LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core

theorem ScalarPrimitive.descriptor (op : ScalarPrimitive) :
    ∃ descriptor, LeanExe.Wasm.ScalarDescriptor.U64Op.ofIR op.toIR = some descriptor := by
  cases op <;> exact ⟨_, rfl⟩

/-- The proved production source traversal always produces IR accepted by the
existing scalar backend recognizer. This is a property of all source trees,
not an extra success hypothesis on programs. -/
theorem extractScalarExpr_descriptor {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    ∃ descriptor, LeanExe.Wasm.ScalarDescriptor.Expr.ofIR target = some descriptor := by
  have supported := extractScalarExpr_supported compiled
  generalize hlen : locals.length = arity at supported
  induction supported generalizing target with
  | var hi =>
    simp only [extractScalarExpr, Option.map_eq_some_iff] at compiled
    obtain ⟨slot, hs, rfl⟩ := compiled
    exact ⟨_, rfl⟩
  | literal =>
    cases compiled
    exact ⟨_, rfl⟩
  | ofNat =>
    simp only [extractScalarExpr_literalExpr, Option.some.injEq] at compiled
    subst target
    exact ⟨_, rfl⟩
  | binary op _ _ ihl ihr =>
    rw [extractScalarExpr_binary op] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := compiled
    obtain ⟨da, hda⟩ := ihl ha hlen
    obtain ⟨db, hdb⟩ := ihr hb hlen
    obtain ⟨dop, hop⟩ := p.descriptor
    exact ⟨.bin dop da db, by simp [ScalarPrimitive.lower,
      LeanExe.Wasm.ScalarDescriptor.Expr.ofIR, hop, hda, hdb]⟩
  | metadata _ ih => exact ih compiled hlen

end LeanExe.Extract.Core
