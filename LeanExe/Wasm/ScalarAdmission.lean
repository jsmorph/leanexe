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
  refine extractScalarExprWith_invariant
    (fun expression => ∃ descriptor,
      LeanExe.Wasm.ScalarDescriptor.Expr.ofIR expression = some descriptor)
    (fun _ => ⟨_, rfl⟩) ?_ compiled ?_
  · intro p a b ha hb
    obtain ⟨da, hda⟩ := ha
    obtain ⟨db, hdb⟩ := hb
    obtain ⟨dop, hop⟩ := p.descriptor
    exact ⟨.bin dop da db, by simp [ScalarPrimitive.lower,
      LeanExe.Wasm.ScalarDescriptor.Expr.ofIR, hop, hda, hdb]⟩
  · intro expression member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    exact ⟨_, rfl⟩

end LeanExe.Extract.Core
