import LeanExe.Wasm.ScalarAdmission
import LeanExe.Wasm.ScalarSemantics

namespace LeanExe.Wasm.ScalarDescriptor

inductive Expr.Arithmetic : Expr → Prop where
  | get : Arithmetic (.get index)
  | const : Arithmetic (.const value)
  | bin (left : Arithmetic a) (right : Arithmetic b) : Arithmetic (.bin op a b)
  | choose (op : LeanExe.Source.Scalar.Comparison)
      (left : Arithmetic a) (right : Arithmetic b) (onTrue : Arithmetic t) (onFalse : Arithmetic e) :
      Arithmetic (.ite (comparison op a b) t e)

end LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

theorem extractScalarExpr_arithmetic {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    ∃ descriptor, Expr.ofIR target = some descriptor ∧ descriptor.Arithmetic := by
  refine extractScalarExprWith_invariant
    (fun expression => ∃ descriptor, Expr.ofIR expression = some descriptor ∧ descriptor.Arithmetic)
    (fun _ => ⟨_, rfl, .const⟩) ?_ ?_ compiled ?_
  · intro p a b ha hb
    obtain ⟨da, hda, aa⟩ := ha
    obtain ⟨db, hdb, ab⟩ := hb
    obtain ⟨dop, hop⟩ := p.descriptor
    exact ⟨.bin dop da db, by simp [ScalarPrimitive.lower, Expr.ofIR, hop, hda, hdb], .bin aa ab⟩
  · intro op a b t e ha hb ht he
    obtain ⟨da, hda, aa⟩ := ha
    obtain ⟨db, hdb, ab⟩ := hb
    obtain ⟨dt, hdt, aTrue⟩ := ht
    obtain ⟨de, hde, ae⟩ := he
    exact ⟨.ite (comparison op da db) dt de, by
      simp [Expr.ofIR, lowerComparison_descriptor op hda hdb, hdt, hde], .choose op aa ab aTrue ae⟩
  · intro expression member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    exact ⟨_, rfl, .get⟩

end LeanExe.Extract.Core
