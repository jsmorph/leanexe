import LeanExe.Wasm.ArithmeticAdmission

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

/-- Typed public inputs, including Boolean normalization, produce arithmetic
WASM descriptors whose reads stay within the public argument slots. -/
theorem extractScalarPublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {target : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith (publicBindings inputs) source = some target) :
    ∃ descriptor, Expr.ofIR target = some descriptor ∧ descriptor.Arithmetic ∧
      ∀ index ∈ descriptor.reads, index < inputs.length := by
  let P := fun ir => ∃ descriptor, Expr.ofIR ir = some descriptor ∧ descriptor.Arithmetic ∧
    ∀ index ∈ descriptor.reads, index < inputs.length
  have literal (n : Nat) : P (.u64 n) := ⟨_, rfl, .const, by simp [Expr.reads]⟩
  have choice (op : LeanExe.Source.Scalar.Comparison) (a b t e : LeanExe.IR.Expr)
      (ha : P a) (hb : P b) (ht : P t) (he : P e) : P (.ite (lowerComparison op a b) t e) := by
    obtain ⟨da, hda, aa, ba⟩ := ha
    obtain ⟨db, hdb, ab, bb⟩ := hb
    obtain ⟨dt, hdt, aTrue, bt⟩ := ht
    obtain ⟨de, hde, ae, be⟩ := he
    refine ⟨.ite (comparison op da db) dt de, by
      simp [Expr.ofIR, lowerComparison_descriptor op hda hdb, hdt, hde], .choose op aa ab aTrue ae, ?_⟩
    intro index member
    simp only [Expr.reads, comparison_reads, List.mem_append] at member
    rcases member with ((member | member) | member) | member
    · exact ba index member
    · exact bb index member
    · exact bt index member
    · exact be index member
  refine extractScalarExprWith_invariant P literal ?_ choice compiled ?_
  · intro op a b ha hb
    obtain ⟨da, hda, aa, ba⟩ := ha
    obtain ⟨db, hdb, ab, bb⟩ := hb
    obtain ⟨dop, hop⟩ := op.descriptor
    refine ⟨.bin dop da db, by simp [ScalarPrimitive.lower, Expr.ofIR, hop, hda, hdb], .bin aa ab, ?_⟩
    intro index member
    rcases List.mem_append.mp member with member | member
    · exact ba index member
    · exact bb index member
  · apply publicBindingsFor_holds P literal choice
    intro slot member
    exact ⟨.get slot, rfl, .get, by simpa [Expr.reads] using member⟩

end LeanExe.Extract.Core
