import LeanExe.Extract.ScalarFunc
import LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Wasm.ScalarDescriptor

def comparison : LeanExe.Source.Scalar.Comparison → Expr → Expr → Cond
  | .eq, a, b => .eq a b
  | .lt, a, b => .ltU a b
  | .le, a, b => .leU a b
  | .gt, a, b => .not (.leU a b)
  | .ge, a, b => .not (.ltU a b)
  | .beq, a, b => .eq a b
  | .bne, a, b => .not (.eq a b)

@[simp] theorem comparison_reads (op : LeanExe.Source.Scalar.Comparison) (a b : Expr) :
    (comparison op a b).reads = a.reads ++ b.reads := by
  cases op <;> rfl

@[simp] theorem comparison_scratch (op : LeanExe.Source.Scalar.Comparison) (a b : Expr) :
    (comparison op a b).scratchWidth = max a.scratchWidth b.scratchWidth := by
  cases op <;> rfl

end LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

theorem ScalarPrimitive.descriptor (op : ScalarPrimitive) :
    ∃ descriptor, U64Op.ofIR op.toIR = some descriptor := by
  cases op <;> exact ⟨_, rfl⟩

theorem lowerComparison_descriptor (op : LeanExe.Source.Scalar.Comparison)
    {a b : LeanExe.IR.Expr} {da db : Expr}
    (ha : Expr.ofIR a = some da) (hb : Expr.ofIR b = some db) :
    Cond.ofIR (lowerComparison op a b) = some (comparison op da db) := by
  cases op <;> simp [lowerComparison, comparison, Cond.ofIR, ha, hb]

/-- The proved production source traversal produces IR accepted by the scalar
backend recognizer, including both branches of nested conditionals. -/
theorem extractScalarExpr_descriptor {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    ∃ descriptor, Expr.ofIR target = some descriptor := by
  refine extractScalarExprWith_invariant
    (fun expression => ∃ descriptor, Expr.ofIR expression = some descriptor)
    (fun _ => ⟨_, rfl⟩) ?_ ?_ compiled ?_
  · intro p a b ha hb
    obtain ⟨da, hda⟩ := ha
    obtain ⟨db, hdb⟩ := hb
    obtain ⟨dop, hop⟩ := p.descriptor
    exact ⟨.bin dop da db, by simp [ScalarPrimitive.lower, Expr.ofIR, hop, hda, hdb]⟩
  · intro op a b t e ha hb ht he
    obtain ⟨da, hda⟩ := ha
    obtain ⟨db, hdb⟩ := hb
    obtain ⟨dt, hdt⟩ := ht
    obtain ⟨de, hde⟩ := he
    exact ⟨.ite (comparison op da db) dt de, by
      simp [Expr.ofIR, lowerComparison_descriptor op hda hdb, hdt, hde]⟩
  · intro expression member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    exact ⟨_, rfl⟩

/-- Static bounds cover reads in both branches, including an unexecuted branch. -/
theorem extractScalarExpr_reads {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} {descriptor : Expr} {count : Nat}
    (compiled : extractScalarExpr locals source = some target)
    (recognized : Expr.ofIR target = some descriptor)
    (bounded : ∀ slot ∈ locals, slot < count) :
    ∀ index ∈ descriptor.reads, index < count := by
  have invariant : ∃ d, Expr.ofIR target = some d ∧ ∀ index ∈ d.reads, index < count := by
    refine extractScalarExprWith_invariant
      (fun expression => ∃ d, Expr.ofIR expression = some d ∧ ∀ index ∈ d.reads, index < count)
      (fun _ => ⟨_, rfl, by simp [Expr.reads]⟩) ?_ ?_ compiled ?_
    · intro p a b ha hb
      obtain ⟨da, hda, ba⟩ := ha
      obtain ⟨db, hdb, bb⟩ := hb
      obtain ⟨dop, hop⟩ := p.descriptor
      refine ⟨.bin dop da db, by simp [ScalarPrimitive.lower, Expr.ofIR, hop, hda, hdb], ?_⟩
      intro index member
      rcases List.mem_append.mp member with member | member
      · exact ba index member
      · exact bb index member
    · intro op a b t e ha hb ht he
      obtain ⟨da, hda, ba⟩ := ha
      obtain ⟨db, hdb, bb⟩ := hb
      obtain ⟨dt, hdt, bt⟩ := ht
      obtain ⟨de, hde, be⟩ := he
      refine ⟨.ite (comparison op da db) dt de, by
        simp [Expr.ofIR, lowerComparison_descriptor op hda hdb, hdt, hde], ?_⟩
      intro index member
      simp only [Expr.reads, comparison_reads, List.mem_append] at member
      rcases member with ((member | member) | member) | member
      · exact ba index member
      · exact bb index member
      · exact bt index member
      · exact be index member
    · intro expression member
      obtain ⟨slot, hs, rfl⟩ := List.mem_map.mp member
      exact ⟨.get slot, rfl, by simpa [Expr.reads] using bounded slot hs⟩
  obtain ⟨d, hd, bounds⟩ := invariant
  have same : d = descriptor := Option.some.inj (hd.symm.trans recognized)
  simpa [same] using bounds

end LeanExe.Extract.Core
