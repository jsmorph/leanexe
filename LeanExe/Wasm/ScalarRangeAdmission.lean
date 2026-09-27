import LeanExe.Wasm.ScalarRangeCertificate
import LeanExe.Wasm.ScalarArithmeticBounds
import LeanExe.Extract.ScalarRangeInvariant

namespace LeanExe.Wasm.ScalarDescriptor

def Range.All (P : Expr → Prop) (descriptor : Range) : Prop :=
  P descriptor.count ∧ P descriptor.initial ∧ P descriptor.step ∧ P descriptor.result

end LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

/-- Every captured binding satisfies the arithmetic descriptor and read bound. -/
theorem extractScalarRangeWith_admitted {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith locals slot source = some plan)
    (bounded : ∀ binding ∈ locals, binding.Holds (ScalarArithmeticBounded (slot + 3))) :
    ∃ descriptor : Range, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) := by
  have invariant : plan.Holds (ScalarArithmeticBounded (slot + 3)) :=
    extractScalarRangeWith_invariant _ (ScalarArithmeticBounded.literal _)
      (fun op _ _ => ScalarArithmeticBounded.primitive op)
      (fun op _ _ _ _ => ScalarArithmeticBounded.choice op)
      (ScalarArithmeticBounded.get slot (by omega))
      (ScalarArithmeticBounded.get (slot + 1) (by omega)) compiled bounded
  obtain ⟨⟨dc, hc, ac, bc⟩, ⟨di, hi, ai, bi⟩, ⟨ds, hs, aStep, bs⟩, ⟨dr, hr, ar, br⟩⟩ := invariant
  exact ⟨⟨dc, di, ds, dr⟩, ⟨hc, hi, hs, hr⟩, ⟨ac, ai, aStep, ar⟩, ⟨bc, bi, bs, br⟩⟩

/-- The word-local specialization of arithmetic range admission. -/
theorem extractScalarRange_admitted {source : Lean.Expr} {locals : List Nat}
    {slot : Nat} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith (locals.map fun index => .word (.local index)) slot source = some plan)
    (bounded : ∀ index ∈ locals, index < slot) :
    ∃ descriptor : Range, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) := by
  apply extractScalarRangeWith_admitted compiled
  intro binding member
  obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
  exact ScalarArithmeticBounded.get index (Nat.lt_trans (bounded index present) (by omega))

/-- Public Boolean normalization also stays within the captured argument slots. -/
theorem extractScalarRangePublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {slot : Nat} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith (publicBindings inputs) slot source = some plan)
    (len : inputs.length = slot) :
    ∃ descriptor : Range, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) :=
  extractScalarRangeWith_admitted compiled (ScalarArithmeticBounded.bindings inputs (by omega))

end LeanExe.Extract.Core
