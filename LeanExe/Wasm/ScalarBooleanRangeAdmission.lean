import LeanExe.Wasm.ScalarRangeExitAdmission
import LeanExe.Extract.ScalarBooleanRangeInvariant

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

/-- Every captured binding satisfies the arithmetic descriptor and read bound. -/
theorem extractScalarBooleanRangeWith_admitted {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith locals slot source = some plan)
    (bounded : ∀ binding ∈ locals, binding.Holds (ScalarArithmeticBounded (slot + 3))) :
    ∃ descriptor : RangeExit, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) := by
  have invariant : plan.Holds (ScalarArithmeticBounded (slot + 3)) :=
    extractScalarBooleanRangeWith_invariant _ (ScalarArithmeticBounded.literal _)
      (fun op _ _ => ScalarArithmeticBounded.primitive op)
      (fun op _ _ _ _ => ScalarArithmeticBounded.choice op)
      (ScalarArithmeticBounded.get slot (by omega))
      (ScalarArithmeticBounded.get (slot + 1) (by omega)) compiled bounded
  obtain ⟨⟨dc, hc, ac, bc⟩, ⟨di, hi, ai, bi⟩, ⟨ds, hs, aStep, bs⟩, ⟨dd, hd, ad, bd⟩, ⟨dr, hr, ar, br⟩⟩ := invariant
  exact ⟨⟨dc, di, ds, dd, dr⟩, ⟨hc, hi, hs, hd, hr⟩, ⟨ac, ai, aStep, ad, ar⟩, ⟨bc, bi, bs, bd, br⟩⟩

/-- Public Boolean normalization also stays within the captured argument slots. -/
theorem extractScalarBooleanRangePublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith (publicBindings inputs) slot source = some plan)
    (len : inputs.length = slot) :
    ∃ descriptor : RangeExit, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) :=
  extractScalarBooleanRangeWith_admitted compiled (ScalarArithmeticBounded.bindings inputs (by omega))


end LeanExe.Extract.Core
