import LeanExe.Wasm.ScalarBooleanRangeAdmission
import LeanExe.Extract.ScalarWordRange

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

/-- Every captured binding satisfies the arithmetic descriptor and read bound. -/
theorem extractScalarWordRangeWith_admitted {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith locals slot source = some plan)
    (bounded : ∀ binding ∈ locals, binding.Holds (ScalarArithmeticBounded (slot + 3))) :
    ∃ descriptor : RangeExit, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) := by
  have invariant : plan.Holds (ScalarArithmeticBounded (slot + 3)) :=
    extractScalarWordRangeWith_invariant _ (ScalarArithmeticBounded.literal _)
      (fun op _ _ => ScalarArithmeticBounded.primitive op)
      (fun op _ _ _ _ => ScalarArithmeticBounded.choice op)
      (ScalarArithmeticBounded.get slot (by omega))
      (ScalarArithmeticBounded.get (slot + 1) (by omega)) compiled bounded
  obtain ⟨⟨dc, hc, ac, bc⟩, ⟨di, hi, ai, bi⟩, ⟨ds, hs, aStep, bs⟩, ⟨dd, hd, ad, bd⟩, ⟨dr, hr, ar, br⟩⟩ := invariant
  exact ⟨⟨dc, di, ds, dd, dr⟩, ⟨hc, hi, hs, hd, hr⟩, ⟨ac, ai, aStep, ad, ar⟩, ⟨bc, bi, bs, bd, br⟩⟩

/-- Public word computations stay within the captured argument slots. -/
theorem extractScalarWordRangePublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith (publicBindings inputs) slot source = some plan)
    (len : inputs.length = slot) :
    ∃ descriptor : RangeExit, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) :=
  extractScalarWordRangeWith_admitted compiled (ScalarArithmeticBounded.bindings inputs (by omega))


end LeanExe.Extract.Core
