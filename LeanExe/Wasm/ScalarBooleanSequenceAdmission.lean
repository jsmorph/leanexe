import LeanExe.Wasm.ScalarSequenceAdmission
import LeanExe.Extract.ScalarBooleanSequenceInvariant

namespace LeanExe.Extract.Core
open LeanExe.Wasm.ScalarDescriptor

/-- Every read in an extracted sequence stays within the supplied local allocation. -/
theorem extractScalarBooleanSequenceWith_admitted {source : Lean.Expr} {locals : List ScalarBinding}
    {slot limit : Nat} {plan : ScalarSequencePlan}
    (compiled : extractScalarBooleanSequenceWith locals slot source = some plan)
    (room : slot + plan.width ≤ limit)
    (bounded : ∀ binding ∈ locals, binding.Holds (ScalarArithmeticBounded limit)) :
    ∃ descriptor : LoopSequence, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < limit) := by
  apply ScalarSequencePlan.holds_admitted
  exact extractScalarBooleanSequenceWith_invariant _ (ScalarArithmeticBounded.literal _)
    (fun op _ _ => ScalarArithmeticBounded.primitive op)
    (fun op _ _ _ _ => ScalarArithmeticBounded.choice op) limit
    (fun index bound => ScalarArithmeticBounded.get index bound) compiled room bounded

theorem extractScalarBooleanSequencePublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {slot : Nat} {plan : ScalarSequencePlan}
    (compiled : extractScalarBooleanSequenceWith (publicBindings inputs) slot source = some plan)
    (len : inputs.length = slot) :
    ∃ descriptor : LoopSequence, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + plan.width) :=
  extractScalarBooleanSequenceWith_admitted compiled (Nat.le_refl _)
    (ScalarArithmeticBounded.bindings inputs (by omega))

end LeanExe.Extract.Core
