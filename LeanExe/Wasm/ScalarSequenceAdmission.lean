import LeanExe.Wasm.ScalarSequenceCertificate
import LeanExe.Wasm.ScalarRangeExitAdmission
import LeanExe.Extract.ScalarSequenceInvariant

namespace LeanExe.Wasm.ScalarDescriptor

def LoopSequence.All (P : Expr → Prop) : LoopSequence → Prop
  | .leaf descriptor => descriptor.All P
  | .bind first second => first.All P ∧ second.All P

end LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core
open LeanExe.Wasm.ScalarDescriptor

/-- The uniform expression invariant supplies descriptors for every sequence leaf. -/
theorem ScalarSequencePlan.holds_admitted {plan : ScalarSequencePlan} {limit : Nat}
    (invariant : plan.Holds (ScalarArithmeticBounded limit)) :
    ∃ descriptor : LoopSequence, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < limit) := by
  induction plan with
  | leaf plan =>
    obtain ⟨⟨dc, hc, ac, bc⟩, ⟨di, hi, ai, bi⟩, ⟨ds, hs, astep, bs⟩,
      ⟨dd, hd, ad, bd⟩, ⟨dr, hr, ar, br⟩⟩ := invariant
    exact ⟨.leaf ⟨dc, di, ds, dd, dr⟩, .leaf ⟨hc, hi, hs, hd, hr⟩,
      ⟨ac, ai, astep, ad, ar⟩, ⟨bc, bi, bs, bd, br⟩⟩
  | bind first second firstIH secondIH =>
    obtain ⟨a, ma, aa, ba⟩ := firstIH invariant.1
    obtain ⟨b, mb, ab, bb⟩ := secondIH invariant.2
    exact ⟨.bind a b, .bind ma mb, ⟨aa, ab⟩, ⟨ba, bb⟩⟩

/-- Every read in an extracted sequence stays within the supplied local allocation. -/
theorem extractScalarSequenceWith_admitted {source : Lean.Expr} {locals : List ScalarBinding}
    {slot limit : Nat} {plan : ScalarSequencePlan}
    (compiled : extractScalarSequenceWith locals slot source = some plan)
    (room : slot + plan.width ≤ limit)
    (bounded : ∀ binding ∈ locals, binding.Holds (ScalarArithmeticBounded limit)) :
    ∃ descriptor : LoopSequence, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < limit) := by
  apply ScalarSequencePlan.holds_admitted
  exact extractScalarSequenceWith_invariant _ (ScalarArithmeticBounded.literal _)
    (fun op _ _ => ScalarArithmeticBounded.primitive op)
    (fun op _ _ _ _ => ScalarArithmeticBounded.choice op) limit
    (fun index bound => ScalarArithmeticBounded.get index bound) compiled room bounded

theorem extractScalarSequencePublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {slot : Nat} {plan : ScalarSequencePlan}
    (compiled : extractScalarSequenceWith (publicBindings inputs) slot source = some plan)
    (len : inputs.length = slot) :
    ∃ descriptor : LoopSequence, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + plan.width) :=
  extractScalarSequenceWith_admitted compiled (Nat.le_refl _)
    (ScalarArithmeticBounded.bindings inputs (by omega))

end LeanExe.Extract.Core
