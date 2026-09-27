import LeanExe.Wasm.ScalarArithmeticBounds

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

/-- Typed public inputs, including Boolean normalization, produce arithmetic
WASM descriptors whose reads stay within the public argument slots. -/
theorem extractScalarPublic_admitted {source : Lean.Expr}
    {inputs : List LeanExe.Source.Scalar.PublicArgument} {target : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith (publicBindings inputs) source = some target) :
    ∃ descriptor, Expr.ofIR target = some descriptor ∧ descriptor.Arithmetic ∧
      ∀ index ∈ descriptor.reads, index < inputs.length := by
  exact extractScalarExprWith_invariant (ScalarArithmeticBounded inputs.length)
    (ScalarArithmeticBounded.literal _) (fun op _ _ => ScalarArithmeticBounded.primitive op)
    (fun op _ _ _ _ => ScalarArithmeticBounded.choice op) compiled
    (ScalarArithmeticBounded.bindings inputs (Nat.le_refl _))

end LeanExe.Extract.Core
