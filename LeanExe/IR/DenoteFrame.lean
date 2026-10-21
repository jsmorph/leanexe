import LeanExe.IR.Denote

namespace LeanExe.IR

private theorem lt_max_nat (j a b : Nat) : j < max a b ↔ j < a ∨ j < b := by omega

def Expr.denoteLocals : {type : ScalarType} → Expr type → Nat
  | _, .get j | _, .getF32 j => j + 1
  | _, .bin _ left right | _, .eq left right | _, .ne left right
  | _, .ltU left right | _, .leU left right | _, .and left right | _, .or left right
  | _, .binF32 _ left right | _, .eqF32 left right | _, .ltF32 left right
  | _, .leF32 left right => max left.denoteLocals right.denoteLocals
  | _, .not operand | _, .unF32 _ operand | _, .ofBits32 operand | _, .toBits32 operand =>
    operand.denoteLocals
  | _, .ite condition yes no | _, .iteF32 condition yes no =>
    max condition.denoteLocals (max yes.denoteLocals no.denoteLocals)
  | _, .read _ position => position.denoteLocals
  | _, _ => 0

theorem Expr.denote_congr {type : ScalarType} (e : Expr type)
    (locals next : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (same : ∀ j, j < e.denoteLocals → next j = locals j) :
    e.denote next arrays = e.denote locals arrays := by
  induction e generalizing locals next <;>
    simp_all [Expr.denoteLocals, Expr.denote, lt_max_nat, or_imp, forall_and]

end LeanExe.IR
