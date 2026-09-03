import Interpreter.Wasm.Wp.Tactic

/-!
# Talos compatibility for the pre-floating-point migration

The Lean 4.34 Talos baseline removes a few convenience declarations while
preserving the definitions they wrapped.  Existing audited integer proofs keep
their old surface through these proved, project-local adapters.  New proofs use
the current Talos APIs directly.
-/

namespace Wasm

namespace UInt32

/-- Compatibility name for frame arithmetic now supplied by Lean core rather
than CodeLib. -/
theorem toNat_sub_of_le (a b : _root_.UInt32) (h : b ≤ a) :
    (a - b).toNat = a.toNat - b.toNat :=
  _root_.UInt32.toNat_sub_of_le a b h

end UInt32

@[simp, wp_simp]
def Locals.validIndex (s : Locals) (i : Nat) : Prop :=
  i < s.params.length + s.locals.length

@[simp]
def Locals.set (s : Locals) (i : Nat) (v : Value) (_ : s.validIndex i) : Locals :=
  if i < s.params.length then { s with params := s.params.set i v }
  else { s with locals := s.locals.set (i - s.params.length) v }

theorem wp.imp {Q Q' : Assertion α}
    (h : wp m c Q st s env) (hq : ∀ continuation, Q continuation → Q' continuation) :
    wp m c Q' st s env :=
  wp.conseq hq h

/-! The 4.34 decoder preserves the validation types attached to structured
control.  Execution uses the checked arities and deliberately ignores these
proof metadata fields, while the pre-FP WP convenience lemmas still state
their rules with the default empty lists.  Normalize only at the WP boundary;
the decoded module itself retains the exact metadata. -/

theorem exec_block_control_types (fuel : Nat) {ps rs : Nat} {body rest : Program}
    {paramTypes resultTypes : List ValueType} :
    exec fuel m st s (.block ps rs body paramTypes resultTypes :: rest) env =
      exec fuel m st s (.block ps rs body :: rest) env := by
  cases fuel <;> simp only [exec, execOne]

theorem exec_iff_control_types (fuel : Nat) {ps rs : Nat}
    {thenBody elseBody rest : Program} {paramTypes resultTypes : List ValueType} :
    exec fuel m st s
        (.iff ps rs thenBody elseBody paramTypes resultTypes :: rest) env =
      exec fuel m st s (.iff ps rs thenBody elseBody :: rest) env := by
  cases fuel <;> simp only [exec, execOne]

@[simp, wp_simp]
theorem wp_block_control_types {ps rs : Nat} {body rest : Program}
    {paramTypes resultTypes : List ValueType} {Q : Assertion α} :
    wp m (.block ps rs body paramTypes resultTypes :: rest) Q st s env =
      wp m (.block ps rs body :: rest) Q st s env := by
  unfold wp
  simp only [exec_block_control_types]

@[simp, wp_simp]
theorem wp_iff_control_types {ps rs : Nat} {thenBody elseBody rest : Program}
    {paramTypes resultTypes : List ValueType} {Q : Assertion α} :
    wp m (.iff ps rs thenBody elseBody paramTypes resultTypes :: rest) Q st s env =
      wp m (.iff ps rs thenBody elseBody :: rest) Q st s env := by
  unfold wp
  simp only [exec_iff_control_types]

/-- Retained proof script for the two grandfathered specifications that peel
low-information structural boundaries before straight-line simplification. -/
macro "wp_peel" : tactic => `(tactic|
  ((repeat (first
    | apply wp_block_cons
    | refine wp_iff_cons rfl ?_));
   wp_run;
   simp))

end Wasm
