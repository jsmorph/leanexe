import Interpreter.Wasm.Wp.Tactic

/-!
# Talos compatibility declarations

Talos for Lean 4.34 does not provide a few convenience declarations, although it
keeps the definitions they wrapped.  These proved, project-local adapters restate
those declarations for the integer proofs that use them.  Other proofs use the
Talos APIs directly.
-/

namespace Wasm

namespace UInt32

/-- Compatibility name for the frame arithmetic lemma
`_root_.UInt32.toNat_sub_of_le` of Lean core. -/
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

/-! The decoder of Talos for Lean 4.34 keeps the validation types of structured
control.  Execution uses the checked arities and ignores these proof metadata
fields, while the `wp` convenience lemmas state their rules with the default
empty lists.  The theorems below remove the types only in `exec` and `wp` terms,
and the decoded module keeps the exact metadata. -/

theorem exec_block_control_types (fuel : Nat) {ps rs : Nat} {body rest : Program}
    {paramTypes resultTypes : List ValueType} :
    exec fuel m st s (.block ps rs body paramTypes resultTypes :: rest) env =
      exec fuel m st s (.block ps rs body :: rest) env := by
  have h : execOne fuel m st s (.block ps rs body paramTypes resultTypes) env =
      execOne fuel m st s (.block ps rs body) env := by
    cases fuel <;> simp only [execOne.eq_def]
  conv_lhs => rw [exec]
  conv_rhs => rw [exec]
  rw [h]

theorem exec_iff_control_types (fuel : Nat) {ps rs : Nat}
    {thenBody elseBody rest : Program} {paramTypes resultTypes : List ValueType} :
    exec fuel m st s
        (.iff ps rs thenBody elseBody paramTypes resultTypes :: rest) env =
      exec fuel m st s (.iff ps rs thenBody elseBody :: rest) env := by
  have h : execOne fuel m st s (.iff ps rs thenBody elseBody paramTypes resultTypes) env =
      execOne fuel m st s (.iff ps rs thenBody elseBody) env := by
    cases fuel <;> simp only [execOne.eq_def]
  conv_lhs => rw [exec]
  conv_rhs => rw [exec]
  rw [h]

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

/-- Applies `wp_block_cons` and `wp_iff_cons` to the leading blocks and conditionals, and then
runs `wp_run` and `simp`. -/
macro "wp_peel" : tactic => `(tactic|
  ((repeat (first
    | apply wp_block_cons
    | refine wp_iff_cons rfl ?_));
   wp_run;
   simp))

#print axioms exec_block_control_types
#print axioms exec_iff_control_types
#print axioms wp_block_control_types
#print axioms wp_iff_control_types
end Wasm
