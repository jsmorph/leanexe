# Function bindings inside propositions — next after relation choices

The preserved compound probe elaborates as And (x < y) (let f : UInt64 → Bool :=
fun n => n == y; (f x || f 0) = true). guardLetType? currently supports only word
and Bool bindings. Standard evidence substitutes the helper lambda into the
Boolean calls without beta reduction; GuardLet.evidence already uses instantiate1.
The diagnostic file shows the exact syntax and must remain the fixed fixture.

A possible bounded extension: add GuardLetType.predicate with bare Bool/UInt64
input kind, forall binder name/info and BooleanType result. Let the ordinary scalar
compiler validate the actual lambda and its body. For this new binding type,
GuardLet.operand can be binding.wrap (.app (.const UInt64.ofNat []) (.lit 0)),
forcing validation even when the proposition ignores the helper. Wrapped guard
operands already preserve lexical scope. No new guard semantics should be needed.

The synthesized zero may require more size overhead than the existing Boolean
relation conversion allowance. Avoid changing the global recursion measure.
Instead measure it and, if needed, define guardOperandOverhead as the max of the
existing allowance and (sizeOf canonicalWordZero - sizeOf True + 1). Prove the
new zero bound and retain guardOperandOverhead_ite/dite/word bounds by decide.
The existing guardOperandOverhead_decide lemma only uses the string "decide";
it can instead bound against the full Decidable.decide constant, which is already
present in the source expression. Its only known consumer is BooleanLocal's
operand-size proof (confirm with rg). That would provide additional legitimate
head-size allowance without altering compiler behavior. Verify all constants and
inequalities in Lean before adopting this plan; estimates are not proofs.

Use a checked unused-helper operand and test unsupported helper bodies even when
unused. Do not omit validation to admit the probe. Parse exact function-domain,
result and binder syntax; preserve all existing word/Bool let behavior. Check
standalone decisions, ordinary/dependent word and Bool choices, compound guards,
negation, proposition lets and loop step/exits. Also compare modules after the
source-to-WASM gate. Broader helper bodies and Id inputs may remain distinct
capabilities depending on what the existing scalar let parser supports.

Kernel measurement completed: current overhead 557, canonical UInt64.ofNat zero
size 1054, True size 440, Bool-ite allowance 758, Bool-dite allowance 862,
Decidable.decide constant size 1556. The proposed max is 615. Lean proves it fits
the Bool-ite and full-decision bounds. The existing string-only "decide" bound
may also fit (verify by decide before changing its statement); keep every existing
bound unchanged when possible. Measurements and two checked inequalities are in
boolean-proposition-helper-let-size.lean and its passing log.
