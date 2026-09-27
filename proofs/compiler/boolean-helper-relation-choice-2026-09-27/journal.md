# Direct Boolean relation choices with helper scopes

The original relation and equality-to-false probes remain rejected after the
propositional-choice increment. Ten additional native declarations also elaborate
and fail extraction on that baseline. They cover either/both Boolean operands,
Eq/Ne, false/true literals, dependent and nested choices, wrappers, loop steps,
break/continue and final results.

BooleanRelationGuard reuses the independently specified Boolean proposition
relation leaf, retaining exact standard evidence and a non-truth side condition.
Eq Bool _ true stays on the existing Boolean-truth choice path. The independent
choice shape preserves result Bool/Id types and optional proof binders. Its four
children have strict size bounds. The parts parser checks evidence through the
existing relation leaf parser, result annotations and proof-binder drop/lift.

The first parser proof attempted to split an unreduced constructor match before
its if branch; dependent elimination then failed. Reducing the constructor match
before splitting the evidence check resolves it. The second parser check passes
all 80 targets. Both failed/successful logs remain. Source totality, execution,
acceptance, functional support and invariants reuse booleanWordChoice 0 and its
existing correctness/closure lemmas; their integrated check follows.

The first scalar correctness check exposed a simplification mismatch between the
source guard's denote alias and the existing comparison lemma's native decision.
The diagnostic state confirms the same Boolean operands and branch condition.
Unfolding the alias and rewriting the selected Boolean outcome resolves the true
branch; the false branch additionally needs Bool.false_eq_true before reducing
its conditional. No compiler behavior changed for this proof adjustment.

The third scalar check passes all 137 targets after the false-branch simplification;
the public compiler build passes 196 targets. The new raw tests compare both
parsers at Eq Bool _ true, preserving the existing truth path, and cover Eq/Ne
with right false/true, helpers in either or both operands and branches, result
annotations, dependent choices and invalid standard evidence.

All ten new probes now pass unchanged. The new tests pass 62,900 comparisons,
97,920 invalid-input checks and 1,280 controls. The Eq-to-true controls continue
to select the previous truth parser; all other tested Eq/Ne conditions select
the new relation parser. Both paths validate operands, both branches, exact
evidence and dependent proof domains. Adjacent tests and the original probes
are being checked before the final candidate proof/engine gates.

Six adjacent tests pass 53,684 comparisons, 62,080 invalid-input checks and
1,280 controls. The original relation and equality-to-false probes now pass;
five previous positive controls remain accepted and the compound/function-typed
proposition-let probe remains rejected. The original fixtures are unchanged.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1487 declarations.
