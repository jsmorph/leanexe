# Propositional choices containing helper scopes

The original six probes include four rejections (word comparison, Boolean relation,
equality to false, compound proposition) and two accepted controls (simple negation
and a proposition let). Adding repeated-call bodies to the latter conditions gives
two further rejected probes while retaining the original controls.

An initial plan converted a raw condition/evidence pair into a Decidable.decide
operand. A size diagnostic showed that this cannot satisfy the current strict
size measure: even minimal expressions measure 1560 for the decision and 774
for the conditional. #eval cannot execute Lean.Expr's sizeOf instance here;
#reduce supplied the counterexample. The scratch fixture, failed log and reduction
log remain. No global measure was changed, and the false size claim was not used.

The implementation instead reuses PropositionGuard and extractGuard. The source
shape preserves result annotations, dependent binders and the guard's independently
checked condition/evidence. Existing guardOperandOverhead bounds prove recursive
operands decrease. Both Boolean branches are recursively checked. Direct Boolean
Eq/Ne conditions remain a separate capability after this increment.

The first parser build exposed a generated self-import and two normalization
issues in the size proof. The import now names the existing truth-choice module;
normalizing the Bool type bound and the guard condition alias resolves the size
proof. The next parser diagnostic was a dependent match rewrite: splitting that
match and excluding its some branch preserves the proof dependency. The fourth
parser check passes all 78 targets. These failures are retained. The source
semantics and scalar lowering proofs are the next checks.

Source totality, scalar correctness, acceptance, functional support and invariants
pass on their first integrated check (135 targets). The public compiler build
also passes (194 targets). Tests now cover propositional guards with recursively
converted helper operands as well as helper scopes in both branches.

The first native run exposed a distinct guard-language gap. In a conjunction,
Lean elaborates the Boolean helper declaration as a function-typed proposition
let, with the Bool-to-Prop coercion inside the let body. GuardLetType currently
admits only word and Boolean bindings, so the guard itself is rejected before
the new conditional parser. The original failing fixture and diagnostic remain;
the extended probe continues to measure this gap. Direct Boolean Eq/Ne and
function-typed proposition lets are separate next capabilities.

The new compound/dependent/exit test cases now use an explicit Boolean-to-word
conversion in the guard, exercising recursively compiled helper operands in an
already supported UInt64 relation. This completes the intended conditional
extension over existing propositional guards. It does not claim that the original
function-typed proposition-let fixture is fixed. The original probe remains in
the evidence and must be addressed in subsequent work.

New tests pass 37,812 comparisons, 51,072 invalid-input checks and 768 controls.
Six adjacent tests pass 41,140 comparisons, 45,056 invalid-input checks and
1,024 controls. Three previously rejected extended probes now pass; two original
positive controls still pass; direct Boolean relation/equality-to-false conditions
and the function-typed proposition-let probe remain rejected. The original
fixtures are retained without rewriting them into the admitted cases.

The general compiler proof and nineteen axiom audits pass (3375 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1477 declarations.
