# Boolean relations under proposition lets

The saved conditional and decision probes reject a bare Bool Eq/Ne proposition
under a retained let. Both are now admitted unchanged. The let fallback carries
the same independent Boolean proposition leaf used in compound guards. It checks
the bound value even when unused, compiles each operand under the original let,
and preserves exact condition syntax and substituted standard decision evidence.
Acceptance, source evaluation and IR invariants use the generic checked leaf
lowering. Nested lets, Boolean/word bindings, Id annotations and lexical captures
retain the existing guard semantics.

The earlier compound-relation increment kept its structural allowance unchanged.
For direct lets, the allowance is now derived from the actual Bool/Ne heads;
closed kernel proofs establish sufficient room for both converted operands.
Every caller still proves strict structural decrease. Conditional callers account
for the checked Bool or UInt64 result annotation, while decide's head supplies
its bound. The scalar compiler retains its result-type parser equation for this
proof. No runtime code or admission limit is added by the size lemmas.

The first compiler-core attempt had no result-type equality in its termination
context. A diagnostic run exposed that omission. Naming the two existing parser
matches supplied the equality; the unchanged algorithm and all scalar correctness
proofs then checked. The source/parser target, core and public compiler pass.
Failed proof attempts and their source/diagnostic log are retained.

Ten elaborated declarations pass 180 native/IR comparisons. They cover direct
conditions, decisions, dependent Boolean results, nested Id, helper calls,
unused bindings, range updates, break, continue and Boolean loop continuations.
Two intentionally unused binder names were prefixed with underscores to keep
native-result JSON output free of linter warnings; the focused test was rerun.
The raw-syntax tests pass 80,640 comparisons, 55,320 invalid-input checks and 1,152
controls across both relation polarities, nested lets, bindings, annotations,
negation, compound guards and five ordinary/dependent word/Boolean result forms.
They reject incorrect decisions, types, scope references and proof domains.

Seven adjacent test files pass 137,604 native/IR comparisons, 77,736 invalid-input
checks and 2,528 controls. The full source-to-WASM proof and selected V8 group run
against the committed candidate. The V8 cohort includes all 28 declarations from
the preceding compound-relation milestone plus the ten new declarations, allowing
all 28 previous module bytes to be compared directly.

The complete compiler proof and nineteen axiom audits pass (3,359 build targets). Native Lean/V8 agree on 729 inputs across 38 declarations, including 21 ranges. All 28 modules shared with the prior milestone retain identical bytes. The full native corpus has 1407 declarations.
