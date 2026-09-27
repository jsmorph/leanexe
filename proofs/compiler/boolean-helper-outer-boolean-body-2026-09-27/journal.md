# General predicate bodies before Boolean-result loops

Five fixed native probes reject nested predicate bodies before Boolean-result
loops. They cover UInt64 and Bool inputs, word and Boolean accumulators, wrapped
Id bodies and results, and an unused helper. Ten additional declarations cover
captured predicates, bounds, initial values, continue/break and deeper nesting.

The BooleanRange predicate rules retain raw Lean expressions. The scalar
conversion premise still proves that every function result is a Boolean encoded
as zero or one. The parser checks every body at zero, including unused helpers,
and preserves the exact input domains and Boolean result annotations. The
predicate-first dispatcher keeps its direct/wrapped loop-valued helper fallback
and conditional continuation path. The success lemma retains its expression
equality witness so existing support and invariant proofs keep their structure.

The other outer grammars remain unchanged in this capability. Focused source,
continuation, acceptance, support, correctness and invariant checks come before
the public compiler target and full proof/WASM gates.

The first continuation proof failed on a quantifier syntax error: Lean requires a comma before the second existential after a typed binder. The corrected statement passes with the source target (171 targets). Source acceptance/support then pass (174 targets). All ten additional native probes elaborate and reject before this change.

Correctness/invariants pass (181 targets), then the public target passes (196). Four of the five original probes and eight of the ten new probes are restored. The Boolean-accumulator probes remain rejected: this is a separate loop-accumulator gap, rather than a helper-body failure. The first native test stops at that unsupported declaration. The original probes and failed test are retained unchanged in the evidence; the eight supported declarations enter the corpus. No claim of Boolean-accumulator support is made.

The eight native tests pass 192 comparisons. The first word syntax test needed explicit Id.run before comparing the native loop result to a UInt64; without it, typeclass inference tried BEq (Id UInt64). The corrected fixtures use an explicit UInt64 expected result in both input suites. This was a test elaboration failure.

Both corrected syntax suites pass: 3,456 + 6,912 comparisons and 1,152 + 2,736 invalid-input checks. Total new tests: 10,560 comparisons and 3,888 invalid-input checks. Four remaining-outer-grammar probes elaborate and reject unchanged, giving the next bounded capability. Boolean accumulators remain a separate recorded gap.

The prior direct-continuation test stopped on exact plan equality. Scalar-only helper choices now use the expanded predicate path, so their plan need not equal the direct argument-binding plan. The test retains plan equality for loop-containing modes and now compares the public result, helper plan and direct-binding control against native semantics for every input. This adds 8,064 comparisons; the original failing test is retained.

The direct-call test passes after checking all three executions (24,192 comparisons). Review found the same scalar-plan equality assumption in wrapped, saved and Id-forwarded call tests. They retain equality for loop-containing modes and also compare the direct-binding control against native semantics for all inputs. The expanded tests are included in this candidate.

Wrapped and saved call tests pass 145,152 comparisons each. The forwarded test rejected-fixture list included callback bvar 0, returning a Boolean argument while leaving the scalar helper unused. The expanded parser correctly admits it for the scalar-only Boolean-input case. An indexed diagnostic confirms fixture 6. The test now checks both public and direct-plan values for that valid case and uses a UInt64 literal callback as the invalid-result fixture. Original failure and indexed diagnostic are retained.

All prior suites now pass: 540,144 comparisons, 279,216 invalid-input checks and 15,744 controls. No production changes were needed for the fixture corrections. The candidate is ready for the full source-to-WASM proof and independent engine checks.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 1005 native Lean / independent Wasm engine comparisons across 52 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1545 declarations. Prior tests pass 540144 comparisons, 279216 invalid-input checks and 15744 controls.
