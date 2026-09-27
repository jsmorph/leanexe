# General predicate bodies in the remaining word-result outer grammars

Four fixed native probes reject nested-body predicates around Boolean-derived
word results and word conditionals. Each grammar is tested with UInt64 and Bool
predicate inputs. The next native corpus also includes unused definitions,
Id bodies and inputs, captures, nested helpers, break and continue.

The proposed change retains raw bodies in the two outer source grammars and
uses their existing scalar-conversion premises. Each parser validates unused
bodies before compiling the continuation. Type/result annotations, helper scope
and loop behavior keep the same rules. Support, acceptance, correctness and
invariants drop only the redundant BooleanLocal body witness.

The two extraction modules will build separately before the public target.
Syntax tests cover both grammars, both input kinds, invalid unused bodies,
captures and malformed types. The affected predicate sections of the existing
word-helper suites are copied unchanged to focused scratch files so unrelated
helper families do not run again. Their originals and focused copies will be
included with the evidence.

All eight additional native probes elaborate and reject before the change. Source and extraction of Boolean-derived word results pass on the first focused build (183 targets), including equations, acceptance, support, correctness and invariants.

The word-conditional source/extraction target passes on its first build (185 targets), followed by the public target (196). Both functional induction proofs retain their case numbering. All four original probes and eight new probes pass unchanged. Native tests pass 192 comparisons; word-input syntax passes 6,912 comparisons and 2,304 invalid-input checks; Boolean-input syntax passes 13,824 comparisons and 5,472 invalid-input checks. All tests passed on their first runs.

Prior predicate sections and Boolean-result tests pass 139,584 comparisons, 77,616 invalid-input checks and 9,216 controls. Four original general-body probes remain positive; identityInput remains rejected. No test or proof failures occurred in this increment.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 1005 native Lean / independent Wasm engine comparisons across 52 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1553 declarations. Prior tests pass 139584 comparisons, 77616 invalid-input checks and 9216 controls.
