# Boolean-input predicates declared inside loop steps

The Step source grammar now admits Boolean-input/Boolean-result helper
declarations. Each closure retains scalar lexical values projected from the
step environment. Its parameter is a Boolean binding and its compiled output is
a zero/one word. Converted calls reuse the preceding scalar proof. The source
requires every Boolean operand to evaluate for each possible parameter and
keeps captured values fixed when the accumulator subsequently changes.

The existing Bool-input declaration dispatch preserves both word and step result
paths. A rejected step-result type now falls through to checked Boolean result
types and Boolean body parsing. The body is validated before a closure is added,
even if the helper is unused. Source totality, extraction equations, acceptance,
soundness, evaluation correctness and IR invariants passed the first focused
proof run. Generated function-induction branches required one new admitted case
and one additional result-type rejection.

Six native loops pass 144 comparisons. Systematic syntax tests vary binder kinds,
result Id depth, negation, declaration dependency flags and literal Boolean
arguments; they pass 3,456 comparisons and 2,304 invalid-input checks. Cases
exercise early exit, continuing, repeated calls, capture before updates, nested
closures and captured helpers inside step-valued functions. Wrong domains,
results and argument/value kinds, unsupported unused bodies and unsupported
Boolean-context calls reject. Prior scalar Boolean-input tests pass 2,156
comparisons and 2,304 invalid-input checks; prior word-input step predicate tests
pass 1,872 comparisons and 864 invalid-input checks.

The general source-to-WASM theorem and all eighteen axiom audits pass. Native Lean/V8 agree on 1,249 inputs across 68 declarations, including 31 ranges. All 62 prior modules retain identical bytes. The full native corpus contains 786 declarations.
