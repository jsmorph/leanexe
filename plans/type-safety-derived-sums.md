# Derived Option and Except: specification and proof obligations

This plan is for the independent strict language on `typesafety`. The definitions
and theorems below are intended work, not completed results. Representation by
an existing type constructor does not establish an API's evaluation behavior.

## Representation and initial scope

Use transparent type abbreviations:

```text
Option α   := Sum Unit α
Except ε α := Sum ε α
```

None is the left injection of Unit; Some is the right injection of its payload.
Error is the left injection of its error value; Ok is the right injection of its
success value. An injection retains the annotation needed to determine its
absent summand. These are independent language aliases, consistent with the
checked array operations' result convention. They do not prove translation of
Lean's nominal Option/Except definitions or any compiler representation.

The first API consists of constructors, Option map/bind, Except map/bind, and
Except map-error. No new primitive expression, runtime value, or transition is
needed. Each API is a transparent expression expansion with checked laws.

## Binding and evaluation

Each operation evaluates its scrutinee once, before selecting a branch. A
callback is an expression scoped under `payload :: Γ`: index zero denotes its
payload, and index `i + 1` denotes original context index `i`. It is code, not a
first-class function value. It evaluates only in the selected branch. The
callback keeps the scrutinee's captured lexical environment; any direct call
inside it still enters a fresh callee environment.

| Operation | Left result | Right result |
|-----------|-------------|--------------|
| Option map | Consume Unit with `unitCase`, return None of the result type. | Evaluate the callback and wrap its value in Some. |
| Option bind | Consume Unit with `unitCase`, return None of the result type. | Evaluate the callback, whose result is already an Option. |
| Except map | Forward the unchanged error value. | Evaluate the callback and wrap its value in Ok. |
| Except bind | Forward the unchanged error value. | Evaluate the callback, whose result is already an Except with the same error type. |
| Except map-error | Evaluate the error callback and wrap its value in Error. | Forward the unchanged success value. |

Scrutinee overflow or stuckness is retained. A skipped callback contributes no
execution. A selected callback may return, overflow, become stuck in the raw
calculus, or have no finite terminal execution. Nothing in these definitions
requires termination or makes arbitrary malformed states permitted failures.
The None arm checks its Unit shape through the ordinary Unit eliminator. A raw
left injection of a non-Unit value is malformed, and that selected arm is stuck.

## Admission and payload use

Ordinary typing requires a scrutinee of the indicated sum type, a callback typed
under its payload context, and well-formed absent summand annotations. Public
admission retains formation of the complete declaration/signature/context tables.

The profile requires admissibility of the scrutinee and callback and a syntactic
occurrence of callback index zero. The forwarding arm uses its actual payload;
the None arm uses the existing zero-field Unit eliminator. No fabricated use is
inserted to make an ignored payload pass relevance. As elsewhere, this is
syntactic occurrence, not linearity or a guarantee of semantic necessity.

Payload-discarding tests (`isSome`, `isOk`), Except-to-Option conversion, and
error-discarding fallback are outside this first API. A conventional branch that
binds and ignores the payload is rejected by the current profile. Their final
inclusion or exclusion must be recorded explicitly in the coverage ledger;
calling them expressible using unrestricted raw sums is insufficient. Defaults,
filters, and other eliminators also need their own evaluation and binding
contracts before admission is claimed.

## Required results

1. Reusable continuation laws: exact stepping away from the empty-return
   boundary, successful trace extension, and finite execution decomposition at
   that boundary. Appending a continuation can enable a step from `ret value []`,
   so unconditional equality of optional step results would be false.
2. Constructor and combinator typing, exact inference characterizations, free
   occurrence equations, and exact profile-admission equations. General source
   safety is inherited only through proved expansion typing.
3. Exact execution laws for supplied sums and for arbitrary scrutinee executions.
   Returned values, operand faults, and selected-callback faults must be
   distinguished. Both directions are required for return/fault characterizations;
   forward examples alone do not establish an exact semantics.
4. Behavioral regressions for captures, missing or unused payloads, nested sums,
   fresh calls, skipped failing callbacks, selected failing callbacks, and strict
   scrutinee evaluation. Run the maintained gate and audit every new theorem.

Full language coverage, compiler correspondence, and application-library
correctness remain separate claims. This plan closes no coverage row until the
corresponding definitions and proofs pass the gate.
