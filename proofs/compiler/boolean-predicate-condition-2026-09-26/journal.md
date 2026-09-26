# Direct Boolean conditions containing Boolean-input predicates

The source guard form now exposes its actual Boolean inputs: one for a truth
condition, two for Eq/Ne. Each input is smaller than the original condition.
The shared condition compiler lowers their encoded results to a truth test or
Boolean equality comparison. Its correctness, acceptance, input-admission and
IR choice-property lemmas are independent of recursive scalar extraction.

The scratch's first pass needed complete simplification of two-element list
membership and explicit existential result expressions in acceptance proofs.
Those corrections passed. The compiler recursively processes actual source
inputs rather than a synthesized whole Boolean comparison, whose constant and
instance names can distort the expression-size measure.

New ordinary/dependent source rules use a typed Bool-input function witness,
encoded evaluations for all condition inputs and evaluation of the selected
branch. The old guard path remains selected when no such function is referenced.
Core integration is in progress; subsequent extraction proofs, focused tests,
full theorem/audits and WASM execution remain required before this capability
is complete.

Core integration first needed explicit continuation indentation after the else
branch and a size-bound annotation stated using guard.condition before rewriting
parser soundness. Both ordinary and dependent core paths then built successfully.
The extractor's induction theorem places branch IHs before callback IHs because
of the shared continuation; those generated cases were inspected before editing
soundness. Correctness must split the dispatch before unpacking the successful
conditional result. This correction passed the aggregate proof build. Old source
rules derive dispatch absence from their word-input predicate environment.

Native examples cover truth/==/!=/Eq/Ne conditions, ordinary and dependent
branches, nested calls and choices, captures, shadowing, Id computations, scalar
helper bodies and scalar expressions inside loop bounds, steps and final results.
A focused scalar syntax matrix varies binder annotations, Id result depth,
negation, guard form, dependency and literal arguments. Separate tests check
active and inactive invalid branches, condition result types, universes, decision
evidence and proof-variable use in scalar and loop-nested scalar contexts.
Focused totals are 5,556 native/IR comparisons, 5,844 invalid-input checks and
420 admission controls. The selected engine group contains 28 declarations,
including fourteen ranges, with eighteen modules shared with the loop-let archive.

Selected prior fixtures pass 7,636 native/IR comparisons and 5,274 invalid-input
checks, including 336 controls. The full theorem and focused WASM execution are
next for the committed candidate.

The full compiler proof and eighteen audits pass. The first engine gate stopped
at an old exclusion for boolFnBooleanResult, whose direct predicate condition is
now intentionally supported. Moved that declaration to the acceptance list;
focused execution cases already cover the same negated-helper condition. No
compiler or theorem change was required. The failed gate log is retained.

The general compiler theorem and eighteen axiom audits pass. Native Lean/V8
agree on 519 inputs across 28 declarations, including fourteen ranges. Eighteen
shared modules retain identical bytes. The full native corpus has 882 declarations.
The post-proof candidate changes only the old admission-test expectation.
