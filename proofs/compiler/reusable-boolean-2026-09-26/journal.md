# Reusable Boolean function proof journal

Reusable UInt64-to-Bool helpers need a typed closure that can be called more than
once from an arbitrary supported scalar body. BooleanFunction already names
Bool-to-UInt64 helpers, so predicateFunction is a distinct source binding kind,
source value and compiler binding. A compiler predicate closure returns the
existing IR word representation of its native Bool result. The matching relation
requires exactly Bool.toUInt64 of that result. Lookup, totality and structural
closure properties preserve the type distinction.

BooleanEnvironment contains separate flag and predicate-function maps. Ordinary
value binders shift both maps and do not install a predicate in the new slot.
The initial representation change preserves all existing Boolean denotations.
VariablesMean currently constrains only flags because no predicate-call node
exists yet. Adding call syntax must also add typed/matching predicate-reference
conditions; the predicate map must never remain unconstrained for an admitted
call.

Environment and binding proofs pass, and the existing scalar compiler proofs
pass with the new representation. Step compatibility also passes, and the current named application fixtures
pass 2,200 comparisons and 720 invalid-input checks before predicate calls are added.
The full compiler theorem and native/V8 checks will run after reusable helper
admission is complete. No claim of completed reusable-helper coverage is made.

Predicate calls now reconstruct the original bound-function application and use
separate flag/function reference lists. The lexical source relations and compiler
proofs distinguish these kinds explicitly. Function lookup shifts under value
binders; successful lookup proves no bound value is used as a predicate function.
The lowering file is split into its algorithm, facts, acceptance and correctness
so each induction can be checked independently. Core source/parser proofs, all
four lowering modules, the lexical wrapper and existing scalar compiler proofs
pass. A wrapper structural-proof attempt supplied goals in the wrong order;
explicit placeholders fixed this without changing the statement. Reusable helper
creation remains the next source/extractor extension.

Reusable UInt64-to-Bool declarations now have independent source evaluation and
support rules. The source totality proof constructs the captured Boolean
function from source operand evaluations for each word argument. Compilation
checks the helper body once, then captures a compiler closure for repeated calls.
Its semantic relation requires exactly the Boolean zero/one result. Acceptance,
soundness, evaluation correctness and IR closure proofs pass, as do existing
step, range, whole-function and reannotation proofs. The first correctness
attempt needed explicit word value/binding arguments for the matching relation;
the first acceptance attempt over-simplified the closure expression. Explicit
arguments and a direct definitional equality resolved both elaboration issues.

Ten concrete Lean definitions pass 140 native/IR comparisons. Systematic binder,
result-annotation and negation combinations add 1,008 comparisons and 864
invalid-input tests. They include function/value type confusion, mismatched
parameter domains, invalid result types, unsupported arguments and invalid unused
bodies. Full compiler-theorem and selected V8 checks follow this candidate.

The general compiler theorem and all sixteen axiom audits pass. Native Lean/V8
agree on 1,727 inputs across 105 declarations, including 27 range declarations.
All 95 prior modules retain identical bytes. The full native corpus contains
745 declarations. The prior named-helper tests pass 2,200 comparisons and 720
invalid-input checks. Reusable predicate bindings in loop scopes are next.
