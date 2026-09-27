# Consecutive bounded scalar loops

All six fixed probes reject: direct and dependent word loops, break/continue,
unused first result, three loops and word-to-Boolean composition. The first
capability is word-result sequences; Boolean combinations remain the next step.

Finite-store framing is proved for writes, expressions, conditions and statements.
An appended local suffix is untouched by an existing checked execution. The first
scratch check caught the reserved constructor spelling `local`, an equality-field
projection and an overly broad simplification; explicit constructor quoting,
the named write theorem and a direct bound resolve them. The second check passes.
The production version removes the deprecated if_pos spelling.

The existing range-plan proof is factored at its body execution boundary, keeping
the public theorem unchanged. The new source sequence semantics prove totality
for word computations, lets, standard Id binds/run/pure and metadata. All three
foundation modules pass together (187 targets).

A recursive sequence plan gives each leaf four fresh locals. Width and result-slot
bounds are proved. Its meaning records the exact preserved prefix, allocated
suffix and result local. Sequential execution uses the frame theorem to allocate
future locals before the first computation. The public result slot is written
only after both computations finish. The first plan check exposed a renamed list
lemma and two simplifier/decision details; the corrected boundary passes 177
targets. Source extraction and complete admission are being checked next.

The recursive extractor preserves existing single-loop admission and checks both
computations in word lets and standard Id binds. Exact result annotations and
instances are retained. Termination and complete admission pass on the first
check (205 targets). Source reconstruction also passes first try. The captured
binding module initially used Lean's reserved `prefix` token as a variable;
renaming it to `earlier` fixes that syntax error. Correctness initially used a
field projection for a theorem in the wrong namespace; the fully qualified
leaf theorem fixes it. Correctness and generic bounded IR invariants then pass
208 targets. The invariant shares a final local bound across both children, so
captured functions may safely consume later result locals.

All five word-result probes are now accepted by the sequence extractor. The
Boolean-result probe still rejects, as planned. The probe driver first needed an
explicit Option type and the public-binding import; its second check passes.
Sequence descriptors match every leaf, preserve exact production instructions,
and prove scratch widths and bounded arithmetic reads. The descriptor boundary
passes 237 targets. A constructor named `bind` initially shadowed Bind.bind in
one simplification; the explicit typeclass name resolves the equation.

A general finite target-loop trace now supplies a decreasing iteration measure
for the existing total-correctness WASM rule. Its proof chooses the least remaining
trace length and passes 3068 cached targets. Lifting finite IR while execution
into this trace passes 3069 targets. Lean cannot structurally recurse on a proof
whose statement index is fixed to a while constructor; generalizing that index
and using induction on the execution derivation proves the same result without
an added assumption. These proofs will compose complete emitted sequences.

Generic scalar-program execution now composes loop-free statements, finite loops
and statement sequences. It preserves source locals and the target state's
capacity and passes 3286 cached targets on its first check. Scratch accounting
for statements, loops and complete programs passes 224 targets. The sequence's
stack-typing/encoding theorem passes 3293 cached targets on the first check,
including all leaf expressions, control-flow instructions and final result-slot
copy. An adapted draft briefly confused the flag local with the shared scratch
boundary; inspection corrected the two indices before Lean was run.

Whole-function execution passes 3292 targets. Initial-state proofs must rewrite
the matched scratch width before simplifying the function record, otherwise the
simplifier unfolds the record and loses that rewrite shape. The complete emitted
function-body bytes parse and execute with the source result (3337 targets).
The first byte check needed the proved positive plan width to establish a
nonempty local declaration. Public compiler integration is next.

Public admission, source application, compiler correctness, complete function
bytes and module validation now include sequence plans. Their focused integration
passes 3379 targets on the first check. The unchanged probes report five admitted
word cases and one deferred Boolean-result case through normal public extraction.
Eight native fixtures pass 192 comparisons. Retained Id annotations made native
HAdd instance inference ambiguous in one fixture; explicit UInt64.add resolves
that test elaboration without changing production code. All failed checks remain
in the logs. The raw syntax matrix passes first try: 13,824 comparisons, 18,432
invalid-input tests and 576 controls forcing the new admission path. It covers
all result annotation depths, wrappers, binder flags, two/three loops, dependent
bounds, exits and empty-range rejection checks. The V8 group keeps all 114 prior
modules and adds eight. Eight sequence proof boundaries are added to the audit.

The complete proof gate passes 3413 targets and all 53 axiom audits. The first
engine gate finds an old admission expectation rejecting rangeTwice. The unchanged
program is now proved by the sequence path, so it moves to accepted declarations
and gains an independent V8 fixture. The group now contains 123 declarations.
The test-only update does not require rebuilding the unchanged proof candidate.

A second old exclusion, rangeLetTwoLoops, is the equivalent ordinary-let form.
It also moves unchanged to admission and independent V8 checks. The group now
contains 124 declarations. The remaining exclusions are inspected before rerun.
