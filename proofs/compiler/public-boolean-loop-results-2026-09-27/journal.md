# Boolean result computed from a word loop

This increment starts with an explicit UInt64 let binding whose value is a
checked word-valued loop and whose body computes a Boolean. Metadata and exact
standard Boolean Id run/pure wrappers are included. General Boolean-result Id/do
sequencing is subsequent work, as are the previously recorded helper-body and
compound proposition gaps.

BooleanRange.Eval independently returns a Bool; its let-result rule combines
word loop evaluation with checked Boolean continuation evaluation. Supported
syntax has a totality proof. The new extractor reuses ScalarRangeExitPlan and
replaces only its result expression with the Boolean conversion. Existing yielding,
early-exit, continue, stride and capture rules apply to the bound word loop.

The source evaluation/totality and exact wrapper parser proofs pass on the first
focused build. The first extraction equation for wrappers unfolded a dependent
parser match too far; retaining and rewriting the proved wrapper parse equation
keeps that boundary explicit. Acceptance, support, result evaluation and invariant
proofs are being checked before public signature integration.

The wrapper equation now explicitly splits the outer source match and the inner
parser match; the proved parse equation resolves both branches. Extraction
acceptance, supported-source recovery, Boolean evaluation/result preservation and
the shared IR invariant all pass focused builds. No changes to the existing word
loop semantics, scalar expression traversal or WASM loop implementation were
needed. Public declaration integration is the next step for this same increment.

Public integration adds a fourth extraction case: a Boolean-result range plan.
The public application theorem preserves typed arguments and returns a Bool
whose encoding agrees with the plan. The existing complete range emitter,
byte encoding and validation proofs accept the new admission invariant. All
three focused WASM targets pass (3316 jobs). The first public proof check needed
an explicit Bool annotation on its existential flag; the corrected target passes.
Ten native source declarations pass 240 IR comparisons, including break, continue,
strides, captures, mixed word/Boolean inputs and standard Id wrappers.

The raw syntax matrix passes 16,128 native/IR comparisons and 13,824 invalid-input
checks. It varies typed input order, Id depth, binder info, let dependency flags,
yield/exit/continue behavior, wrappers and Boolean continuation forms. Rejected
cases include word/Boolean kind confusion, unsupported dead tails and steps,
invalid unused bindings, wrong wrapper types/universes and custom wrapper heads.
Two initial test-file checks failed on structure indentation and an inferred
Id UInt64 native value; explicit structure binding and Id.run corrected the
fixture. Both failed logs are retained.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 559 inputs across 28 declarations, including eighteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1116 declarations.
