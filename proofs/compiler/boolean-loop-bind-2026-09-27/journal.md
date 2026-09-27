# Boolean continuation of a monadic word loop

The preceding explicit-let loop-result capability passed the complete compiler
proof and nineteen audits plus 559 native/V8 comparisons, and its evidence was
committed as 14d13901. This increment admits exact standard Id Bind.bind with a
word-valued loop action and a Boolean continuation. Input and lambda-domain
annotations agree structurally; arbitrary standard Id layers are retained on
word input and Boolean result. The parser checks the complete standard bind
instance and both continuation/action syntax.

The source relation has a distinct bindResult constructor, with the same native
word loop and Boolean continuation evaluation as letResult. Extraction reuses the
word range-exit plan and replaces its final result. Public application and WASM
theorem shapes remain unchanged. General setup before Boolean loops is subsequent
work, as are the helper/proposition gaps recorded in task.md.

Source, parser, acceptance, supported-source recovery, evaluation and invariant
proofs pass on the first focused build. Public function correctness and descriptor
admission also pass. The first native fixture pass exposed the existing Boolean
helper-let body limitation when a helper call is wrapped in Pure.pure in the
continuation. The failed fixture is retained. This increment's captured-helper
case keeps its captured loop helper and compares the final value directly; wrapped
helper-let continuation bodies join the recorded subsequent helper-body work.

The corrected native fixture passes 240 comparisons across ten declarations.
The syntax matrix passes 32,256 native/IR comparisons, 46,080 invalid-input
checks and 2,304 explicit-let controls. Every monadic case produces identical
IR to its explicit-let counterpart. Cases vary typed input order, Id input/output
depth, binder info, wrappers, continuation forms and loop behavior. Wrong lambda
domains, result kinds, universes, heads, instances, dead tails and steps are
rejected. The initial syntax fixture used the reserved identifier instance;
renaming it to evidence corrected the test without compiler changes.

The complete compiler proof passes all nineteen audits (3345 targets). The first
runtime gate then found three fixture-name collisions with earlier Boolean bind
tests. All ten new fixtures now use the distinct rangeBoolResultBind prefix;
prior declarations and corpus memberships are preserved. The only candidate
changes are fixture names and test registrations, so the completed compiler proof
is reused with identical compiler and proof sources. The failed gate is retained.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 579 inputs across 28 declarations, including twenty ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1126 declarations.
