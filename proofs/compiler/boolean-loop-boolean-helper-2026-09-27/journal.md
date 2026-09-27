# Boolean-input word helpers before Boolean loops

The source model now admits Bool-to-UInt64 helpers before a Boolean-result loop.
A Boolean-function binding keeps its native Bool input distinct from words; the
compiled binding receives the canonical word encoding. The helper captures its
surrounding values once. The matching proof holds for every accumulator, index,
stop and exit flag, so loop state changes cannot alter those captures.

The existing word-loop Boolean helper semantics supplied the source constructors
and totality proof. The Boolean-loop word helper proof supplied the acceptance,
soundness and IR-invariant structure. Both focused proof builds passed on the
first attempt. No change to the public compiler theorem or WASM lowering was
needed. Unused bodies are validated before the continuation is extracted.

Ten native declarations cover repeated calls, bounds, initialization, nested
helpers, a captured public Boolean, break, continue, stride, Id results and
shadowing. They pass 240 comparisons. Raw syntax tests vary public parameter
order, binder information, nondependent flags, nested helper depth, Id results,
loop forms and Boolean tails. They pass 32,256 comparisons, 27,648 invalid-input
checks and 2,304 unused-helper controls on the first attempt. Negative cases
include invalid bodies on unused or unselected paths, mismatched arrow/lambda
input types, invalid result types and nonstandard Id heads or universes.

Selected preceding word-helper, let-annotation and flag-setup tests are rerun;
unrelated extraction modules are reused from the build cache. Full compiler
proof and bounded native Lean/V8 execution checks follow this candidate.

Boolean-result helpers before Boolean loops, retained helper input annotations,
other helper forms, loop-containing continuations and the remaining LeanExe
dialect still require work.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1176 declarations.
