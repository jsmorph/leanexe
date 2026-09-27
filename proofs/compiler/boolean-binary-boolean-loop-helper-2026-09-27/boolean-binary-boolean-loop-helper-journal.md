# Binary Boolean helpers around Boolean-result loops

Five fixed probes reject before this extension; the word-tail probe already
compiles through WordRange. All six are preserved unchanged. The source rules
reuse the scalar binary predicate kind and prove totality for every captured
source environment. That boundary passes 82 targets on its first attempt.

Extraction retains the scalar-conversion path and tries the binary Boolean helper
only after word-result and many-word recognition reject. The unused body is
checked with two word placeholders, and the continuation uses the captured
closure. The isolated termination/equation check passes first try. Functional
induction adds case 7, shifting later cases by one.

Complete acceptance, source reconstruction, correctness across all loop states
and IR invariants pass 197 targets on the first combined attempt. No new source
value kind, IR form or axiom is required. Function integration and the focused
native/syntax checks are next, followed by the full WASM and engine checks.

Function integration passes 211 targets. All six fixed probes now compile; the
word-tail probe remains explicitly recorded as admitted before this extension.
Eight native fixtures pass 192 comparisons. The syntax matrix passes on its first
run: 9,216 comparisons, 17,664 invalid-input checks and 384 admission controls.
It covers ordinary and retained Id results, both parameter binder annotations,
wrappers, Boolean junctions, unused helpers, helper-dependent bounds and initial
flags, saved Boolean loop results and post-loop calls. Malformed signatures,
bodies and calls are checked in variable and empty ranges. The V8 group retains
all 106 prior declarations and adds eight fixtures.
