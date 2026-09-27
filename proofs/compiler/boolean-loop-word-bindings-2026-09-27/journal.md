# Pure bindings around word results of Boolean loops

The word-result path now composes pure word/Boolean setup before its recursive
body and pure word continuations after a recursively extracted word result.
Boolean loop-value candidates keep their prior priority. Word bindings try scalar
setup before the loop-value fallback. Standard Id annotations and exact monadic
input/domain equality are retained.

The previous Boolean binding combinator is now ScalarRangeBinding with the generic
name scalarRangeValueBinding, reused for word bindings. The new loop-first form
preserves the existing Boolean-to-word path and delays scalar setup until needed.
Source totality passed immediately. The first helper proof attempt let simp
simplify the alternative before using the equation for its first candidate;
explicitly rewriting that candidate first fixed the proofs. Extraction acceptance
then passed; unused simp arguments were removed before the preservation build.

Support recovery, evaluation preservation, generic invariants and public WASM
admission pass. Raw tests pass 129,024 native/IR comparisons, 76,800 invalid-input
checks and 6,144 lexical/direct-conversion controls. The first native fixture
build failed to elaborate arithmetic directly on retained Id word aliases;
explicit Id.run bindings now supply the word operands while preserving the
annotated inputs. The failed native fixture and log are retained.

All ten native fixtures now pass 240 comparisons. The explicit Id.run operands
retain the nested Id bind annotations and additionally exercise scalar word setup.
No production changes were needed for the native fixture correction.

The correctness guide now describes current Boolean/word loop continuations,
setup bindings, local loop calls and conditional arms. It removes stale statements
that public Boolean inputs or loop-containing local continuations are excluded,
and retains the limits on multiple dynamic loops and broader helper placement.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1327 declarations.
