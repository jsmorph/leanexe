# Word prefixes with Boolean-result loop continuations

Preserve the rejected word-to-Boolean sequence probe. Extend the sequence grammar
with Boolean-result leaves and word-result prefixes, including two/three prior
loops, dependent bounds, early exits, unused values, captures and retained Id
annotations. Each prefix uses the existing proved word sequence, and the Boolean
continuation recursively uses the new grammar. The result is encoded as zero or
one. This increment does not yet add Boolean-result bound prefixes.

Reuse ScalarSequencePlan, finite-store framing, descriptor admission, WASM
execution, function bytes and stack typing. Prove new independent source
semantics and totality, extractor completeness and soundness, capture preservation,
result encoding and bounded reads. Add a separate public admission branch so
existing plans keep their bytes. Check native/raw syntax cases and invalid inputs,
then the public proof gate and V8 before the next capability.
