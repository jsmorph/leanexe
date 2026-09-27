# Scalar helper declarations within Boolean steps

Preserve four fixed probes before changing admission. Add native UInt64-to-UInt64,
UInt64-to-Bool, Bool-to-UInt64 and Bool-to-Bool closures using the existing scalar
binding kinds projected by BooleanStep.Value.toScalar and BooleanStepBinding.toScalar.
Check exact input/domain/output annotations with arbitrary standard Id layers.
Reuse scalar expression totality, acceptance, correctness and invariants for every
function body. Check unused bodies as well. Calls remain in scalar operands, so the
existing scalar call proofs preserve captures and results; no new call evaluator
is needed in the Boolean step extractor. Prove source and extraction rules through
the public source-to-WASM theorem and independent V8 execution before proceeding.
