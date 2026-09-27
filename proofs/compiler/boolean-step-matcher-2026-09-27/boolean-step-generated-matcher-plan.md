# Generated Boolean step matchers

Ordinary match elaborates to a generated declaration such as inspectStep.match_1,
with the motive, scrutinee, done handler and yield handler as arguments. The pure
extractScalarFunc API receives no environment, so recognizing names or suffixes
alone cannot justify expansion. Keep the fixed pure-expression match probe
unchanged and add a production/environment admission probe before implementation.

Inspect the actual generated declaration's type, body, universe parameters,
safety and totality. Recognize its exact canonical nondependent Boolean-step
eliminator definition, with arbitrary binder names. Do not accept a declaration
because its name looks like a generated matcher. Preserve malformed/altered
matcher fixtures as negative controls.

Define an independent source expansion/reduction relation justified by the checked
declaration body, plus congruence under the original expression constructors.
Prove the environment normalizer produces that relation; relate the original
expression to source application after expansion through an explicit environment
source semantics. Do not define source correctness solely by running the compiler
or by giving arbitrary constants the semantics of a matcher.

Preserve the existing pure extraction path and its theorems. An environment-aware
fallback may expand checked matchers only after direct extraction fails. Connect
that fallback at both ordinary and arithmetic production entries, and extend the
public source-to-WASM theorem to the original environment/source relation while
reusing the proved pure extractor and WASM backend. Audit new public theorems.
Keep the canonical source-to-byte path for already admitted programs unchanged.

Complete this capability through actual generated match examples, arbitrary
captures and nesting, exact type/universe/domain rejection tests, source proofs,
production extraction, binary decoding/validation/execution, and independent V8
comparison before admitting broader top-level calls or recursive declarations.
