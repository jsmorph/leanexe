# Two-argument UInt64-to-Bool local helpers

Preserve the six fixed native probes. Add a distinct binary predicate kind to
source values and compiled lexical bindings. Its semantic relation must encode
native Bool results as zero or one and keep both argument values in source order.
Do not reuse word-returning function kinds: malformed word/predicate uses must
remain distinguishable in the independently checked source grammar.

Start with two bare UInt64 inputs and Bool results under standard Id layers.
Retain both arrow and lambda binders, the local declaration name and nondep flag.
Match both domains exactly. Check unused bodies with two typed placeholder
arguments. Capture outer values lexically; allow repeated calls and general
Boolean bodies and continuations. Both scalar lets and lets inside Bool.toUInt64
need support. Recursively check both call arguments, including unused arguments.

Use separate exact declaration/call descriptions and parser proofs. Reuse the
existing general Boolean conversion checker for helper bodies rather than adding
a second Boolean evaluator. Add source totality and extraction evaluation,
acceptance, reconstruction and IR invariant proofs. Prove the new lexical-kind
projections and mappings preserve all existing helper and step behavior.

Work through small dependency boundaries. Complete fixed probes, malformed input
and kind checks, native/IR comparisons, the complete source-to-WASM theorem and
independent V8 execution. Archive logs and hashes, update task.md and commit/push
frequently. Bool inputs, retained Id input annotations, larger arities and other
compiler coverage remain separate increments.
