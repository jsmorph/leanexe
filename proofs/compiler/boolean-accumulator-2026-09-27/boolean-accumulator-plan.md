# Boolean loop accumulators

The previous helper-body probes exposed three rejected Boolean-accumulator
programs. Six additional fixed probes cover toggling, index comparisons,
conditional updates, break, continue and positive stride. Run them before editing
production and retain their elaborated toggle/break bodies.

Start with a Boolean step grammar sufficient for direct yield/done, standard Id
pure/run, metadata, checked conditional branches and scalar word/Boolean lets.
Expand composition only after this grammar has a complete source-to-WASM proof.
Do not claim support for local step-returning functions until they are covered.

Reusable proof structure:

- A Boolean accumulator iteration and native strided-list/range theorem.
- `encodeStep` maps ForInStep Bool to ForInStep UInt64, retaining yield/done.
- `iterate_encode` relates Boolean iteration to the existing word iteration,
  decoding the word accumulator with `value != 0` on every step. The initial
  state and all step results are encoded as zero or one.
- Normalize the compiled accumulator binding as
  `guardWord (lowerComparison .bne (.local slot) (.u64 0))`, exactly as public
  Boolean arguments do. This permits the existing loop Meaning theorem to
  quantify over arbitrary UInt64 accumulator words, not just zero and one.
- A Boolean step extractor can return the existing ScalarStepCode, with Meaning
  applied to the encoded Boolean outcome. Scalar expression correctness,
  acceptance and invariants remain reusable.
- A Boolean range syntax/view mirrors the small existing Range.Exit head/call
  and scalarRangeExit? parser, using Bool in the accumulator positions. Keep the
  entire standard range instance, checked positive stride and metadata-aware Nat
  index checks. Avoid changing the existing word range syntax.
- The Boolean range plan uses the existing count/stride lowering, four fresh
  locals and ScalarRangeExitPlan.Meaning. Native iteration encoding supplies the
  final result equality.
- Extend Source.Scalar.BooleanRange Eval/Supported with this new range rule.
  The extractor's final fallback (the `none` branch of booleanRangeWrapper?) can
  call the new nonrecursive Boolean-accumulator extractor. This keeps existing
  functional case numbering and wrapper recursion. Update source totality,
  acceptance/support, correctness and invariants, then public/compiler audits.

Relevant existing files: Source/ScalarRangeStride.lean (native stride proof),
Source/ScalarRangeExitSyntax.lean and Extract/ScalarRangeExitSyntax.lean (small
exact range parser), Extract/ScalarStepBindings.lean (code/Meaning),
Extract/ScalarRangeExitCorrectness.lean (plan Meaning and range construction),
Extract/ScalarPublicBindings.lean (normalized Boolean local),
Extract/ScalarBooleanRange.lean (final wrapper fallback), and its correctness
and invariant modules. A scratch iteration proof is ready but has not run while
the preceding candidate is being checked.

Id inputs in converted helper scopes, multiple dynamic loops, retained instances,
broader signatures and the rest of the dialect remain open.
