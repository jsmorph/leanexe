# Four-byte GPT-2 model and numerical proofs

This directory defines a small GPT-2-style transformer and proves bounds on
its binary64 computation.  It takes four byte tokens and 2,488 parameters
and produces all 256 next-byte logits.  Its single transformer block has
width four, two attention heads of width two, and feed-forward width eight.

The numerical proofs compare this computation with a real-arithmetic model.
They cover runtime weights in a specified range and give stronger range
certificates for the stored trained checkpoint.  The
[GPT guide](../../../../../docs/gpt/README.md) places this work alongside the
longer tiny models and pretrained GPT-2.

## Model and proof structure

Embedding adds each token row to its position row.  Normalization precedes
causal self-attention and the feed-forward network.  Each sublayer adds its
output to its input.  A final normalization and vocabulary projection
produce the logits for the fourth position.

| Source | Responsibility |
|--------|----------------|
| [Parameter layout](Layout.lean), [binary64 model](Model.lean), and [inference entry](Inference.lean) | Define tensor offsets, the ordered floating-point operations, and construction of the 256-logit output. |
| [Checked entry](Checked.lean) and [checked bounds](CheckedBounds.lean) | Validate byte tokens and weights, clip accepted weights, and connect the wrapper to range and error theorems. |
| [Real model](Real.lean) and [decoding](Decoding.lean) | Define real-arithmetic inference and interpret stored binary64 parameter words. |
| [Runtime stages](RuntimeStages.lean), [runtime logits](RuntimeLogits.lean), and [weight bounds](WeightBounds.lean) | Establish ranges for arbitrary weights within the allowed cap. |
| [Error budget](ErrorBudget.lean) and [numerical logits](NumericalLogits.lean) | Compose rounding, approximation, and input-perturbation errors through the model. |
| [Checkpoint words](CheckpointWords.lean), [checkpoint bounds](CheckpointBounds.lean), and [checkpoint logits](CheckpointLogits.lean) | Check the stored checkpoint and prove input-independent intermediate and output bounds for it. |

The [checked generated-WAT proof](../TinyGpt2Checked/README.md) connects these
source results to executable inference.  The separate raw-inference proof
in [the inference workspace](../TinyGpt2Infer/Inference.lean) covers the
unchecked entry used by arithmetic comparisons.

## Numerical claims

The checked entry accepts exactly 2,488 finite weight words and a finite
bound B in [0, 10], then clips weights to [-B, B].  Every accepted four-byte
input produces finite logits with magnitude at most 1,260.  The error theorem
compares those logits with real arithmetic on the clipped weights.  It uses
the smaller of a composed error formula and the magnitude estimate
1,260 + 12B² + B.

The composed formula takes lower bounds for the denominators in the three
normalization stages.  These bounds concern the real quantity
`sqrt(variance + epsilon)`, where epsilon is 1/100000.  Each bound must hold
for both the ideal real input row and the row obtained by decoding computed
binary64 values.  The square root of epsilon always qualifies.  At B = 10,
the composed formula with these floors evaluates to about 2.934 × 10¹⁴.
The magnitude estimate gives the smaller bound, 2,470 per logit.  This
estimate is too coarse to certify precision.

For the stored checkpoint, `Checkpoint.infer_bounded` proves finite logits
with magnitude at most 117 for every four-byte input.  That theorem uses
facts about the original checkpoint words.  It applies to a checked call
when clipping preserves those words.  The
[checkpoint record](../../../../../data/tiny-gpt2-v1/README.md) includes the
supporting range certificates, adversarial token search, and cancellation
audit.  Sampled audit errors and universally quantified Lean bounds have
different scopes.

## Reproduction

The [training and audit programs](../../../../../training/tiny-gpt2/README.md)
produce checkpoints and numerical evidence.  Commands run from the repository
root after the [development setup](../../../../../DEVELOPING.md):

```sh
tools/tiny-gpt2.js --text 'To b'
tools/tiny-gpt2-certificate.js --check
tools/leanrun --timeout 3m lake -d proofs/talos/lean build \
  Project.TinyGpt2.CheckpointLogits
tools/talos-proof.js check tiny_gpt2_checked
```

The certificate command checks the generated Lean weight array against the
stored checkpoint.  The final command regenerates the checked inference module
and checks its registered execution and numerical specification.
