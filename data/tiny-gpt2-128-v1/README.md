# Tiny GPT-2 with 128 positions

This checkpoint has 128 byte-token positions, 2,984 binary64 parameters,
model width four, two attention heads, feed-forward width eight, and one
block.  The inference implementation and source-equivalence proof are
in progress.

## Training record

The [checkpoint](checkpoint.json) contains parameter words, training
settings, losses, and sampled intermediate ranges.  Its SHA-256 is
`1e98ac0661cec2eed22473af75bb5ca2dac8bf1dd9a1788567981f57df4e6356`.
All weights are finite.  The largest magnitude is 2.3113755988772042.

Training used CPU PyTorch 2.9.1, binary64, seed 17, and 4,000 Adam steps
with batches of 128 and learning rate 0.001.  The pinned Tiny Shakespeare
corpus has SHA-256
`86c4e6aa9db7c042ec79f339dcb96d42b0075e16b8fc2e86bf0ca57e2dc565ed`.

| Cross-entropy | Before training | After training |
|---|---:|---:|
| Training sample | 5.560414376350679 | 2.691717849358304 |
| Validation sample | 5.5597421815995585 | 2.691612944826216 |

## Reproduction and verification scope

The [training instructions](../../training/tiny-gpt2/README.md) describe
the approved environment.  From the repository root:

```sh
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --context 128 --corpus build/tiny-gpt2/tiny-shakespeare.txt \
  --output build/tiny-gpt2/context128-checkpoint.json
```

The [inference plan](../../plans/tiny-transformer.md) requires a checked
proof that the generated module computes its Lean source, including
termination and memory guarantees.  The proof will accept runtime weights.
Further real-arithmetic error bounds are deferred.  The checkpoint's
sampled ranges remain empirical measurements.
