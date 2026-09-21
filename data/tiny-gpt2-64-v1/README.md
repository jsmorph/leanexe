# Tiny GPT-2 with 64 positions

This checkpoint extends the [four-byte model](../tiny-gpt2-v1/README.md)
to 64 byte-token positions.  It has 2,728 binary64 parameters, model width
four, two attention heads, feed-forward width eight, and one block.
The inference implementation and its proofs remain in progress.
The [GPT guide](../../docs/gpt/README.md) explains the model families and
verification goals.  The [training programs](../../training/tiny-gpt2/README.md)
produce this checkpoint and its CPU measurements.

## Training record

The [checkpoint](checkpoint.json) contains raw parameter words, training
settings, losses, and sampled intermediate ranges.  Its SHA-256 is
`af60facd001d370103c85be793f61585fd290131662a86175f166b5967fd83ff`.
All parameters are finite.  The largest magnitude is 2.7499298233598095.

Training used the pinned Tiny Shakespeare corpus, CPU PyTorch 2.9.1,
binary64 arithmetic, seed 17, and 4,000 Adam steps with batches of 128.
The learning rate was 0.001.  The corpus SHA-256 is
`86c4e6aa9db7c042ec79f339dcb96d42b0075e16b8fc2e86bf0ca57e2dc565ed`.

| Cross-entropy | Before training | After training |
|---|---:|---:|
| Training sample | 5.565727318069322 | 2.696126407289435 |
| Validation sample | 5.567620995482236 | 2.696367581735353 |

The model accepts nonempty prefixes through length 64.  CPU tests check
output shapes, causal prefix equality, and finite gradients for both
context sizes.  The checkpoint's sampled ranges and these tests provide
empirical evidence.  Formal inference bounds must follow from the weight
checker and proved numerical components.

## Reproduction

The [training instructions](../../training/tiny-gpt2/README.md) describe
the approved environment.  From the repository root:

```sh
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --context 64 --corpus build/tiny-gpt2/tiny-shakespeare.txt \
  --output build/tiny-gpt2/context64-checkpoint.json
```
