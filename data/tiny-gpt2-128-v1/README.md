# Tiny GPT-2 with 128 positions

This checkpoint has 128 byte-token positions, 2,984 binary64 parameters,
model width four, two attention heads, feed-forward width eight, and one
block.  The WASM implementation produces text completions.  Its complete
source-equivalence proof is paused.  The
[GPT guide](../../docs/gpt/README.md) explains how this byte-token model
relates to four-byte numerical verification and pretrained GPT-2 execution.

## Command-line generation

```sh
tools/tiny-gpt2.js --context 128 --text 'ROMEO:' --generate 160 --seed 42
```

The command prints the prompt and generated text.  Sampling defaults to
top 40 logits and temperature 0.8.  `--top-k 1` selects the highest logit.
`--json` adds token IDs, checkpoint identity, and sampling settings.
Omitting `--generate` returns all 256 logits as JSON.  Prompts contain
one through 128 UTF-8 bytes.  Generation keeps the most recent 128 bytes
and assigns them positions starting at zero for each inference call.

The [recorded completions](completions.json) contain three 160-byte samples.
They consist mostly of invented words and fragments.  All 480 sampled
bytes match CPU PyTorch with the same random draws.  Across those steps,
the largest absolute difference among 122,880 logits was
2.3092638912203256e-14.  Each WASM sample took about 4.4 seconds on the
development machine.  These are execution measurements.

The [module manifest](manifest.json) records the 24,596-byte WASM artifact
and its verification status.  Sampling uses the existing Lean SplitMix64
WASM program.  The host applies temperature and computes sampling weights.

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
