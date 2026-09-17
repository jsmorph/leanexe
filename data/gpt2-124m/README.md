# Pretrained GPT-2 124M

The CPU reference runs the original 124,439,808-parameter GPT-2 checkpoint
with its byte-pair tokenizer.  It has twelve layers, width 768, twelve
attention heads, a 3,072-wide feed-forward layer, and 50,257 vocabulary
entries.  The reference limits the prompt and completion together to
128 tokens.  The checkpoint retains its original 1,024 positional rows.

## Run the reference

The approved environment already contains PyTorch 2.9.1+cpu.  Install the
pinned reference dependencies and download the pinned model files:

```sh
.venv-tiny-gpt2/bin/python -m pip install -r training/gpt2/requirements.txt
.venv-tiny-gpt2/bin/python training/gpt2/reference.py fetch
.venv-tiny-gpt2/bin/python training/gpt2/reference.py generate \
  --text 'Once upon a time, in a small village' --max-new-tokens 64 --seed 42
```

Generation uses CPU PyTorch FP32 and Transformers 4.57.6.  The default
sampling parameters are top-k 40 and temperature 0.8.  `--top-k 1` selects
greedy generation.  `--json` includes token IDs, checkpoint identity,
settings, elapsed time, and the stopping condition.  Generation stops at
the requested count, the end-of-text token, or the 128-token boundary.

The manifest pins each downloaded file by SHA-256.  The command checks
these hashes before loading the model.  Downloads live in the ignored
`build/gpt2-124m` directory.  The 548,105,171-byte safetensors file includes
legacy attention masks.  Its learned FP32 parameters occupy 497,759,232 bytes.

## Execution evidence

The [reference completions](reference-completions.json) record three CPU
runs.  The first prompt continued:

> , there was a man named Miho who had been raised by his mother and father, and it was for his father to send him to the capital and teach him the law.

That run generated 64 tokens in 3.8 seconds using one CPU thread.
LeanExe/WASM execution of this model is the current development target.
The user approved FP32 arithmetic and packed binary tensors and paused
proof development.  The [implementation plan](../../plans/gpt2-124m.md)
records the remaining work.

The first attention projection runs through LeanExe/WASM with the
pretrained 768 × 2,304 matrix and bias.  Its 2,304 FP32 outputs match a
serial PyTorch evaluation with the same operation order bit-for-bit.
The maximum absolute difference from PyTorch's standard matrix
multiplication is 2.6226043701171875e-6.  The measured host call took
0.034 seconds, including module startup and binary input loading.
The [kernel test record](kernel-test.json) identifies the artifact and
checkpoint.  Reproduce it with:

```sh
node test/packed.js --gpt2-kernel
```

## Sources

The [pinned checkpoint](https://huggingface.co/openai-community/gpt2/tree/607a30d783dfa663caf39e06633721c8d4cfcd7e),
[original model](https://github.com/openai/gpt-2/blob/master/src/model.py),
and [original tokenizer](https://github.com/openai/gpt-2/blob/master/src/encoder.py)
define the model and tokenization used for this reference.
