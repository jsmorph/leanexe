# Pretrained GPT-2 124M

The CPU reference runs the original 124,439,808-parameter GPT-2 checkpoint
with its byte-pair tokenizer.  It has twelve layers, width 768, twelve
attention heads, a 3,072-wide feed-forward layer, and 50,257 vocabulary
entries.  The reference limits the prompt and completion together to
128 tokens.  The checkpoint retains its original 1,024 positional rows.

## Run WASM inference

From the repository root:

```sh
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
```

The command compiles the Lean model, keeps its packed weights in one
Wasmtime instance, and prints the prompt and completion.  The original
tokenizer handles text.  Model arithmetic runs in WASM.  Top-k sampling
uses the Lean SplitMix64 WASM generator for random draws and Python for
the sampling probabilities.  Defaults are top-k 40, temperature 0.8, and
seed 42.  Use `--top-k 1` for greedy decoding and `--json` for token IDs,
timing, allocation counts, and the stopping condition.

Generation stops at the requested count, end-of-text, or 128 total tokens.
`--logits PATH` saves the final evaluated context's 50,257 logits as
little-endian FP32 words.  Those logits select the last generated token.
The command currently recomputes the prefix at each step.  A key/value
cache is in development.  The [first WASM completion](wasm-completion-uncached.json)
generated sixteen tokens in 93 seconds and used 514,654,208 bytes of WASM
linear memory.  It continued the example prompt with:

> called Hukur. The village is a great expanse of white sand and

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
LeanExe/WASM execution now generates text from the same checkpoint.
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

The complete first transformer block also runs in WASM.  For the nine-token
story prompt, its output differs from PyTorch by at most
0.00026702880859375 in absolute value.  The test compares all intermediate
stages, then checks that the composed block matches the separately invoked
WASM stages bit-for-bit.  Allocation counters show eighteen freed
temporaries, with the two inputs and one output remaining.  The block call
took 0.291 seconds.  The [block test record](block-test.json) contains each
stage's measurement.  Reproduce it with:

```sh
node test/packed.js --gpt2-block
```

The full model returns all 50,257 next-token logits.  On the same nine-token
prompt, its maximum absolute difference from PyTorch is 0.00009918212890625,
and its RMS difference is 0.000040563035721151586.  Both select token 11,
the comma, as the maximum.  The host call took 3.874 seconds.  Its 235
allocations and 232 frees leave the weights, input tokens, and output.
The [full inference test record](inference-test.json) identifies the run.

```sh
node test/packed.js --gpt2-inference
```

## Sources

The [pinned checkpoint](https://huggingface.co/openai-community/gpt2/tree/607a30d783dfa663caf39e06633721c8d4cfcd7e),
[original model](https://github.com/openai/gpt-2/blob/master/src/model.py),
and [original tokenizer](https://github.com/openai/gpt-2/blob/master/src/encoder.py)
define the model and tokenization used for this reference.
