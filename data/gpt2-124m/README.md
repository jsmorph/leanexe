# Pretrained GPT-2 124M

The CPU reference runs the original 124,439,808-parameter GPT-2 checkpoint
with its byte-pair tokenizer.  It has twelve layers, width 768, twelve
attention heads, a 3,072-wide feed-forward layer, and 50,257 vocabulary
entries.  The reference limits the prompt and completion together to
128 tokens.  The checkpoint retains its original 1,024 positional rows.

## Run WASM inference

The [reference setup](#run-the-reference) downloads the checkpoint.  Both
commands use `uv` to install their pinned Python dependencies.  From the
repository root:

```sh
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
```

The equivalent CPU PyTorch command is:

```sh
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
```

The WASM command compiles the Lean model, keeps its packed weights and attention
cache in one Wasmtime instance, and prints the prompt and completion.
The original tokenizer handles text.  Model arithmetic runs in WASM.  Top-k sampling
uses the Lean SplitMix64 WASM generator for random draws and Python for
the sampling probabilities.  Defaults are top-k 40, temperature 0.8, and
seed 42.  Use `--top-k 1` for greedy decoding and `--json` for token IDs,
timing, allocation counts, and the stopping condition.

Generation stops at the requested count, end-of-text, or 128 total tokens.
`--logits PATH` saves the final evaluated context's 50,257 logits as
little-endian FP32 words.  Those logits select the last generated token.
The default uses cached keys and values for prior tokens.  `--full`
recomputes the prefix for comparison.  The [first WASM completion](wasm-completion-uncached.json)
generated sixteen tokens in 93 seconds and used 514,654,208 bytes of WASM
linear memory.  It continued the example prompt with:

> called Hukur. The village is a great expanse of white sand and

The [cached completions](wasm-completions.json) record three runs.  The
story prompt generated 64 tokens in 35.4 seconds, with the same first
sixteen tokens as the earlier full-prefix run.  A sixteen-token greedy
completion matches PyTorch's token sequence exactly.

## Run the reference

The [uv project](../../training/gpt2/pyproject.toml) and its lockfile pin
PyTorch 2.9.1, Transformers 4.57.6, and their dependencies.  Linux and Windows
use PyTorch's CPU wheel index.  `uv` creates `training/gpt2/.venv` on the
first invocation.  The project selects Python 3.13.  Download the pinned
model files once:

```sh
uv run --project training/gpt2 training/gpt2/reference.py fetch
```

Both Python programs also run through `uv` directly:

```sh
uv run --project training/gpt2 training/gpt2/wasm.py --text 'Once upon a time, in a small village' --generate 32
uv run --project training/gpt2 training/gpt2/reference.py generate --text 'Once upon a time, in a small village' --generate 32
```

Generation uses CPU PyTorch FP32 and Transformers 4.57.6.  The default
count is 32 new tokens, with top-k 40, temperature 0.8, and seed 42, matching
the WASM command's settings.  `--max-new-tokens` remains an alias for
`--generate`.  PyTorch uses its seeded sampler, while the WASM command uses
Lean SplitMix64 draws.  `--top-k 1` selects greedy generation.  `--json`
includes token IDs, checkpoint identity,
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
The user approved FP32 arithmetic and packed binary tensors.
The [development plan](../../plans/gpt2-124m.md) records the completed
implementation and the resumed exact execution proofs.

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

The [cached inference test](cached-test.json) compares 6,432,896 logits
against PyTorch across all prefix lengths from one to 128 tokens.  The
maximum absolute difference is 0.0014495849609375.  Every comparison passes
the test tolerance of 0.002 + 0.0001 times the reference magnitude.  Cached
and full-prefix WASM logits match bit-for-bit for the nine-token prompt.
The test also checks cache reset, the position limit, invalid token IDs,
invalid cache lengths, and incorrect weight lengths.  These are execution
measurements for the recorded checkpoint and token sequence.

The 128-position test took 63.2 seconds and reached 1,107,361,792 bytes of
WASM linear memory.  After each call, only the weights and current cache
remain allocated.  The allocator reuses whole freed blocks.  Growing cache
buffers leave smaller blocks on the free list, which accounts for the
difference between the linear-memory size and live tensor storage.
The final key/value cache contains 9,437,184 bytes.

```sh
node test/packed.js --gpt2-cached
node test/packed.js --gpt2-completions
```

The [cached Lean model](../../LeanExe/Models/Gpt2/Cached.lean) defines the
token step.  The [command-line client](../../training/gpt2/wasm.py) keeps the
WASM instance resident and releases each superseded cache and logit buffer.

## Formal execution proof

The [public cached-step theorem](../../proofs/talos/lean/Project/Gpt2CachedStep/Spec.lean)
proves that the generated module terminates and returns the exact cache and
logit bytes specified by the Lean token step.  It covers embedding, all twelve
transformer blocks, final normalization, all 50,257 scores, allocation, and
temporary-buffer cleanup.  Invalid weight length, token, position, or cache
length returns empty outputs with the store unchanged.

The [128-position theorem](../../proofs/talos/lean/Project/Gpt2CachedStep/Session/Spec.lean)
derives the initial heap, input representation, and allocation conditions.
It starts with module initialization, reset, weight allocation, and the byte
copy that encodes the input.  It then composes up to 128 token calls, releases
each previous cache, reads every returned logit vector, and releases that
vector.  Each cache and logit vector equals the corresponding result of the
Lean `cachedStep` recurrence.  The theorem takes arbitrary 497,759,232-byte
weights and vocabulary token IDs.  Its heap-top allowance is 512 MiB plus
16 MiB per token, within the module's 4 GiB address limit.

The proof uses Lean's logical Float32 model and Talos execution semantics.
The command-line host uses Wasmtime 44.0.0 with Cranelift and canonical NaNs,
as required for exact NaN words.  Tokenization, token selection, the native
host implementation, and Wasmtime are outside the Lean proof.  The theorem
specifies and proves the host's WASM call sequence and byte input/output
boundary.  Numerical error bounds, exact-byte packaging, and comparison with
the separate full-prefix Lean algorithm remain outside this proof target.

The [canonical-mode test record](canonical-mode-test.json) records 86 FP32
cases, all 6,432,896 logits across contexts one through 128, rejection and
reset checks, and three text completions.  The greedy completion matches
PyTorch's token sequence.  The tested module has the same SHA-256 hash as
the source-artifact gate's generated module.

Regenerate the module and check its execution proof with:

```sh
tools/talos-proof.js check gpt2_cached_step
```

## Sources

The [pinned checkpoint](https://huggingface.co/openai-community/gpt2/tree/607a30d783dfa663caf39e06633721c8d4cfcd7e),
[original model](https://github.com/openai/gpt-2/blob/master/src/model.py),
and [original tokenizer](https://github.com/openai/gpt-2/blob/master/src/encoder.py)
define the model and tokenization used for this reference.
