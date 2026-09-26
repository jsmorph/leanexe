# GPT inference and verification

LeanExe runs transformer inference written in Lean as WebAssembly. The examples
range from small byte-token models with numerical error bounds to pretrained
GPT-2 124M with complete cached-inference execution proofs. Model weights are
runtime data; LeanExe compiles the inference algorithm.

Each inference call returns logits: one score for every possible next token.
The host selects a token, extends the prompt, and repeats. Pretrained GPT-2 uses
its byte-pair tokenizer and keeps an attention key/value cache between calls.
The tiny models assign one token to each byte.

## Run pretrained GPT-2

Configure the [development environment](../../DEVELOPING.md#prerequisites) and
install `uv`. From the repository root, fetch the pinned checkpoint:

```sh
uv run --project training/gpt2 training/gpt2/reference.py fetch
```

Run FP32 inference, quantized inference, or the CPU PyTorch reference:

```sh
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
tools/gpt2 --quantized --text 'Once upon a time, in a small village' --generate 32
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
```

`uv` manages the pinned Python dependencies. The WASM commands prepare packed
weights when needed and check weight and tokenizer identities. The FP32 command
builds the selected Lean entry. The quantized command loads the exact binary
selected by its [model manifest](../../data/gpt2-quantized-v1/model.json).

| Option | Use |
|--------|-----|
| `--generate N` | Request up to N new tokens. Prompt and completion together are limited to 128 tokens. |
| `--top-k 1` | Select greedy decoding. The default samples among the top 40 logits at temperature 0.8. |
| `--seed N` | Set the sampling seed; the default is 42. |
| `--json` | Return token IDs, model and binary identity, timing, allocation information, and stopping condition. |
| `--logits PATH` | Save the last evaluated context's 50,257 little-endian FP32 logits. |
| `--full` | Recompute the FP32 prefix instead of using the cache; mutually exclusive with `--quantized`. |

Generation also stops at the end-of-text token. FP32 parameters occupy
497,759,232 bytes; quantized weights occupy 127,695,972 bytes. Runtime memory
includes weights, caches, and intermediate tensors. See the model records for
measured memory and runtime under their stated conditions.

## Models and results

| Model | Computation | Verification and evidence |
|-------|-------------|---------------------------|
| [Pretrained GPT-2 124M](../../data/gpt2-124m/README.md) | Twelve width-768 transformer blocks, FP32 arithmetic, 50,257 output logits, and up to 128 tokens. | Exact cached token-step and session proofs, plus a separately identified exact-binary package. Reference tests compare 6,432,896 logits across 128 prefixes. Real-arithmetic error bounds remain open. |
| [Quantized GPT-2 124M](../../data/gpt2-quantized-v1/README.md) | INT8 projection weights and activations grouped in 64 coordinates, signed 32-bit partial sums, and surrounding FP32 computation. | Complete session and exact-binary proofs, including rejection, termination, allocation, and release. Tests compare every logit and cache against the independent quantized reference. Numerical bounds are proved but too coarse to establish all greedy choices. |
| [Four-byte tiny GPT-2](../../data/tiny-gpt2-v1/README.md) | Four byte tokens, 2,488 binary64 parameters, one width-four block, and 256 output logits. | Generated-WASM execution and numerical proofs, with runtime weight validation and clipping. The unconditional error bound is too coarse to certify precision. |
| [64-position](../../data/tiny-gpt2-64-v1/README.md) and [128-position tiny GPT-2](../../data/tiny-gpt2-128-v1/README.md) | Byte-token models with longer position tables. | Trained checkpoints and CPU tests; the 128-position model generates text in WASM. Its complete execution proof remains open. |

The pretrained checkpoint contains 1,024 positional embeddings; this implementation
and its session theorem support positions zero through 127. Quantized inference
implements a different arithmetic recurrence from FP32 and can select different
tokens. The [quantized measurements](../../data/gpt2-quantized-v1/README.md)
describe speed, memory, and token agreement for the measured prompts and settings.

Run the tiny examples with:

```sh
tools/tiny-gpt2.js --text 'To b'
tools/tiny-gpt2.js --context 128 --text 'ROMEO:' --generate 160
```

The 128-position tiny model advances a window of byte tokens, so its output
length is not limited to 128 total tokens.

## Data and execution

The [Python tools](../../training/gpt2/README.md) fetch and validate a pinned
checkpoint, pack the weights, and tokenize text. The
[Lean model](../../LeanExe/Models/Gpt2/README.md) implements embeddings,
normalization, attention, projection, activation, and cached inference.

The native host loads the WASM module and weights into one Wasmtime instance.
Each token call takes weights, a cache, a token ID, and a position; it returns
the extended cache and a logit vector. The host releases the preceding cache,
retains the returned cache, reads and releases the logits, and selects the next
token. Model arithmetic executes inside WASM. Tokenization, sampling
probabilities, and text decoding execute in the host; WASM SplitMix64 supplies
the WASM command's sampling draws.

The [tiny-model training tools](../../training/tiny-gpt2/README.md) provide the
PyTorch model, exporter, checkpoints, and numerical audits. The four-byte entry
validates inputs and clips finite weights to the requested bound before inference.

## Proofs and evidence

| Question | Proof boundary |
|----------|----------------|
| Does a token call compute the Lean algorithm? | The [cached-step theorem](../../proofs/talos/lean/Project/Gpt2CachedStep/README.md) proves exact cache and logit bytes, termination, a valid resulting heap, and preservation of protected inputs under its representation and capacity assumptions. |
| Does a complete session behave correctly? | The session theorem composes initialization, weight loading, successive token calls, and buffer release. It derives the per-call heap and representation conditions for the specified inputs. |
| Do particular binary bytes have that behavior? | Exact-artifact proofs check embedded bytes, decoding, validation, and translation to the proved execution model. Their guarantee applies to the identified binary. |
| Are the logits close to real arithmetic? | Separate numerical theorems bound error under stated input and weight conditions. Execution equality alone does not establish numerical accuracy or token agreement with another implementation. |

The FP32 source check regenerates compiler output and verifies its execution
model. Its exact-artifact check verifies the binary named in the package, a
separate proof subject. The FP32 CLI reports its emitted binary hash with
`--json`. The quantized CLI checks its selected binary against the artifact
manifest before running it. [Checking instructions](../../proofs/talos/lean/Project/Gpt2CachedStep/README.md#checking-and-evidence)
and the [quantized proof package](../../proofs/talos/lean/Project/Gpt2QuantizedCached/README.md)
identify the respective commands and theorem targets.

Execution equality fixes the implemented arithmetic, including approximations
and exceptional floating-point values. The FP32 runtime uses Wasmtime with
canonical NaNs. Tokenization, sampling, the native host, and Wasmtime are outside
the Lean proof. The session theorem specifies the required host call sequence.

For the four-byte model, accepted weights are clipped to a bound B in [0, 10].
At B = 10, the theorem gives finite logits of magnitude at most 1,260 and
absolute error at most 2,470 against the real model with clipped weights.
These bounds do not establish useful output precision.

The quantized [numerical certificates](../../data/gpt2-quantized-v1/certificates/README.md)
cover 302 evaluated prefixes. Propagated forward bounds certify no token choices;
separate certificates from measured logits establish 232 individual greedy
choices. Operand identity with the source recurrences remains an explicit
assumption, and data evaluation trusts the pinned native Lean compiler and runtime.

The [Talos inventory](../../proofs/talos/README.md) lists theorem targets and
checks. The [cached execution report](../../paper/gpt2-verification-report/README.md)
and [comprehensive GPT report](../../paper/gpt2-comprehensive-report/README.md)
provide detailed accounts of the algorithms and verification.
