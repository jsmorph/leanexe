# Pretrained GPT-2 host and reference

This directory loads the pretrained GPT-2 124M checkpoint, runs a CPU PyTorch
reference, and drives the LeanExe-compiled WASM model.  It exports checkpoint
weights and comparison tensors, tokenizes text, selects output tokens, and
records execution results.  The [GPT guide](../../docs/gpt/README.md) explains
the development goals and model families.

The two generation commands share a pinned checkpoint and tokenizer.
PyTorch evaluates the reference model in binary32.  The WASM path evaluates
the [Lean algorithm](../../LeanExe/Models/Gpt2/README.md) in a resident
Wasmtime instance.  Both limit the prompt and completion together to
128 tokens.

## Components and data flow

| File | Responsibility |
|------|----------------|
| [Reference and export program](reference.py) | Download and check checkpoint files, load the PyTorch model, export packed weights and comparison tensors, and generate reference text. |
| [WASM host client](wasm.py) | Check exported weights, compile the Lean entry, start the C host, manage cache and logit buffers, and generate text. |
| [WASM comparison test](test_wasm.py) | Compare cached logits with PyTorch across 128 prefixes and exercise cache reset and rejected inputs. |
| [Python project](pyproject.toml) and [dependency lock](uv.lock) | Pin the Python environment used by both commands. |

The [checkpoint manifest](../../data/gpt2-124m/manifest.json) pins downloaded
files by SHA-256.  Downloads and packed weights live under the ignored
`build/gpt2-124m` directory.  The exporter writes weights as little-endian
binary32 tensors in the order expected by the Lean model.

The WASM client loads the weights once.  Each cached call receives one token
and the preceding cache, then returns the updated cache and a logit vector.
The client releases the preceding cache and returned logits, and retains
the new cache for the next call.  A repeated, changed, or shortened prefix
causes a cache reset.  `--full` selects full-prefix recomputation.

## Setup and commands

The [development guide](../../DEVELOPING.md) specifies the Lean, Node,
Wasmtime, and compiler prerequisites.  `uv` creates this project's Python
environment from its pinned dependencies.  From the repository root:

```sh
uv run --project training/gpt2 training/gpt2/reference.py fetch
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
```

The WASM command compiles the model and builds the C host before generation.
Its Lean subprocesses use `tools/leanrun`.  Defaults are top-k 40,
temperature 0.8, and seed 42.  `--top-k 1` selects the highest logit.
`--json` records token IDs, settings, timing, allocation counts, stopping
conditions, and the compiled module's `wasm_sha256`.  `--logits PATH` saves
the last evaluated vector as raw binary32 words.  Generation accepts a prompt
of one to 127 tokens, leaving room for at least one output token.  The
`WasmModel.infer` API accepts a prefix of up to 128 tokens.  PyTorch and WASM
use different random-number generators for sampling.

The repository test driver prepares inputs, builds the selected WASM modules,
and runs the comparison programs:

```sh
node test/packed.js --gpt2-cached
node test/packed.js --gpt2-completions
```

## Verification boundary

The [cached-inference proofs](../../proofs/talos/lean/Project/Gpt2CachedStep/README.md)
specify exact WASM results and the sequence of token calls, input encoding,
and buffer releases.  They use Lean's logical binary32 arithmetic and
Talos execution semantics.  The C host selects Wasmtime's canonical-NaN mode
to match the specified NaN words.

Tokenization, token selection, the Python and C implementations, and Wasmtime
remain outside the formal proof.  The
[checkpoint records](../../data/gpt2-124m/README.md) contain measured comparison
errors, memory use, and completions.  The formal session theorem accepts
arbitrary correctly sized weights.  This client additionally checks the
pinned pretrained checkpoint's identity.

The WASM CLI compiles current Lean source on each invocation.  The exact-binary
theorem covers the frozen module identified in the
[artifact proof instructions](../../proofs/talos/lean/Project/Gpt2CachedStep/README.md#checking-and-evidence).
The recorded `wasm_sha256` identifies which binary a generation run used.

## Quantized candidate

The quantized prototype uses signed eight-bit weights and activations in
learned projections, signed 32-bit sums, and FP32 attention, normalization,
and nonlinear operations.  Its [format and session API](../../plans/gpt2-quantized-format.md)
define initialization checks and failure results.  The
[evaluation record](../../data/gpt2-quantized-v1/README.md) gives reproduction
commands, binary identities, memory and timing results, generated text, and
activation-error diagnostics.

| Program | Responsibility |
|---------|----------------|
| [Checkpoint quantizer](quantized.py) | Export packed matrices, per-output scales, retained FP32 tensors, and the model manifest. |
| [Quantized reference](quantized_reference.py) | Evaluate integer projections and serial FP32 operations in the specified order. |
| [Quantized WASM client](quantized_wasm.py) | Validate the loaded model, retain the cache, reject failed calls, and release buffers. |
| [Session tests](test_quantized_session.py) | Check malformed models, rejected inputs, numerical failures, cache preservation, reset, and close. |
| [Complete-model comparison](test_quantized_model.py) | Compare all cached prefixes bit for bit with the quantized reference and measure differences from frozen FP32 WASM. |
| [Repeated model benchmark](benchmark_quantized_model.py) | Compare both binaries with CPU PyTorch, warm the full prefix sequence, and record repeated cached-call timing and memory. |
| [Completion comparison](compare_quantized_text.py) | Generate from fixed prompts using shared Lean PRNG draws and retain both token streams. |
| [Projection diagnostics](diagnose_quantized.py) | Separate activation and weight reconstruction errors at the FP32 model's projection inputs. |
| [Grouped reference](grouped_reference.py) and [prefix experiment](experiment_grouped.py) | Evaluate the approved groups of 64 and an FP32 vocabulary-activation control against the frozen binaries. |
| [Grouped completion comparison](compare_grouped_text.py) | Evaluate the reference variants using the retained prompts and shared sampling draws. |
| [Grouped projection benchmark](benchmark_grouped.py) | Compare the experimental WASM projection with the per-row and FP32 projection binaries. |

`tools/gpt2 --quantized` loads the verified frozen grouped binary selected by the
[deployment record](../../data/gpt2-quantized-v1/model.json).  It verifies the
artifact-manifest identity, file sizes, and WASM, weights, tokenizer, and configuration hashes before generation and
records those identities in the result.  The grouped checkpoint is exported
when absent.  FP32 remains the default.

```sh
tools/gpt2 --quantized --text 'Once upon a time, in a small village' --generate 32
```

The [complete cached-session package](../../proofs/talos/lean/Project/Gpt2QuantizedCached/README.md)
passes execution, termination, allocation, release, and exact-binary checks.
Conditional numerical propagation and outward evaluation cover all 302 retained
and held-out prefixes.  The propagated bounds certify zero greedy margins.
Observed-logit certificates establish 232 individual choices.  The original
per-row projection has a checked [exact-binary package](../../proofs/talos/lean/Project/Gpt2QuantizedLinearRows/README.md).
The [grouped projection](../../proofs/talos/lean/Project/Gpt2QuantizedGroupedRows/README.md)
has a checked exact-binary theorem, including allocation and release.
