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
`--json` records token IDs, settings, timing, allocation counts, and stopping
conditions.  `--logits PATH` saves the last evaluated vector as raw binary32
words.  PyTorch and WASM use different random-number generators for sampling.

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
