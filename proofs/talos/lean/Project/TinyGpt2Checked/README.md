# Checked four-byte GPT-2 execution

This directory proves that the generated WASM entry `inferChecked` implements
the [four-byte GPT-2 model](../TinyGpt2/README.md), including input validation,
weight clipping, transformer inference, and output construction.  It also
transfers the model's numerical bounds to the returned WASM values.

The entry takes an array of 2,488 binary64 weight words, a bound, and four
byte tokens.  It rejects invalid tokens, an incorrect weight count,
nonfinite weights, a nonfinite bound, or a bound outside [0, 10].  Accepted
weights are clipped to [-B, B].  Success returns 256 binary64 logit words.
Rejection returns an empty array.

## Public results and assumptions

| Entry point | Result |
|-------------|--------|
| [Execution theorem](Entry.lean), `Spec.inferChecked_exact` | Termination, the exact source output, preservation of the supplied weight array and earlier memory, and a fixed page count.  It covers acceptance and rejection. |
| [Numerical execution theorem](Numerical.lean), `Spec.inferChecked_real_error` | The execution result plus finite accepted logits of magnitude at most 1,260 and an error bound against real inference using clipped weights. |
| [Registered specification](Spec.lean) | Imports the numerical theorem and checks compiler annotations for the generated module. |

The execution theorem assumes the input array has its specified memory
representation and lies below the allocation top.  The initial state has
an empty free list.  The theorem requires reserved capacity for clipping and
inference allocations within the current pages and 32-bit address range.
For n weight words, the reservation beyond the initial allocation top is
48 + 8(n + 1) + 277,560 bytes.  The numerical theorem adds acceptance and
positive denominator bounds for the three normalization stages, covering
their real and computed inputs.

These proofs describe the generated-WAT execution model.  The
[pretrained cached-inference directory](../Gpt2CachedStep/README.md) contains
the separate exact-binary GPT proof.  The
[GPT guide](../../../../../docs/gpt/README.md) distinguishes those proof
boundaries and the remaining numerical work.

## Internal composition

`Program.lean` is the tracked generated execution model.  The clipping
modules establish validation, allocation, copying, and each branch of the
wrapper.  [Component proofs](Components.lean) establish hidden-state and
logit calls.  The output modules compose allocation, append, copy, release,
and the loop over 256 vocabulary entries. The loop retains the initial empty
buffer, proves each subsequent output is distinct, and follows the generated
alias guards before releasing an old output. Final cleanup preserves the
returned owner. [Inference composition](Inference.lean)
joins those results.  The public entry theorem adds token validation and
the exported call.

The proof driver regenerates `Program.lean` for comparison with its tracked
copy.  [Talos proof documentation](../../../README.md) describes cache
refresh and the source-driven verification procedure.

## Running and checking

The [checkpoint instructions](../../../../../data/tiny-gpt2-v1/README.md)
document input files, JSON output, hashes, and the Wasmtime host.  From the
repository root:

```sh
tools/tiny-gpt2.js --tokens 0 0 36 82
tools/tiny-gpt2.js --checkpoint data/tiny-gpt2-v1/checkpoint.json --bound 3 --text 'To b'
tools/talos-proof.js check tiny_gpt2_checked
```

The proof command regenerates the module and checks the registered theorem
targets through the repository's Lean runner.  The native CLI and host
remain outside these Lean theorems.
