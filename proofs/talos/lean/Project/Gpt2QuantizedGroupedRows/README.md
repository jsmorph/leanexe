# Grouped quantized projection proof

The `gpt2_quantized_grouped_rows` case proves exact execution of the [grouped projection](../../../../../LeanExe/Models/Gpt2/Quantized/Grouped.lean).  Its measured 5,441-byte binary has SHA-256 `f3aa382e2e810499b73494e9a74ed380c7ef64883e65cd286353493b74f3be8b`.  Exact-binary certificates are in progress.

## Algorithm and guarantees

Each activation row has independent scales for consecutive groups of 64 coordinates.  The projection quantizes each group, computes its signed integer dot product, rescales the partial in FP32, and adds partials in increasing group order from positive zero.  Bias is added once.  Weights retain one scale per output channel.

The [source lemmas](Source.lean) identify every integer prefix with its mathematical sum and bound its magnitude by 1,032,256.  The [helper transport](Helpers.lean) reuses the checked quantizer, integer dot product, and FP32 rescaling through exact function-region equality.  The [entry theorem](Linear.lean), `Spec.linearGroupedRows_exact`, proves termination, exact output bytes, ownership of the returned buffer, preservation of protected inputs, and release of the activation and scale buffers.  It uses only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem assumes represented input buffers, a positive input width divisible by 64 and representable in `UInt64`, valid tensor extents, a valid heap, protected inputs, and capacity for each allocation when reuse fails.  Arithmetic follows raw-word FP32 semantics, including exceptional values.  The source range theorem additionally assumes permitted weight coefficients.  The output heap records three allocations, two releases, and two frees, with no retains.

## Proof structure

| Modules | Result |
|---------|--------|
| [Group integer prefix](ProjectionDot.lean), [rescaling](ProjectionRescale.lean), and [FP32 update](ProjectionGroupFinish.lean) | Exact instruction execution for one group. |
| [Group loop](ProjectionGroups.lean), [total read](ProjectionTotal.lean), and [bias](ProjectionBias.lean) | Ordered reduction and final value. |
| [Output word](ProjectionWord.lean) and [output loop](ProjectionLoop.lean) | Exact packed output with writes confined to the destination. |
| [Input quantization](ProjectionInput.lean), [output size](ProjectionSize.lean), and [output allocation](ProjectionAllocate.lean) | Input representation, checked dimensions, heap reuse, growth, and separation. |
| [Temporary release](ProjectionRelease.lean) and [complete entry](Linear.lean) | Returned ownership, heap counters, protected regions, and memory-capacity preservation. |
| [Module-parametric specification](Exact.lean) | Specification for transfer to the decoded binary. |

The [evaluation record](../../../../../data/gpt2-quantized-v1/README.md) retains projection comparisons, complete-model reference comparisons, generated text, and controlled timing.  The cached model's internal projection has two extra owner parameters and returns an owner slot.  Its [separate entry proof](../Gpt2QuantizedCached/GroupedProjection/Linear.lean) now passes with those owner slots.

```sh
tools/leanrun --timeout 3m lake -d proofs/talos/lean build Project.Gpt2QuantizedGroupedRows.Spec
```
