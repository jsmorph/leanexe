# Binary64 subtraction primitive

The source entry LeanExe.Examples.Float64Bits.subBits accepts raw UInt64
binary64 words and returns the raw result of one WebAssembly f64.sub.
The generated [Program.lean](Program.lean) is checked by [Spec.lean](Spec.lean).

The exact theorem subBits_exact quantifies over every input encoding,
terminates independently of fuel, and preserves the complete store.  It
returns the pure Talos IEEE64 sub result.  The source and generated-WAT
numerical theorems prove a finite result with absolute error at most 2^-52
when both finite operands have absolute value at most one.  These are explicit theorem premises,
not implicit runtime guards on the unrestricted primitive.

All three public theorems use only propext, Classical.choice, and Quot.sound.
Native Lean Float and Wasmtime comparisons are regression evidence.  NaN
payload behavior in host runtimes is tested by class; the exact formal subject
is the deterministic pinned Talos semantics.  This primitive is a source-driven
proof case; the independent binary-verifier extension is a separate checkpoint.

Run the focused gate from the repository root, after selecting the pinned
local environment:

```sh
tools/talos-proof.js check f64_sub_bits
node test/f64_extended_bits.js
```
