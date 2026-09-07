# Binary64 square root primitive

The source entry LeanExe.Examples.Float64Bits.sqrtBits accepts raw UInt64
binary64 words and returns the raw result of one WebAssembly f64.sqrt.
The generated [Program.lean](Program.lean) is checked by [Spec.lean](Spec.lean).

The exact theorem sqrtBits_exact quantifies over every input encoding,
terminates independently of fuel, and preserves the complete store.  It
returns the pure Talos IEEE64 sqrt result.  The source and generated-WAT
numerical theorems prove a finite result with absolute error at most 2^-52
when the input is positive, finite, nonzero, and at most one.  These are explicit theorem premises,
not implicit runtime guards on the unrestricted primitive.

All three public theorems use only propext, Classical.choice, and Quot.sound.
Native Lean Float and Wasmtime comparisons are regression evidence.  NaN
payload behavior in host runtimes is tested by class; the exact formal subject
is the deterministic pinned Talos semantics.  The [frozen manifest](../../../../artifacts/f64_sqrt_bits/7b236ffd9b15e117e80a60d4b4515682801c4a84bd9d4aeb34239d394d522841/manifest.json) registers
its exact bytes against this specification.  The independent profile supports
the operation.  The exact-package check passes, including the behavioral
declarations and axiom audit.

Run the focused gate from the repository root, after selecting the pinned
local environment:

```sh
tools/talos-proof.js check f64_sqrt_bits
node test/f64_extended_bits.js
```
