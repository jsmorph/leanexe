# GCD through the proved WASM encoder

The [source](../../LeanExe/Examples/EncodingGcd.lean) defines Euclid's algorithm
on two `UInt64` inputs.  The [source proofs](../../LeanExe/Examples/EncodingGcdProof.lean)
show for every input that the result is `UInt64.ofNat (Nat.gcd a.toNat b.toNat)`,
that swapping inputs preserves the result, and that `gcd a 0 = a`.

The [module generator](../../proofs/talos/lean/Project/EncodingGcd/GenerateProgram.lean)
compiles that source to LeanExe's IR.  The [direct translation](../../proofs/talos/lean/Project/EncodingGcd/Direct.lean)
turns the compiler's instruction trees and runtime functions into the
[Talos module](../../proofs/talos/lean/Project/EncodingGcd/Program.lean).
The [module proofs](../../proofs/talos/lean/Project/EncodingGcd/Spec.lean)
establish termination and the same GCD result for every pair of `UInt64` inputs
under Talos's WASM execution semantics.  They also establish the zero and
symmetry corollaries.

The [encoding theorem](../../proofs/talos/lean/Project/EncodingGcd/Encoded.lean)
applies the proved encoder to this module: if `encode` returns `bytes`, then
`bytes` satisfies the independent binary-encoding relation for the module with
the GCD theorem.  The same file's `main` writes [gcd.wasm](gcd.wasm) with that
encoder.  The source and module theorems prove the same result independently.
This example does not prove that LeanExe's compilation preserves source
semantics.  The encoder theorem concerns its returned byte array; the file
write and Wasmtime run are checked by the commands below.

From the repository root:

```sh
tools/leanrun --timeout 2m lake build LeanExe.Examples.EncodingGcdProof
tools/leanrun --timeout 3m lake -d proofs/talos/lean build Project.EncodingGcd.Direct
tools/leanrun --timeout 3m lake -d proofs/talos/lean env lean --run proofs/talos/lean/Project/EncodingGcd/GenerateProgram.lean proofs/talos/lean/Project/EncodingGcd/Program.lean
tools/leanrun --timeout 10m lake -d proofs/talos/lean build Project.EncodingGcd.Encoded
tools/leanrun --timeout 3m lake -d proofs/talos/lean env lean --run proofs/talos/lean/Project/EncodingGcd/Encoded.lean demos/encoding-gcd/gcd.wasm
"${WASM_TOOLS:-wasm-tools}" validate demos/encoding-gcd/gcd.wasm
"${WASMTIME:-build/tools/wasmtime/current/wasmtime}" run --invoke gcd demos/encoding-gcd/gcd.wasm 1071 462
```

Set `WASM_TOOLS` and `WASMTIME` when those programs are installed elsewhere.
The last command returns `21`.
