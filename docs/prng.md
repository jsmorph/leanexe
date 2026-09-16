# Pseudorandom number generator

From the repository root:

```sh
tools/prng.js 42 5 100
```

The arguments are the seed, result count, and positive modulus.  Each accepts an unsigned decimal integer through `18446744073709551615`.  The tool prints one integer per line in `[0, modulus)`, preserving every bit through decimal text.  A zero count produces empty output.  Invalid input produces an error on stderr and exit status 2.

The tool builds the Lean example and compiler through the repository resource runner, compiles `LeanExe.Examples.Prng.generate` to `build/prng/prng.wasm`, and executes its `generate` export through the Wasmtime C host.  It uses the tools listed in [Developing LeanExe](../DEVELOPING.md).  Later invocations reuse Lake's compiled modules and regenerate the WASM file.

After running the command above, invoke the built artifact with the Wasmtime host:

```sh
build/tools/leanexe-wasmtime-host call build/prng/prng.wasm generate array-u64 i64:42 i64:5 i64:100
```

The three inputs remain seed, count, and modulus.  The host decodes the returned array and prints:

```text
[13, 91, 58, 64, 50]
```

The Wasmtime CLI's `--invoke` option returns the array's memory address.  This host reads the array elements from WASM memory.

## Generator

The [Lean source](../LeanExe/Examples/Prng.lean) implements [Sebastiano Vigna's SplitMix64 reference](https://prng.di.unimi.it/splitmix64.c).  Each step adds `0x9e3779b97f4a7c15` to the 64-bit state and mixes the resulting word with two multiply-and-xor stages.  Integer arithmetic wraps modulo `2^64`.  The same seed produces the same sequence.

Each output is the mixed word modulo the supplied modulus.  The state advance is independent of the modulus.  Reduction introduces modulo bias when the modulus does not divide `2^64`: some residues have one more preimage among the possible 64-bit words.  The CLI requires a positive modulus.

The generated function returns an array.  Current LeanExe array pushes allocate and copy the accumulated values, so time and allocated memory grow quadratically with the requested count.  The tool limits execution to 60 seconds and captures at most 64 MiB of output.  A resource failure produces stderr and a nonzero exit status.

## Tests

```sh
node test/prng.js
```

The test compares WASM output with native Lean and a C implementation of the reference algorithm.  It covers zero count, repeatability, maximum seeds, several moduli, full-width results, and malformed CLI inputs.  This example has execution tests.  Formal proofs are outside this task's scope.
