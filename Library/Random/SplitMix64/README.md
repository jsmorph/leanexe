# Prng: SplitMix64

## SplitMix64 and a float in `[0, 1)`

[The program](Program.lean) is SplitMix64, the generator of Steele, Lea, and Flood in the form of
Sebastiano Vigna's reference C code.  `splitMix state` adds the constant `0x9e3779b97f4a7c15` to the
state and mixes the new state into an output word with two multiply-and-xor rounds and a final xor,
returning the new state and the word.  `unitFloat x` maps a word to the float `(x >>> 11) / 2^53` in
`[0, 1)`, which is exact because the numerator has at most 53 bits.

## The verified module

`verified_compile compiled := [splitMix, unitFloat]` in [the verified compilation](Compiled.lean)
compiles both definitions into a 1,498-byte module.  `splitMix` returns a pair, which the compiled
function returns as two WebAssembly results.  Both functions take and return scalars and allocate
nothing, so the generated `compiled.splitMix.pure` and `compiled.unitFloat.pure` state that
functions 2 and 3 return their Lean results from every store without a trap and leave the store
unchanged.  `prng_module` combines them with the module's bytes and the two exports.

| Theorem | Statement |
|---------|-----------|
| `prng_module` | `encode` succeeds on `compiled.module`, the bytes decode to it, its exports `splitMix` and `unitFloat` are functions 2 and 3, and each function returns its Lean result from every store without a trap and keeps the store. |
| `prng_file`, `prng_file_decode` | `build/verified/prng.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`, as [the file module](File.lean) states. |

For each function, `prng_module` states `ImplementsPureA false`, which [the verified compiler
manual](../../../docs/verified-manual.md#the-implements-family) defines for scalar arguments and
results: a call from any store returns the Lean result and leaves the store unchanged, and `false`
excludes the trap.  The theorems concern this module, so another verified program reuses the
functions by listing them in its own `verified_compile`, as [the verified GPT-2
module](../../../Demos/Gpt/Verified.lean) does, or by appending this program with `Prog.append`, as
[module composition](../../../docs/verified-manual.md#module-composition) in the manual describes.
The generated `compiled.splitMix.native` and `compiled.unitFloat.native` state the computations for
the C functions of the module's translation.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Random.SplitMix64.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Random.SplitMix64.Compiled Library.Random.SplitMix64.compiled.module \
  build/verified/prng.wasm
build/tools/leanexe-wasmtime-host call build/verified/prng.wasm splitMix list:i64,i64 i64:0
build/tools/leanexe-wasmtime-host call build/verified/prng.wasm unitFloat f64 \
  i64:16294208416658607535
uv run tests/prng/compare.py
tests/verified/run.sh --cases prng
tests/native/verified.sh --module prng
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, compare it with the reference, and run the tests, with the setup of [the repository
README](../../../README.md#commands).  From state 0, `splitMix` prints the new state
11400714819323198485 and the word 16294208416658607535, which is `0xe220a8397b1dcdaf`, the first
output that Vigna's code gives for seed 0.  `unitFloat` of that word prints 4606131375998723001, the
bits of 0.8833108082136426.

[`tests/prng/compare.py`](../../../tests/prng/compare.py) reads `build/verified/prng.wasm` when
given no path, and it checks one step from 106 seeds, 1,000 successive steps from seeds 0 and 42,
and `unitFloat` on 40 words against a Python transcription of the reference code.  [The verified
driver](../../../tests/verified/run.sh) compares 96 calls of each function with native Lean in
Wasmtime, from 0, 1, and four seeds whose advance wraps or reaches zero, 40 arbitrary words, and 50
successive states from 0, and checks that no call allocates.  The seeds are `splitMixSeeds` of [the
verified library cases](../../../tests/TestSupport/LibraryCases.lean), and [the native
driver](../../../tests/native/verified.sh) runs the same calls on the module's translation to C,
compiled with CompCert.  Without `--cases`, the verified driver also checks the file module against
the file it wrote, and it fails unless `prng_file` and `prng_file_decode` report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Related examples

[`Gpt`](../../../Demos/Gpt/README.md) imports this program and calls both functions in its sampler.
[`Scale`](../../../Examples/Scale/README.md) has word arithmetic without the pair result.
[`Lcg`](../Lcg/README.md), [`ParkMiller`](../ParkMiller/README.md), and
[`Xorshift`](../Xorshift/README.md) are further generators of the library, each with a verified
module.

## References

- G. L. Steele Jr., D. Lea, and C. H. Flood, "Fast Splittable Pseudorandom Number Generators,"
  *Proceedings of OOPSLA 2014*, ACM, pp. 453–472,
  [doi:10.1145/2660193.2660195](https://doi.org/10.1145/2660193.2660195).
- S. Vigna, [`splitmix64.c`](https://prng.di.unimi.it/splitmix64.c), 2015, dedicated to the
  public domain to the extent possible under law, with permission to use, copy, modify, and
  distribute it for any purpose.
