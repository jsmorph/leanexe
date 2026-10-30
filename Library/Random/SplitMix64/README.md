# Prng: SplitMix64

## SplitMix64 and a float in `[0, 1)`

[The program](Program.lean) is SplitMix64, the generator of Steele, Lea, and Flood in the form of
Sebastiano Vigna's reference C code.  `splitMix state` adds the constant `0x9e3779b97f4a7c15` to the
state and mixes the new state into an output word with two multiply-and-xor rounds and a final xor,
returning the new state and the word.  `unitFloat x` maps a word to the float `(x >>> 11) / 2^53` in
`[0, 1)`, which is exact because the numerator has at most 53 bits.  [The module
definition](Module.lean) compiles both into the 1,478-byte `prng.wasm`, and [the verified
compilation](Compiled.lean) compiles both with the verified compiler into a 1,498-byte module.

## Theorems that hold in any module

`splitMix` returns a pair, which the compiled function returns as two WebAssembly results.  The two
`_pure` theorems hold in any module that contains the compiled functions, at any index, so another
program can compile them into its own module and use them without a new proof.  The GPT-2 sampler in
[`Gpt`](../../../Demos/Gpt/README.md) does this: its `sampleTopK` threads the generator state through its calls.

| Theorem | Statement |
|---------|-----------|
| `splitMix_pure` | In any module whose function `2 + i` is the compiled `splitMix`, that function keeps the store and returns the new state and the output word. |
| `unitFloat_pure` | Same for `unitFloat`, which returns the bits of `(x >>> 11).toFloat / 2^53`. |
| `splitMix_implements`, `unitFloat_implements` | Functions 2 and 3 of `prng.module` implement `splitMix` and `unitFloat`. |
| `prng_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements both functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  `ImplementsPure`, defined in [the
manual](../../../docs/leanexe-manual.md#the-implements-family), is the form of `Implements` for functions on
scalars that leave the store unchanged.  The proofs step through straight-line statements with
`Stmt.run_spec`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Random.SplitMix64.Verify
mkdir -p build/prng
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Random.SplitMix64.Module Library.Random.SplitMix64.prng.module build/prng/prng.wasm
build/tools/leanexe-wasmtime-host call build/prng/prng.wasm splitMix list:i64,i64 i64:0
build/tools/leanexe-wasmtime-host call build/prng/prng.wasm unitFloat f64 \
  i64:16294208416658607535
uv run tests/prng/compare.py
```

The commands build the proofs, write the module, call it in the Wasmtime host, and compare it with
the reference, with the setup of [the repository README](../../../README.md#commands).  From state 0,
`splitMix` prints the new state 11400714819323198485 and the word 16294208416658607535, which is
`0xe220a8397b1dcdaf`, the first output that Vigna's code gives for seed 0.  `unitFloat` of that word
prints 4606131375998723001, the bits of 0.8833108082136426.
[`tests/prng/compare.py`](../../../tests/prng/compare.py) checks one step from 106 seeds, 1,000
successive steps from seeds 0 and 42, and `unitFloat` on 40 words against a Python transcription of
the reference code.

## The verified compiler's module

`verified_compile compiled := [splitMix, unitFloat]` in [the verified compilation](Compiled.lean)
compiles the same definitions.  Both functions take and return scalars and allocate nothing, so the
generated `compiled.splitMix.pure` and `compiled.unitFloat.pure` state that functions 2 and 3
return their Lean results from every store without a trap and leave the store unchanged.
`prng_module` combines them with the module's bytes and the two exports.

| Theorem | Statement |
|---------|-----------|
| `prng_module` | The module's bytes decode to the module, whose exports `splitMix` and `unitFloat` are functions 2 and 3, and each function returns its Lean result from every store without a trap and keeps the store. |

`splitMix_pure` and `unitFloat_pure` of the LeanExe module allow a trap and hold in any module that
contains the compiled functions at any index, so another LeanExe program calls them without a new
proof.  The verified theorems hold for this module, and another verified program reuses the
functions by listing them in its own `verified_compile`, as [the verified GPT-2
module](../../../Demos/Gpt/Verified.lean) does, or by appending this program with `Prog.append`.
The generated `compiled.splitMix.native` and `compiled.unitFloat.native` state the computations for
the C functions of the module's translation.

```sh
tools/leanrun --timeout 60m lake build Library.Random.SplitMix64.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Random.SplitMix64.Compiled Library.Random.SplitMix64.compiled.module \
  build/verified/prng.wasm
uv run tests/prng/compare.py build/verified/prng.wasm
tests/verified/run.sh --cases prng
tests/native/verified.sh --module prng
```

`compare.py` runs its checks of the reference code on the verified module.  [The verified
driver](../../../tests/verified/run.sh) compares 96 calls of each function with native Lean in
Wasmtime, from 0, 1, and four seeds whose advance wraps or reaches zero, 40 arbitrary words, and 50
successive states from 0, and checks that no call allocates.  [The native
driver](../../../tests/native/verified.sh) runs the same calls on the module's translation to C,
compiled with CompCert.

## Related examples

[`Gpt`](../../../Demos/Gpt/README.md) imports this program and calls both functions in its sampler.
[`Scale`](../../../Examples/Scale/README.md) has word arithmetic without the pair result.  The LTG entries
[`splitmix64`](../../../ltg/entries/splitmix64/README.md) and
[`straight-line-run`](../../../ltg/entries/straight-line-run/README.md) describe the library and the
proof method.

## References

- G. L. Steele Jr., D. Lea, and C. H. Flood, "Fast Splittable Pseudorandom Number Generators,"
  *Proceedings of OOPSLA 2014*, ACM, pp. 453–472,
  [doi:10.1145/2660193.2660195](https://doi.org/10.1145/2660193.2660195).
- S. Vigna, [`splitmix64.c`](https://prng.di.unimi.it/splitmix64.c), the reference C code.
