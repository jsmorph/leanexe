# Scale: word arithmetic and division by zero

## `a * b / c + 1` on words

[The program](Program.lean) computes `a * b / c + 1` on 64-bit words, with wrapping multiplication
and addition.  Lean defines `a / 0 = 0`, while WebAssembly's `i64.div_u` traps on a zero divisor, so
the compiled code must test the divisor to compute the Lean function.  [The module
definition](Module.lean) compiles `scale` into the 1,397-byte `scale.wasm`, which exports `scale`.

## The divisor test and its proof

The IR's division tests the divisor and gives 0 for 0, as [the LeanExe compiler manual's table of
word operations](../../docs/leanexe-manual.md#words-and-booleans) states, so `scale 6 7 0` is 1 in
Lean and in WebAssembly.  `scale_implements` follows from `Func.implements`, the rule for a body
without loops or calls, and one `simp` call that evaluates the body, with a case split on the
divisor.  `scale_bytes` carries the theorem to the bytes through the encoder's round trip.

| Theorem | Statement |
|---------|-----------|
| `scale_implements` | Function 2 of `scale.module` implements `scale`: from any store that satisfies the runtime invariant, a call returns `scale a b c` or stops at `unreachable`. |
| `scale_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `scale`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The verified compiler
manual](../../docs/verified-manual.md#the-implements-family) defines `Implements`.  Functions 0 and 1
of every module are the runtime's `alloc` and `release`, so the first compiled function is function
2.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Scale.Verify
mkdir -p build/scale
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Scale.Module Examples.Scale.scale.module build/scale/scale.wasm
build/tools/leanexe-wasmtime-host call build/scale/scale.wasm scale i64 i64:6 i64:7 i64:4
build/tools/leanexe-wasmtime-host call build/scale/scale.wasm scale i64 i64:6 i64:7 i64:0
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup
of [the repository README](../../README.md#commands).  The first call prints 11 and the second
prints 1.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 49 cases of
[`Cases.lean`](Cases.lean) with native Lean, including products that wrap and a zero divisor.

## The verified compiler's module

`verified_compile compiled := [scale]` in [the verified compilation](Compiled.lean) compiles the
same definition into the 1,415-byte `scale.wasm` of [the module
registry](../../tests/verified/modules.txt).  The function allocates nothing, so the generated
`compiled.scale.implements` states that function 2 returns `scale a b c` without a trap, where
`scale_implements` allows a stop at `unreachable`.  The generated `compiled.scale.native` states the
same of the C function of the module's translation, and the theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `compiled.scale.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `scale a b c` without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `scale`. |
| `scale_file`, `scale_file_decode` | `build/verified/scale.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

```sh
tools/leanrun --timeout 60m lake build Examples.Scale.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Scale.Compiled Examples.Scale.compiled.module build/verified/scale.wasm
build/tools/leanexe-wasmtime-host call build/verified/scale.wasm scale i64 i64:6 i64:7 i64:4
build/tools/leanexe-wasmtime-host call build/verified/scale.wasm scale i64 i64:6 i64:7 i64:0
tests/verified/run.sh --cases scale
tests/native/verified.sh --module scale
```

The calls print 11 and 1, as the LeanExe module's calls do.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state that a call allocates no block.

## Related examples

[`Gcd`](../../Library/Numerics/Arithmetic/Gcd/README.md) uses `%`, which the IR tests in the same way (`a % 0 = a`), inside a
tail-recursive loop.  [`PairSum`](../PairSum/README.md) and [`SumCount`](../SumCount/README.md) add
arrays to straight-line code.  [`Axpy`](../Axpy/README.md) is the same kind of program on binary64
values.

## References

- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
- Lean 4 core, v4.34.0-rc2, `UInt64.div` in
  [`Init/Data/UInt/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Init/Data/UInt/Basic.lean).
