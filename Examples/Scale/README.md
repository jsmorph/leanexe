# Scale: word arithmetic and division by zero

## `a * b / c + 1` on words

[The program](Program.lean) computes `a * b / c + 1` on 64-bit words, with wrapping multiplication
and addition.  Lean defines `a / 0 = 0`, while WebAssembly's `i64.div_u` traps on a zero divisor, so
the compiled code must test the divisor to compute the Lean function.  The command
`verified_compile compiled := [scale]` in [the verified compilation](Compiled.lean) compiles `scale`
into the 1,415-byte `scale.wasm` of [the module registry](../../tests/verified/modules.txt).

## The divisor test and the theorems

The module's division tests the divisor and gives 0 when it is 0, the meaning that [the verified
compiler manual's section on expressions](../../docs/verified-manual.md#expressions) states for
word division, so `scale 6 7 0` is 1 in Lean and in WebAssembly.  The function allocates nothing,
so the generated `compiled.scale.implements` states that function 2 returns `scale a b c` without a
trap, and `compiled.scale.native` states the same of the C function of the module's translation.
Functions 0 and 1 of the module are the runtime's `alloc` and `release`, so the first compiled
function is function 2.

| Theorem | Statement |
|---------|-----------|
| `compiled.scale.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `scale a b c` without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `scale`. |
| `scale_file`, `scale_file_decode` | `build/verified/scale.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

Without `--cases`, [the verified driver](../../tests/verified/run.sh) checks the file module after
it writes `build/verified/scale.wasm`, and it requires the axiom reports of both file theorems to
name only `propext`, `Classical.choice`, and `Quot.sound`.  [The verified compiler
manual](../../docs/verified-manual.md#the-implements-family) defines `ImplementsA`, which
`compiled.scale.implements` states, and [its section on generated
declarations](../../docs/verified-manual.md#generated-declarations) gives the numbering of the
functions.

## Building, running, and testing

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

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  The first
call prints 11 and the second prints 1.  [The verified driver](../../tests/verified/run.sh) runs the
inputs of [`Cases.lean`](Cases.lean), including products that wrap and a zero divisor, in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state that a call allocates no block.

## Related examples

[`Gcd`](../../Library/Numerics/Arithmetic/Gcd/README.md) uses `%`, whose compiled code tests the
divisor in the same way (`a % 0 = a`), inside a tail-recursive loop.
[`PairSum`](../PairSum/README.md) and [`SumCount`](../SumCount/README.md) add arrays to
straight-line code.  [`Axpy`](../Axpy/README.md) is the same kind of program on binary64 values.

## References

- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
- Lean 4 core, v4.34.0-rc2, `UInt64.div` in
  [`Init/Data/UInt/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Init/Data/UInt/Basic.lean).
