# Scale: word arithmetic and division by zero

## What it is

[The program](Program.lean) computes `a * b / c + 1` on 64-bit words, with wrapping multiplication
and addition.  Lean defines `a / 0 = 0`, while WebAssembly's `i64.div_u` traps on a zero divisor, so
the compiled code must test the divisor to compute the Lean function.  [The module
definition](Module.lean) compiles `scale` into the 1,397-byte `scale.wasm`, which exports `scale`.

## What it shows

The IR's division tests the divisor and gives 0 for 0, as [the manual's table of word
operations](../../docs/manual.md#words-and-booleans) states, so `scale 6 7 0` is 1 in Lean and in
WebAssembly.  `scale_implements` follows from `Func.implements`, the rule for a body without loops
or calls, and one `simp` call that evaluates the body, with a case split on the divisor.
`scale_bytes` carries the theorem to the bytes through the encoder's round trip.

| Theorem | Statement |
|---------|-----------|
| `scale_implements` | Function 2 of `scale.module` implements `scale`: from any store that satisfies the runtime invariant, a call returns `scale a b c` or stops at `unreachable`. |
| `scale_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `scale`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The manual](../../docs/manual.md#the-implements-family)
defines `Implements`.  Functions 0 and 1 of every module are the runtime's `alloc` and `release`, so
the first compiled function is function 2.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Scale.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Scale.Module Examples.Scale.scale.module build/scale/scale.wasm
build/tools/leanexe-wasmtime-host call build/scale/scale.wasm scale i64 i64:6 i64:7 i64:4
build/tools/leanexe-wasmtime-host call build/scale/scale.wasm scale i64 i64:6 i64:7 i64:0
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup
of [the repository README](../../README.md#commands).  The first call prints 11 and the second
prints 1.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 49 cases of
[`Cases.lean`](Cases.lean) with native Lean, including products that wrap and a zero divisor.

## Related examples

[`Gcd`](../Gcd/README.md) uses `%`, which the IR tests in the same way (`a % 0 = a`), inside a
tail-recursive loop.  [`PairSum`](../PairSum/README.md) and [`SumCount`](../SumCount/README.md) add
arrays to straight-line code.  [`Axpy`](../Axpy/README.md) is the same kind of program on binary64
values.

## References

- WebAssembly Core Specification, [numeric
  instructions](https://webassembly.github.io/spec/core/exec/numerics.html): `idiv_u` is undefined
  for a zero divisor, and the instruction traps.
- Lean 4 core, `UInt64.div` in
  [`Init/Data/UInt/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Init/Data/UInt/Basic.lean)
  at the toolchain's tag: "Division by zero is defined to be zero."
