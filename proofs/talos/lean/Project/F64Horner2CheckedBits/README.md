# Guarded Binary64 Quadratic Horner Example

This example is the numerical and control-flow rehearsal for the Euler
Rusanov artifact.  It accepts raw binary64 words `x`, `c₂`, `c₁`, and `c₀`,
checks that every magnitude is at most one half, and evaluates the explicitly
rounded expression

```text
(c₂ * x + c₁) * x + c₀
```

with two `f64.mul` and two `f64.add` instructions.

On success it returns status zero and the result bits.  On rejection it
returns status one and positive-zero bits without entering the floating-point
branch.  The accepted pure-model theorem proves the output finite and within
`3 * 2^-52` of the exact real quadratic.  The first stage's `2 * 2^-52` error
is attenuated by `|x| ≤ 1/2` before the second two-operation error is added.

`Numerical.lean` contains the total source-facing contract.  `Program.lean`
is generated from the compiler-emitted WAT and must not be handwritten.
`Execution.lean` and the completed `Spec.lean` will establish total,
store-preserving generated-WAT execution, an explicit small-step trace, and
the same numerical result contract.  Native floating-point execution remains
a regression oracle and is not proof evidence.

## Generated-program audit

The compiler output and decoded proof cache currently have this exact
identity:

| Artifact | Size (bytes) | SHA-256 |
| --- | ---: | --- |
| `program.wasm` | 1,237 | `8c665a1634643065c35e3ed7a81bf8538e4a8e264cb240fcc1ad3494b41757bd` |
| `program.wat` | 11,383 | `df55f1f5370319078cfa07ce9b2a78b515fb9ed770ba0a33164e878390c0712d` |
| `Program.lean` | 11,369 | `1c88282f23c425b18972901cefbfdebd8ab3774993a409b2a08ac9d82fdea9c8` |

`program.wasm` and `program.wat` are generated compiler artifacts;
`Program.lean` is generated from that WAT by the Talos verifier.  They are
not handwritten proof inputs.  `Numerical.lean`, `Execution.lean`, and the
public proof root are the handwritten layer.

The decoded module assigns function index 0 to the raw-bit guard, index 1 to
the exported `horner2CheckedBits` entry, and indices 2 through 5 to `alloc`,
`reset`, `retain`, and `release`/`free`.  The passing shared runtime check pins
`func2Def` to `allocFuncDef`, `func3Def` to `resetFuncDef`, `func4Def` to
`retainFuncDef`, and `func5Def` to `releaseFuncDef 5`, erasing only the
module-local type index.

The external ABI is four `i64` parameters in source order
`(x, c₂, c₁, c₀)` and two `i64` results in order `(status, bits)`.  Talos's
operand stack is top-first, so an execution theorem supplies
`[c₀, c₁, c₂, x]` and observes `[bits, status]`.

The entry short-circuits four sign-cleared raw-bit magnitude guards in the
order `x`, `c₂`, `c₁`, `c₀`.  Only the accepted branch performs the staged
operations `c₂*x`, then `+c₁`, then `*x`, then `+c₀`: exactly two
`f64.mul`, two `f64.add`, and a bit round-trip after every operation.  There
is no fused multiply-add or reassociation.  Rejection performs no floating
arithmetic and returns `(status, bits) = (1, 0)`, where zero is positive-zero
bits.

The generated-WAT big-step proof now covers all five guard paths, exact
results, total termination, store preservation, and the transferred
`3 * 2^-52` real-error contract.  Its axiom reports contain only the standard
logical axioms.

The case remains registered with `complete: false`.  Completion still
requires explicit small-step trace closure and the exact-program-byte gate.
Release manifests, receipts, and self-host packaging remain outside this
branch's completion gate.
