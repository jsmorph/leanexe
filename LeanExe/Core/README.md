# Restricted Lean compiler

Compile ordinary Lean definitions to a Talos `Wasm.Module` with a kernel-checked
proof that execution preserves the original Lean computation.

The compiler implementation is in `LeanExe/Core`; the Talos lowering and its
correctness proofs are in `proofs/talos/lean/Project/Core`. Use the latter Lake
project for the public entry points.

```lean
import Project.Core.Frontend

def total (count : UInt64) : UInt64 := Id.run do
  let mut accumulator : UInt64 := 0
  for index in [:count.toNat] do
    accumulator := accumulator + UInt64.ofNat index
  return accumulator

run_elab Project.Core.Frontend.compile ``total `totalModule
```

`totalModule` is a Talos `Wasm.Module`. The generated declarations include:

- `totalModule.entry`: the entry function index, exported as `main` by default.
- `totalModule.correct`: execution returns `total` applied to the supplied
  arguments and preserves the caller's store.
- `totalModule.valid`: the module satisfies the existing encoder's typing rules.
- `totalModule.ready`: the existing encoder accepts the module's structure and
  finite format sizes.

A third argument to `Frontend.compile` changes the export name. Compilation
fails if extraction, proof generation, or a finite module check fails.

## Source subset

Functions have monomorphic `UInt64` arguments and a `UInt64` result. They may use
integer arithmetic and bit operations, comparisons, `let`, `if`, ordinary `Id`
`do` blocks, named helpers, and self-recursion accepted by Lean's termination
checker. Recursive calls may occur inside larger expressions. Runtime `let`
bindings and monadic bind results must also be UInt64; use comparisons directly
as conditions rather than storing Boolean locals.

Bounded loops use `for index in [:bound.toNat]`, with a UInt64 bound and one
mutable UInt64 accumulator. Convert an index with `UInt64.ofNat`. Loops start
at zero, advance by one, and complete their finite range. The emitted module
uses a Talos loop. Native iteration bodies are compiled as functions. A loop may
call an independently recursive helper; a recursive call back to the enclosing
function from its iteration body is rejected.

Stateful definitions return `StateM ByteArray UInt64`. Compile them with
`Frontend.compileState` and use these ordinary Lean operations:

| Operation | Native behavior |
| --- | --- |
| `LeanExe.Core.Memory.read address` | Read a byte as UInt64; return zero outside memory. |
| `LeanExe.Core.Memory.write address value` | Write the low byte; ignore an address outside memory; return zero. |
| `LeanExe.Core.Memory.size` | Return the byte count. |
| `LeanExe.Core.Memory.grow pages` | Interpret the page count as UInt32; append zero-filled 64 KiB pages, returning the old page count; return 4294967295 on failure. |

The stateful correctness theorem preserves the native result and final bytes.
The memory representation covers page-aligned arrays up to 4 GiB, with a
65536-page growth limit. The generated module starts with sixteen zero-filled
pages; a theorem establishes that this actual initial store satisfies the
representation.

Floating point, GPU operations, and I/O are outside this subset. Polymorphic,
unsafe, partial, and mutually recursive declaration groups are rejected. Other
Lean data types require an explicit representation in words and byte memory.

## Proof boundary

The frontend generates a proof relating each original Lean definition to its
compiled internal statements. Lean checks that proof. The general lowering
theorem relates those statements to execution of the exact emitted Talos module.
The existing verified encoder handles the subsequent module-to-binary step.

The correctness result is about Talos execution. For each input, it establishes
successful execution with sufficient finite fuel. It does not assume a fixed
execution budget or claim that an external runtime has unlimited resources.

The focused examples in `Project.Core.FrontendExamples` and
`Project.Core.LoopExamples` check this complete path. Recursive and stateful
examples also appear in `Project.Core.Examples` and `Project.Core.StateExamples`.
