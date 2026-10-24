# LeanExe

LeanExe compiles functions in a restricted Lean dialect to WebAssembly, with proofs that the
decoded bytes compute the Lean functions.  The repository contains two compilers: one uses a proof
for each program, and the other has a correctness theorem for every typed source program.

Both compilers target Talos, a WebAssembly interpreter written in Lean, and share the runtime,
encoder, and decoder.  Their pure-function theorems use the `Implements` family of correctness
statements and cover return values, ownership of results, and preservation of the caller's heap
under the premises described [below](#trusted-base).

## The two compilers

### The LeanExe compiler

`leanexe_compile p := [f, …]` translates Lean definitions to an intermediate language and records
proof hints.  `compile` produces a module, and `encode` produces its bytes.  A proof for each
function combines shared compiler rules with facts about the program to establish `Implements`.
[The LTG knowledge base](ltg/README.md) describes those rules and their use.

[The LeanExe compiler manual](docs/leanexe-manual.md) defines the accepted dialect and the proof
procedure.  [The verified-executable skill](.claude/skills/verified-executable/SKILL.md) uses this
compiler to turn an English request into a specification, a program, and a theorem about its bytes.

### The verified compiler

The library `Verified` defines `compileWith`, a Lean function from a typed source program to a
module.  `Prog.correctStaticWith` proves that compiled code computes its source meaning,
`denote`, when its static pool covers the program's byte literals.  `Prog.correctWith` specializes
the theorem to programs with no nonempty byte literals.  The command `verified_compile p := [f, …]`
reflects ordinary Lean definitions into that source language and proves that each reflected
definition has the same meaning.  The command derives `p.f.implements` from those equations and
the universal compiler theorem.  Lean's kernel checks the generated proofs.

The command also generates allocation bounds, their equations in the function's parameters, and
trap-free theorems.  Eligible scalar functions receive store-preservation theorems for composition
with other programs.  The dialect uses `UInt64`, `Bool`, `Float`, and `Float32`, with scalar tuples
and sums, flat arrays, packed byte buffers, records with array fields, lists, fixed-layout recursive
types, and array updates in place.
[The verified compiler manual](docs/verified-manual.md) states the type restrictions, ownership
rules, generated declarations, and proof premises.  [The internals guide](Verified/README.md)
describes the compiler and its universal proof.

`verified_compile_wasi` compiles `LeanExe.Wasi.Action` definitions with stdin reads, stdout and
stderr writes, bounded effectful loops, and exit.  The shared native API uses Lean `do` notation
and UInt64 counts, lengths, and statuses.  Generated callable-entry and `_start` theorems relate
exported execution to the native actions, including ordered effects and committed effects before
errors or traps.  Total-execution theorems require a typed resource-prefix bound and assumptions
about reached host operations.  [The WASI manual](docs/wasi.md) defines the API, export forms,
proof premises, native interpreter, and standard Wasmtime host.

### Comparison

| Topic | LeanExe compiler | Verified compiler |
|---|---|---|
| Correctness proof | A theorem per program, from rule lemmas and hints | `Prog.correctStaticWith` for programs with tables and wrappers, and `Prog.correctStatic` without tables.  `Prog.correctWith` and `Prog.correct` specialize to programs with no nonempty byte literals. |
| Pure compilation command | `leanexe_compile p := [f, …]` | `verified_compile p := [f, …]` |
| WASI Preview 1 I/O | Application hosts perform I/O around compiled calls. | `verified_compile_wasi` compiles stdin reads, stdout and stderr writes, and exit, with native source-to-export refinement proofs. |
| Total execution | `ImplementsA false` with a proved memory budget | Pure `p.f.trapFree` under generated allocation and depth conditions.  WASI `.total` under typed resource-prefix and reached-host conditions. |
| `Float32` and WGSL kernels | Binary32 arithmetic and proved WGSL kernels | Binary32 arithmetic and a proved WGSL path for supported word, Boolean, and binary32 array builds |
| Lists and recursive types | `List UInt64` and user recursive types | Lists and fixed-layout recursive types, including matching, guarded recursion, tail loops, copying, release, and header reuse |
| Sum types | Supported, with fields | Enumerations and sums with scalar fields |
| Tail recursion | Compiled as a loop | Recognized tail recursion compiles as a loop.  Other recursion uses a depth limit of 1,000. |
| Folds | `Array.foldl` over `Array UInt64` and `Array Float` with a `UInt64` or `Float` accumulator, and `List.foldl` over `List UInt64` with a `UInt64` or `Float` accumulator | Whole-array `Array.foldl` over every accepted element type, with an accumulator of any dialect type.  `List.foldl` over `List UInt64` with a scalar accumulator and borrowed captures. |
| Array updates | `set!`, `setIfInBounds`, `insertIdx!`, `eraseIdxIfInBounds`, and `push` on `Array UInt64`, and `++` with an owned left operand | `set!`, `setIfInBounds`, `push`, `++`, `insertIdx!`, `insertIdxIfInBounds`, `eraseIdxIfInBounds`, `LeanExe.insertAt`, and `LeanExe.eraseAt` on arrays of every accepted element type |
| `@[inline]` helpers | Unfolded at their use | Unfolded at their use.  A listed helper compiles as a function. |
| Records with array fields | Arrays passed as separate parameters | Borrowed parameters, results, local values, and loop states |
| Constant arrays | Array literals of words, allocated at each call | Tables in data segments, passed by wrappers |
| Loops, builds, and calls in loop bodies and branches | Subject to placement rules | Any expression of the dialect |
| Composition across modules | `ImplementsPure` for functions that keep the store | Typed program reuse and call relocation, transported meaning proofs, and generated scalar store-preservation proofs |

Both compilers compile the [Euler solvers](Demos/Euler/README.md),
[binary64 GPT-2](Demos/Gpt/README.md), [binary32 GPT-2](Demos/Gpt32/README.md), and
[drone planner](Demos/Drone/README.md).  Their numerical libraries add proofs of accuracy,
exceptional values, exact fused multiply-add, correctly rounded parsing, shortest-decimal printing,
and generator periods.  [The algorithm index](index.md) lists each algorithm and its strongest
proved result, with links to the theorem statements and their domains.

### Trusted base

Lean's kernel checks the proofs using `propext`, `Classical.choice`, and `Quot.sound`.  The
theorems use Talos's semantics and binary decoder.  Calls require the allocator invariant, a cap
of at most 65,535 memory pages, representations of their arguments, and separation of consumed heap
blocks from the caller's retained heap regions.  Programs with nonempty byte literals also require
the static pool's contents and heap region, separated from blocks consumed by the call.  An
`implements` theorem may permit a trap at `unreachable`.  The verified compiler's `trapFree`
theorem proves a return when its allocation bound fits within the memory cap and every guarded
call stays below depth 1,000.  Wrappers whose callees take no call depth also
receive that theorem.  The LeanExe compiler has total-execution proofs with memory budgets for the
Euler solvers, drone planner, and increment example.

WASI entry theorems additionally assume a satisfying host, valid byte and static-pool
representations, and separation from the guest scratch region.  They match normal returns,
accepted exits, and host traps to source executions with the same world and ordered trace.
Permitted guest resource traps match source prefixes and residual actions.  WASI total execution
requires allocation room, the typed prefix budget, and `NoTrapsAlong` for the native action.
The modeled initial-store theorem establishes allocator and static-data invariants.  Real engine
instantiation, OS streams, and the native stream adapter remain outside the execution proofs.

Floating-point theorems use WebAssembly's deterministic profile.  The Wasmtime host enables NaN
canonicalization to match it.  WGSL theorems prove kernel results and race freedom in the shared
device model, which uses strict binary32 arithmetic.  The numerical file theorems connect particular
emitted files to their proved encodings.  Other file emission
relies on the writer's evaluation of module constants.  Execution tests check the host executables,
engines, and I/O.  [The design document](docs/design.md#scope-of-the-theorem)
states these proof limits.

## Documentation

| Document | Contents |
|---|---|
| [The LeanExe compiler manual](docs/leanexe-manual.md) | Dialect, compilation, proof rules, tests, examples, and development practice. |
| [The verified compiler manual](docs/verified-manual.md) | The verified compiler's dialect, the declarations that `verified_compile` adds, bounds, tests, and examples. |
| [The verified compiler's internals](Verified/README.md) | Its code scheme, the structure of its proof, and the reflector. |
| [The WASI manual](docs/wasi.md) | Native action and byte APIs, `verified_compile_wasi`, callable and command exports, execution proofs, host policies, and tests. |
| [The WASI design](docs/verified-wasi-design.md) | Reviewed architecture, pinned sources, host assumptions, proof boundaries, acceptance work, and design decisions. |
| [The design document](docs/design.md) | Architecture, decisions, proof scope, tests, and open work. |
| [The development journal](devnotes.md) | The record of the work. |
| [The algorithm library](Library/README.md) | Native algorithms, compilation modules, mathematical proofs, and imports. |
| [The application demos](Demos/README.md) | Application definitions, proofs, host programs, and tests. |
| [The algorithm index](index.md) | Algorithms, applications, compiler examples, and their proved results. |

## Layout

| Directory | Contents |
|---|---|
| [Shared libraries and LeanExe compiler](LeanExe) | The dialect, original compiler and IR, runtime, correctness statements, encoding, proof lemmas, and shared WGSL translation. |
| [Verified compiler](Verified) | The typed source language, compiler, universal proof, reflector, WGSL lowering, and compiled examples. |
| [Reusable algorithms](Library/README.md) | Implementations, mathematical specifications, accuracy and period proofs, and compiler proofs, grouped by algorithm family. |
| [Application demos](Demos/README.md) | Euler solvers, GPT-2, the drone planner, and the order book, with application proofs and host programs. |
| [Compiler examples](Examples) | Small programs, specifications, proofs, and cases that demonstrate compiler features. |
| [Manuals and design](docs) | The compiler manuals and design document. |
| [Proof guidance](ltg) | The LTG knowledge base and its declaration checker. |
| [Tools](tools) | The Lean runner, module and shader emitters, execution hosts, build scripts, and application tools. |
| [Tests](tests) | Module, decoder, numerical, allocation, GPU, and complete-generation tests, plus the browser pages. |
| [Run records](data), [reports](paper) | Measurements, reproduction records, papers, and their review history. |

## Commands

Commands run from the repository root.  They require Lean through Elan at the version in
[the toolchain file](lean-toolchain), the dependencies in [the Lake manifest](lake-manifest.json),
`wasm-tools` at [the pinned version](.wasm-tools-version), and a C compiler for the Wasmtime host.
Python tools use `uv`.  On Linux, the Lean runner requires a systemd user session with cgroup
controls.  [The host setup](docs/leanexe-manual.md#the-wasmtime-host) also covers macOS.

The GCD example builds its program and proof, writes the module, validates it, and runs a call:

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/download-wasmtime.sh
tools/build-wasmtime-host.sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.Gcd.Verify
mkdir -p build/gcd
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.Gcd.Module Library.Numerics.Arithmetic.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
```

The call prints `6`.  Every Lean or Lake command uses [the resource-limited runner](tools/leanrun),
as [the repository instructions](AGENTS.md) require.  A focused verified-compiler build, such as
`tools/leanrun --timeout 60m lake build Library.Random.Lcg.Verified`, builds that example and its imports.

The default build covers `LeanExe`, `Examples`, and `Demos`.  The `Verified` aggregate also imports
`Demos.Verified`, which checks the applications with the verified compiler.  The complete `Library` build includes
the numerical proofs and can take several hours.  Its lgamma root-range proofs use a 10 GiB memory
high limit and a 12 GiB maximum:

```sh
tools/leanrun --timeout 60m lake build
tools/leanrun --memory-high 10G --timeout 12h lake build Verified Library
tests/verified/run.sh
```

[The full-check procedure](docs/leanexe-manual.md#the-full-check) adds the other execution, decoder,
allocation, and GPU tests.  The test drivers invoke the runner themselves.
`tests/wasi/run.sh` checks the WASI proofs, reflected modules, byte ownership, and native and
WebAssembly I/O.  Its `--foundations-only` form runs the proof and semantic foundations without
the external-engine tests.  [The WASI development journal](devnotes.md#2026-10-23-implementing-the-wasi-agenda)
records proof, execution, and integration runs.

The [module driver](tests/modules/run.sh) compares every module of the LeanExe compiler except
`gpt`, `gpt32`, and `prng` with native Lean on the cases in each example's `Cases.lean`, which
[`tests/modules/Cases.lean`](tests/modules/Cases.lean) runs in turn, and
the [binary64 GPT driver](tests/gpt/run.sh) does the same for `gpt.wasm`.  Both read the modules from
`build/NAME/NAME.wasm`.  [`tests/verified/run.sh`](tests/verified/run.sh) writes the verified
compiler's modules to `build/verified/` and compares them with native Lean on [the shared case
corpus](Verified/Examples/Cases.lean), then checks numerical file theorems and accuracy tests.

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/.  One runs the WGSL kernel
tests on a browser's WebGPU, and the other runs GPT-2 with its kernels on WebGPU, in WebAssembly, or
on both and compares them.  [The description of the pages](tests/web/README.md) covers their setup
and what is proved about what they run.  The GPT-2 page needs the binary32 weights that `uv run
tests/gpt32/generate.py --export` writes.
