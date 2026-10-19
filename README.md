# LeanExe

LeanExe compiles Lean functions to WebAssembly and proves that the bytes compute the Lean functions.
The repository holds two compilers, which share a trusted base, a runtime, and a statement of
correctness.  The LeanExe compiler translates a definition during elaboration, and a proof per
program, built from proved rules, establishes that the program's module computes the program.  The
verified compiler is a Lean function with one theorem that covers every program it accepts, and its
command derives from that theorem a theorem for each definition it compiles.  Both produce modules
of Talos, a WebAssembly interpreter written in Lean, and both state correctness with `Implements`
and its relatives: from any store that satisfies the runtime's allocator invariant, the exported
function returns the Lean function's value or, where the theorem allows it, traps at `unreachable`.
`decode_encode` gives each theorem for the module that the decoder reads from the bytes.

## The two compilers

### The LeanExe compiler

The LeanExe compiler, `leanexe_compile` in [`LeanExe/Compiler/`](LeanExe/Compiler/), is meta code
that translates a Lean definition to a small IR and records hints for the prover.  `compile`
translates the IR to a module, `encode` produces the bytes, and a proof per function establishes
`Implements`.  Each compiler rule has its own theorem, such as `Func.tail_implements` for tail
recursion, which reduces each program's proof to the parts the rule does not cover.  Entries of [the
LTG knowledge base](ltg/README.md) describe the rules and the methods that apply them, and [the
design document's open work](docs/design.md#open-work) lists the rules that have no entry.  The
compiler's dialect includes `Float32` with a proved path to WGSL kernels, lists and trees, sum
types, and folds, and its examples include GPT-2, two Euler solvers, and a drone planner.  For the
Euler solvers, the drone planner, and the increment example, `ImplementsA` with a memory budget also
proves that the call returns within a stated number of pages.

### The verified compiler

The verified compiler, in the library [`Verified`](Verified/README.md), is a Lean function,
`compileWith`, that translates programs of a typed source language to modules.  The source language
has a meaning in Lean, `denote`, and the theorem `Prog.correctWith` states that the module of every
program computes the program's meaning.  The command `verified_compile p := [f, …]` translates
ordinary Lean definitions to the source language, proves with kernel-checked equations that each
translation means its definition, and adds for each definition `f` the theorem `p.f.implements` that
the module computes `f`.  For each source function it also adds `p.f.trapFree`, which states that
the call returns without a trap when the allocator's `top` can rise by the bound `p.f.bound x`
and, for recursive code, when every call stays below depth 1,000, and `p.f.bound_eq`, which states that bound as a Lean term in
the parameters.  Wrappers whose callees take no call depth receive the corresponding bound and
trap-free theorem.  The dialect covers words, `Bool`s, floats, tuples, structures, enumerations, arrays
of these, records with array fields, recursion, constant tables, and array updates in place.  The
examples include elementary and special functions ported from fdlibm, Arm's optimized-routines,
and CORE-MATH, decimal parsers and printers, binary64 GPT-2, two Euler solvers, an order book,
the drone planner, and three random-number generators with theorems about their periods.  [The numerical index](index.md)
lists the algorithms and their strongest proved results, including numerical accuracy, exact
fused multiply-add, correctly rounded parsing, and shortest-decimal printing.  Each function's
document states its theorem's domain and exceptional cases.

### Comparison

| Topic | LeanExe compiler | Verified compiler |
|---|---|---|
| Correctness proof | A theorem per program, from rule lemmas and hints | `Prog.correctWith` for programs with tables and wrappers, and `Prog.correct` without tables |
| Command | `leanexe_compile p := [f, …]` | `verified_compile p := [f, …]` |
| Total execution | `ImplementsA false` with a memory budget, proved for the Euler solvers, the drone planner, and the increment example | `p.f.trapFree` for source functions and wrappers without call depth, under the allocation bound and, for recursive code, a frames condition |
| `Float32` and WGSL kernels | Supported | Outside the dialect |
| Lists and recursive types | `List UInt64` and user recursive types | Outside the dialect |
| Sum types | Supported, with fields | Enumerations only |
| Tail recursion | Compiled as a loop | Compiled as recursion, under a depth limit of 1,000 |
| Folds | `Array.foldl` over `Array UInt64` and `Array Float` with a `UInt64` or `Float` accumulator, and `List.foldl` over `List UInt64` | Whole-array `Array.foldl` over every element type, with an accumulator of any dialect type |
| Array updates | `set!`, `setIfInBounds`, `insertIdx!`, `eraseIdxIfInBounds`, and `push` on `Array UInt64`, and `++` with an owned left operand | `set!`, `setIfInBounds`, `push`, `++`, `insertIdx!`, `insertIdxIfInBounds`, `eraseIdxIfInBounds`, `LeanExe.insertAt`, and `LeanExe.eraseAt` on arrays of every element type |
| `@[inline]` helpers | Unfolded at their use | Unfolded at their use.  A listed helper compiles as a function. |
| Records with array fields | Outside the dialect | Supported |
| Constant arrays | Array literals of words, allocated at each call | Tables in data segments, passed by wrappers |
| Loops, builds, and calls in loop bodies and branches | Subject to placement rules | Any expression of the dialect |
| Composition across modules | `ImplementsPure` for functions that keep the store | Within one program |

A program within the verified compiler's dialect needs no proof of its own.  The generated
trap-free theorems cover source functions and wrappers without call depth under their allocation
bounds and, for recursive source functions, their frames conditions.  A program that needs
`Float32`, WGSL kernels, lists or trees, or sum types with fields
compiles only with the LeanExe compiler.  Binary64 GPT-2 and the Euler solvers compile with both
compilers.  [The verified-executable skill](.claude/skills/verified-executable/SKILL.md), which takes a request in
English to a program and a theorem about its bytes, uses the LeanExe compiler.  The verified
compiler has its own definitions of the IR parts it needs, and nothing in `LeanExe` or `Examples`
imports `Verified`, so a change to either compiler's code leaves the other compiler unchanged.

### Trusted base

The theorems of both compilers depend on Lean's kernel with the axioms `propext`,
`Classical.choice`, and `Quot.sound`, Talos's semantics, the binary decoder, which the official
WebAssembly testsuite tests, and the step from a module constant to a file.  Neither compiler is
trusted, since the kernel checks every theorem and a wrong translation makes a proof fail.  The
floating-point theorems describe the WebAssembly deterministic profile, which the Wasmtime host
matches by enabling NaN canonicalization, and the WGSL theorems hold under a model of the GPU.  No
theorem covers the host or the I/O around a call.

## Documentation

| Document | Contents |
|---|---|
| [The LeanExe compiler manual](docs/leanexe-manual.md) | The LeanExe compiler's dialect, commands, theorems and rules, tests, and examples, the skill, and the development practice. |
| [The verified compiler manual](docs/verified-manual.md) | The verified compiler's dialect, the declarations that `verified_compile` adds, bounds, tests, and examples. |
| [The verified compiler's internals](Verified/README.md) | Its code scheme, the structure of its proof, and the reflector. |
| [The design document](docs/design.md) | The design, its decisions, what is proved and tested, and the open work. |
| [The development journal](devnotes.md) | The record of the work. |
| [The numerical index](index.md) | The compiled numerical algorithms and their proved results. |

## Layout

| Path | Contents |
|---|---|
| [`LeanExe/`](LeanExe/) | The library `LeanExe`: the LeanExe compiler and the parts that both compilers share. |
| [`LeanExe/Dialect/`](LeanExe/Dialect/) | The modules a program may import.  Both compilers accept the combinators `LeanExe.loop`, `LeanExe.build`, and `LeanExe.repeatWhile`.  The verified compiler accepts `LeanExe.insertAt` and `LeanExe.eraseAt`, and the LeanExe compiler accepts `LeanExe.Float32.nearest`. |
| [`LeanExe/Compiler/`](LeanExe/Compiler/) | The LeanExe compiler and the `leanexe_compile` command. |
| [`LeanExe/IR/`](LeanExe/IR/) | The IR, `compile`, the statement and template rules, and the `Live` invariant of composite bodies. |
| [`LeanExe/Runtime/`](LeanExe/Runtime/) | The code of the runtime functions `alloc` and `release`, and the free-list layout. |
| [`LeanExe/Pipeline/`](LeanExe/Pipeline/) | `Implements` and `ImplementsA`, the allocator invariant `Heap.At`, the allocation and release specifications, and the memory budget. |
| [`LeanExe/Encoding/`](LeanExe/Encoding/) | The encoder, the decoder, and `decode_encode`. |
| [`LeanExe/ProofKit/`](LeanExe/ProofKit/) | General lemmas: memory, arrays, allocation, binary32 and binary64 arithmetic and enclosures, and the raw-bit float wrappers that the float proofs state their results about. |
| [`LeanExe/WGSL/`](LeanExe/WGSL/) | The WGSL subset, its printer, parser, and semantics, and the proved translation of IR kernels into WGSL. |
| [`Verified/`](Verified/) | The library `Verified`: the verified compiler, its theorem, the `verified_compile` command in `Reflect/`, and its examples in `Examples/`.  It is not a default target of `lake build`. |
| [`Examples/`](Examples/) | The library `Examples`: a directory for each example of the LeanExe compiler, which holds a README, the program, the module, the proofs, and the module cases, and in some examples a specification, a request, and run records.  The directories `Lcg`, `ParkMiller`, and `Xorshift` hold programs, which the verified compiler compiles, and theorems about them, and `Orbit` holds lemmas that they share. |
| [`docs/`](docs/) | The two manuals and the design document. |
| [`ltg/`](ltg/) | The LTG knowledge base and its checker, `Check.lean`. |
| [`.claude/skills/verified-executable/`](.claude/skills/verified-executable/SKILL.md) | The skill that takes a request in English to a program and a theorem about its bytes. |
| [`tools/`](tools/) | The resource-limited Lean runner, `Emit.lean` and `EmitWgsl.lean`, which write modules and kernels, the Wasmtime and WebGPU hosts and their build scripts, the checker `demo-check`, and the Euler and GPT-2 command-line tools. |
| [`tests/`](tests/) | Module, decoder, drone, PRNG, WGSL, and verified-compiler tests, the binary64 GPT tests of [`tests/gpt/`](tests/gpt/), the binary32 GPT-2 tests of [`tests/gpt32/`](tests/gpt32/), and the WebGPU pages of [`tests/web/`](tests/web/). |
| [`data/`](data/), [`paper/`](paper/) | Records of runs, and reports. |

## Commands

Commands run from the repository root.  Lean uses the version in [the toolchain file](lean-toolchain)
and the dependencies in [the Lake manifest](lake-manifest.json).  The examples need `wasm-tools`
at the version in [the version file](.wasm-tools-version), a C compiler for the Wasmtime host, and
`uv` for the Python tests.  On Linux, the runner needs a systemd user session with cgroup controls.
[The manual](docs/leanexe-manual.md#the-wasmtime-host) also describes the macOS setup.

Every Lean or Lake command runs through [`tools/leanrun`](tools/leanrun), as [the repository
instructions](AGENTS.md) require.  The commands below build the host and three libraries, write the bytes of
the LeanExe compiler's `gcd`, validate them, run them in Wasmtime, check the LTG entries, and test
every module of the verified compiler against native Lean.  The manuals list the other tests and the
full check.

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/download-wasmtime.sh
tools/build-wasmtime-host.sh
tools/leanrun --timeout 60m lake build
tools/leanrun --memory-high 10G --timeout 12h lake build Verified
mkdir -p build/gcd
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Gcd.Module Examples.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
tools/leanrun --timeout 10m lake env lean --run ltg/Check.lean ltg/entries
tests/verified/run.sh
```

The full `Verified` build includes the numerical proofs and can take several hours.  Its lgamma
root-range proofs use `--memory-high 10G`, which sets the memory maximum to 12 GiB.  Focused
builds, such as `tools/leanrun --timeout 60m lake build Verified.Examples.Lcg`, build the selected
example and its imports.  [The verified compiler manual](docs/verified-manual.md#the-full-check)
describes the full check.

[`tests/modules/run.sh`](tests/modules/run.sh) compares every module of the LeanExe compiler except
`gpt`, `gpt32`, and `prng` with native Lean on the cases in each example's `Cases.lean`, which
[`tests/modules/Cases.lean`](tests/modules/Cases.lean) runs in turn, and
[`tests/gpt/run.sh`](tests/gpt/run.sh) does the same for `gpt.wasm`.  Both read the modules from
`build/NAME/NAME.wasm`.  [`tests/verified/run.sh`](tests/verified/run.sh) writes the verified
compiler's modules to `build/verified/` and compares them with native Lean on the cases of
[`Verified/Examples/Cases.lean`](Verified/Examples/Cases.lean).

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/.  One runs the WGSL kernel
tests on a browser's WebGPU, and the other runs GPT-2 with its kernels on WebGPU, in WebAssembly, or
on both and compares them.  [The description of the pages](tests/web/README.md) covers their setup
and what is proved about what they run.  The GPT-2 page needs the binary32 weights that `uv run
tests/gpt32/generate.py --export` writes.
