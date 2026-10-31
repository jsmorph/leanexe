# LeanExe

LeanExe compiles functions written in a restricted dialect of Lean to WebAssembly, C, and WGSL, and proves in Lean that the compiled code computes those functions.

The compiler has one correctness theorem for every typed source program that it accepts.  The WebAssembly theorems hold in [Talos](https://github.com/cajal-technologies/talos)'s semantics, and an execution theorem may allow a trap at `unreachable`, which the theorem `p.f.trapFree` excludes under its allocation and call-depth premises.  The compiled modules also translate to a subset of [CompCert](https://compcert.org/compcert-C.html)'s C, with a theorem about each C function in the Lean copy of CompCert's Clight, and CompCert compiles the C for x86-64 and AArch64, under an operating system or on bare-metal AArch64.  Only the bare-metal programs have a theorem about the whole program, which a Rocq proof carries to CompCert's Asm, and an executable under an operating system also depends on a C host that no theorem covers.  Array builds compile to WGSL compute kernels with theorems about a modeled GPU dispatch, and Lean actions with stdin, stdout, stderr, and exit compile to WASI Preview 1 modules.

## Background

This project is inspired by small languages designed to simplify analysis, implementation, and verification: [PreScheme](https://dustycloud.org/misc/prescheme.pdf), [Low\*](https://arxiv.org/abs/1703.00053), [ACL2](https://doi.org/10.1109/32.588534), [CompCert C / Clight](https://xavierleroy.org/publi/Clight.pdf), [CakeML](https://cakeml.org/popl14.pdf), and [TinyGo](https://tinygo.org/).

Donald Knuth's [The Art of Computer Programming](https://cs.stanford.edu/~knuth/taocp.html) and in particular its "Seminumerical Algorithms" are major inspirations as well.  We are explicitly organizing some development in a similar spirit.  For example, see the current set of [elementary and special functions](https://github.com/jsmorph/leanexe/blob/main/index.md#6-elementary-and-special-functions).

We strive to be both pragmatic and demanding.  For example, floating-point operations have been in scope since the beginning of the project.  IEEE 754 is an impressive, challenging beast.  See David Goldberg's ["What Every Computer Scientist Should Know About
Floating-Point Arithmetic"](https://dl.acm.org/doi/10.1145/103162.103163).  We are building machinery for complete floating-point accuracy.  The [fused multiply-add](https://github.com/jsmorph/leanexe/blob/main/Library/Numerics/Arithmetic/Fma/FmaTheorem.lean#L144-L149) development is a good example.

These days rewriting a large codebase in a different source language is almost automatic (given appropriate stern oversight).  So inventing a new language today doesn't necessarily impose the classic high hurdles to adoption.  However, AI is of course trained on existing corpora.  Lean in particular continues to receive a lot of investment by AI companies.  So we decided to proceed from a [strict subset of Lean](https://github.com/jsmorph/leanexe/tree/main/docs).

## Demos

Here are some of the demos in this repo:

- [Binary32 GPT-2](Demos/Gpt32/README.md): one generation step of GPT-2 124M in `Float32`, compiled to WGSL kernels with dispatch theorems and to WebAssembly.  `generate_host` composes the kernels' theorems into the step's scores, and a browser page runs the model on WebGPU and in WebAssembly and compares the scores.
- [Binary64 GPT-2](Demos/Gpt/README.md): the model in `Float`, with `steps_exact`, which proves that cached generation equals full inference bit for bit, and `forward_causal`.
- [Euler solvers](Demos/Euler/README.md): finite-volume solvers for the compressible Euler equations.  `euler_solve_call` proves that the module returns the solvers' results without a trap within a memory cap, the balance theorems bound the rounding error of conservation, and the solver also runs as C and as a bare-metal AArch64 program.
- [Drone planner](Demos/Drone/README.md): flights over terrain that `drone_compute` and `drone_safe` prove optimal and safe in a point-mass model.
- [Slew planner](Demos/Slew/README.md): spacecraft attitude slews that keep body vectors outside keep-out cones and inside keep-in cones, with `plan_safe` for the constraints and `plan_optimal` for least duration.
- [Running sums](Demos/RunningSum/README.md): WASI programs that read numbers from stdin and print cumulative totals, with proofs of canonical output and eventual exit.  [The binary64 version](Demos/RunningSumFp/README.md) composes proved parsing, IEEE 754 addition, and printing.
- [Energy authorizer](Demos/Energy/README.md): decides whether a gateway may send proposed battery power limits to the inverter of a solar-and-battery site for one window of time.  `authorize_sound` proves that, under accepted limits, every trajectory that the model admits keeps the site's energy and grid limits or stays no further outside them than a return to the inverter's fallback mode would, and `energy_authorize` carries the decision to the module's bytes.
- [SHA-256](#a-worked-example-sha-256): from a transcription of FIPS 180-4 to WebAssembly, C, and a bare-metal AArch64 image whose whole-program theorem a Rocq proof carries to CompCert's Asm.
- [Elementary and special functions](index.md#6-elementary-and-special-functions): binary64 implementations with proved accuracy bounds, and a software [fused multiply-add](Library/Numerics/Arithmetic/Fma/README.md) proved equal to IEEE 754's fusedMultiplyAdd for all operands.

## Selected documentation

- [Verified compiler manual](docs/verified-manual.md): the dialect, `verified_compile`, the generated theorems, and the tests.
- [Verified compiler internals](Verified/README.md): the source language, the compiler, and its universal proof.
- [Algorithm index](index.md): each program with its proved results and compiled forms.
- [Trusted base](docs/trusted-base.md): what each kind of theorem trusts.
- [Design document](docs/design.md): the architecture and its decisions.

## Artifacts

Each artifact has a code, which [the algorithm index](index.md) uses to list the compiled forms of the library algorithms, applications, and example programs.  The index also marks a specification theorem with S.  [The SHA-256 example](#a-worked-example-sha-256) builds and runs the WebAssembly, file, C, and bare-metal artifacts of one program.

| Code | Artifact | Written by | Theorem and its semantics | Runs on | Examples |
|---|---|---|---|---|---|
| V | WebAssembly module from the verified compiler | `verified_compile` defines the module and its theorems, and `tools/Emit.lean` writes the file | `p.f.implements`, from the universal theorem `Prog.correctStaticWith`, with `p.f.bound`, `p.f.trapFree`, and `p.bytes`, in Talos's semantics and the binary decoder | Wasmtime | `Compiled` and `Verified` modules of [the library](Library/README.md), [the demos](Demos/README.md), and [the example programs](Examples), and [the compiler fixtures](Verified/Examples), most of which [the module registry](tests/verified/modules.txt) lists |
| F | Emitted `.wasm` file with a file theorem | [`tests/verified/run.sh`](tests/verified/run.sh) writes `build/verified/NAME.wasm` with `tools/Emit.lean` and then checks the file module | `NAME_file` and `NAME_file_decode`: the bytes that the trusted elaborator `binary_file%` reads from the file equal `encode p.module` and decode to the module | Wasmtime | Modules of [the file-theorem registry](tests/verified/numerics.txt), which holds every module of [the module registry](tests/verified/modules.txt) but `byhand`, the hand-built module of `Verified.Examples.Modes`, which has no `p.module` |
| I | WASI Preview 1 module, callable or command | `verified_compile_wasi`, and `tools/Emit.lean` writes the file | Callable `p.f.implements`, command `p.start`, and the conditional `p.f.total` and `p.total`: the exports perform the actions' ordered effects with the same results and terminal outcomes, in Talos's semantics with the modeled WASI host | Wasmtime's Preview 1, through `leanexe-wasmtime-host run` for a command and `--wasi call` for a callable export | [Running sum](Demos/RunningSum/README.md), [floating-point running sum](Demos/RunningSumFp/README.md), and [the stdio example](Verified/Examples/WasiStdio.lean) |
| C | C file and its native executable | `native-verified build MODULE CONSTANT NAME DIR` writes `NAME.c` and its glue, has `clightgen` read the C back, compares that Clight with the translation, and compiles `NAME.o` with `ccomp` only when they agree, and `ccomp` links the object with [the C host](tools/native-host.c) | `p.f.native`, stated as `NativeImpl`, `NativeTablesImpl`, or `NativeStaticImpl`: the C function terminates with the words of the Lean result or, when the function may abort, with a trap code, in the Lean copy of Clight | Linux on AArch64 and on x86-64 | `verified_compile` modules of the registry, [packed byte values](Verified/Examples/Bytes.lean), and [byte literals](Verified/Examples/Literals.lean) |
| A | C file without the alignment test | `native-verified build --aligned`, which refuses with status 4 a module whose theorems do not cover that translation | `p.f.nativeAligned`, stated as `NativeAlignedImpl` or `NativeTablesAlignedImpl`, from an aligned input, in the Lean copy of Clight | Linux on AArch64 and on x86-64 | [SHA-256](Library/Hashing/Sha256/Compiled.lean), [SHA-3](Library/Hashing/Sha3/Compiled.lean), [CRC](Library/Hashing/Crc/Compiled.lean), [insertion sort](Library/Sorting/Insertion/Compiled.lean), [Euler solvers](Demos/Euler/Verified.lean), and [binary32 GPT-2](Demos/Gpt32/Verified.lean) |
| B | Bare-metal AArch64 image | `native-bare emit` or `emit-in` writes the translation with a generated `main`, `native-bare check` or `check-in` compares the Clight of `clightgen` with the whole program, and [the bare-metal build](tools/baremetal/build.sh) links it with the startup code | `p.f.program`, which `bare_program` proves, and `sha256_input`: the whole program terminates with the stores of the result's bytes to the UART, in the Lean copy of Clight, and [the Rocq composition](rocq/Clight2Asm.v) carries such a termination to Asm.  `p.f.program` also allows the code of `unreachable` with no output when the entry may abort, and `sha256_input` allows it when `alloc` traps. | QEMU's `virt` machine under TCG and under KVM | [GCD](tests/TestSupport/Bare/Gcd.lean), [CRC-32, SHA-256, Euler, and a deep recursion](tests/TestSupport/Bare/Theorems.lean), and [SHA-256 of a loaded message](tests/TestSupport/Bare/Input.lean) |
| G | WGSL kernel | [`tools/EmitWgsl.lean`](tools/EmitWgsl.lean) prints the kernel after checking that the parser reads the text back | Dispatch theorem, such as `scale32_dispatch` or `gpu.dispatch_eq`: the dispatch writes the Lean function's result and is race-free, in the WGSL device model with strict binary32 arithmetic | wgpu-native through `build/tools/leanexe-webgpu-host` on SwiftShader and llvmpipe, and WebGPU in a browser | [Binary32 example](Examples/Binary32/README.md), [binary32 GPT-2](Demos/Gpt32/README.md), and [the verified kernel examples](Verified/Examples/Wgsl.lean) |

### Properties carried to the artifacts

| Property | Theorems | Artifacts reached |
|---|---|---|
| Specification theorems: accuracy bounds, equality with transcriptions of FIPS 180-4, FIPS 198-1, FIPS 202, ITU-T V.42, RFC 3720, the SipHash paper, and the xxHash specification, generator periods, and the safety and optimality of the drone and slew planners | Such as `exp_bytes_accuracy`, `sha256_call`, `lcg_advance`, `drone_safe`, and `plan_safe` | V: the theorem composes, as `sha256_call` composes `compiled.sha256.implements` with `sha256_spec` and `gcd_call` composes `compiled.gcd.pure` with `gcd_eq`.  `drone_safe` states the safety of the Lean function's result for valid nonempty terrain beside the module's execution theorem, which allows a trap, so the safety holds of every result that the module returns, and `plan_safe` states the slew planner's safety for the Lean function.  F: the combination of `sha256_file_decode` with `sha256_call`.  C and A: the combination of `compiled.sha256.native` or `compiled.sha256.nativeAligned` with `sha256_spec`.  B: `sha256_input` composes `compiled.sha256.native` with `sha256_bytes` into the bytes of `SHS.SHA256.Impl.sha256`, or the code of `unreachable` with no output when `alloc` traps, and its combination with `SHS.Equiv.SHA256.sha256_correct` gives the digest of the transcription of FIPS 180-4.  G: `generate_host` composes the kernels' dispatch theorems into the scores of `step32`. |
| Allocation bounds | `p.f.bound` with its equation `p.f.bound_eq`, closed forms such as `sortInsert_bound`, `pushSquare_bound`, `jump_bound`, and the Euler solvers' `solve_bound`, the memory caps of the Euler and drone call theorems, and the WASI processes' allocation charges | V: `p.f.trapFree` takes room for the bound as a premise.  `euler_solve_call` and `drone_compute_call` state that room as a memory cap in pages: `solvePages n`, at most 1,563 for every grid, for the Euler solvers, from the store in which the module starts, and 35 for the drone planner, with `top` at most 8192.  `increment_call` takes room for `top` to rise by 120 bytes, the closed form `compute_bound` of the bound, from any store with the allocator invariant.  I: the running sums prove the allocation charges of each process step from limits on their input.  F: the combination of `NAME_file_decode` with `p.f.trapFree`, for the `verified_compile` modules of the file-theorem registry. |
| Return without a trap | `p.f.trapFree`, `euler_solve_call`, `drone_compute_call`, and `increment_call`, the WASI theorems `p.f.total`, `p.total`, and `compiled_process_total_run`, and their applications `retain_total`, `initial_terminates_integer`, and `initial_terminates_fp` | V: under room for `p.f.bound` and the depth limit, and for the Euler solvers and the drone planner under the memory caps of `euler_solve_call` and `drone_compute_call`, and for the increment example under room for 120 bytes in `increment_call`.  I: under a typed resource-prefix bound and assumptions about the host operations that a run reaches.  C and A: `p.f.native` and `p.f.nativeAligned` state that the C function terminates, with no trap code for a function whose abort flag is false, as `loop_native_init` states for GCD from the state that `lx_init` leaves.  For a function that may abort, `ImplementsA.nativeImpl` applied to `p.f.trapFree` proves that conclusion under the premises of `p.f.trapFree`, and no generated theorem states it.  B: `p.f.program` states that the whole program terminates, with result 0 for an entry whose abort flag is false, as the GCD program's theorem does.  F: the combination of `NAME_file_decode` with `p.f.trapFree`, as for the allocation bounds. |

### A worked example: SHA-256

[The SHA-256 proof](Library/Hashing/Sha256/Proof.lean) relates the Lean implementation to a transcription of FIPS 180-4.  The commands require the [Wasmtime host](#commands) and CompCert 3.18's `ccomp` and `clightgen` on the search path.  A CompCert built in a source tree `DIR` and not installed needs `-stdlib DIR/runtime` on the `ccomp` link command and `CCOMP_STDLIB=DIR/runtime` for `tests/baremetal/inputs.sh`.

| Step | Code | Files written | Theorem |
|---|---|---|---|
| Verified compilation | V S | Module constant `Library.Hashing.Sha256.compiled.module` in Lean's build | `compiled.sha256.implements`, `compiled.bytes`, and [`sha256_call`](Library/Hashing/Sha256/Bytes.lean), which composes the first with [`sha256_spec`](Library/Hashing/Sha256/Proof.lean) |
| Emission | F | `build/verified/sha256.wasm` | [`sha256_file` and `sha256_file_decode`](Library/Hashing/Sha256/File.lean) |
| Call in Wasmtime | V | None | `sha256_call`, for the message `abc` packed into the word 6,513,249 |
| Native build | C | `build/native/sha256/sha256.c`, `sha256_glue.c`, `sha256.exports`, `sha256.depth`, `sha256.v`, `sha256.o`, and the executable `sha256` | `compiled.sha256.native` |
| Native build without the alignment test | A | Same files in `build/native/sha256-aligned/` | `compiled.sha256.nativeAligned` |
| Bare-metal image with input | B | `build/baremetal/inputs/sha256in.c`, `sha256in.v`, `sha256in.elf`, and its stack bound `sha256in.elf.bound` | [`sha256_input`](tests/TestSupport/Bare/Input.lean), which also allows the code of `unreachable` with no output when `alloc` traps, with `clight2_bigstep_asm_reads` of [the Rocq composition](rocq/Clight2Asm.v) |

```sh
tools/leanrun --timeout 60m lake build Library.Hashing.Sha256.Bytes native-verified
mkdir -p build/verified build/native/sha256 build/native/sha256-aligned
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Hashing.Sha256.Compiled Library.Hashing.Sha256.compiled.module build/verified/sha256.wasm
tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha256/File.lean
build/tools/leanexe-wasmtime-host call build/verified/sha256.wasm sha256 \
  list:i64,i64,i64,i64 array-u64:6513249 i64:3
tools/leanrun --timeout 10m lake env .lake/build/bin/native-verified build \
  Library.Hashing.Sha256.Compiled Library.Hashing.Sha256.compiled.module sha256 build/native/sha256
ccomp -I tools -o build/native/sha256/sha256 build/native/sha256/sha256.o \
  build/native/sha256/sha256_glue.c tools/native-host.c
build/native/sha256/sha256 call sha256 list:i64,i64,i64,i64 array-u64:6513249 i64:3
tools/leanrun --timeout 10m lake env .lake/build/bin/native-verified build --aligned \
  Library.Hashing.Sha256.Compiled Library.Hashing.Sha256.compiled.module sha256 \
  build/native/sha256-aligned
tests/baremetal/inputs.sh
```

`tests/baremetal/inputs.sh` builds `native-bare`, writes and checks the program, links it with the startup code, and runs it under QEMU on eleven messages of 0 to `2^24 - 8` bytes, whose outputs must equal those of `sha256sum`, and on two longer lengths, which must give no output and the status 64.  With `ACCEL=kvm` the same script runs the image under KVM.  [The SHA-256 guide](Library/Hashing/Sha256/README.md) describes the program, and [the bare-metal design](docs/native-bare-metal.md#arguments-not-fixed-in-advance) describes the input path.

## Compiler

### Pure functions

`Verified.compileWith` translates a typed source program to a module.  The universal theorem `Prog.correctStaticWith` proves that the module computes the source meaning, `denote`, under its heap and static-data premises.  `verified_compile p := [f, …]` reflects Lean definitions into that source language and proves their correspondence.  It derives `p.f.implements` from those equations and the universal theorem, and Lean's kernel checks the generated proofs.

The command also generates each function's allocation bound and a trap-free theorem under that bound.  For a scalar function of a program without byte literals, when its rules prove that execution does not depend on the store, it generates `p.f.pure`: from any store, the call returns the Lean result and leaves the store unchanged, which lets other compiled programs call the function.  [The verified compiler manual](docs/verified-manual.md) states the type restrictions, ownership rules, generated declarations, and proof premises, and [the internals guide](Verified/README.md) describes the compiler and its universal proof.  [The verified-request skill](.claude/skills/verified-request/SKILL.md) turns an English request into a specification that a fresh agent reviews, a program, and a theorem `Verified.CallSpec` that the program's export returns the specification's value without a trap under its generated allocation bound, which [`tools/verified-request-check`](tools/verified-request-check) states and checks.

The dialect covers words, Booleans, floats of both widths, tuples, structures, enumerations, sums, arrays, records with array fields, packed bytes, lists, and recursive types, and each row below links fixtures that compile them.  [The verified compiler manual](docs/verified-manual.md#the-dialect) states the representations, ownership rules, and restrictions.  Integers are `UInt64`, so a program and its module compute the same values, wraparound included.

| Types and forms | Examples |
|---|---|
| Words, Booleans, and their operations | [`Poly`](Verified/Examples/Poly.lean), [`Mix`](Verified/Examples/Mix.lean), and [`Select`](Verified/Examples/Select.lean) |
| Binary64 and binary32 floats | [`Floats`](Verified/Examples/Floats.lean) and [`Floats32`](Verified/Examples/Floats32.lean) |
| Tuples, structures, enumerations, and sums with scalar fields, and structure patterns that fix fields to enumeration constructors | [`Pairs`](Verified/Examples/Pairs.lean), [`Records`](Verified/Examples/Records.lean), [`Enums`](Verified/Examples/Enums.lean), [`Sums`](Verified/Examples/Sums.lean), and [structure patterns](Verified/Examples/Patterns.lean) |
| Arrays of words, Booleans, floats, tuples, and structures, with updates, growth, insertion, and removal in place | [`Arrays`](Verified/Examples/Arrays.lean), [`Elements`](Verified/Examples/Elements.lean), [`Grids`](Verified/Examples/Grids.lean), [`Tuples`](Verified/Examples/Tuples.lean), [`Updates`](Verified/Examples/Updates.lean), [`Grow`](Verified/Examples/Grow.lean), [`Insert`](Verified/Examples/Insert.lean), [`Owned`](Verified/Examples/Owned.lean), and [`Modes`](Verified/Examples/Modes.lean) |
| Records with array fields | [`Fields`](Verified/Examples/Fields.lean) |
| Packed byte buffers and byte literals | [Packed byte values](Verified/Examples/Bytes.lean) and [byte literals](Verified/Examples/Literals.lean) |
| Sums whose fields hold byte buffers, arrays, trees, and lists | [Sums with heap fields](Verified/Examples/HeapSums.lean) |
| Lists of words | [Lists](Verified/Examples/Lists.lean), [guarded list recursion](Verified/Examples/ListRecursion.lean), [list loops](Verified/Examples/ListLoops.lean), and [list tail recursion](Verified/Examples/ListTail.lean) |
| Recursive types, with one or several record constructors | [User-defined recursive values](Verified/Examples/RecursiveTypes.lean), [tagged recursive values](Verified/Examples/TaggedTypes.lean), and [the word trees](Library/Trees/README.md) |
| Tree records with `Bool`, binary64, binary32, word, structure, enumeration, and sum fields | [Trees with typed fields](Verified/Examples/TypedTrees.lean) |
| Tree records with array fields, and with byte-buffer fields and their lengths | [Trees with array fields](Verified/Examples/ArrayTrees.lean) and [trees with buffer fields](Verified/Examples/BufferTrees.lean) |
| Counted loops, builds, `repeatWhile`, and array folds | [`Loops`](Verified/Examples/Loops.lean), [`Owned`](Verified/Examples/Owned.lean), [`Repeat`](Verified/Examples/Repeat.lean), and [array folds](Verified/Examples/Fold.lean) |
| Tail recursion as loops, and guarded recursion to depth 1,000 | [Tail loops](Verified/Examples/Tail.lean), [tail conditions](Verified/Examples/TailConditions.lean), and [`Recursion`](Verified/Examples/Recursion.lean) |
| Calls, `@[inline]` helpers, constant tables, and wrappers | [`Calls`](Verified/Examples/Calls.lean), [frontend forms](Verified/Examples/Frontend.lean), [`Tables`](Verified/Examples/Tables.lean), and [the sine and cosine](Library/Numerics/Float64/Trig/Program.lean) |
| Composition and relocation of compiled programs | [Composition](Verified/Examples/Composition.lean), [scalar composition](Verified/Examples/ScalarComposition.lean), and [relocation](Verified/Examples/Relocation.lean) |

### WASI programs

`verified_compile_wasi` compiles `LeanExe.Wasi.Action` definitions with stdin reads, stdout and stderr writes, bounded effectful loops, and exit.  Actions use Lean `do` notation and `UInt64` counts, lengths, and statuses.  Callable-entry and `_start` theorems relate exported execution to the native actions, preserving ordered effects and effects committed before an error or trap.  Total execution requires a typed resource-prefix bound and assumptions about reached host operations.  [The WASI manual](docs/wasi.md) defines the API, export forms, proof premises, native interpreter, and Wasmtime's exit-acceptance policy.

`LeanExe.Wasi.Process` composes bounded actions through an unbounded outer loop.  [The running-sum application](Demos/RunningSum/README.md) reads decimal integers through EOF, prints each cumulative total, and handles short writes, and [its compiled theorem](Demos/RunningSum/Correct.lean) proves canonical output and eventual accepted exit under limits on the bytes of each line and the digits of each total.  The theorem also assumes a Talos host environment that meets the specifications of the three imports, a host whose reads return the input stream without an error and whose writes make progress, and a host that accepts the exit statuses 0 and 28.  [The floating-point version](Demos/RunningSumFp/README.md) parses binary64 values and prints each sequential binary64 total, and its proofs compose the parser and printer theorems with IEEE 754 addition and the process proof.  Each application proves the allocation charges of each step from limits on its input, and corollaries cover lines of up to 9,000,000 bytes and totals of up to 9,000,000 digits for the integer sum and lines of up to 50,000,000 bytes for the floating-point sum.

## Native code

### The translation to C

The translator, `LeanExe.Native.translate`, accepts the modules that pass a decidable check of its subset of WebAssembly.  It writes one C function for each WebAssembly function that it translates and holds the linear memory in a static array, whose size `verified_compile` sets to `nativeCap`, 4,096 pages or 256 MiB.  Its simulation theorem, `translate_correct`, carries every Talos run that ends in a return or a trap to a terminating execution in the Lean copy of CompCert 3.18's Clight, and `p.f.native` follows from it and `p.f.implements` for each function.  The `clightgen` comparison of each build covers the printer and the written file, so neither needs a theorem.  [The translator's design](docs/native-translator.md) gives the subset, the translation scheme, the proof layers, and the trusted base.

Every module of [the module registry](tests/verified/modules.txt) lies inside the subset.  `tests/native/verified.sh` translates each module, compiles it with CompCert and the C host `tools/native-host.c`, and compares every case that the translation can run with the line that the Wasmtime host gives, with the same rules for traps and allocation counters.  `tests/native/run.sh` compares translated programs with Talos's runs, `tests/native/bytes.sh` runs the byte and literal examples, and `tests/native/clight.sh` compares the Lean copy of Clight with `ccomp -interp` on random programs under the NaN parameters of either target.  [The development journal](devnotes.md#2026-10-29-the-wasm-to-c-translator-the-bound-in-a-temporary) records the corpus runs.

### The translation without the alignment test

The translation option `alignedAccess` makes every 64-bit load and store read or write one word of `lx_mem` after the bounds check, without the test of the address's low three bits and the eight byte accesses of an unaligned address.  With `set_option verified_compile.alignedNative true`, `verified_compile` also emits that translation, `p.translationAligned`, and the theorem `p.f.nativeAligned`, whose statement `NativeAlignedImpl` or `NativeTablesAlignedImpl` adds the premise `AlignedInput` and concludes, beside the conclusions of `p.f.native`, an aligned final heap and a result whose blocks meet `AlignedOutput`.  `tests/native/aligned.sh` tests the refusal of `native-verified build --aligned` for a module without those theorems, and a program with byte literals has none.

`tests/native/bench.sh` times corpus workloads in their native form and in Wasmtime.  CompCert aligns a function to 4 bytes on AArch64, so `--placements` also links each native program at sixteen code offsets and reports the mean over them, as [the benchmark method](docs/native-translator.md#benchmark-method) describes.  [The placement benchmark](devnotes.md#2026-10-29-the-placement-benchmark-with-and-without-the-alignment-test) of 2026-10-29 ran on AArch64 only, with CompCert built from the 3.18 sources and Wasmtime's C API 44.0.0, and gave these mean times per call:

| Workload | Module | With the test (ms) | Without the test (ms) | Change |
|---|---|---:|---:|---:|
| `sort` | Insertion sort | 23.732 | 18.583 | -21.7% |
| `linear32` | Binary32 GPT-2 | 2.294 | 1.777 | -22.5% |
| `layernorm32` | Binary32 GPT-2 | 3.567 | 2.867 | -19.6% |
| `euler` | Euler solvers | 179.073 | 176.153 | -1.6% |
| `crc32` | CRC | 3.819 | 3.764 | -1.4% |
| `sha256` | SHA-256 | 12.891 | 12.791 | -0.8% |
| `sha3` | SHA-3 | 9.878 | 9.845 | -0.3% |

`sort`, `linear32`, and `layernorm32` run 19.6 to 22.5 percent faster without the test, and the remaining workloads change by less than 2 percent.  The translation with the test stays the default, because the whole-program theorems and the bare-metal path exist only for it.  [An earlier run](devnotes.md#2026-10-29-the-wasm-to-c-translator-the-benchmark-of-the-bound-in-a-temporary) of the translation with the test measured Wasmtime's median time per call as 0.28 times the native median for `sort`, 0.71 for `crc32`, 0.78 for `euler`, 0.86 for `sha256`, 1.11 for `sha3`, 1.18 for `linear32`, and 1.38 for `layernorm32`.

### Bare-metal programs

A bare-metal program is the translation of a module, a volatile global `lx_out` at the UART's data register of QEMU's `virt` machine, and a generated `main` that calls `lx_init`, calls one entry on arguments fixed when the program is built, and writes the bytes of the result to `lx_out`.  `bare_program p.f x [args] r` proves `p.f.program`: the whole program terminates with result 0 and a trace of one volatile store per byte of the result's encoding or, when the entry may abort, with result 1 and an empty trace.  The Rocq theorem `clight2_bigstep_to_asm` in [the Rocq composition](rocq/Clight2Asm.v) composes CompCert's forward simulations from Clight to Asm, and `clight2_bigstep_asm_unique` shows that, for a trace without inputs, such a termination is the only behavior of the Asm program.  Both Rocq theorems take the termination as a judgment of CompCert's own Clight in Coq, and the step from the Lean theorem to that judgment rests on the Lean copy's agreement with CompCert's definitions and on the `clightgen` comparison of each build, which no proof covers.  The startup code in `tools/baremetal/` turns on the MMU and the caches.  The build fails when the static stack bound of `main` exceeds the stack or when the assembly contains an instruction that requires an aligned access.  [The bare-metal design](docs/native-bare-metal.md) gives the statement, the startup code, the input path, the stack bound, and the trusted base.

| Program | Entry and arguments | Theorem |
|---|---|---|
| GCD | `gcd 1071 462` of test support, whose tail recursion compiles as a loop | [GCD program](tests/TestSupport/Bare/Gcd.lean) |
| CRC-32 | `crcCheck` of the ASCII digits 1 to 9, from the library's `crcWith` and table | [Program theorems](tests/TestSupport/Bare/Theorems.lean) |
| SHA-256 of a constant | `shaCheck` of `abc`, from the library's `sha256With` and round constants | [Program theorems](tests/TestSupport/Bare/Theorems.lean) |
| Euler solver | `solve 4` of the verified Euler module | [Program theorems](tests/TestSupport/Bare/Theorems.lean) |
| Deep recursion | `recursive 1000` of [the fold example](Verified/Examples/Fold.lean), which reaches the depth limit | [Program theorems](tests/TestSupport/Bare/Theorems.lean) |
| SHA-256 with input | Library export `sha256` on a message of at most `2^24 - 8` bytes that QEMU's loader places at `lx_in` | `sha256_input` in [the input program](tests/TestSupport/Bare/Input.lean) |

`tests/baremetal/programs.sh` and `tests/baremetal/inputs.sh` run these programs on QEMU's `virt` machine, under TCG on an emulated Cortex-A57 by default and, with `ACCEL=kvm`, under KVM on AArch64 hardware.  Each run must write the bytes of the Lean result and exit with the expected status, and its stack's high-water mark must stay within the bound of `main`.  `tests/baremetal/verified.sh` runs the cases of every module of the registry on the emulated Cortex-A57 without libc or an operating system, and it fails a call whose stack exceeds its function's static bound.

## Trusted base

[The trusted-base document](docs/trusted-base.md) lists, for each artifact code, what its theorem trusts, how the project checks each item, and where each item is stated, and it gathers the definitions that the statements reach.  Every theorem trusts Lean's kernel, at the release candidate 4.34.0-rc2, whose kernel rejects a reproduction of a defect that earlier kernels accepted, and the core definitions that give a Lean program its meaning.  The WebAssembly theorems also trust Talos's execution semantics and the binary decoder, and a file without a file theorem also trusts Lean's compiled code for its emission.  The native theorems use Talos only as an intermediate language and trust the Lean copy of CompCert 3.18's Clight, which review, differential tests, and the `clightgen` comparison of each build check, and the bare-metal theorems add the Rocq composition, the startup code, the stack-bound tool, and the machine.  The WASI theorems trust a model of the Preview 1 host, the WGSL theorems a device model with strict binary32 arithmetic, and every specification theorem its transcription of a standard or its definitions from Mathlib.

## Documentation

| Document | Contents |
|---|---|
| [Verified compiler manual](docs/verified-manual.md) | Dialect, declarations that `verified_compile` adds, bounds, tests, and examples. |
| [Verified compiler internals](Verified/README.md) | Code scheme, proof structure, and reflector. |
| [WASI manual](docs/wasi.md) | Native action and byte APIs, `verified_compile_wasi`, callable and command exports, execution proofs, host policies, and tests. |
| [WASI design](docs/verified-wasi-design.md) | Reviewed architecture, pinned sources, host assumptions, proof boundaries, acceptance work, and design decisions. |
| [Wasm-to-C translator design](docs/native-translator.md) | C subset and its Lean semantics, translation, `p.f.native`, translation without the alignment test, trusted base of the native path, and milestones. |
| [Bare-metal design](docs/native-bare-metal.md) | Generated `main`, whole-program theorem, Rocq step to Asm, startup code, inputs, stack bound, trusted base, and tests. |
| [Design document](docs/design.md) | Architecture, decisions, proof scope, tests, and open work. |
| [Trusted base](docs/trusted-base.md) | What each kind of artifact's theorem trusts, how each item is checked, and the definitions that statements reach. |
| [Development journal](devnotes.md) | Dated record of the work: decisions and their reasons, plans, runs, and measurements. |
| [Status](STATUS.md) | Commit, dates, toolchain, and steps of the last full check, with each step's status, duration, and counts, and what did not run. |
| [Algorithm library](Library/README.md) | Native algorithms, compilation modules, mathematical proofs, and imports. |
| [Application demos](Demos/README.md) | Application definitions, proofs, host programs, and tests. |
| [Algorithm index](index.md) | Algorithms, applications, example programs, their proved results, and their compiled forms. |
| [Verification knowledge base](VKB/README.md) | Lemmas, recipes, worked examples, and failures that proofs about compiled programs have needed, and the rules for admitting entries. |
| [Shared proof lemmas](LeanExe/ProofKit/README.md) | Memory and array representations, allocator invariants, alignment, floating-point error bounds, and polynomial checks. |
| [Test suites](tests/README.md) | Which checks cover a change, their prerequisites, test inputs, generated files, and execution comparisons. |
| [Repository tools](tools/README.md) | How runners, emitters, hosts, and numerical generators combine in builds and tests. |
| [Test inputs](data/README.md) | Hash-vector provenance, byte conventions, and decimal cases calculated with exact rational arithmetic. |
| [CompCert proof composition](rocq/README.md) | Clight-to-Asm theorem premises, CompCert setup, and the assumption check. |

## Layout

| Directory | Contents |
|---|---|
| [LeanExe library](LeanExe) | Dialect, runtime, correctness statements, encoding, proof lemmas, WGSL translation, WASI action API, and translator to C with its Lean copy of Clight and its proofs. |
| [Verified compiler](Verified) | Typed source language, compiler, universal proof, reflector, alignment proof, WGSL lowering, WASI compiler, native and bare-metal theorem generation, and compiled examples. |
| [Reusable algorithms](Library/README.md) | Implementations, mathematical specifications, accuracy and period proofs, and compiler proofs, grouped by algorithm family. |
| [Application demos](Demos/README.md) | Euler solvers, GPT-2, the drone planner, the order book, the slew planner, the energy authorizer, and integer and binary64 running sums, with application proofs and host programs. |
| [Example programs](Examples) | Small programs, specifications, proofs, and cases that demonstrate compiler features. |
| [Manuals and design](docs) | Verified compiler and WASI manuals, design document, trusted-base document, and WASI, translator, and bare-metal designs. |
| [Verification knowledge base](VKB/README.md) | Entries of lemmas, proof recipes, worked examples, and recorded failures for compiled programs, their template, and the declaration check. |
| [Rocq proofs](rocq/README.md) | Composition of CompCert's proofs from Clight to Asm and uniqueness lemmas, checked against a CompCert 3.18 tree. |
| [Tools](tools/README.md) | Lean runner, module and shader emitters, execution hosts, native host, bare-metal startup code and checks, build scripts, and application tools. |
| [Tests](tests/README.md) | Module, decoder, numerical, allocation, WASI, native, bare-metal, GPU, and complete-generation tests, plus the browser pages. |
| [Test inputs](data/README.md) | Hash vectors and decimal conversion cases that the tests read.  Papers, reports, and run records are in the private repository [leanexe-papers](https://github.com/jsmorph/leanexe-papers). |

## Commands

Commands run from the repository root.  They require Lean through Elan at the version in [the toolchain file](lean-toolchain), the dependencies in [the Lake manifest](lake-manifest.json), `wasm-tools` at [the pinned version](.wasm-tools-version), and a C compiler for the Wasmtime host, with Elan's tools, `wasm-tools`, and `uv`, which runs the Python tools, on the search path.  On Linux, the Lean runner requires a systemd user session with cgroup controls.  [The host setup](docs/verified-manual.md#the-wasmtime-host) also covers macOS.

The GCD example builds the verified compilation of GCD, writes the module, validates it, and runs a call, which prints `6`.  Every Lean or Lake command uses [the resource-limited runner](tools/leanrun), as [the repository instructions](AGENTS.md) require, and the test drivers call the runner themselves.  A focused build, such as `tools/leanrun --timeout 60m lake build Library.Random.Lcg.Verified`, builds that module and its imports.

```sh
tools/download-wasmtime.sh
tools/build-wasmtime-host.sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.Gcd.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.Gcd.Compiled Library.Numerics.Arithmetic.Gcd.compiled.module \
  build/verified/gcd.wasm
wasm-tools validate build/verified/gcd.wasm
build/tools/leanexe-wasmtime-host call build/verified/gcd.wasm gcd i64 i64:48 i64:18
```

The default build covers `LeanExe`, `Examples`, and `Demos`.  The `Verified` aggregate also imports `Demos.Verified`, which compiles the applications with `verified_compile`.  The complete `Library` build includes the numerical proofs and can take several hours.

```sh
tools/leanrun --timeout 60m lake build
tools/leanrun --timeout 60m lake build Verified
```

[The full check](docs/verified-manual.md#the-full-check), `tools/full-check`, builds every library with the test executables, runs the module, native, WASI, bare-metal, GPU, knowledge-base, Rocq, and Talos checks, and writes [the status record](STATUS.md).  On a machine with about 12 GiB of memory, a cold proof cache first needs [one-worker builds of the memory-heavy numerical proofs](docs/verified-manual.md#memory-heavy-numerical-proofs), with a 10 GiB memory high limit and a 12 GiB maximum.  The manual gives the full check's resource settings.

[The verified driver](tests/verified/run.sh) writes modules to `build/verified/` and compares them with native Lean on [the shared case corpus](Verified/Examples/Cases.lean), then checks numerical file theorems and accuracy tests.  [The binary64 GPT driver](tests/gpt/run.sh), the other scripts of `tests/gpt/`, [the drone driver](tests/drone/run.sh), [the order-book sessions](tests/modules/chunks.py), [the SplitMix64 comparison](tests/prng/compare.py), and [the GPT-2 text generator](tools/gpt2.py) run the verified modules in `build/verified/` unless given the path of another module.  `tests/wasi/run.sh` checks the WASI proofs, reflected modules, byte ownership, and native and WebAssembly I/O, and its `--foundations-only` form runs the proof and semantic foundations without the external-engine tests.  [The WASI development journal](devnotes.md#2026-10-23-implementing-the-wasi-agenda) records proof, execution, and integration runs.

The native drivers need CompCert 3.18's `ccomp` and `clightgen`, built from one source tree for the target, which the variables `CCOMP` and `CLIGHTGEN` name when they are not on the search path.  The bare-metal drivers also need `qemu-system-aarch64`.  Each script's header states its checks, its options, and the other tools that it needs.

```sh
tests/native/verified.sh              # the registry's modules in C, against Wasmtime
tests/native/verified.sh --aligned    # modules without the alignment test
tests/native/aligned.sh               # the refusal of modules without aligned theorems
tests/native/bench.sh --placements    # native and Wasmtime times at sixteen placements
tests/baremetal/programs.sh           # the programs with a generated main
tests/baremetal/inputs.sh             # SHA-256 of messages that QEMU's loader places
tests/baremetal/verified.sh           # the registry's cases on bare-metal AArch64
ACCEL=kvm tests/baremetal/programs.sh # the same programs under KVM
```

`uv run tests/web/serve.py` serves, on http://127.0.0.1:8000/, a page that runs the WGSL kernel tests on a browser's WebGPU and a page that runs GPT-2 with its kernels on WebGPU, in WebAssembly, or on both and compares the scores.  The GPT-2 page needs the binary32 weights that `uv run tests/gpt32/generate.py --export` writes.  [The browser test guide](tests/web/README.md) covers setup and proof scope.

## References

- Richard A. Kelsey, [Pre-Scheme: A Scheme Dialect for Systems Programming](https://dustycloud.org/misc/prescheme.pdf)
- Jonathan Protzenko et al., [Verified Low-Level Programming Embedded in F\*](https://arxiv.org/abs/1703.00053)
- Matt Kaufmann and J Strother Moore, [An Industrial Strength Theorem Prover for a Logic Based on Common Lisp](https://doi.org/10.1109/32.588534)
- Sandrine Blazy and Xavier Leroy, [Mechanized Semantics for the Clight Subset of the C Language](https://xavierleroy.org/publi/Clight.pdf)
- Ramana Kumar, Magnus O. Myreen, Michael Norrish, and Scott Owens, [CakeML: A Verified Implementation of ML](https://cakeml.org/popl14.pdf)
- [TinyGo](https://tinygo.org/)
- Donald E. Knuth, [The Art of Computer Programming](https://cs.stanford.edu/~knuth/taocp.html)
- David Goldberg, [What Every Computer Scientist Should Know About Floating-Point Arithmetic](https://dl.acm.org/doi/10.1145/103162.103163)
- [IEEE 754-2019, IEEE Standard for Floating-Point Arithmetic](https://doi.org/10.1109/IEEESTD.2019.8766229)
- [WebAssembly Core Specification](https://webassembly.github.io/spec/core/)
- [WebGPU](https://www.w3.org/TR/webgpu/) and [WebGPU Shading Language](https://www.w3.org/TR/WGSL/)
- [Lean](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4)
- [Talos](https://github.com/cajal-technologies/talos)
- [CompCert](https://compcert.org/compcert-C.html)
