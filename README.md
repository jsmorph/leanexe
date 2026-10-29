# LeanExe

LeanExe compiles functions written in a restricted dialect of Lean to WebAssembly, C, and WGSL, and proves in Lean that the compiled code computes those functions.  Two compilers produce WebAssembly: the LeanExe compiler builds a proof for each program from proved rules, and the verified compiler has one correctness theorem for every typed source program that it accepts.  The verified compiler's modules also translate to a subset of CompCert's C, with a theorem about each C function, and CompCert compiles the C for x86-64 and AArch64, under an operating system or on bare-metal AArch64.  Array builds compile to WGSL compute kernels with theorems about a modeled GPU dispatch, and Lean actions with stdin, stdout, stderr, and exit compile to WASI Preview 1 modules.

## Capabilities

The proofs of both compilers concern execution in Talos, a WebAssembly interpreter written in Lean.  A bytes theorem states that a module's encoding decodes to a module whose exports compute the Lean functions, in the `Implements` family of statements, which describe return values, result ownership, and preservation of the caller's heap.  Specification theorems carry further properties to the bytes: accuracy bounds of the elementary and special functions, equality with transcriptions of FIPS 180-4, FIPS 198-1, FIPS 202, ITU-T V.42, RFC 3720, the SipHash paper, and the xxHash specification for the hash functions, generator periods, and the safety and optimality of two planners.  File theorems state, through the trusted elaborator `binary_file%`, that an emitted file holds a module's encoding.  The verified compiler also generates an allocation bound for each function and a theorem that the function returns without a trap when the heap has room for the bound and guarded recursion stays below depth 1,000.

`verified_compile` translates each module that lies in a checked subset of WebAssembly to a program of CompCert's Clight and proves `p.f.native` for each function: from a C state that corresponds to a store meeting the premises of `p.f.implements`, the C function terminates with words that represent the Lean result or, when the function may abort, with a trap code.  The native build prints the C text, has CompCert's `clightgen` read it back, compares that Clight with the translation, and compiles the file with `ccomp` only when the two agree.  With `set_option verified_compile.alignedNative true`, which six modules set, the command also proves `p.f.nativeAligned` about a translation whose 64-bit loads and stores omit the alignment test.  The command `bare_program` proves that a whole bare-metal AArch64 program, the translation followed by a generated `main`, terminates in the Lean copy of CompCert's Clight semantics with one UART store per byte of the result, and a Rocq proof carries such a termination to the behavior of the Asm program that CompCert produces.

`verified_compile_wasi` compiles Lean actions to WebAssembly with three WASI Preview 1 imports, and its theorems relate each export's execution to the action's ordered effects, results, and terminal outcomes.  Both compilers translate array builds to WGSL kernels, whose theorems state the dispatch result and race freedom in a device model with strict binary32 arithmetic.  [The algorithm index](index.md) gives the forms and checks of every library algorithm, application, and compiler example.

| Capability | Theorems and checks | Programs |
|---|---|---|
| WebAssembly from the LeanExe compiler | A proof of `Implements` for each function and a bytes theorem for the decoded module | [Euler solvers](Demos/Euler/README.md), [binary64 GPT-2](Demos/Gpt/README.md), [drone planner](Demos/Drone/README.md), [order book](Demos/Clob/README.md), [GCD](Library/Numerics/Arithmetic/Gcd/README.md), [prime-factor count](Library/Numerics/Arithmetic/PrimeFactors/README.md), [sum of squares](Library/Numerics/Statistics/SumSquares/README.md), [mean](Library/Numerics/Statistics/Mean/README.md), [SplitMix64](Library/Random/SplitMix64/README.md), and [the compiler examples](Examples) |
| WebAssembly from the verified compiler | Generated `p.f.implements`, allocation bounds, `p.f.trapFree`, and `p.bytes`, from the universal theorem | The `Compiled` and `Verified` modules of [the library](Library/README.md) and [the demos](Demos/README.md), among them [the slew planner](Demos/Slew/README.md), and [the compiler fixtures](Verified/Examples), most of which [the module registry](tests/verified/modules.txt) lists |
| Specification theorems about module bytes | Accuracy, standards, periods, and application properties | [Elementary and special functions](index.md#6-elementary-and-special-functions), [decimal conversion](index.md#9-conversion-between-decimal-strings-and-binary-floating-point), [hash functions](index.md#11-hash-functions), [regular expressions](index.md#12-regular-expressions), [generators](index.md#3-pseudorandom-number-generators), and [the applications](index.md#14-applications) |
| File theorems | `binary_file%` reads the emitted file, and the kernel compares it with the encoding | The 32 modules of [the file-theorem registry](tests/verified/numerics.txt) and [binary64 GPT-2's module](Demos/Gpt/File.lean) |
| Allocation bounds and total execution | `p.f.bound` and `p.f.trapFree`, and the LeanExe compiler's `ImplementsA false` with memory budgets | [Euler in 1,407 pages](Demos/Euler/Total.lean), [drone in 70 pages](Demos/Drone/Total.lean), [increment in 16 pages](Examples/Increment/Verify.lean), [drone in 2,251,064 bytes](Demos/Drone/Verified.lean), [slew in 68,020,488 bytes](Demos/Slew/Bound.lean), [regular expressions](Library/Regex/README.md), and [xorshift jump-ahead in 36,920 bytes](Library/Random/Xorshift/Verified.lean) |
| WASI Preview 1 | Callable `.implements`, command `.start`, conditional `.total`, and process theorems | [Running sum](Demos/RunningSum/README.md), [floating-point running sum](Demos/RunningSumFp/README.md), [the stdio example](Verified/Examples/WasiStdio.lean), and [the reflection cases](Verified/Wasi/ReflectCommandCases.lean) |
| Native code through C and CompCert, for AArch64 and x86-64 | `p.f.native`, the `clightgen` comparison of each build, and the corpus cases compared with Wasmtime | The `verified_compile` modules of [the module registry](tests/verified/modules.txt), [packed byte values](Verified/Examples/Bytes.lean), and [byte literals](Verified/Examples/Literals.lean) |
| Native code without the alignment test | `p.f.nativeAligned`, and `native-verified build --aligned` refuses a module without it | [SHA-256](Library/Hashing/Sha256/Compiled.lean), [SHA-3](Library/Hashing/Sha3/Compiled.lean), [CRC](Library/Hashing/Crc/Compiled.lean), [insertion sort](Library/Sorting/Insertion/Compiled.lean), [Euler solvers](Demos/Euler/Verified.lean), and [binary32 GPT-2](Demos/Gpt32/Verified.lean) |
| Bare-metal AArch64 under QEMU | Whole-program theorems `p.f.program` and `sha256_input`, and the Rocq step to Asm | [GCD](tests/TestSupport/Bare/Gcd.lean), [CRC-32, SHA-256, Euler, and a deep recursion](tests/TestSupport/Bare/Theorems.lean), [SHA-256 of a loaded message](tests/TestSupport/Bare/Input.lean), and the corpus cases of [the bare-metal driver](tests/baremetal/verified.sh) |
| WGSL compute kernels | Dispatch results and race freedom in the device model, and a host theorem for a GPT-2 step | [The binary32 example](Examples/Binary32/README.md), [binary32 GPT-2](Demos/Gpt32/README.md), and [the verified kernel examples](Verified/Examples/Wgsl.lean) |

The verified compiler's dialect covers words, Booleans, floats of both widths, tuples, structures, enumerations, sums, arrays, records with array fields, packed bytes, lists, and recursive types, and each row below links fixtures that compile them.  [The verified compiler manual](docs/verified-manual.md#the-dialect) states the representations, ownership rules, and restrictions.  Integers are `UInt64`, so a program and its module compute the same values, wraparound included.

| Types and forms | Examples |
|---|---|
| Words, Booleans, and their operations | [`Poly`](Verified/Examples/Poly.lean), [`Mix`](Verified/Examples/Mix.lean), and [`Select`](Verified/Examples/Select.lean) |
| Binary64 and binary32 floats | [`Floats`](Verified/Examples/Floats.lean) and [`Floats32`](Verified/Examples/Floats32.lean) |
| Tuples, structures, enumerations, and sums with scalar fields | [`Pairs`](Verified/Examples/Pairs.lean), [`Records`](Verified/Examples/Records.lean), [`Enums`](Verified/Examples/Enums.lean), and [`Sums`](Verified/Examples/Sums.lean) |
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

## The two compilers

### The LeanExe compiler

`leanexe_compile p := [f, …]` translates Lean definitions to an intermediate language and records proof hints.  `compile` produces a module, and `encode` produces its bytes.  A proof for each function combines shared compiler rules with facts about the program to establish `Implements`.  [The LTG knowledge base](ltg/README.md) describes those rules and their use.

[The LeanExe compiler manual](docs/leanexe-manual.md) defines the accepted dialect and the proof procedure.  [The verified-executable skill](.claude/skills/verified-executable/SKILL.md) uses this compiler to turn an English request into a specification, a program, and a theorem about its bytes.  The compiler is untrusted, since a wrong translation makes a proof fail and cannot produce a false theorem.

### The verified compiler

`Verified.compileWith` translates a typed source program to a module.  The universal theorem `Prog.correctStaticWith` proves that the module computes the source meaning, `denote`, under its heap and static-data premises.  `verified_compile p := [f, …]` reflects Lean definitions into that source language and proves their correspondence.  It derives `p.f.implements` from those equations and the universal theorem, and Lean's kernel checks the generated proofs.

The command generates allocation bounds and conditional trap-free theorems.  Eligible scalar functions also receive store-preservation theorems for composition.  [The verified compiler manual](docs/verified-manual.md) states the type restrictions, ownership rules, generated declarations, and proof premises, and [the internals guide](Verified/README.md) describes the compiler and its universal proof.

### WASI programs

`verified_compile_wasi` compiles `LeanExe.Wasi.Action` definitions with stdin reads, stdout and stderr writes, bounded effectful loops, and exit.  Actions use Lean `do` notation and `UInt64` counts, lengths, and statuses.  Callable-entry and `_start` theorems relate exported execution to the native actions, preserving ordered effects and effects committed before an error or trap.  Total execution requires a typed resource-prefix bound and assumptions about reached host operations.  [The WASI manual](docs/wasi.md) defines the API, export forms, proof premises, native interpreter, and Wasmtime's exit-acceptance policy.

`LeanExe.Wasi.Process` composes bounded actions through an unbounded outer loop.  [The running-sum application](Demos/RunningSum/README.md) reads decimal integers through EOF, prints each cumulative total, and handles short writes, and [its compiled theorem](Demos/RunningSum/Correct.lean) proves canonical output and eventual accepted exit under limits on the bytes of each line and the digits of each total.  [The floating-point version](Demos/RunningSumFp/README.md) parses binary64 values and prints each sequential binary64 total, and its proofs compose the parser and printer theorems with IEEE 754 addition and the process proof.  Each application proves the allocation charges of each step from limits on its input, and corollaries cover lines of up to 9,000,000 bytes and totals of up to 9,000,000 digits for the integer sum and lines of up to 50,000,000 bytes for the floating-point sum.

### Comparison

| Topic | LeanExe compiler | Verified compiler |
|---|---|---|
| Correctness proof | A theorem per program, from rule lemmas and hints | A universal typed-source compiler theorem, combined with generated source-correspondence proofs |
| Pure compilation command | `leanexe_compile p := [f, …]` | `verified_compile p := [f, …]` |
| WASI Preview 1 I/O | Application hosts perform I/O around compiled calls. | `verified_compile_wasi` compiles stdin reads, stdout and stderr writes, and exit, with native source-to-export refinement proofs. |
| Native code | No translation to C.  Whether this compiler emits the translation and native theorems is an open decision of [the translator's design](docs/native-translator.md#risks-open-decisions-and-effort). | `p.f.native` for each function of a module that translates to C, `p.f.nativeAligned` under `verified_compile.alignedNative`, and bare-metal whole-program theorems through `bare_program` |
| Total execution | `ImplementsA false` with a proved memory budget | Pure `p.f.trapFree` under generated allocation and depth conditions.  WASI `.total` under typed resource-prefix and reached-host conditions.  Processes require application progress proofs and allocation charges for begin and each step, with room for the copies of the state. |
| `Float32` and WGSL kernels | Binary32 arithmetic and proved WGSL kernels | Binary32 arithmetic and a proved WGSL path for supported word, Boolean, and binary32 array builds |
| Lists and recursive types | `List UInt64` and user recursive types | Lists of words and fixed-layout recursive types whose records hold words, Booleans, floats of both widths, flat structures, enumerations, sums, arrays, and byte buffers, with matching, guarded recursion, tail loops, copying, release, and header reuse |
| Sum types | Sums whose fields are words, floats, or enumerations | Enumerations, sums with scalar fields, and sums whose fields hold byte buffers, arrays, or recursive types |
| Tail recursion | Compiled as a loop | Recognized tail recursion compiles as a loop.  Other recursion uses a depth limit of 1,000. |
| Folds | `Array.foldl` over `Array UInt64` and `Array Float` with a `UInt64` or `Float` accumulator, and `List.foldl` over `List UInt64` with a `UInt64` or `Float` accumulator | Whole-array `Array.foldl` over every accepted element type, with an accumulator of any dialect type.  `List.foldl` over `List UInt64` with a scalar accumulator and borrowed captures. |
| Array updates | `set!`, `setIfInBounds`, `insertIdx!`, `eraseIdxIfInBounds`, and `push` on `Array UInt64`, and `++` with an owned left operand | `set!`, `setIfInBounds`, `push`, `++`, `insertIdx!`, `insertIdxIfInBounds`, `eraseIdxIfInBounds`, `LeanExe.insertAt`, and `LeanExe.eraseAt` on arrays of every accepted element type |
| `@[inline]` helpers | Unfolded at their use | Unfolded at their use.  A listed helper compiles as a function. |
| Records with array fields | Arrays passed as separate parameters | Borrowed parameters, results, local values, and loop states |
| Constant arrays | Word-array literals allocate when evaluated. | Closed word arrays use data segments and wrapper arguments. |
| Loops, builds, and calls in loop bodies and branches | Subject to placement rules | Any expression of the dialect |
| Composition across modules | `ImplementsPure` for functions that keep the store | Typed program reuse and call relocation, transported meaning proofs, and generated scalar store-preservation proofs |

Both compilers compile the [Euler solvers](Demos/Euler/README.md), [binary64 GPT-2](Demos/Gpt/README.md), [binary32 GPT-2](Demos/Gpt32/README.md), [drone planner](Demos/Drone/README.md), and [order book](Demos/Clob/README.md).  The LeanExe compiler's binary32 GPT-2 module has no WebAssembly theorem, and its proofs concern the WGSL kernels and the host program.  The numerical libraries add proofs of accuracy, exceptional values, exact fused multiply-add, correctly rounded parsing, shortest-decimal printing, and generator periods.

## Native code

### The translation to C

The translator, `LeanExe.Native.translate`, accepts the modules that pass a decidable check of its subset of WebAssembly.  It writes one C function for each WebAssembly function that it translates and holds the linear memory in a static array, whose size `verified_compile` sets to `nativeCap`, 4,096 pages or 256 MiB.  Its simulation theorem, `translate_correct`, carries every Talos run that ends in a return or a trap to a terminating execution in the Lean copy of CompCert 3.18's Clight, and `p.f.native` follows from it and `p.f.implements` for each function.  The statement of `p.f.native` is `NativeImpl` for a function, `NativeTablesImpl` for a wrapper, and `NativeStaticImpl` for a program with byte literals.  The `clightgen` comparison of each build covers the printer and the written file, so neither needs a theorem.  [The translator's design](docs/native-translator.md) gives the subset, the translation scheme, the proof layers, and the trusted base.

Every module of [the module registry](tests/verified/modules.txt) lies inside the subset.  `tests/native/verified.sh` translates each module, compiles it with CompCert and the C host `tools/native-host.c`, and compares every case that the translation can run with the line that the Wasmtime host gives, with the same rules for traps and allocation counters.  `tests/native/run.sh` compares translated programs with Talos's runs, `tests/native/bytes.sh` runs the byte and literal examples, and `tests/native/clight.sh` compares the Lean copy of Clight with `ccomp -interp` on random programs under the NaN parameters of either target.  [The development journal](devnotes.md#2026-10-29-the-wasm-to-c-translator-the-bound-in-a-temporary) records the corpus runs.

### The translation without the alignment test

The translation option `alignedAccess` makes every 64-bit load and store read or write one word of `lx_mem` after the bounds check, without the test of the address's low three bits and the eight byte accesses of an unaligned address.  With `set_option verified_compile.alignedNative true`, `verified_compile` also emits that translation, `p.translationAligned`, and the theorem `p.f.nativeAligned`, whose statement `NativeAlignedImpl` or `NativeTablesAlignedImpl` adds the premise `AlignedInput` and concludes an aligned final heap, a result whose blocks meet `AlignedOutput`, and the cap and region conclusions of `ImplementsA`.  The six modules that set the option are [SHA-256](Library/Hashing/Sha256/Compiled.lean), [SHA-3](Library/Hashing/Sha3/Compiled.lean), [CRC](Library/Hashing/Crc/Compiled.lean), [insertion sort](Library/Sorting/Insertion/Compiled.lean), [the Euler solvers](Demos/Euler/Verified.lean), and [binary32 GPT-2](Demos/Gpt32/Verified.lean).  `native-verified build --aligned` compiles a module only when its theorems cover that translation, and otherwise it names each missing theorem and exits with status 4, which `tests/native/aligned.sh` tests.  A program with byte literals has no aligned theorems.

`tests/native/bench.sh` times seven workloads of the corpus in their native form and in Wasmtime.  CompCert aligns a function to 4 bytes on AArch64, so `--placements` also links each native program at sixteen code offsets and reports the mean over them.  [The placement benchmark](devnotes.md#2026-10-29-the-placement-benchmark-with-and-without-the-alignment-test) of 2026-10-29 ran on AArch64 only, with CompCert built from the 3.18 sources and Wasmtime's C API 44.0.0, and gave these mean times per call:

| Workload | Module | With the test (ms) | Without the test (ms) | Change |
|---|---|---:|---:|---:|
| `sort` | Insertion sort | 23.732 | 18.583 | -21.7% |
| `linear32` | Binary32 GPT-2 | 2.294 | 1.777 | -22.5% |
| `layernorm32` | Binary32 GPT-2 | 3.567 | 2.867 | -19.6% |
| `euler` | Euler solvers | 179.073 | 176.153 | -1.6% |
| `crc32` | CRC | 3.819 | 3.764 | -1.4% |
| `sha256` | SHA-256 | 12.891 | 12.791 | -0.8% |
| `sha3` | SHA-3 | 9.878 | 9.845 | -0.3% |

`sort`, `linear32`, and `layernorm32` run 20 to 23 percent faster without the test, and the other four workloads change by less than 2 percent.  The translation with the test stays the default, because the whole-program theorems and the bare-metal path exist only for it.  [An earlier run](devnotes.md#2026-10-29-the-wasm-to-c-translator-the-benchmark-of-the-bound-in-a-temporary) of the translation with the test measured Wasmtime's median time per call as 0.28 times the native median for `sort`, 0.71 for `crc32`, 0.78 for `euler`, 0.86 for `sha256`, 1.11 for `sha3`, 1.18 for `linear32`, and 1.38 for `layernorm32`.

### Bare-metal programs

A bare-metal program is the translation of a module, a volatile global `lx_out` at the UART's data register of QEMU's `virt` machine, and a generated `main` that calls `lx_init`, calls one entry on arguments fixed when the program is built, and writes the bytes of the result to `lx_out`.  `bare_program p.f x [args] r` proves `p.f.program`: the whole program terminates with result 0 and a trace of one volatile store per byte of the result's encoding or, when the entry may abort, with result 1 and an empty trace.  The Rocq theorem `clight2_bigstep_to_asm` in [the Rocq composition](rocq/Clight2Asm.v) composes CompCert's forward simulations from Clight to Asm, and `clight2_bigstep_asm_unique` shows that, for a trace without inputs, such a termination is the only behavior of the Asm program.  The startup code in `tools/baremetal/` turns on the MMU and the caches.  The build fails when the static stack bound of `main` exceeds the stack or when the assembly contains an instruction that requires an aligned access.  [The bare-metal design](docs/native-bare-metal.md) gives the statement, the startup code, the input path, the stack bound, and the trusted base.

| Program | Entry and arguments | Theorem |
|---|---|---|
| GCD | `gcd 1071 462` of test support, whose tail recursion compiles as a loop | [The GCD program](tests/TestSupport/Bare/Gcd.lean) |
| CRC-32 | `crcCheck` of the ASCII digits 1 to 9, from the library's `crcWith` and table | [The program theorems](tests/TestSupport/Bare/Theorems.lean) |
| SHA-256 of a constant | `shaCheck` of `abc`, from the library's `sha256With` and round constants | [The program theorems](tests/TestSupport/Bare/Theorems.lean) |
| Euler solver | `solve 16` of the verified Euler module | [The program theorems](tests/TestSupport/Bare/Theorems.lean) |
| Deep recursion | `recursive 1000` of [the fold example](Verified/Examples/Fold.lean), which reaches the depth limit | [The program theorems](tests/TestSupport/Bare/Theorems.lean) |
| SHA-256 with input | The library export `sha256` on a message of at most `2^24 - 8` bytes that QEMU's loader places at `lx_in` | `sha256_input` in [the input program](tests/TestSupport/Bare/Input.lean) |

`tests/baremetal/programs.sh` and `tests/baremetal/inputs.sh` run these programs on QEMU's `virt` machine, under TCG on an emulated Cortex-A57 by default and, with `ACCEL=kvm`, under KVM on AArch64 hardware.  Each run must write the bytes of the Lean result and exit with the expected status, and its stack's high-water mark must stay within the bound of `main`.  `tests/baremetal/verified.sh` runs the cases of every module of the registry on the emulated Cortex-A57 without libc or an operating system, and it fails a call whose stack exceeds its function's static bound.

## Trusted base

Lean's kernel checks the proofs using `propext`, `Classical.choice`, and `Quot.sound`.  The WebAssembly theorems use Talos's semantics and binary decoder.  Heap-based calls require the allocator invariant, a cap of at most 65,535 memory pages, represented arguments, and separation of consumed blocks from retained and borrowed regions.  Tables and byte literals add static-data premises.  An `implements` theorem may permit a trap at `unreachable`, and the verified compiler's `trapFree` theorem proves a return under its allocation and call-depth conditions.  The LeanExe compiler has total-execution proofs with memory budgets for the Euler solvers, drone planner, and increment example.  [The LeanExe compiler manual](docs/leanexe-manual.md#trusted-base) and [the verified compiler manual](docs/verified-manual.md#trusted-base) list the definitions that the statements reach.

WASI entry theorems additionally assume a satisfying host, valid byte and static-pool representations, and separation from the guest scratch region.  They match normal returns, accepted exits, and host traps to source executions with the same world and ordered trace, and permitted guest resource traps match source prefixes and residual actions.  [The total-process theorem](Verified/Wasi/ProcessTotalCorrect.lean) uses a well-founded progress relation, a charge that bounds the cost of each step with room for the copies of the state, and final-exit acceptance.  The modeled initial-store theorem establishes allocator and static-data invariants.  Real engine instantiation, OS streams, and the native stream adapter require conformance to the modeled behavior, which execution tests check on concrete inputs.

For native code, Talos serves as an intermediate language whose meaning only the proofs use, so Talos's fidelity to the WebAssembly specification, the encoder and decoder, and Wasmtime leave the trusted base.  The native theorems trust the Lean copy of CompCert 3.18's Clight, which review and a differential test against `ccomp -interp` check, CompCert's proofs, and CompCert's unverified parser and elaborator, which the `clightgen` comparison of each build checks.  They also trust CompCert's extraction to OCaml, its assembly printer, the assembler and linker, the run-time helpers of `libcompcert.a`, the C host glue, the stack, the toolchain, and the CPU, as [the trusted base of the native path](docs/native-translator.md#trusted-base-of-the-native-path) lists with the check of each.  The statements `NativeA`, `NativeTablesA`, and `NativeStaticA`, and for the translation without the test `NativeAlignedA` and `NativeTablesAlignedA` with `AlignedInput`, `AlignedOutput`, and `Heap.Aligned`, are definitions that the native theorems reach.  On bare metal, `main` enters the proofs, and libc, the operating system, and the C host leave the trusted base, while CompCert's Rocq proofs with Coq's kernel, the startup code, the linker script, the stack-bound tool, QEMU and KVM, the UART, and the absence of instructions that require aligned accesses enter it, as [the bare-metal trusted base](docs/native-bare-metal.md#trusted-base) lists.

Floating-point theorems use WebAssembly's deterministic profile, and the Wasmtime host enables NaN canonicalization to match it.  The translated C canonicalizes each NaN result, so the native theorems hold under the NaN choices of both CompCert targets.  WGSL theorems prove kernel results and race freedom in the shared device model, which uses strict binary32 arithmetic, while a GPU may flush subnormal values and fuse multiply-adds.  File emission evaluates module constants with Lean's compiled code, and file theorems identify the encodings of particular emitted files.  [The design document](docs/design.md#scope-of-the-theorem) states the assumptions about engines, hosts, and file emission.

## Documentation

| Document | Contents |
|---|---|
| [LeanExe compiler manual](docs/leanexe-manual.md) | Dialect, compilation, proof rules, tests, examples, and development practice. |
| [Verified compiler manual](docs/verified-manual.md) | Dialect of the verified compiler, declarations that `verified_compile` adds, bounds, tests, and examples. |
| [Verified compiler internals](Verified/README.md) | Code scheme, proof structure, and reflector. |
| [WASI manual](docs/wasi.md) | Native action and byte APIs, `verified_compile_wasi`, callable and command exports, execution proofs, host policies, and tests. |
| [WASI design](docs/verified-wasi-design.md) | Reviewed architecture, pinned sources, host assumptions, proof boundaries, acceptance work, and design decisions. |
| [Wasm-to-C translator design](docs/native-translator.md) | The C subset and its Lean semantics, the translation, `p.f.native`, the translation without the alignment test, the trusted base of the native path, and milestones. |
| [Bare-metal design](docs/native-bare-metal.md) | The generated `main`, the whole-program theorem, the Rocq step to Asm, the startup code, inputs, the stack bound, the trusted base, and tests. |
| [Design document](docs/design.md) | Architecture, decisions, proof scope, tests, and open work. |
| [Development journal](devnotes.md) | Record of the work. |
| [Algorithm library](Library/README.md) | Native algorithms, compilation modules, mathematical proofs, and imports. |
| [Application demos](Demos/README.md) | Application definitions, proofs, host programs, and tests. |
| [Algorithm index](index.md) | Algorithms, applications, compiler examples, their proved results, and their compiled forms. |

## Layout

| Directory | Contents |
|---|---|
| [Shared libraries and LeanExe compiler](LeanExe) | The dialect, original compiler and IR, runtime, correctness statements, encoding, proof lemmas, shared WGSL translation, the WASI action API, and the translator to C with its Lean copy of Clight and its proofs. |
| [Verified compiler](Verified) | The typed source language, compiler, universal proof, reflector, alignment proof, WGSL lowering, WASI compiler, native and bare-metal theorem generation, and compiled examples. |
| [Reusable algorithms](Library/README.md) | Implementations, mathematical specifications, accuracy and period proofs, and compiler proofs, grouped by algorithm family. |
| [Application demos](Demos/README.md) | Euler solvers, GPT-2, the drone planner, the order book, the slew planner, and integer and binary64 running sums, with application proofs and host programs. |
| [Compiler examples](Examples) | Small programs, specifications, proofs, and cases that demonstrate compiler features. |
| [Manuals and design](docs) | The compiler manuals, the WASI, translator, and bare-metal designs, and the design document. |
| [Proof guidance](ltg) | The LTG knowledge base and its declaration checker. |
| [Rocq proofs](rocq) | The composition of CompCert's proofs from Clight to Asm and the uniqueness lemmas, checked against a CompCert 3.18 tree. |
| [Tools](tools) | The Lean runner, module and shader emitters, execution hosts, the native host, the bare-metal startup code and checks, build scripts, and application tools. |
| [Tests](tests) | Module, decoder, numerical, allocation, WASI, native, bare-metal, GPU, and complete-generation tests, plus the browser pages. |
| [Run records](data), [reports](paper) | Measurements, reproduction records, papers, and their review history. |

## Commands

Commands run from the repository root.  They require Lean through Elan at the version in [the toolchain file](lean-toolchain), the dependencies in [the Lake manifest](lake-manifest.json), `wasm-tools` at [the pinned version](.wasm-tools-version), and a C compiler for the Wasmtime host.  Python tools use `uv`.  On Linux, the Lean runner requires a systemd user session with cgroup controls.  [The host setup](docs/leanexe-manual.md#the-wasmtime-host) also covers macOS.

The GCD example builds its program and proof, writes the module, validates it, and runs a call, which prints `6`.  Every Lean or Lake command uses [the resource-limited runner](tools/leanrun), as [the repository instructions](AGENTS.md) require.  A focused verified-compiler build, such as `tools/leanrun --timeout 60m lake build Library.Random.Lcg.Verified`, builds that example and its imports.

```sh
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
tools/download-wasmtime.sh
tools/build-wasmtime-host.sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.Gcd.Verify
mkdir -p build/gcd
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.Gcd.Module Library.Numerics.Arithmetic.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
```

The default build covers `LeanExe`, `Examples`, and `Demos`.  The `Verified` aggregate also imports `Demos.Verified`, which checks the applications with the verified compiler.  The complete `Library` build includes the numerical proofs and can take several hours.

```sh
tools/leanrun --timeout 60m lake build
tools/leanrun --timeout 60m lake build Verified
```

[The full-check procedure](docs/leanexe-manual.md#the-full-check) gives its resource settings and the execution, decoder, allocation, numerical, and GPU tests.  On an 8-CPU host with about 12 GiB of memory, the procedure stages [memory-heavy numerical proofs](docs/leanexe-manual.md#memory-heavy-numerical-proofs) individually before a two-worker aggregate, with a 10 GiB memory high limit and 12 GiB maximum.  Test drivers invoke the runner themselves.

`tests/wasi/run.sh` checks the WASI proofs, reflected modules, byte ownership, and native and WebAssembly I/O.  Its `--foundations-only` form runs the proof and semantic foundations without the external-engine tests.  [The WASI development journal](devnotes.md#2026-10-23-implementing-the-wasi-agenda) records proof, execution, and integration runs.

The [module driver](tests/modules/run.sh) compares the LeanExe modules other than `gpt`, `gpt32`, and `prng` with native Lean, using each example's `Cases.lean` through [the shared case runner](tests/modules/Cases.lean).  The [binary64 GPT driver](tests/gpt/run.sh) does the same for `gpt.wasm`.  Both read modules from `build/NAME/NAME.wasm`.  The [verified driver](tests/verified/run.sh) writes modules to `build/verified/` and compares them with native Lean on [the shared case corpus](Verified/Examples/Cases.lean), then checks numerical file theorems and accuracy tests.

The native drivers need CompCert 3.18's `ccomp` and `clightgen`, built from one source tree for the target, which the variables `CCOMP` and `CLIGHTGEN` name when they are not on the search path.  The bare-metal drivers also need `qemu-system-aarch64`.  Each script's header states its checks, its options, and the other tools that it needs.

```sh
tests/native/verified.sh              # the registry's modules in C, against Wasmtime
tests/native/verified.sh --aligned    # the six modules without the alignment test
tests/native/aligned.sh               # the refusal of modules without aligned theorems
tests/native/bench.sh --placements    # native and Wasmtime times at sixteen placements
tests/baremetal/programs.sh           # the programs with a generated main
tests/baremetal/inputs.sh             # SHA-256 of messages that QEMU's loader places
tests/baremetal/verified.sh           # the registry's cases on bare-metal AArch64
ACCEL=kvm tests/baremetal/programs.sh # the same programs under KVM
```

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/.  One runs the WGSL kernel tests on a browser's WebGPU, and the other runs GPT-2 with its kernels on WebGPU, in WebAssembly, or on both and compares them.  [The browser test guide](tests/web/README.md) covers setup and proof scope.  The GPT-2 page needs the binary32 weights that `uv run tests/gpt32/generate.py --export` writes.
