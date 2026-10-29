# LeanExe Wasm-to-C translator: design and plan

2026-10-26 · Jamie Stephens. Living copy: https://claude.ai/artifact/44U9A3qFctHseiDraeUC4E

## Goal and end-to-end theorem

The translator turns the Talos module that `verified_compile` produces into a program in a small subset of CompCert's C, with a Lean proof that the C program computes what the module computes. Composed with the existing `p.f.implements` theorems, every reflected Lean function gets a theorem about a C function, and CompCert compiles that C to x86-64 or AArch64.

The pipeline, with the status of each step:

1. Lean definition → typed source program: the reflector, with kernel-checked meaning equations (exists).
2. Typed program → Talos `Module`: the Verified compiler, `Prog.correctWith` (exists).
3. Talos `Module` → C-subset program: this translator, with a new simulation proof.
4. C-subset program → C text: a printer, unverified, checked on every build by comparing the Clight that CompCert's `clightgen` produces from it with the program Lean generated.
5. C text → machine code: CompCert, proved in Rocq.

The target theorem, `p.f.native`, mirrors `ImplementsA`. From any C state that corresponds to a Talos store and arguments meeting `ImplementsA`'s premises, the translated C function terminates and either returns words that represent `f x`, with the heap, region and cap conclusions carried over, or returns with the code of a trap in `lx_status`, which is allowed only when `aborts` holds.  For the translation without the alignment test, the theorem's statement is `NativeAlignedA`, which adds the premise that the input is aligned (`AlignedInput`) and concludes, beside the conclusions of `NativeA`, that the final heap and the blocks of the result are aligned.

What stays trusted afterwards:

- Lean's kernel, with `propext`, `Classical.choice` and `Quot.sound`.
- The Lean transcription of the C subset's semantics, checked against CompCert by testing (section 6).
- The printer and CompCert's unverified front end, checked per build with `clightgen`.
- CompCert's correctness theorem, its unverified assembler and linker, libc's `malloc`, the OS, and the C host that places arguments and calls the function.
- The CPU.

What stops being trusted: Talos's fidelity to the Wasm specification, the Wasm encoder and decoder, and Wasmtime. Talos becomes an intermediate language whose meaning only the proofs consume.

Not in scope: Wasm features outside the subset, WGSL kernels, verified I/O, and performance work beyond what CompCert does. The per-program LeanExe compiler is covered automatically for any module that passes the subset check.

## Input: the Wasm subset and the semantics to simulate

The Verified compiler emits 73 instruction forms, one memory, four i64 globals, and no imports, tables or exceptions. The translator accepts exactly the modules that pass a decidable subset check (milestone M0), so the proof never meets anything else.

**Module shape** (`compileWith` in `Verified/Compile.lean`):

- Functions: 0 is `alloc` and 1 is `release` (the runtime); the program's functions start at 2; then one entry per depth-taking function, which calls it with depth 0; then the wrappers, which push table addresses before calling their callee.
- Memory: one, `pagesMin` = max(16, pages the tables need), `pagesMax` = 65,535. The data segments write the constant tables from the heap base, 4096.
- Globals: four mutable i64 values: the bump pointer (4096 or the end of the tables), the free-list head, and the allocation and free counters.
- Exports: `alloc`, `release`, each function by name, the wrappers, the memory and the two counters.
- Locals: parameters are i64, f64 or f32; each function also has an i64, an f64 and an f32 local for every position it uses.

**Instruction forms**, from the code generators in `Verified/` (`Compile.lean` and the `Tree*` and `ListFold*` code files), `LeanExe/Runtime/` and the allocator programs in `LeanExe/ProofKit/`, at LeanExe `d1f8517` against Talos `87e3aa5`, with the byte loads and stores of `Verified/Bytes/`, which typed fields added later:

| Group | Forms | Count |
| --- | --- | --- |
| i64 arithmetic and comparison | `constI64` `addI64` `subI64` `mulI64` `divUI64` `remUI64` `andI64` `orI64` `xorI64` `shlI64` `shrUI64` `eqI64` `neI64` `ltUI64` `leUI64` `geUI64` `eqzI64` | 17 |
| i32 | `const` `eq` `eqz` `and` `wrapI64` `extendUI32` | 6 |
| Variables | `localGet` `localSet` `localTee` `globalGet` `globalSet` | 5 |
| Memory | `load64` `store64` `load8U` `store8` `memorySize` `memoryGrow` | 6 |
| Control | `block` `loop` `iff` `br` `br_if` `call` `ret` `unreachable` | 8 |
| binary64 | `f64Const` `f64Add` `f64Sub` `f64Mul` `f64Div` `f64Eq` `f64Lt` `f64Le` `f64Sqrt` `f64Abs` `f64ConvertI64U` `f64ReinterpretI64` `i64ReinterpretF64` `i64TruncSatF64U` | 14 |
| binary32 | `f32Const` `f32Add` `f32Sub` `f32Mul` `f32Div` `f32Eq` `f32Lt` `f32Le` `f32Sqrt` `f32Abs` `f32Nearest` `f32ConvertI64U` `f32ConvertI32S` `f32ReinterpretI32` `i32ReinterpretF32` `i64TruncSatF32U` `i32TruncSatF32S` | 17 |

The count comes from a text search; M0 replaces it with the decidable check. Five facts about how the forms are used shape the design:

- Branches leave more than one level: tail bodies branch to `exitLabel` and `nextLabel` through nested `iff`s, whose depth grows by one per level.
- Every `block`, `loop` and `iff` has at most one result, for example `.iff 0 1 … [.i64]`.
- Every memory access is 8 bytes wide, except the byte loads and stores of byte buffers (`Verified/Bytes/`), which typed fields added. `memory.size` and `memory.grow` appear only in the allocator's growth code.
- Division and remainder are guarded against a zero divisor by the emitted code. The translator still handles zero, because its theorem covers every module in the subset.
- f64 negation is emitted as subtraction from −0, and `Float.ofBits` as a reinterpretation followed by adding −0, which canonicalizes NaN.

**The semantics to simulate** is Talos's big-step, fuel-indexed `run` in `Semantics.lean`:

- `run fuel m id st args` takes the top `numParams` arguments, reversed, as `Locals.params`, zeroes the declared locals, runs the body with `exec`, and returns the top `results.length` values.
- `execOne` returns a `Continuation`: `Fallthrough`, `Break k`, `Return`, `Trap store msg`, `Invalid` or `OutOfFuel`. `ReturnCall` and `Throwing` never arise in the subset.
- `block`, `loop` and `iff` each consume one unit of fuel. `Break 0` leaves a block or `iff` keeping its top `resultArity` values; `Break 0` to a loop re-runs it with one less fuel; `Break (k+1)` becomes `Break k`.
- `call` runs the callee with one less fuel.
- `load64` and `store64` trap with `"out of bounds memory access"` when `a + off + 8 > pages × 65536`; otherwise they read or write 8 little-endian bytes. `load8U` and `store8` trap when `a + off + 1 > pages × 65536`; otherwise `load8U` reads one byte as an unsigned i32, and `store8` writes the low byte of its i32 value.
- `memory.grow` succeeds when `pages + delta ≤ memoryCap`, the cap recorded in the store, and returns the old page count; otherwise it returns −1. `memory.size` returns the page count as an i32.
- Float operations are Talos's IEEE 754 functions on bit patterns. Every NaN result is the positive canonical quiet NaN. `abs` acts on the bits.
- `unreachable`, and division or remainder by zero, return `Trap`.

The existing theorems need only part of this. `ImplementsA` is stated with `Runs aborts`: there is an `N` such that for every fuel ≥ `N`, `run` returns `Success` satisfying the postcondition or, when `aborts`, `Trap st "unreachable"`. So the translator's theorem has to cover runs that end in `Success` or `Trap`, and never `Invalid` or `OutOfFuel`.

## Target: the C subset and its Lean semantics

The proofs target CompCert's Clight in the form `clightgen` produces: after `SimplExpr` and `SimplLocals`, with parameters and locals as temporaries. This is the form VST verifies against, and CompCert proves both passes. The Lean copy transcribes the big-step semantics of `ClightBigstep.v`, which CompCert connects to the small-step semantics by `bigstep_semantics_sound`. The big-step semantics has no `goto`, so the translator never emits one.

**What the generated C uses** (prefix `lx_` throughout):

- Types: `unsigned int`, `int` (comparison results), `unsigned long long`, `float`, `double`, `unsigned char`, and pointers to these.
- Globals: `lx_mem`, an array of `unsigned long long` holding the linear memory, zero-initialized; `lx_pages`; `lx_g0` to `lx_g3`, the Wasm globals; `lx_r0_i`, `lx_r0_l`, `lx_r0_d`, `lx_r0_f`, `lx_r1_i`, …, the result globals of functions with several results, one `unsigned int`, one `unsigned long long`, one `double`, and one `float` per position; `lx_pun`, an array of one `unsigned long long`, the scratch cell for reinterpreting bits; `lx_status`, the code of a trap, 0 while none has occurred.
- Locals: one C local per Wasm local and per operand-stack slot, plus `brk` for multi-level branches. None has its address taken, so `SimplLocals` turns them all into temporaries.
- Expressions: integer constants, temporaries, global variables, dereferences of `lx_mem` and `lx_pun`, each cast to a pointer to the type it is read or written at, with no address-of, the binary operators at the types above, and casts between the scalar types. Float constants are printed as literals; `clightgen` exports them as bit patterns, so the per-build check (section 6) compares them exactly.
- Statements: `Sset`, `Sassign`, `Scall`, `Ssequence`, `Sifthenelse`, `Sloop`, `Sbreak`, `Scontinue`, `Sreturn`, `Sskip`.
- Built-ins: two.  `__builtin_fsqrt` stays a call in `clightgen`'s output, an `Scall` of the external function `EF_builtin "__builtin_fsqrt"`, which the program declares, and its semantics is `Float.sqrt` (`Builtins0.v`).  `__builtin_fabs` becomes the unary operator `Oabsfloat` in CompCert's front end (`cfrontend/C2C.ml`, line 974), and its semantics is `sem_absfloat` (`cfrontend/Cop.v`, line 490), which is `Float.abs` (`lib/Floats.v`, line 279), `Babs` with `abs_nan` (line 215), which keeps a NaN's payload and clears its sign.  Both definitions in the Lean copy are part of the trusted base.
- No other external function.  A trap stores its code in `lx_status` and returns, as section 4 describes.

**Transcription plan.** Each Lean definition names the CompCert 3.18 definition it copies. The copy keeps CompCert's names so a reviewer can read the two side by side, and it keeps only the cases the translator can reach:

| Lean part | CompCert 3.18 source | What is kept |
| --- | --- | --- |
| Values and integers | `common/Values.v`, `lib/Integers.v` | `val`; the `Int` and `Int64` operations used, over Lean's fixed-width integers |
| Floats | `lib/Floats.v` | `add`, `sub`, `mul`, `div`, `sqrt`, `cmp`, `of_longu`, `to_longu`, `of_int`, `to_int`, single↔double, `of_bits`, `to_bits`; the NaN result is a parameter |
| Memory values | `common/Memdata.v` | `memval` (bytes and `Undef` only), `encode_val`, `decode_val`, `size_chunk`, `align_chunk` |
| Memory | `common/Memory.v` | blocks for globals, permissions, `load`, `store`, `valid_access` with its alignment test |
| Operators | `cfrontend/Cop.v` | `sem_cast`, `sem_binary_operation` and `sem_shift` for the emitted type pairs |
| Expressions | `cfrontend/Clight.v` | `eval_expr`, `eval_lvalue`, `deref_loc`, `assign_loc`, `function_entry2` |
| Statements and calls | `cfrontend/ClightBigstep.v` | `exec_stmt`, `eval_funcall`, `outcome_result_value` |
| Initial memory | `common/Globalenvs.v` | `init_mem` for `Init_int64`, `Init_space`, `Init_int32` |
| Externals | `common/Events.v`, `common/Builtins0.v` | `EF_external` has the parameter `external_functions_sem` as its semantics, and the translator calls no such function; the built-ins `__builtin_fsqrt` and `__builtin_sqrt` are `Float.sqrt`, and `__builtin_fabs` and `__builtin_fabsf` are `Float.abs` and `Float32.abs` |

Three rules keep the copy honest:

- **Undefined stays undefined.** Where CompCert returns `None` or `Vundef`, so does the copy: a shift by the type's width or more, division or remainder by zero, a float-to-integer conversion out of range, a misaligned or out-of-bounds access, and a read of `Undef`. A stuck program has no outcome, so the theorem can never lean on it.
- **NaN is a parameter.** CompCert chooses NaN results per architecture: the default NaN is negative on x86-64 and positive on AArch64, and operand payloads may propagate. The copy leaves the choice abstract, so every theorem holds on both targets.  A result that is a number or an infinity is the result of Talos's `Wasm.IEEE64` or `Wasm.IEEE32`, the functions that the translation simulates, which LeanExe's `F64*` and `F32*` lemmas relate to Lean's `Float` and `Float32`.  Talos computes the conversions between the two formats with Lean's native floats, so the copy defines `of_single` and `to_single` from Talos's exact rounding helpers.
- **No rule, no outcome.** The AST type covers all of Clight, so the `clightgen` output always parses. Constructs outside the subset have no evaluation rule.

An executable evaluator, `LClight.run` with fuel, is proved sound against the relation. It is what the conformance tests in section 6 run. Estimated size: 2,500–4,000 lines of Lean.

## Translation scheme

The translator is a Lean function `translate : Module → Option LClight.Program`. It returns `none` when the subset check or the static stack analysis fails, and the theorem covers every `some`. Each Wasm function becomes one C function. Every value lives in a C temporary named by its position, and a trap returns from the function at once, so no operation follows it.

**Functions left out.** A module in the subset translates, but the translation leaves out three kinds of function, and `verified_compile` adds no `p.f.native` for them: a function that uses a form of a later milestone, as every float form was until M5 and M6; a function with several results that branches to its own outermost label, which returns in Talos; and a function that calls one left out.  The second restriction keeps the result globals out of the relation for branches.  Surveys of the modules of `tests/verified` at M4, M5, and M6 found no function left out for that reason alone, and since M6 every function of the corpus translates.

**Static stack analysis.** Locals and operand-stack slots become C locals named by index, height and type: `l3`, `s5_l` (i64), `s5_i` (i32), `s5_d` (f64), `s5_f` (f32). The analysis computes the type stack at every instruction, which is possible because every block type here has no parameters and at most one result. A mismatch makes `translate` return `none`. Declared Wasm locals are assigned 0 at entry, as `Function.toLocals` zeroes them; stack slots are always written before they are read.

**Functions and calls.** A function with no result returns `void`, and one with one result returns that scalar. With two or more results, it writes result `i` to the global `lx_r<i>_<t>` of its type, where `t` is `i`, `l`, `d`, or `f`, and returns `void`, and the caller copies the results into its stack slots straight after the call, before its test of `lx_status`.  The program holds the result globals of as many positions as its function with the most results, and such a function returns only by `ret` or at the end of its body, as the restrictions above require. Arguments are the top `n` slots, deepest first, which matches Talos's reversal of the top `numParams` values. The call-depth parameter is an ordinary `unsigned long long`.  A function is `lxf_<name>` when the module exports it under a name that is a C identifier, and `lxf_<index>` otherwise: a bare export name can be a C keyword, as `double` is, or collide with a library function or with the `lx_` globals.  A call whose result is stored has the form that `clightgen` produces from `x = f(args);`, a call into a temporary of its own, one per call site, followed by a copy to the slot.

**Traps.** A trap stores its code in `lx_status`, one of unreachable, out of bounds, and divide by zero, and returns from the function at once, with `return;` in a function without a result and `return 0;` at the result's type otherwise.  After a call to a function that can trap, directly or through its own calls, the caller tests `if (lx_status != 0) return …;` before it copies the results, so a trap leaves every C frame up to the exported function without running more of its code.  The first translator tests after every call, at the cost of one load and one branch; a static pass over the call graph could omit the test after a call to a function that cannot trap.  The host reads `lx_status` after the exported function returns: 0 means that the call returned its results, and any other value names the trap.  No external function is called, so no assumption that one never returns enters the proof.

**Control flow.** Every `block`, `loop` and `iff`, and the function body itself, becomes a loop the body leaves with `break`:

- `block`: `for (;;) { body; break; }`
- `loop`: the same shape, where a branch to the loop is `continue`
- `iff`: `for (;;) { if (cond != 0) { then } else { else } break; }`

A branch first copies the target's kept values (at most one) into the target's result slot, then:

- to depth 0, it is `break` for a block or `iff`, and `continue` for a loop;
- to depth `k` ≥ 1, it is `brk = k; break;`.

After every construct the translator emits a dispatch, which does nothing unless a branch left the construct by more than one level: `if (brk != 0) { brk = brk - 1; if (brk == 0) <break or continue, for the parent> else break; }`. `br_if` wraps the same code in `if (cond != 0)`. `ret` copies the results and returns. This needs no `goto`, so it stays inside the big-step semantics.

**Memory.** `lx_mem` holds `LX_CAP` pages and `lx_pages` is the current page count.  `LX_CAP` is the argument `cap` of `translate`, which refuses a module whose initial pages exceed it and a cap above 65,535 pages, the most that the compiled modules declare.  `verified_compile` uses `nativeCap`, 4,096 pages or 256 MiB, for every module: a larger static `lx_mem` approaches the 2 GiB limit on static data under the small code model, and every translated case of the corpus fits, as does the slew planner's bound of 68,020,488 bytes.  A module that needs more memory needs a cap of its own, which is future work.  Each function keeps the memory's size in bytes in the temporary `lim`, `lim = (unsigned long long) lx_pages * 65536ULL;`, which it sets at entry, after each call of a function of the module that returns without a trap, and after each `memory.grow` that succeeds, the only statements after which `lx_pages` can differ.  A `load64` with offset `off` computes its address in the `i64` slot at the height of its address, here `s4`, and compares it with `lim`:

```c
s4_l = (unsigned long long) s4_i + 16ULL;           /* off = 16; 64-bit sum, no wrap */
if (s4_l + 8ULL > lim) { lx_status = 2U; return 0ULL; }
if ((s4_l & 7ULL) == 0ULL) s4_l = lx_mem[s4_l >> 3ULL];   /* aligned: one 8-byte load */
else s4_l = (unsigned long long) ((unsigned char *) lx_mem)[s4_l]
          | (unsigned long long) ((unsigned char *) lx_mem)[s4_l + 1ULL] << 8ULL
          | ...                                     /* eight byte loads, little-endian */
```

`store64` mirrors it, with eight byte stores of `(unsigned char) (v >> 8 k)` on the unaligned path.  `load8U` and `store8` compute the address and test the bound in the same way for one byte, and then access one `unsigned char` of `lx_mem`: `s4_i = (unsigned int) ((unsigned char *) lx_mem)[s4_l]`, and `((unsigned char *) lx_mem)[s4_l] = (unsigned char) s5_i`, whose conversion to `unsigned char` reduces the value modulo 256, which is `store8`'s meaning.  The byte-wise expressions are emitted inline rather than as helper functions, which would add calls and their `lx_status` tests; the proof covers them once, for every address.  `memory.size` reads `lx_pages`.  `memory.grow` adds in 64-bit arithmetic, succeeds when the sum is at most `LX_CAP`, and otherwise yields `0xFFFFFFFF`, exactly Talos's rule with the store's cap set to `LX_CAP`.  Bytes past `lx_pages` hold the same values in both semantics, because every write is bounds-checked and neither semantics changes a byte on growth.

**Initialization.** `lx_g0` to `lx_g3` and `lx_pages` have static initializers.  `lx_init()` writes the data segments into `lx_mem` with straight-line stores: a word store for each 8-byte-aligned word that a segment covers, and a byte store for each other byte.  A static initializer on `lx_mem` itself would put the whole array into the binary, and a copy loop from a constant table would need a loop invariant in the proof; the stores' text grows with the data, as a table would.  The host calls `lx_init()` once before anything else.

**Numeric operations.** Integer operations map one-to-one, with the guards CompCert's semantics needs:

| Wasm form | C shape | Why |
| --- | --- | --- |
| `shlI64`, `shrUI64` | `a << (b & 63)`, `a >> (b & 63)` | Wasm masks the amount; CompCert leaves a shift by 64 or more undefined |
| `divUI64`, `remUI64` | `if (b == 0) { lx_status = LX_DIV0; return 0; }`, then `a / b` | Talos traps; C leaves it undefined |
| comparisons, `eqz` | `(unsigned int)(a < b)` | C comparisons yield `int` |
| `wrapI64`, `extendUI32` | casts between `unsigned int` and `unsigned long long` | |
| f64 and f32 `add`, `sub`, `mul`, `div`, `sqrt` | the C operator or `__builtin_fsqrt`, then `if (t != t) t = canonical NaN`, the NaN stored as an integer in `lx_pun` and loaded as a double or a float | CompCert's NaN choice differs by architecture; Talos always gives the positive canonical NaN |
| `eq`, `lt`, `le` on floats | C comparisons | IEEE 754 comparisons on both sides |
| `abs` | for a double, `__builtin_fabs`, the operator `Oabsfloat`; for a float, its bits through `lx_pun` with the mask `0x7FFFFFFF` | `Float.abs` keeps the payload and clears the sign, as Talos's `abs` does; CompCert's absolute value of a float goes through `double`, which quiets a signaling NaN |
| reinterpretations, NaN and infinite constants | through `lx_pun`: store as one type, load as the other | exact on the bits; `encode_val` and `decode_val` define it for numeric chunks |
| finite constants | an exact hexadecimal literal, negated for a negative constant | `clightgen` reads a negative literal as `Oneg` of the positive one, which is exact |
| `f64ConvertI64U`, `f32ConvertI64U`, `f32ConvertI32S` | C casts | CompCert's `of_longu` and `of_int` round correctly |
| `trunc_sat` (three forms) | NaN → 0, below the range → the minimum, at or above 2^64 or 2^31 → the maximum, else the C cast | the bare cast is undefined out of range |
| `f32Sqrt` | `(float) __builtin_fsqrt((double) a)` | correct because binary64 has at least 2 × 24 + 2 bits; `double_round` proves it on Talos's integer definitions |
| `f32Nearest` | integer code on the bit pattern: exponent test, then round half to even on the significand | CompCert has no builtin; integer reasoning avoids a floating-point proof |

The result is ordinary C99 that `ccomp` compiles with one option, `-fno-common`, which makes `lx_mem` and `lx_pun` definitions rather than common symbols so that `ccomp` addresses them without the global offset table. It is also what `clightgen` reads for the per-build check.

## Correctness theorem and proof architecture

One simulation theorem, `translate_correct`, carries every Talos `run` that ends in `Success` or `Trap` to a terminating C execution with matching results. It is proved by induction on Talos's fuel. `p.f.native` then follows from `p.f.implements` in a few lines per function.

**The relation.** `Match σ (st, s) (le, m)` relates a Talos store and frame to a C temporary environment and memory at a point whose static type stack is `σ`:

- Locals: each `l_i` holds `s.get i`, as `Vint`, `Vlong`, `Vsingle` or `Vfloat` of the same bits.
- Stack: `s.values` has length `|σ|`, and slot `k` holds the value at depth `|σ| − 1 − k`.
- Globals: the blocks of `lx_g0` to `lx_g3` hold the encoding of `st.globals`.
- Memory: every byte of `lx_mem` below `LX_CAP × 65536` equals `st.mem.bytes` at that address and can be written; `lx_pages = st.mem.pages ≤ LX_CAP`; and the store's first memory cap, `st.memoryCaps[0]`, is `LX_CAP`.
- `brk` and `lx_status` are 0, and `lim` holds `st.mem.pages × 65536`. The result globals can be written. `lx_pun`, the values of the result globals, and slots above the stack are unconstrained.

**Outcomes.** Each Talos continuation corresponds to one C outcome:

| Talos | C |
| --- | --- |
| `Fallthrough st' s'` | normal completion, with `Match` at the next point |
| `Break k st' s'` | `break` or `continue` with `brk` set as section 4 encodes it, and the kept value already in the target's result slot |
| `Return st' vs` | `return`, with the result or with the result globals holding `vs.take results.length` |
| `Trap st' msg` | `return` from every frame up to the exported function, with `lx_status` holding the code for `msg` (unreachable, out of bounds, or divide by zero) and the globals and memory matching `st'` |

**Proof layers**, bottom up, with rough sizes:

1. **Lean Clight lemmas** (1,000–2,000 lines): load after store; punning round trips for the four scalar types; agreement of little-endian `decode_val` with Talos's `Mem.read64` and `write64`; evaluation of each expression shape the translator emits; determinism of the big-step relation.
2. **Instruction lemmas** (3,000–5,000 lines): one per form. If `execOne` gives `Fallthrough` or `Trap` from a matched state, the instruction's C statement completes normally with `Match`, or returns with the right code in `lx_status`. Most are 20–60 lines; the float forms cite layer 4.
3. **Control and calls** (3,000–5,000 lines): a mutual induction on fuel over `execOne`, `exec` and `run`, following Talos's own mutual definition. It covers sequences, the loop wrappers and the `brk` dispatch, `br`, `br_if`, `ret`, function entry through `function_entry2`, and calls with the test of `lx_status` after them. A loop that re-runs itself and a call each use the hypothesis at fuel − 1, exactly where Talos spends fuel.
4. **Float lemmas** (1,000–3,000 lines): canonicalization equals Talos's NaN result for every NaN choice CompCert might make; the `trunc_sat` guards; f32 square root through binary64 (the double-rounding lemma); `f32Nearest` by integer arithmetic; the conversions agree with Talos's IEEE 754 functions. LeanExe's existing `F32*` and `F64*` lemmas in `LeanExe/ProofKit` cover part of this.
5. **Module theorem.** `translate_correct`: if `translate LX_CAP m = some p` and `run fuel m id st args` returns `Success vs st'` or `Trap st' msg`, then from any C state matching `st` and the arguments, `eval_funcall` of the C function terminates with results matching `vs` and a state matching `st'`, or terminates with the code for `msg` in `lx_status` and globals and memory matching `st'`.
6. **Initialization.** `lx_init_correct`: running `lx_init` from CompCert's initial memory gives a state matching Talos's `Module.initialStore`, with the cap set to `LX_CAP`.  The allocator invariant and the tables of `compileWith_initialStore` do not depend on the cap, so they hold of that store for the first call.
7. **Composition.** `ImplementsA.native` takes `p.f.implements` and `translate_correct`. It picks a fuel at least the `N` from `Runs` and concludes, for a C memory related to the store, that the call terminates in a memory related to a final store that meets the postcondition of `p.f.implements`; the bytes are equal, so every heap reading of that postcondition carries over unchanged.

**The statement of `p.f.native`.**  `NativeA`, which `p.f.native` states for the function's translation, assumes `ImplementsA`'s premises on the store, the heap, and the arguments, and the following of the C side.  The environment `E` finds `lx_status`, the C globals `lx_g<i>`, `lx_pages`, `lx_mem`, the scratch cell `lx_pun`, the external function `__builtin_fsqrt`, the result globals of `unsigned int`, `unsigned long long`, `double`, and `float` for each position below `E.nres`, at least the translation's number of positions, and every function of the translation, in distinct blocks (`EnvOk`).  The memory relates the C globals and `lx_mem` to the store, keeps `lx_pages`, the result globals, and `lx_pun` writable with their contents otherwise unconstrained (`StoreRel`), and holds 0 in `lx_status` (`StatusRel`).  The cell, the external function, and the `double` result globals entered with M5, and the `float` result globals with M6; `start` proves every premise on the environment for the program's own global environment and the memory that `lx_init` leaves.

**What `verified_compile` adds.** For a module in the subset, the command evaluates `translate nativeCap p.module` natively, with `nativeCap` 4,096 pages, and the kernel checks one theorem, `p.translation_funcs`, that the translation exists and that its functions are those of the native result.  `p.translation` is that translation, made irreducible after its equation `p.translation_eq`, so that later proofs use the equation rather than unfold the translation.  For every definition `f` whose function the translation contains, `p.f.native` follows from `p.f.implements`, the equation, and the function's membership, as `NativeImpl` states, or `NativeTablesImpl` for a wrapper.  The C text comes from the executable `native-verified`, which runs the same translator.  Its native build, `native-verified build`, writes the `.c` file, has `clightgen` read that file, compares the Clight that `clightgen` gives with the translation, and compiles the same file with `ccomp` only when they match.  The per-build comparison therefore covers the printer and the write of the file together, and no file theorem is needed for either.

**Why the result transfers to the binary.** The C execution terminates, after a trap as well as after a return of results, and the Lean copy's big-step relation is deterministic, so the call has exactly one outcome and does not go wrong.  CompCert's `bigstep_semantics_sound` is about a whole program: its judgment `bigstep_program_terminates` requires a `main` of type `int(void)`, called with no arguments from the memory of `init_mem`, whose result is an `int`.  The translator's theorems conclude `eval_funcall` of one function, and the Lean copy omits the program-level judgment, so one more step reaches a program.  For arguments fixed in advance, a generated `main` calls the function on them and returns an `int` computed from the result and `lx_status`.  Its `eval_funcall` follows from the function's by the rules for a call and a return, and `bigstep_program_terminates` holds for the generated program, from `globalenv` and `init_mem`.  CompCert's compiler theorem then makes that program's behaviour, its trace and its exit status, the behaviour of the machine code.  A host that reads arguments at run time is a separate C file outside the Lean proofs, and for it the argument rests on `separate_transf_c_program_correct` and on the host's assumptions listed below.  The steps through CompCert are in Rocq; the trust argument for crossing between the two provers is in section 6.

**When `translate_correct` speaks about CompCert.**  The theorem concludes `eval_funcall` of the Lean copy for every `Archi`, `ExtSem`, global environment, and memory that meet its hypotheses.  Its conclusion is a CompCert `eval_funcall` under five conditions.  `A` and `X` are CompCert's values: the `Archi` instance of the target and the image of CompCert's `external_functions_sem`.  `E.ge` is the image of `Genv.globalenv` of the whole linked program that `ccomp` compiles, CompCert's built-in declarations included.  The memory is extensionally the image of CompCert's memory at the call.  Every identifier is positive, which the translator ensures by emitting none below 1.  The copy's rules correspond one to one to CompCert's, which the reviews and the differential tests support and no proof covers.  The step from such a call to a whole program through `main` remains open.

**The translation without the alignment test.**  The option `alignedAccess` of `translate`, `false` by default, makes every `load64` and `store64` read or write the one word `lx_mem[t >> 3]` after the bound check, without the test `(t & 7) == 0` and the eight byte accesses that the test selects otherwise.  The word is the access of the Talos run only when the address is a multiple of 8, so the simulation needs that fact about the run.  `AlignedOne`, `AlignedExec`, and `AlignedRun` in [the aligned run definitions](../LeanExe/ProofKit/AlignedDefs.lean) state it for an instruction, a list of instructions, and a call, and take every intermediate state from Talos's own functions.  `InstrSimL` and `ProgSim` in [the control proofs](../LeanExe/Native/Proof/Control.lean) and `RunSimFun` in [the call proofs](../LeanExe/Native/Proof/Calls.lean) take the fact as a premise when the option holds, and `translate_correct` holds for `translate cap m al` at both values of `al`.  At `false` the premises are vacuous, so `Runs.native`, `NativeA`, and `ImplementsA.native` keep their statements for `translate cap m`.

`RunsA.native` and `ImplementsAligned.native` in [the aligned native step](../LeanExe/Native/Proof/AlignedNative.lean) take the fact from the compiler's `ImplementsAligned` in [the aligned statement](../LeanExe/Pipeline/ImplementsAligned.lean): `ImplementsA` from an input that meets `AlignedInput`, with every run of the entry making only aligned 64-bit accesses inside memory from some fuel on, and with an aligned final heap and a result whose blocks meet `AlignedOutput`.  They conclude `NativeAlignedA`, which is `NativeA` with the premise `AlignedInput` after `Separate` and the conclusions `heap'.Aligned` and `AlignedOutput` after a return, so that a host can meet `AlignedInput` again at its next call.  `ImplementsTablesAligned.native` in [the aligned wrappers](../Verified/AlignedNative.lean) gives `NativeTablesAlignedA` for a wrapper in the same way.  `native-verified build --aligned` and `tests/native/verified.sh --aligned` build the corpus with the option.

The option stays off by default.  The compiler states `ImplementsAligned` for functions and entries and `ImplementsTablesAligned` for wrappers, and no aligned form for modules with literals, whose theorems are `ImplementsStatic`.  One translation covers a whole module, so the native build may use the option only for a module every one of whose `p.f.native` theorems has an aligned form, and a module with a theorem whose form has no aligned variant keeps the test in every function.  In the corpus of `tests/verified`, 21 modules state theorems for wrappers, among them `sha256` and `crc` of the benchmark, and no module states a theorem for literals.

## Trust argument and validation

Three links connect the Lean theorem to the binary:

1. The Lean copy of Clight must mean what CompCert's Clight means. This is checked by review and by differential testing.
2. The C text must parse to the program the proofs are about. This is checked on every build with `clightgen`.
3. CompCert must compile that program correctly. CompCert's Rocq proof covers this.

**Fidelity of the Lean copy.** This is the one link that crosses between provers, so it gets the most checking:

- **Side-by-side review.** Every Lean definition cites its CompCert 3.18 file and name. The project pins 3.18 and reviews the copy again before moving to a newer version.
- **Random programs.** Generate C-subset programs from the Lean AST, biased toward edge values: shift amounts at 63 and 64, NaN payloads, ±0, subnormals, and conversion boundaries such as 2^64 and −1. Run each with `ccomp -interp`, CompCert's reference interpreter for its own C semantics, and with `LClight.run`, then compare return values and final globals. `-interp` runs the program before `SimplExpr` and `SimplLocals`, but CompCert proves both passes preserve behaviour.
- **The real corpus.** Translate every module the `tests/verified` drivers build. Run each one compiled by `ccomp`, under `ccomp -interp` and under `LClight.run`, and compare with today's Wasmtime and native-Lean results.
- **Floats.** Test binary32 unary operations exhaustively over all 2^32 inputs where the run time allows, and sample the rest.
- **Interpreter soundness.** `LClight.run` is proved sound against the relation, so each test exercises the relation itself.

**The per-build front-end check.** `clightgen`, built with `./configure -clightgen` from the same 3.18 tree as `ccomp`, runs the same parser and elaborator, then `SimplExpr` and `SimplLocals`. It prints the resulting Clight as Rocq terms, with float constants as bit patterns. A small parser reads that output into the Lean AST, and the build compares it with `p.cprogram` up to renaming of temporaries. Any difference fails the build. What remains trusted is that `ccomp` and `clightgen` from one tree run the same front end on the same text; the `clightgen` README calls the tool experimental.

`clightgen`'s exporter changes some statements as it prints them: it prints `Ssequence Sskip s` and `Ssequence s Sskip` as `s`, and two forms of loop as `Swhile` (`export/ExportClight.ml`, lines 104 to 115).  The program that the check reads is therefore `exportProgram` of the program inside `clightgen`, where this design took it to be that program itself.  `bigstep_program_terminates_export` (`LeanExe/Native/Proof/Export.lean`) closes the step: a run of the printed program is a run of the program inside `clightgen`, with the same trace and result.

**CompCert's side.** The Rocq theorems relied on are `transf_c_program_correct`, or `separate_transf_c_program_correct` when the host is a separate C file, together with `bigstep_semantics_sound` for semantics2; the `SimplExpr` and `SimplLocals` proofs sit inside the compiler theorem. CompCert's own unverified parts are its parser and elaborator (covered by the `clightgen` check), its assembler and linker (AbsInt sells a validator for these), and the OCaml extraction of CompCert itself, which every CompCert user shares.

**Assumptions about the host and environment.** The generated header states these:

- The host is compiled with `ccomp`. It calls `lx_init()` once, places arguments in `lx_mem` through the exported `alloc` so that they meet the `Represent` premises, and reads results through the same representation.
- The host reads `lx_status` after each call, and treats a nonzero value as a trap of that call.
- The stack does not overflow. CompCert's theorem assumes this. The 1,000-call depth guard bounds the number of frames, so measure the deepest stack use under `ccomp` and size the thread stack from that.
- `LX_CAP` pages fit in memory and in the toolchain's addressing limits (section 8).

**Still trusted at the end:** the components of the next section.

## Trusted base of the native path

`p.f.native` is a Lean theorem about the Clight program `p.translation`.  A machine-code function computes `f` only if every component below does what the table says, and none of them is proved in Lean.  The table lists each component, what it must do, and how the project checks it.  The printer and the written file appear in it although they are not trusted, because the per-build comparison is what removes them.

| Component | What is trusted | How it is checked |
| --- | --- | --- |
| Lean | The kernel, with `propext`, `Classical.choice`, and `Quot.sound`; the toolchain pinned in `lean-toolchain` | `#print axioms` of the native theorems; no `sorry`, `native_decide`, or `bv_decide` |
| The Lean copy of Clight | `LeanExe/Native/Clight/` means what CompCert 3.18's Clight means for the programs the translator produces: `Clight.v`, `ClightBigstep.v`, `Cop.v`, `Memory.v`, `Values.v`, `Floats.v`, and the parts of `Globalenvs.v` and `Events.v` that they use, with the NaN choices of `Archi` left as parameters | Side-by-side review against the cited definitions; the differential test `tests/native/clight.sh` against `ccomp -interp` on 921 programs, under both targets' NaN parameters; and the corpus run natively |
| CompCert's proof | The theorems `bigstep_semantics_sound` (`ClightBigstep.v`), which turns a terminating big-step execution into a behaviour of Clight's small-step semantics, and `transf_c_program_correct`, or `separate_transf_c_program_correct` when the host is a separate file (both in `Compiler.v`), which carry the behaviour to assembly; `SimplExpr` and `SimplLocals` are inside the compiler theorem.  These rest on Coq's kernel; on the axioms of CompCert's `lib/Axioms.v`, functional extensionality and proof irrelevance, and the classical logic that `Behaviors.v` imports; and on its hypotheses about the target: the `Archi.v` parameters, which the Lean copy's two `Archi` instances copy, the assembly semantics, and the semantics of the run-time helper functions | CompCert's development, checked by Coq when it is built from the release archive whose SHA-256 and SHA-512 the journal records |
| CompCert's unverified parts | The parser and elaborator that turn the C text into CompCert C; the extraction of the compiler to OCaml; the printer of assembly; and the assembler and linker it calls.  The translation is compiled with `-fno-common`, which makes the printer emit `lx_mem` and `lx_pun`, globals without initializers, as `.bss` definitions rather than `.comm` symbols, and makes the AArch64 and x86-64 back ends address them directly rather than through the global offset table.  The option changes no Clight program, and the compiler's proof holds for either addressing | The front end by the `clightgen` comparison below; the rest is shared by every CompCert user |
| The printer | `LeanExe/Native/Print.lean` and `CText.lean` write C text whose parse is `p.translation` | Not trusted: `native-verified build` has `clightgen` read the text back, and `ClightCheck.lean` compares the result with the translation before `ccomp` runs |
| The written file | The C file that `ccomp` compiles is the file whose parse matched the translation | Not trusted: `native-verified build` compiles the very file that `clightgen` read, after the comparison passes, so the comparison covers the write |
| `clightgen` as a check | `ccomp` and `clightgen`, built from one 3.18 tree, run the same front end on the same text, through `SimplExpr` and `SimplLocals`; `ClightCheck.lean` reads `clightgen`'s Coq file correctly and compares it with the translation, renaming only call temporaries | `clightgen` is CompCert's own code; the reader and the comparison are unverified Lean code, and a file they cannot read fails the check |
| The host glue | `tools/native-host.c`, the glue that `native-verified` writes for each module, and the host programs of `tests/native/run.sh` call `lx_init` once, place the arguments so that they meet the premises of `p.f.native` (`StoreRel`, `Represent`, `ArgsTyped`), and, under the translation without the alignment test, so that they meet `AlignedInput` as well, since a host that violates it reads or writes a wrong word without a trap, read `lx_status` after each call, and read the results through the same representation | Unverified C; the corpus and end-to-end runs compare every result with Wasmtime and with Talos.  An application's own host carries the same obligations |
| The run-time library | CompCert's `libcompcert.a`, hand-written assembly that implements the helper functions whose semantics CompCert assumes.  On x86-64 the translations of the corpus call `__compcert_i64_utod`, `__compcert_i64_utof`, and `__compcert_i64_dtou` for conversions between unsigned 64-bit integers and floats.  The translated code calls no other library function; `alloc` and `release` are functions of the module, so their translations are proved | The conversions are exercised at their boundaries by `fops`, `f32ops`, and the corpus |
| Call depth and the stack | CompCert's theorem assumes that the stack does not overflow.  A function that takes the call depth traps at `unreachable` when the depth reaches `depthLimit`, 1,000, so a call nests at most 1,000 frames of the module's functions, and the thread's stack must hold the deepest of them as `ccomp` lays them out | M2's test of the recursive GCD called it at depths 997 to 1,000 and saw the trap; the stack that 1,000 frames need is not yet measured |
| The toolchain and platform | `ccomp` and `clightgen` 3.18, built with Coq 8.18.0, OCaml 4.14.1, and Menhir 20231231 from Ubuntu's packages, configured for `aarch64-linux` and for `x86_64-linux`; the GNU assembler and linker of the target, the cross toolchain `gcc-x86-64-linux-gnu` 13.3.0 for x86-64; glibc and its start-up code; the operating system; and the CPU.  The x86-64 tests run under `qemu-x86_64`, which only the tests need | Shared by every program that the toolchain builds |

## Milestones and exit criteria

M0 and M1 can run in parallel. From M2 on, each milestone adds instruction forms to the translator and its proof, and ends with native code whose theorem `verified_compile` generates and the kernel checks.

| Milestone | Work | Exit criterion |
| --- | --- | --- |
| M0 · Subset check and corpus | Decidable `InSubset`, emitted as `p.inSubset` | every `tests/verified` module passes |
| M1 · Lean copy of Clight | Semantics, evaluator, soundness, random tests | no mismatch with `ccomp -interp` |
| M2 · Integer core, end to end (needs M0, M1) | Locals, globals, control flow with `brk`, calls, traps, printer, `clightgen` check | GCD runs natively, with its theorem and a matching `clightgen` AST |
| M3 · Memory and runtime | `load64`, `store64`, `memory.size` and `grow`, `lx_init`, the `alloc` and `release` runtime | array, list, hashing and sorting examples native with theorems |
| M4 · Generated theorems | `verified_compile` emits `p.f.native` for every function; host compiled with `ccomp` | the integer cases of the `tests/verified` corpus pass natively |
| M5 · binary64 | Arithmetic with NaN canonicalization, comparisons, conversions, `sqrt`, `trunc_sat` | the Euler solvers native with theorems |
| M6 · binary32 | `nearest` by integer code, `sqrt` through binary64, `trunc_sat`, conversions; `f64PromoteF32` and `f32DemoteF64` stay outside the subset, with the subset check's warning, since no corpus module uses them and Talos computes them with Lean's native floats | binary32 GPT-2 native with theorems |
| M7 · Hardening | Benchmarks against Wasmtime, optional alignment proof, the per-build comparison in the native build, every check in CI | a release with its trusted base written down |

M2 carries the most design risk, because it proves the `brk` control-flow encoding; nothing after it changes that encoding. M5 and M6 carry the most schedule risk, because of the float lemmas.

## Risks, open decisions, and effort

The largest risk is a gap between the Lean copy and CompCert's Clight in some case the translator reaches.  The `brk` encoding of M2 and the binary32 lemmas of M6, which earlier versions of this table listed as risks to the schedule, are proved.  The cost of the emitted checks is the subject of M7's benchmark against Wasmtime.

| Risk | Effect | Mitigation |
| --- | --- | --- |
| The Lean copy differs from CompCert in a reachable case | The theorem is about a different program | Keep the subset small; cite every definition; run differential tests; review again on each CompCert upgrade |
| `clightgen` and `ccomp` front ends diverge | The per-build check proves nothing | Build both from one 3.18 tree.  `native-verified build` compares `clightgen`'s Clight for the C file with the translation and then has `ccomp` compile the same file.  No check compares the Clight of `ccomp` itself: `ccomp -dclight` prints Clight between `SimplExpr` and `SimplLocals`, and `clightgen -dclight` prints it after `SimplLocals`, so the two dumps differ in every function's locals |
| `lx_mem` outgrows the static-array limit | Large demos cannot be built | CompCert's x86-64 code reaches globals through 32-bit PC-relative offsets, and a static array past 2 GiB risks relocation overflow, so `LX_CAP` should stay below about 32,767 pages unless tests show more works; beyond that, switch to an allocated region zeroed on growth, which adds `malloc` to the Lean copy |
| The emitted checks cost too much time | Native code is slower than expected | Measure against Wasmtime from M2; later prove 8-byte alignment to drop the byte-wise path, and canonicalize NaN only where bits become observable |
| Stack use under `ccomp` is unknown | The 1,000-call guard may not fit the default stack | Measure the deepest frame chain and set the thread stack size from it |
| CompCert licensing | Commercial use needs a license | Free for research; buy an AbsInt license before commercial use |

**Open decisions:**

- A cap per module, or a region allocated at run time, for a module that needs more than `nativeCap` pages.
- Whether to prove 8-byte alignment of every address in the Verified compiler's invariants, which removes the byte-wise path.
- Whether the per-program LeanExe compiler emits the translation and the native theorems, as `verified_compile` has since M4.  It shares the runtime, and the subset check decides module by module.

**Effort**, in lines of Lean:

| Component | Estimate |
| --- | --- |
| Subset check | 300–600 |
| Lean copy of the Clight subset and its evaluator | 2,500–4,000 |
| Translator and printer | 1,500–2,500 |
| Proof layers 1–3 | 7,000–12,000 |
| Float lemmas | 1,000–3,000 |
| Initialization, composition and `verified_compile` changes | 1,000–2,000 |
| **Total** | **about 13,000–24,000** |

Tooling outside Lean comes on top: the `clightgen` reader, the test harness and CI. For calibration, the Verified compiler grew from its first commit on 2026-10-06 to about 43,000 lines in 743 commits by 2026-10-25. The translator is roughly a third to a half of that. These figures are estimates, not measurements.

## Sources

- jsmorph/leanexe at `d1f8517`: `Verified/Compile.lean`, `Verified/README.md`, `LeanExe/Pipeline/Implements.lean`, `LeanExe/Pipeline/Aborts.lean`, `LeanExe/Runtime/Defs.lean`
- jsmorph/talos at `87e3aa5`: `interpreter/Interpreter/Wasm/Semantics.lean`, `Syntax.lean`, `Locals.lean`, `Continuation.lean`
- AbsInt/CompCert 3.18: `cfrontend/Clight.v`, `cfrontend/ClightBigstep.v`, `common/Memdata.v`, `common/Memory.v`, `common/Builtins0.v`, `x86_64/Archi.v`, `aarch64/Archi.v`, `driver/Compiler.v`, `driver/Driver.ml`, `export/README.md` (`clightgen`)
