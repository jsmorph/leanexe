# LeanExe native code on bare metal: design and plan

2026-10-27 · Jamie Stephens

## Goal and end-to-end statement

[The translator's design](native-translator.md) ends at `p.f.native`, a theorem about one call of one C function in the Lean copy of CompCert's Clight.  A C host, linked with libc and run under an operating system, places that call's arguments and reads its results, outside every proof.  This design replaces the host, libc, and the operating system with a startup routine of about fifty instructions and a `main` that the translator writes and proves.  The binary runs on QEMU's `virt` machine for AArch64 and, in a later milestone, on a board.  The goal is one theorem per program that states the program's whole observable behaviour in the terms of CompCert's semantics, and an argument, checked in Rocq where CompCert's proofs reach, that carries the theorem to the Asm program that `ccomp` produces.

The program is the translation of a module, a volatile global `lx_out` that the linker places at the UART's data register, and a generated `main`.  `main` calls `lx_init`, calls an entry `run` that the verified compiler compiled, on arguments fixed when the program is built, and writes the bytes of the result to `lx_out`.  The theorem `p.f.program` of an entry `f` has two cases.  Either the program terminates with result 0 and a trace of one volatile store per byte of the result's encoding, or, when `run` may abort, it terminates with result 1 and an empty trace.  The design covers no interrupts, no second core, no input device other than a memory region that a loader fills, and no timing.

| Step | From | To | Covered by |
| --- | --- | --- | --- |
| 1 | Lean definition | `p.run.native` | the existing proofs |
| 2 | `p.run.native` | `bigstep_program_terminates` of the whole program in the Lean copy | a new Lean proof, described below |
| 3 | the Lean copy | CompCert's `Clight2.bigstep_program_terminates` of the program that `clightgen` reads | review, differential tests, the per-build check, and a renaming lemma |
| 4 | the program that `clightgen` reads | the program that `ccomp` compiles | trusted: one front end, with identifiers numbered differently |
| 5 | Clight big-step termination | the behaviour of the Asm program | a composition of CompCert's proofs in Rocq, proved in the experiments |
| 6 | the Asm program | the machine | trusted: printer, assembler, linker, startup code, CPU, and UART |

## Target machine

The target is AArch64, on QEMU's `virt` machine with 1 GiB of RAM, compiled with CompCert's `aarch64-linux` configuration.  QEMU runs the image on an emulated Cortex-A57 under TCG and, in B8, on the processor of AArch64 hardware under KVM.  CompCert 3.18 has no bare-metal configuration for any 64-bit target: its `configure` lists `-eabi` variants only for PowerPC and 32-bit ARM (lines 43 to 62).  The Lean copy fixes `ptr64 = true`, so x86-64, RISC-V, and AArch64 remain, and AArch64 needs the least outside the proofs:

| Target | CompCert run-time functions that the translations need | The Lean copy | Startup |
| --- | --- | --- | --- |
| AArch64 | none: `runtime/Makefile` builds only `vararg.o` for it (line 26), and a translated module links with no library | `Archi.aarch64`, with the corpus passing natively on AArch64 | QEMU enters the image at EL1 |
| x86-64 | `__compcert_i64_dtou` and `__compcert_i64_utod`, which `backend/SplitLong.vp` calls for unsigned conversions (lines 136 and 140), since `x86/SelectLong.vp` selects none of its own.  The library is compiled outside CompCert's proofs | `Archi.x86_64` | a Multiboot loader enters in 32-bit protected mode with paging off, so page tables must exist before any CompCert code runs in 64-bit mode |
| RISC-V 64 | not checked.  `runtime/Makefile` builds the whole set of 64-bit helpers for RISC-V (line 28) | no `Archi` instance, so a new one and new differential tests | not tested |

`ccomp` passes the link to gcc and accepts `-nostdlib`, `-static`, `-T` with a linker script, and `-Wl,` (`driver/Linker.ml`, lines 66 to 95).  It always appends `-L<stdlib> -lcompcert` (lines 21 to 30), but on AArch64 that library holds only the variadic-argument helpers, which no translation calls.  In the experiments, the object file of the translation of each of eight corpus modules had no undefined symbol, and only the test host's replacement for `printf` drew on CompCert's library, for the variadic-argument helpers.  The generated code runs from RAM: QEMU's ELF loader writes `.text`, `.rodata`, and `.data` at their link addresses, so the startup code copies nothing.

QEMU documents two fixed addresses of `virt` for bare-metal guests, flash at 0 and RAM at `0x4000_0000`, and places the device tree at the start of RAM.  Every other device address may change between QEMU versions and must come from the device tree.  The image is linked at `0x4010_0000`, above the device tree.  The UART address is fixed in the linker script, and the test harness compares it with the device tree that `-machine virt,dumpdtb=FILE` writes for the QEMU in use: QEMU 8.2.2 gives `pl011@9000000` with `reg = <0x00 0x9000000 0x00 0x1000>` and `stdout-path = "/pl011@9000000"`.  Reading the device tree at startup would avoid the check at the cost of a parser in the trusted startup code.

A board differs in four ways, each outside the proofs: the exception level at entry, the UART's address and setup, the RAM base, and the state of the caches and TLBs at reset, which may need invalidation sequences that the implementation defines (DDI 0487 issue M.d, sections D7.5.6 and D8.16.1, pages D7-7650 and D8-7852).  QEMU 8.2.2 emulates the Raspberry Pi 3B (`raspi3b`, Cortex-A53) but not the 4B, which newer QEMU documentation lists.  The project has not chosen a board.  B8 runs the programs under KVM instead, where the processor, its memory system, and its alignment checks are those of AArch64 hardware and the devices are QEMU's models of `virt`'s.

## The generated main and its outputs

The translator writes `main` after the translation's functions, in the same C file, so that `ccomp` compiles one whole program and `transf_c_program` covers it in one run.  `main` never takes the address of a local, so SimplLocals turns its locals into temporaries, as it does for the translation's functions.  For an entry `lxf_run` with scalar parameters and an `Array UInt64` result, `cmain` (`LeanExe/Native/Bare.lean`) writes:

```c
extern volatile unsigned int lx_out;
int main(void) {
  unsigned long long l0;
  unsigned long long l1;
  unsigned long long l2;
  lx_init();
  l0 = lxf_run(7ULL, 9ULL);                /* the arguments fixed at build time */
  if ((lx_status != 0U)) {
    return ((int)lx_status);
  }
  l1 = /* the word at l0, by the translator's loadBytes */;
  l1 = ((8ULL * l1) + 8ULL);               /* the length word and the elements */
  l2 = 0ULL;
  while ((l2 < l1)) {
    lx_out = ((unsigned int)(*(((unsigned char *)lx_mem) + (l0 + l2))));
    l2 = (l2 + 1ULL);
  }
}
```

`clightgen` and `ccomp` append `return 0;` to `main`.  For a `UInt64` result, eight stores `lx_out = ((unsigned int)((l0 >> 8kULL) & 255ULL));` replace the loop.  The output is the array's representation in `lx_mem`, the length word and then the elements, little-endian, which `Heap.Owned` and `MemRel` describe byte by byte.  Byte loads need no alignment fact about `l0`.  An entry with several results, such as a digest of four words, returns `void` and leaves the words in the translation's result globals (`ResultRel`), so for the kind `words k` `main` calls it without a result and writes the eight bytes of each of the first `k` result globals in order, with the stores of the `UInt64` case.  Other result types reach one of these forms through a Lean function that encodes them as an `Array UInt64`, compiled with the rest of the program.

Arguments fixed in advance take two forms.  A scalar argument is a constant in the call.  A heap argument, such as an array or a byte string, is a constant inside a Lean definition without parameters, `def run : Array UInt64 := encode (f input)`, for which the reflector's theorems take the argument type `Unit` (`Verified/README.md`, lines 772 and 773).  The verified compiler compiles the constant with the rest of the definition, and `p.run.implements` covers the construction of the value.  `main` therefore places nothing in `lx_mem` before the call, and no theorem about a sequence of host calls is needed.  The programs of B4 take their messages as words instead and build them in the heap, since the command `bare_program` does not yet cover `ImplementsStatic`, the theorem of a program with byte literals, which such a constant gives.  A constant table is an argument that a wrapper applies (`Verified/README.md`, lines 448 to 462), so the CRC and SHA programs of B4 are wrappers.

The program can report results in four ways, and CompCert's semantics observes two of them:

| Channel | In CompCert's behaviour | Use |
| --- | --- | --- |
| The `int` that `main` returns | yes: `Terminates t r` carries `r` | 0, the trap code of `lx_status`, or 64 when a program with input reads a length above `inMax`.  The startup code passes `w0` to QEMU's exit status through semihosting |
| Volatile stores to a volatile global | yes: each is an event `Event_vstore chunk id ofs v` of the trace, which every pass preserves | the result's bytes, through `lx_out` at the UART's data register |
| A memory region read after the program halts, by a debugger or QEMU's monitor | no: `program_behaves` records only the trace and the result, so CompCert's theorem says nothing about final memory | none |
| Semihosting calls from C, such as `SYS_WRITEC` | only as an external call, whose event and result come from `external_functions_sem`, a parameter of CompCert.  The Lean theorems hold for every such semantics and so conclude nothing about a call to one | the startup code's exit call, outside the proofs |

A volatile store reaches the trace as follows.  C2C gives an `extern volatile` declaration an empty initializer and `gvar_volatile = true` (`cfrontend/C2C.ml`, lines 1278, 1279, and 1305 to 1307).  SimplExpr turns an assignment to a volatile lvalue into `Sbuiltin None (EF_vstore chunk)` with the lvalue's address and the value (`cfrontend/SimplExpr.v`, lines 184 to 226), and the experiment's `clightgen` output shows this form for a store to `lx_out`.  `volatile_store` of a block that `Senv.block_is_volatile` marks emits `Event_vstore` and leaves memory unchanged, with no permission check (`common/Events.v`, lines 571 to 583).  The assembler and linker resolve `lx_out` by name to the address in the linker script, so the event means a 32-bit store to that address.

The exit status of a program is therefore one of these codes:

| Code | Meaning |
| --- | --- |
| 0 | `main` wrote its output and returned |
| 1, 2, 3 | `lx_status` after a trap at `unreachable`, an access outside memory, or a division by zero, which `main` returns |
| 64 | a program with input read a length above `inMax` |
| 254 | the startup code found an exception level other than 1 |
| 255 | an exception, which the vectors report |

On QEMU, the PL011 model passed every byte to its output in the experiments.  On hardware the transmitter can be busy when `main` writes, and `main` cannot wait for it: a volatile read of the UART's flag register is an input event whose value the theorem would have to quantify over, and a loop that waits on it has no termination proof.  Under KVM each store to the UART reaches QEMU's PL011 model, as under TCG, so B8 leaves the question to a board, which has to settle how output reaches a device that may not accept every write.

## The program-level theorem

### Statement

The Lean copy gains CompCert's judgment for a whole program (`cfrontend/ClightBigstep.v`, lines 252 to 260):

```lean
inductive bigstep_program_terminates (A : Archi) (X : ExtSem) (p : program function) :
    trace → int → Prop
  | intro (b : block) (f : fundef function) (m0 m1 : mem) (t : trace) (r : int) :
      init_mem p = some m0 →
      Genv.find_symbol (globalenv p) p.prog_main = some b →
      Genv.find_funct_ptr (globalenv p) b = some f →
      type_of_fundef f = .Tfunction [] type_int32s cc_default →
      eval_funcall A X (globalenv p) m0 f [] t m1 (.Vint r) →
      bigstep_program_terminates A X p t r
```

The program is `bareProgram pre T (bareMain cap k args kind)` (`LeanExe/Native/Proof/Whole.lean` and `LeanExe/Native/Bare.lean`): CompCert's external declarations `pre`, the translation's definitions in the order of the C text, the declaration of `lx_out`, and `main`, which calls the entry `k` on the words `args` and writes a result of the kind `kind`, with `prog_main` naming `main`.  `clightgen` puts its declarations of CompCert's built-in and run-time functions first, among them `__builtin_fsqrt`, which the translation places between `lx_pun` and the result globals, so that declaration moves into `pre`.  The theorem holds for every `pre` of external function declarations whose identifiers are distinct from the program's and which declares `__builtin_fsqrt` at its signature, the hypotheses of `wholeOk_bare` that `PrefixOk pre` collects, and the per-build check confirms that the program `clightgen` reads has that shape.  The command `bare_program p.f x [args] r` (`Verified/Bare.lean`) states and proves it for the entry of `f`, its argument `x`, whose words are `args`, and its result `r`, which is `f x`:

```lean
theorem p.f.program (A : Archi) (X : ExtSem) (pre) (hpre : PrefixOk pre) :
    bigstep_program_terminates A X (bareProgram pre p.translation (bareMain nativeCap k args kind))
        (outTrace (encode r)) 0 ∨
      (aborts = true ∧ bigstep_program_terminates A X
        (bareProgram pre p.translation (bareMain nativeCap k args kind)) E0 (UInt32.ofNat 1))
```

`encode` is `encodeWord`, the eight bytes of a word from the lowest, or `encodeArray`, the eight bytes of the array's size followed by the eight bytes of each element, and `outTrace` maps each byte `b` to `Event_vstore Mint32 outId 0 (EVint b)`.  The proof follows `main`'s body: `init_mem` of the whole program, with the prefix and `lx_out` before and after the translation's blocks; `lx_init_correct` for the call of `lx_init`; `p.f.native` for the call of the entry, with the premises that `start_whole` proves for the state after `lx_init`, and the quietness of the translation, which makes the call's trace empty; the test of `lx_status`; a loop lemma that produces one event per byte from `UInt64Array.At` and `MemRel`; and `outcome_result_value` for the returned `int`.  The path uses the translation with the alignment test.  Under the translation without it, the call of the entry also needs `AlignedInput`, which the heap after `lx_init` meets: its `top` is `tablesEnd tables`, or the `top` of the literal pool for a module with literals, both multiples of 8, and its free list is empty.

The lemmas of the path exist only for the translation with the test.  Each theorem in the table takes `translate cap m = some T`, whose option `alignedAccess` is `false` by default, and `translate_funcs_of_parts` in [the parts](../LeanExe/Native/Proof/Parts.lean), from which `p.translation_funcs` follows, concludes `(translate cap m).map Translation.funcs = some L` for the same translation.  Every other theorem in the table except `entry_type` depends on `translate_defs`, which lists the program definitions of that translation: directly, or through `lx_init_correct`, `funcs_found`, `wholeOk_of`, `init_whole`, or `translation_fun_quiet`.  No form of `bare_of_nativeA` or `bare_of_nativeTables` takes `NativeAlignedA` or `NativeTablesAlignedA`.  For the runtime's functions, `alloc_nativeA` and `release_nativeA` in [the aligned native step](../LeanExe/Native/Proof/AlignedNative.lean) exist beside `alloc_native` and `release_native`.

| Module | Theorems |
| --- | --- |
| [The initialization](../LeanExe/Native/Proof/Init.lean) | `translate_defs`, `init_spec`, `lx_init_correct`, `funcs_found` |
| [The whole program](../LeanExe/Native/Proof/Whole.lean) | `translation_ids`, `wholeOk_of`, `wholeOk_bare`, `wholeOk_in`, `init_whole`, `lx_init_whole`, `start_whole` |
| [The quiet translation](../LeanExe/Native/Proof/Quiet.lean) | `translation_fun_quiet`, `genvQuiet_whole` |
| [The bare-metal program](../LeanExe/Native/Proof/Main.lean) | `entry_type`, `bare_program`, `bare_of_nativeA` |
| [The input program](../LeanExe/Native/Proof/Input.lean) | `input_program` |
| [The bare-metal wrappers](../Verified/Bare.lean) | `bare_of_nativeTables` |
| [The native test support](../tests/TestSupport/Native/Common.lean) | `start` |

### What the Lean copy must add

| Addition | CompCert 3.18 source |
| --- | --- |
| `bigstep_program_terminates` and `type_int32s` | `cfrontend/ClightBigstep.v`, lines 252 to 260; `cfrontend/Ctypes.v`, line 259 |
| `Genv.find_var_info` and `Genv.block_is_volatile` | `common/Globalenvs.v`, lines 211 and 217 |
| `eventval_match` for `EVint` and `EVlong` | `common/Events.v`, line 270 |
| `Val.load_result` | `common/Values.v`, line 1069 |
| `volatile_store`, `volatile_store_sem`, and the case `EF_vstore` of `external_call` | `common/Events.v`, lines 571 to 583, 820 to 824, and 1530 |
| for inputs: `volatile_load`, `volatile_load_sem`, and the case `EF_vload`, added in B7 | `common/Events.v`, lines 557 to 569, 709 to 713, and 1529 |
| a renaming lemma, `bigstep_program_terminates_rename`: `bigstep_program_terminates A X p t r` implies `bigstep_program_terminates A X' p' (renTrace g t) r` when `p'` renames the globals of `p` by an injective `g` and the temporaries of each function by an injective `τ`, and `X'` does on renamed symbols what `X` does | none |

`external_call` passes `ExtSem` the symbol table alone, and the volatile cases also need the volatility of blocks, so it takes the global environment while `ExtSem` keeps its type.  The differential test of the copy compares volatile stores and loads with `ccomp -interp`, which prints each volatile event at its default level of tracing (`driver/Interp.ml`, lines 56 to 75 and 421 to 424).  The interpreter answers a volatile load from its world, a memory in which the volatile globals hold their initial values and which its volatile stores update (lines 403 to 419 and 566 to 580).  The evaluator `run` takes the value of each load from `world_vload`, the initial memory of that world, so the two agree on programs that load only from globals they never store to, and the test's input programs load from `const volatile` arrays with random initial values.

### From the Lean theorem to the machine code

**The program `clightgen` reads.**  The per-build check compares the whole program, prefix and `main` included, with `bareProgram`, up to a renaming of identifiers, and the renaming lemma moves the theorem across it.  The check compares CompCert's external declarations and the translation's definitions since B3, B4 adds `lx_out` and `main`, and B7 adds `lx_in` and the `main` that reads the input, whose temporaries for volatile loads the check renames as it renames those of calls.  The program of the Coq file is `exportProgram` of the program inside `clightgen`, since the exporter prints `Ssequence Sskip s` and `Ssequence s Sskip` as `s` and two forms of loop as `Swhile` (`export/ExportClight.ml`, lines 104 to 115), and `bigstep_program_terminates_export` (`LeanExe/Native/Proof/Export.lean`) moves the theorem from the program of the file to the program inside `clightgen`.  The whole program numbers its identifiers so that no two parts share one.  The translation takes 1 for `lx_status`, 8, 12, 16, 20, and 24 for `lx_pages`, `lx_mem`, `lx_init`, `lx_pun`, and `__builtin_fsqrt`, `4 i + 2` for the global `i`, `4 k + 3` for the function `k`, and `32 (i + 1) + 4 c` for the result global `i` of the value type with code `c`, a multiple of 4 from 36.  CompCert's `j`-th declaration other than `__builtin_fsqrt` takes `4 j + 5`, `main` takes 4, `lx_out` takes 28, and `lx_in` takes 32.  The check gives each name of `clightgen`'s program its number, a global by its name and a temporary within its function, and requires the numbers to be distinct, so the renaming is injective on the program's own identifiers.

**The program `ccomp` compiles.**  `clightgen` numbers identifiers by a canonical encoding of their names (`export/ExportDriver.ml`, line 207, and `lib/Camlcoq.ml`, lines 288 to 301 and 337 to 345), and SimplExpr's temporaries then start at 128.  `ccomp` numbers names from 1 in the order it meets them, and its temporaries start after the last name (`lib/Camlcoq.ml`, lines 374 to 377).  The Clight program that `clightgen` prints and the one inside `ccomp` therefore differ by a renaming of identifiers, if the two front ends otherwise agree.  The renaming lemma holds for every renaming that is injective on the program's own identifiers (`bigstep_program_terminates_rename_on`), since every such map agrees there with a map injective on all identifiers (`exists_injective_extension`).  The trusted assumption therefore shrinks to this: for the same C text, the Csyntax program `p` inside `ccomp` is the one inside `clightgen` with its identifiers renamed by a map injective on the program's own identifiers.

**From Clight to Asm.**  `transf_c_program_correct` (`driver/Compiler.v`, lines 446 to 451) is a backward simulation from `Csem.semantics p`, the semantics of CompCert C.  Applying it needs a fact about every behaviour of `p` under CompCert C's semantics, which the Lean theorem does not give, while `bigstep_semantics_sound` speaks of `Clight.semantics2` of `p2`, the program after SimplExpr and SimplLocals.  The two theorems therefore do not compose.  CompCert proves a forward simulation for each pass from Cshmgen to Asmgen, the first from `Clight.semantics2` (`cfrontend/Cshmgenproof.v`, line 1962), and composes them inside the proof of `cstrategy_semantic_preservation` (`driver/Compiler.v`, lines 353 to 417), without stating the composition from Clight as a theorem.  The experiment states and proves it in 110 lines of Rocq against CompCert 3.18's compiled proofs:

```coq
Theorem clight2_bigstep_to_asm:
  forall p p1 p2 tp t r,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  ClightBigstep.Clight2.bigstep_program_terminates p2 t r ->
  program_behaves (Asm.semantics tp) (Terminates t r).
```

The proof unfolds `transf_c_program` past SimplLocals, composes the forward simulations of the remaining passes as `cstrategy_semantic_preservation` does, and ends with `Clight2.bigstep_semantics_sound` (`cfrontend/ClightBigstep.v`, line 631), `behavior_bigstep_terminates`, and `forward_simulation_same_safe_behavior` (`common/Behaviors.v`, lines 826 and 337).  Its assumptions are those of `transf_c_program_correct`, CompCert's parameters and Coq's classical axioms, and also `ClassicalEpsilon.constructive_indefinite_description`, which `forward_simulation_same_safe_behavior` uses.  `driver/Complements.v` proves the corresponding result for CompCert C's big-step semantics, `bigstep_cstrategy_preservation` (line 94), in the same way.

**Uniqueness.**  `clight2_bigstep_to_asm` shows that the Asm program can terminate with `t` and `r`, not that it cannot do something else.  Asm's semantics is determinate (`aarch64/Asm.v`, line 1282): two steps from one state match in their events and, with equal events, reach one state.  For a trace of volatile stores, `match_traces` holds only between equal events (`common/Events.v`, lines 505 to 517), so every run from the initial state follows the terminating run.  `clight2_bigstep_asm_unique` (`rocq/Clight2Asm.v`) concludes that every behaviour of `Asm.semantics tp` is `Terminates t r` when `t` has no system call and no volatile load, the only events whose results `match_traces` lets differ.

With volatile loads, runs differ in the values read.  `determinate_behavior_leaves` shows that a behaviour of a determinate semantics with a termination is that termination or leaves its trace at a pair of events that `match_traces` relates and that differ, and `vload_unique` that a behaviour has at most one `k`-th volatile load.  `clight2_bigstep_asm_reads` takes a predicate `Q` and, for every sequence `σ` of 32-bit values, a Clight termination whose trace `reads σ`, with no system call and with `EVint (σ k)` at its `k`-th volatile load, and that satisfies `Q`.  It concludes that the Asm program has such a termination for every `σ` and that every behaviour of the Asm program is one of them.  The proof chooses `σ` from the behaviour with `ClassicalEpsilon.epsilon`, so its assumptions are those of `transf_c_program_correct` and `ClassicalEpsilon.constructive_indefinite_description`, the same as those of `clight2_bigstep_to_asm`.  It excludes a pointer as the value of an `int` load through `Tptr = Tlong`, which holds on AArch64 (`aarch64/Archi.v`, line 22), so the file is specific to AArch64.

**What the Asm behaviour says.**  The initial state has the memory of `Genv.init_mem tp`, the program counter at `main`, the return address and stack pointer null, and every other register undefined (`aarch64/Asm.v`, lines 1238 to 1247).  A final state has the program counter null and `X0` holding `Vint r` (lines 1249 to 1253), the low 32 bits of the register.  Each stack frame is a fresh block of unbounded memory, so the semantics has no stack size.  Under the assumptions that the section on the trusted base lists, the processor that runs `main` performs exactly the stores of `t` to the address of `lx_out`, in order, and returns to the startup code with `r` in `w0`.  Nothing follows about time, about memory outside the trace, or about a run whose stack overflows.

## Startup code

The startup code is GNU assembly, about 125 instructions and a table of exception vectors, linked first:

| Step | Instructions | Reason |
| --- | --- | --- |
| Mask interrupts | `msr daifset, #0xf`, after recording DAIF | DAIF was `0x3c0`, all masked, at entry under QEMU.  A board's firmware may differ |
| Check the exception level | `mrs CurrentEL` | QEMU enters the image at EL1, as the experiment found.  At another level the code reports the level and exits with status 254, which QEMU's machines with the virtualization and security extensions, entering at EL2 and EL3, confirm |
| Record `SCTLR_EL1` | `mrs SCTLR_EL1` | the value at entry, which `tests/baremetal/entry.c` reports: `0x00c50838` under TCG, with `M`, `C`, and `I` clear, and `0x30c509d8` under KVM |
| Install the vectors | `msr VBAR_EL1` | 16 entries of 128 bytes at a 2 KiB boundary.  Each reports `ESR_EL1`, `ELR_EL1`, and `FAR_EL1` and exits with status 255 |
| Build the translation tables | about 50 instructions, with the MMU off | five tables of 4 KiB at `__tables`, as described below |
| Turn on the MMU and the caches | `MAIR_EL1`, `TCR_EL1`, `TTBR0_EL1`, `dsb sy`, `isb`, `tlbi vmalle1`, `dsb nsh`, `isb`, then `SCTLR_EL1` with `M`, `C`, and `I` set and `A` and `WXN` clear, and `isb` | the TLBs' contents at reset are IMPLEMENTATION DEFINED and might be UNKNOWN (section D8.16.1, page D8-7852) |
| Enable floating point | `CPACR_EL1.FPEN = 0b11`, then `isb` | FPEN's reset value is unknown.  Without this step `main` trapped at its third instruction with exception class `0x07` |
| Set the stack | `mov sp, __stack_top` | `SCTLR_EL1.SA` was 1 at entry, so the stack pointer must stay 16-byte aligned |
| Fill the stack with a pattern | a loop of `str` | the high-water mark that the report gives and that the section on the stack uses |
| Clear `.bss` | a loop of `stp xzr, xzr` | `lx_mem` and the uninitialized globals lie in `.bss`, and `init_mem` gives them zeros |
| Call `main` | `bl main` | |
| Report on the exception stack | `mov sp, __exc_stack_top`, then `bl lx_report_exit`, after `main` returns or a call of `lx_exit` | the report's frames lie outside the stack that the pattern fills, so the high-water mark that the report computes is that of `main` and its callees.  The vectors and the check of the level, the exception stack's other users, end at the exit, so that stack holds nothing then |
| Exit | semihosting `SYS_EXIT` with `ADP_Stopped_ApplicationExit` and `w0`, or, built with `PSCI_EXIT`, PSCI `SYSTEM_OFF` through `hvc #0` | under TCG, QEMU exits with `main`'s result.  Under KVM, QEMU exits with status 0 and the report gives the result |

The startup code turns the MMU and the caches on in every build, under TCG and under KVM, so the runs under TCG execute the code that runs on hardware.  With stage 1 translation off, the architecture gives every data access the memory type Device-nGnRnE (Arm Architecture Reference Manual, DDI 0487 issue M.d, section D8.2.12.1, page D8-7730).  An unaligned access to Device memory generates an Alignment fault where the location cannot support unaligned accesses, and otherwise whether it faults is IMPLEMENTATION DEFINED (section B2.8.2, page B2-312).  QEMU 8.2.2 under TCG runs such an access without a fault (QEMU issue 1204).  Under KVM on AArch64 hardware, before the MMU was on, the probe's unaligned 8-byte load took a data abort with `ESR_EL1` `0x96000021`, exception class `0x25` and fault status `0x21`, an alignment fault, at `ELR_EL1` `0x40100074` with `FAR_EL1` `0x40102053`.

The tables map RAM, `0x4000_0000` to `0x7FFF_FFFF`, in blocks of 2 MiB as Normal Inner and Outer Write-Back Read-Allocate Write-Allocate memory, the attribute `0xFF` of `MAIR_EL1`, Inner Shareable, writable and executable at EL1.  They map the 4 KiB page of `lx_out` as Device-nGnRnE memory, the attribute `0x00`, not executable, and leave every other address unmapped.  A level 3 table covers the 2 MiB that hold the guard page below the stack, with an invalid entry for that page, so an access to it takes a level 3 translation fault.  `TCR_EL1` gives a 32-bit input address range, `T0SZ` 32, so walks start at level 1 (Table D8-18, page D8-7711), with the 4 KiB granule, no walks through `TTBR1_EL1`, a 32-bit output range, and Non-cacheable walks.  The code writes the tables with the MMU off, as Device-nGnRnE accesses, so Non-cacheable walks read what it stored without cache maintenance, and it fills the stack and clears `.bss` after the MMU is on, as Cacheable writes.  The descriptors' fields are those of section D8.3.1.2 (pages D8-7739 to D8-7744), and the registers' those of sections D24.2.126, D24.2.174, and D24.2.193 (`MAIR_EL1` from page D24-9450, `SCTLR_EL1` from D24-9690, and `TCR_EL1` from D24-9904).

With RAM as Normal memory and `SCTLR_EL1.A` clear, an unaligned load or store of single or multiple registers is performed (section B2.8.2.1.1, page B2-312).  The rule excludes the Load-Exclusive, Store-Exclusive, Load-Acquire, Store-Release, and atomic instructions, `SETG*`, and the memory copy and set instructions, which keep alignment rules, and the 64-byte single-copy atomic and Read-Check-Write instructions fault on any unaligned address (section B2.8.2.1.2, page B2-313).  `tools/baremetal/access-check.sh` fails the build of a program or a corpus module whose assembly contains one of them, and CompCert's assembly of the programs of tests 2 and 7 and of every corpus module contains none.  The bare-metal path therefore needs no proof that the translated code makes only aligned accesses, which settles the translator's optional M7 alignment proof for bare metal.  Under KVM with the MMU on, the probe's unaligned load ran without a fault.

Semihosting is unavailable under KVM: the probe's `hlt #0xf000` raised `ESR_EL1` `0x02000000`, exception class 0, at `0x401000b8`, and the exception handler's own exit raised it again, so the run looped until its time limit.  Built with `PSCI_EXIT`, the startup code ends a run with PSCI `SYSTEM_OFF`, function ID `0x8400_0008` (Arm DEN0022E, section 5.1.9, page 36), through `hvc #0`.  The device tree names the conduit (DEN0022E, section 6.7, page 86), and QEMU 8.2.2 gives `method = "hvc"` under both accelerators, which the Linux binding defines as `HVC #0` with the binding's register assignments.  KVM turns the call into an exit to QEMU of type `KVM_SYSTEM_EVENT_SHUTDOWN` (Linux `Documentation/virt/kvm/api.rst`, section 5), and QEMU exits on a guest's shutdown unless given `-no-shutdown`.  QEMU's status is then 0, so the tests under KVM take the program's status from the report.  Builds for TCG keep semihosting, since QEMU's exit status is the program's there and the runs at EL2 and EL3 exit through it with status 254.

Outside every proof stay the startup code, the vectors and their reporting code, the linker script with its addresses and stack size, and, in test builds, a reporting routine in C that runs only after `main` returns or after an exception.  That routine is a second compilation unit outside the program of the theorem.  It shares only the UART's symbol with that program and runs only after `main` returns or after an exception has stopped it, so the deployment build replaces it with assembly.  The startup code runs `lx_report_exit`, `lx_report_exception`, and `lx_report_level` on the exception stack of 4 KiB, and the bound tool gives them 112, 128, and 96 bytes.  A fault in `lx_report_exit` enters the vectors, which start the exception's report from the top of the same stack and then exit, so no step reads the frames that they overwrite.

## Arguments not fixed in advance

A loader that writes input into a C global before the start makes the theorem's premise false.  CompCert's semantics starts from `init_mem`, which fixes the initial contents of every global, so a machine whose memory holds loaded bytes in a global starts from a state that no theorem describes.  Input must therefore come through volatile reads.  `volatile_load` of a volatile block returns an arbitrary value of the access's type and records it in the trace as `Event_vload` (`common/Events.v`, lines 557 to 565).

Milestone B7 implements inputs.  The program declares `extern volatile const unsigned char lx_in[];`, which `clightgen` describes as an array of no elements without initialization data, and the linker script places `lx_in` at `0x7000_0000` with 16 MiB of RAM after it and asserts that the stack ends below it.  QEMU's generic loader fills the region with `-device loader,file=FILE,addr=0x70000000,force-raw=on`.  The input is a length `n` of eight bytes, the lowest first, followed by `n` bytes, and `main` reads every byte with a volatile load of `unsigned char`.  The event value of such a load has type `int`, all of whose values the Lean copy's `eventval_match` covers, while a 64-bit volatile load could return a pointer event in CompCert (`ev_match_ptr`), which the copy omits, so a theorem over 64-bit loads would not cover every behaviour of the Asm program.

`inMain` (`LeanExe/Native/Bare.lean`) reads the length, returns 64 when it exceeds `inMax`, `2 ^ 24 - 8`, so that every read lies in the region that the loader fills, and calls `alloc`, the module's function 0, for the length word and `⌈n / 8⌉` words.  When `alloc` sets `lx_status`, `main` returns it.  Otherwise `main` stores the number of words at the returned address and the `n` bytes after it, and calls the entry on the address and `n`.  It then tests `lx_status` and writes the result as `bareMain` does.  The header that `alloc` writes, kind 2 and width 1, is the one that `Heap.Owned` of an array requires, `alloc` writes nothing in the payload, and `main` writes only the payload, so the array is owned by `main` and lent to the entry.

The design first gave the entry a parameter of type `LeanExe.Bytes`.  B7 replaces it with the packed form of the hashing library, an `Array UInt64` of the bytes eight to a word with the byte count, so that `main` calls the verified export `sha256` and its theorem unchanged.  Every export of the hashing library takes this form, so each gets a program with input without new compiled code, while an entry over `LeanExe.Bytes` for SHA-256 would need a compiled wrapper that packs the bytes and a proof of the packing.  The export returns `Words4`, four results in the result globals, and `main` writes them with the kind `words 4`.  The alternative, a compiled wrapper that packs the digest into an array as the SHA-256 program of B4 does, would call a new wrapper instead of the export, and `words` gives every export with several results a program.

`input_program` (`LeanExe/Native/Proof/Input.lean`) states, for every sequence `σ` of the 32-bit values that the loads read, that the program terminates with a trace and a result that `InResult` describes, given the run of the entry from the store after `main`'s writes that `EntryInRuns` states.  The trace begins with `inTrace σ 0 8`, the loads of the length, whose low bytes give `inLen σ`.  A length above `inMax` gives the result 64 after those loads, a trap of `alloc` gives the code 1 after them, a trap of the entry, when it may abort, gives the code 1 after the loads of the message as well, and otherwise the result is 0 and the loads are followed by the stores of the output.  `Reads σ t` holds of every such trace, the form of `reads` that `clight2_bigstep_asm_reads` takes.  `input_owned` gives the heap after the allocation and the writes: the allocator invariant, an owned array, and byte `i` of the array equal to byte `i` of the message.  `sha256_input` (`tests/TestSupport/Bare/Input.lean`) applies the theorem to the export `sha256`: for a length of at most `inMax`, the output is the 32 bytes of `SHS.SHA256.Impl.sha256` of the message, which `sha256_correct` equates with the digest of FIPS 180-4, or the code 1 when `alloc` traps.  The physical assumption is that each volatile read of the region returns the byte the loader placed there.

## The stack

CompCert's Asm semantics gives each frame a fresh block, so its theorem assumes that the stack never overflows.  The verified compiler bounds the nesting of calls: a guarded recursive function, and every function that calls one, takes the call depth, traps at `unreachable` when the depth reaches 1,000, and passes the depth plus one to the functions of this kind that it calls (`Verified/README.md`, lines 322 to 326).  The test comes after the callee's prologue, so at most 1,001 such frames nest below an entry.  Apart from the entries, which call such a function with depth 0, a function that does not take the depth calls none that does, since it would have no depth to pass, so those functions form an acyclic call graph below each chain.

`tools/baremetal/stack-bound.sh` computes a static bound from the assembly that `ccomp` prints.  `aarch64/Asmexpand.ml` emits a `.cfi_adjust_cfa_offset` for each part of a frame's allocation (lines 491 to 516), so a function's frame is the sum of its adjustments, and its callees are the targets of its `bl` and `b` instructions.  The tool fails on a call through a register and on a call of a function that the assembly does not define.  The translator lists the functions that take the depth, those whose code begins with the compiler's test of the depth (`Translation.depthNames`, after `guardCode` of `Verified/Compile.lean`), and the tool fails when a function on a cycle of the call graph is not in the list, since its recursion would have no bound.  The bound of a function is its deepest chain of calls, in which a function of the list at the depth 1,000 calls nothing and a function outside the list, an entry, calls one in it with the depth 0.  `tools/baremetal/build.sh` with `STACK_DEPTHS` fails when the bound of `main`, which covers every chain of calls from it, exceeds the stack size in the linker script.

| Module | Largest frame | Largest bound of a function | Largest stack of a call under QEMU | High-water mark under QEMU, with the test host |
| --- | --- | --- | --- | --- |
| `recursion` | 224 bytes | 224,336 bytes | 224,336 bytes | 230,144 bytes |
| `listrecursion` | 32 bytes | 32,048 bytes | 32,048 bytes | 37,840 bytes |
| `sha256` | 368 bytes | 816 bytes | 816 bytes | 6,624 bytes |
| `crc` | 16 bytes | 48 bytes | 48 bytes | 6,112 bytes |
| `euler` | 352 bytes | 1,760 bytes | 1,760 bytes | 7,568 bytes |
| `gpt` | 368 bytes | 944 bytes | not measured | not measured |

The bounds and the stacks of calls are those of the tool and of test 3.  In the check of the stack mark of `main` alone, the largest stack of a call equals the bound of its function in every module of the 82 with results but `fourier`, 368 bytes of 560, and `libfloatreductions`, 464 of 64,080, so the bounds are tight.  The later run on the merge of the bound in a temporary raised the bound of the largest call of `libsearch` from 16 bytes to 32 and that of `xxhash64` from 112 to 128, and each call still used its whole bound.  The test host's frames on the path to an exported function took 5,792 bytes in B1, and the glue's locals for the arguments add 16 bytes in some modules, which the whole stack's high-water mark shows: 230,144 bytes is 5,808 plus the 224,336 of `deep` at depth 0.  For `sha256` and `crc` the high-water mark lies in the host's own code.  The bound tool is unverified, so it joins the trusted base, and two tests back it.  In the corpus under QEMU, the glue measures each call of a module function: `lx_stack_mark` of the startup code fills the stack below the caller with the pattern, and `lx_stack_used` returns the bytes below it whose pattern changed, so the mark is the callee's alone, and a call whose mark exceeds its function's bound fails the test.  The report after `main` runs on the exception stack, so the whole stack's mark of a program of tests 2 and 7 covers `main` and its callees alone, and it must lie within the bound of `main`.  In the run of milestone B6, the largest bound of module code in the 98 translations of the corpus was the 224,336 bytes of `deep` in `recursion`, so a stack of 1 MiB holds more than four times any of them, and the latest run translated and built all 103 modules of the registry.  The test host needs more: its recursion over nested arguments reached 2,431,392 bytes in `taggedtypes` in the latest run, so `tests/baremetal/verified.sh` gives it 4 MiB.  The unmapped guard page below the stack turns an overflow into a level 3 translation fault when the overflowing frame's first access below the stack lands in that page.  Under KVM, a store to the word below the stack reported `ESR_EL1` `0x96000047`, exception class `0x25`, a write, and fault status `0b000111`, with that word's address in `FAR_EL1`.

## Trusted base

After the change, the trusted base is:

1. Lean's kernel, with `propext`, `Classical.choice`, and `Quot.sound`.
2. The Lean copy of the Clight subset, with the program-level judgment and volatile accesses, checked by review and by differential tests against `ccomp -interp`.
3. The C printer and the front end that `ccomp` and `clightgen` share, checked per build up to a renaming of identifiers, the transcription `exportStmt` of the statement printer of `clightgen`'s exporter (`export/ExportClight.ml`, lines 88 to 136), and the assumption that `ccomp`'s numbering of identifiers renames `clightgen`'s by a map injective on the program's own identifiers.
4. CompCert's Rocq proofs of the passes from Cshmgen to Asmgen, of `bigstep_semantics_sound`, and of Asm's determinacy, with CompCert's parameters and Coq's classical axioms, and Coq's kernel, which checks the composition and the uniqueness lemma.
5. CompCert's extraction to OCaml and its printer of assembly.
6. The GNU assembler and linker, and the linker script, with the addresses of `lx_out` and `lx_in`.
7. The startup code with its translation tables and its move to the exception stack before each of its reports, the exception vectors, and the reporting code of test builds.
8. The static stack bound, its tool, and the stack size, with the translator's list of the functions that take the call depth and the compiler's passing of the depth plus one to them.
9. CompCert's model of AArch64 in `aarch64/Asm.v` as a description of the processor.
10. QEMU, with KVM and the AArch64 hardware under KVM: the ELF loader, the generic loader of the input, the processor, and the UART's acceptance of each store to its data register.
11. QEMU's semihosting, for the exit status under TCG, and PSCI `SYSTEM_OFF` through KVM, which ends a run under KVM.
12. The absence from the compiled code of the instructions that require aligned accesses in Normal memory, which `tools/baremetal/access-check.sh` checks.

Compared with the translator's design, libc, the operating system, and the C host leave the trusted base, and `main` enters the proofs.  The startup code, the linker script, and the device's behaviour enter the trusted base.  The stack, an assumption about the size of a thread's stack in the translator's design, becomes a bound that a tool computes and the build compares with the stack it reserves.

## Test plan

1. **The corpus under QEMU.**  A freestanding build of `tools/native-host.c`, with small replacements for the parts of libc it uses, reads its command line from a block that QEMU's generic loader places in RAM and runs each case of `tests/native/verified.sh` in its own QEMU process.  Each case must give the line that the Wasmtime host and the native host give, under the same rules for traps and allocation counters.  `tests/baremetal/verified.sh` does this with `tools/baremetal/libc`, `JOBS` QEMU processes at a time, 4 by default.  In milestone B1, all 32,547 cases that ran passed in 1,512 seconds, and the 3,581 others called functions that use binary32 forms.  In the latest run that the journal records, on 2026-10-29 with 16 processes at a time, all 39,088 cases of the 82 modules with cases passed in 1,538 seconds, the module cases of `euler` and `sums` included, and no case was left unrun.  The test host lies outside the proofs, as the native host does.
2. **Programs with generated `main`.**  GCD on constants, CRC-32 of `123456789`, SHA-256 of `abc`, an Euler solve, and a recursion that reaches the depth limit run under QEMU.  The UART's bytes and the exit status must equal `encode` of the Lean result and Talos's result of the same entry, or, for a run that Talos ends at `unreachable`, be no byte and the code 1, and each program's theorem must check with the three standard axioms.  `tests/baremetal/programs.sh` runs this test.
3. **Stack.**  For every corpus module, the stack of every call of a module function in every case must stay within its function's static bound, the deep recursion cases at depths 999 and 1,000 included.  `tests/baremetal/verified.sh` runs this test.
4. **The Lean copy.**  The differential tests compare volatile stores and volatile loads with `ccomp -interp` on AArch64 and x86-64.
5. **The per-build check.**  `clightgen` reads the whole program, CompCert's declarations and `main` included, and the check compares it with `bareProgram` up to renaming.
6. **The checks themselves.**  A build without the FP enable, a store to the guard page, a stack below the bound, and a UART address that differs from the device tree must each fail visibly.
7. **Inputs.**  The program with input around SHA-256 runs under QEMU on messages of 0, 3, 55, 56, 63, 64, 65, 1,000, 65,536, 1,048,576, and `2 ^ 24 - 8` bytes, whose output must be the digest that `sha256sum` computes, and on the lengths `2 ^ 24 - 7` and `2 ^ 64 - 1`, which must give no output and the status 64.  `tests/baremetal/inputs.sh` runs this test.
8. **AArch64 hardware under KVM.**  With `ACCEL=kvm`, `tests/baremetal/run.sh`, `programs.sh`, and `inputs.sh` build with `PSCI_EXIT` and run under KVM, and the probes, the programs of test 2, and the program with input must give the results that they give under TCG.  The device tree must name PSCI with the method `hvc` and give the RAM of the linker script.

## Milestones and exit criteria

| Milestone | Work | Exit criterion |
| --- | --- | --- |
| B0 · Toolchain | `tools/baremetal/`: startup code, linker script, build script, the device-tree check | the experiment's programs build from the repository and run under QEMU |
| B1 · Corpus under QEMU | the freestanding test host and a driver beside `tests/native/verified.sh` | every translated case of the corpus and every module case passes under QEMU |
| B2 · Lean copy | the program-level judgment, volatile stores, their differential tests | no difference from `ccomp -interp` in either CompCert configuration |
| B3 · Whole program | `bareProgram`, the prefix of external declarations, `init_mem` and `start` for it, the renaming lemma, the check on the whole program | `start` holds for `bareProgram` of every corpus module, and the check passes for all of them |
| B4 · Generated `main` | the `main` writer, its proof, and `p.f.program` from the command `bare_program` | the programs of test 2 run under QEMU with their theorems |
| B5 · Rocq | `clight2_bigstep_to_asm` and the uniqueness lemma, built against CompCert 3.18's proofs | both check with the assumptions recorded |
| B6 · Stack bound | the bound tool, its cross-check with the translator, and the build's test | test 3 passes for every corpus module |
| B7 · Inputs (optional) | volatile loads, the theorem about `alloc` and stores, the quantified theorem, and the uniqueness lemma for traces with inputs | SHA-256 of a loaded message, with its theorem |
| B8 · KVM | the MMU with an identity map and a guard page, the PSCI exit, the tests' KVM mode, and the check for instructions that require alignment | under KVM with the MMU on, the programs of test 2 and the program with input pass, the unaligned probe runs without a fault, and the guard probe takes a translation fault |

B0 and B1 need no new Lean code and can start at once.  B2 and B5 are independent of each other.  B3 carries the most risk, because it generalizes the proofs of `Init.lean` from the translation's own program to one with a prefix and two more definitions.  B4 depends on B2 and B3.

| Component | Estimate |
| --- | --- |
| Lean copy additions (B2) | 300 to 600 lines of Lean |
| Whole program and renaming (B3) | 1,000 to 2,000 lines of Lean |
| `main`, its proof, and the command (B4) | 800 to 1,500 lines of Lean |
| Rocq (B5) | about 250 lines |
| Startup, linker script, test host, and bound tool (B0, B1, B6) | about 600 lines of assembly, C, and shell |
| Inputs (B7) | 1,000 to 2,000 lines of Lean |

These figures are estimates.

## Open decisions

| Question | Recommendation |
| --- | --- |
| Do the Rocq files of B5 belong in the repository?  They add a build that needs a CompCert 3.18 tree with its proofs compiled. | Yes, in a directory of their own, checked by a script that takes the tree's path, outside the default build. |
| A renaming lemma in Lean (B3), or a per-build check that treats the renaming as trusted? | The lemma, since the numbering differs between `clightgen` and `ccomp` in any case and the lemma covers every injective renaming. |
| How does output reach a device on a board, where `main` cannot wait for the UART? | Decide with a board in hand.  B8 runs under KVM, where QEMU's UART takes every store. |
| Are inputs not fixed in advance (B7) in scope? | Yes, as B7 implements them: a packed array for the hashing library's exports, and `LeanExe.Bytes` when an entry needs it. |
| The MMU on QEMU: off, or on, which would give QEMU's runs a board's memory types? | On in every build, decided at B8.  Under KVM an unaligned load faulted with the MMU off, and one startup path lets the runs under TCG test the code that runs on hardware. |
| A proof that the translated code makes only aligned accesses, the translator's optional M7 alignment proof? | None for bare metal, decided at B8.  With RAM as Normal memory and `SCTLR_EL1.A` clear, unaligned loads and stores of single or multiple registers are performed (B2.8.2.1.1), and `tools/baremetal/access-check.sh` excludes the instructions that keep alignment rules. |
| The entry's form: scalar constants in `main`, heap constants inside a Lean definition without parameters, and a result of type `UInt64` or `Array UInt64` | As designed, with other result types encoded in Lean. |
| The UART's address: fixed in the linker script and checked against QEMU's device tree by the test harness, or read from the device tree at startup? | The linker script and the harness's check. |
| Programs with byte literals, whose theorem is `ImplementsStatic`, in the command `bare_program`? | Add the case when a program needs it, decided on 2026-10-28.  No program of test 2 or of the input test needs it, and code that no program uses has no test behind it. |

## Sources

- CompCert 3.18, the release archive whose digests the translator's notes record: `configure`; `runtime/Makefile`; `driver/Compiler.v`, `Complements.v`, `Linker.ml`, `Interp.ml`; `cfrontend/Clight.v`, `ClightBigstep.v`, `Cshmgenproof.v`, `SimplExpr.v`, `C2C.ml`, `Ctypes.v`; `common/Events.v`, `Globalenvs.v`, `Values.v`, `Behaviors.v`, `Smallstep.v`; `aarch64/Asm.v`, `Asmexpand.ml`, `SelectLong.vp`; `x86/SelectLong.vp`; `backend/SplitLong.vp`; `lib/Camlcoq.ml`; `export/ExportDriver.ml`
- QEMU, the `virt` machine: https://www.qemu.org/docs/master/system/arm/virt.html
- QEMU, the generic loader: https://www.qemu.org/docs/master/system/generic-loader.html
- QEMU, semihosting: https://www.qemu.org/docs/master/about/emulation.html
- QEMU, Raspberry Pi machines: https://www.qemu.org/docs/master/system/arm/raspi.html
- Arm, semihosting specification (`HLT #0xF000`, `SYS_EXIT`, `ADP_Stopped_ApplicationExit`): https://github.com/ARM-software/abi-aa/blob/main/semihosting/semihosting.rst
- Arm, `CPACR_EL1`: https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/CPACR-EL1--Architectural-Feature-Access-Control-Register
- Arm Architecture Reference Manual for A-profile architecture, DDI 0487 issue M.d: sections B2.8.2, B2.8.2.1.1, and B2.8.2.1.2, alignment of data accesses and unaligned accesses to Normal memory (pages B2-312 and B2-313); D7.5.6, caches at reset (page D7-7650); D8.2.8, Table D8-18, the initial lookup level of the 4KB granule (page D8-7711); D8.2.12.1, behavior when stage 1 address translation is disabled (page D8-7730); D8.3.1.2, block and page descriptors (pages D8-7739 to D8-7744); D8.16.1, TLB behavior at reset (page D8-7852); D24.2.126, D24.2.174, and D24.2.193, `MAIR_EL1`, `SCTLR_EL1`, and `TCR_EL1` (pages D24-9450, D24-9690, and D24-9904): https://developer.arm.com/documentation/ddi0487/latest
- Arm Power State Coordination Interface, DEN0022E: sections 5.1.9, `SYSTEM_OFF` (page 36), 5.10 (page 58), and 6.7, discoverability (page 86): https://developer.arm.com/documentation/den0022/latest
- Linux, the device-tree binding of PSCI, `Documentation/devicetree/bindings/arm/psci.yaml`: https://github.com/torvalds/linux/blob/master/Documentation/devicetree/bindings/arm/psci.yaml
- Linux, the KVM API, section 5, `KVM_EXIT_SYSTEM_EVENT`: https://docs.kernel.org/virt/kvm/api.html
- QEMU, invocation, `-no-shutdown` and `-action`: https://www.qemu.org/docs/master/system/invocation.html
- QEMU issue 1204, unaligned accesses with the MMU off: https://gitlab.com/qemu-project/qemu/-/issues/1204
- Multiboot specification, the machine state at entry: https://www.gnu.org/software/grub/manual/multiboot/multiboot.html
