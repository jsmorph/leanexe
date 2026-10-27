# LeanExe native code on bare metal: design and plan

2026-10-27 · Jamie Stephens

## Goal and end-to-end statement

[The translator's design](native-translator.md) ends at `p.f.native`, a theorem about one call of one C function in the Lean copy of CompCert's Clight.  A C host, linked with libc and run under an operating system, places that call's arguments and reads its results, outside every proof.  This design replaces the host, libc, and the operating system with a startup routine of about fifty instructions and a `main` that the translator writes and proves.  The binary runs on QEMU's `virt` machine for AArch64 and, in a later milestone, on a board.  The goal is one theorem per program that states the program's whole observable behaviour in the terms of CompCert's semantics, and an argument, checked in Rocq where CompCert's proofs reach, that carries the theorem to the Asm program that `ccomp` produces.

The program is the translation of a module, a volatile global `lx_out` that the linker places at the UART's data register, and a generated `main`.  `main` calls `lx_init`, calls an entry `run` that the verified compiler compiled, on arguments fixed when the program is built, and writes the bytes of the result to `lx_out`.  The theorem `p.run.program` has two cases.  Either the program terminates with result 0 and a trace of one volatile store per byte of the result's encoding, or, when `run` may abort, it terminates with result 1 and an empty trace.  The design covers no interrupts, no second core, no input device other than a memory region that a loader fills, and no timing.

| Step | From | To | Covered by |
| --- | --- | --- | --- |
| 1 | Lean definition | `p.run.native` | the existing proofs |
| 2 | `p.run.native` | `bigstep_program_terminates` of the whole program in the Lean copy | a new Lean proof, described below |
| 3 | the Lean copy | CompCert's `Clight2.bigstep_program_terminates` of the program that `clightgen` reads | review, differential tests, the per-build check, and a renaming lemma |
| 4 | the program that `clightgen` reads | the program that `ccomp` compiles | trusted: one front end, with identifiers numbered differently |
| 5 | Clight big-step termination | the behaviour of the Asm program | a composition of CompCert's proofs in Rocq, proved in the experiments |
| 6 | the Asm program | the machine | trusted: printer, assembler, linker, startup code, CPU, and UART |

## Target machine

The target is AArch64, on QEMU's `virt` machine with a Cortex-A57 and 1 GiB of RAM, compiled with CompCert's `aarch64-linux` configuration.  Boards follow as an optional milestone.  CompCert 3.18 has no bare-metal configuration for any 64-bit target: its `configure` lists `-eabi` variants only for PowerPC and 32-bit ARM (lines 43 to 62).  The Lean copy fixes `ptr64 = true`, so x86-64, RISC-V, and AArch64 remain, and AArch64 needs the least outside the proofs:

| Target | CompCert run-time functions that the translations need | The Lean copy | Startup |
| --- | --- | --- | --- |
| AArch64 | none: `runtime/Makefile` builds only `vararg.o` for it (line 26), and a translated module links with no library | `Archi.aarch64`, with the corpus passing natively on AArch64 | QEMU enters the image at EL1 |
| x86-64 | `__compcert_i64_dtou` and `__compcert_i64_utod`, which `backend/SplitLong.vp` calls for unsigned conversions (lines 136 and 140), since `x86/SelectLong.vp` selects none of its own.  The library is compiled outside CompCert's proofs | `Archi.x86_64` | a Multiboot loader enters in 32-bit protected mode with paging off, so page tables must exist before any CompCert code runs in 64-bit mode |
| RISC-V 64 | not checked.  `runtime/Makefile` builds the whole set of 64-bit helpers for RISC-V (line 28) | no `Archi` instance, so a new one and new differential tests | not tested |

`ccomp` passes the link to gcc and accepts `-nostdlib`, `-static`, `-T` with a linker script, and `-Wl,` (`driver/Linker.ml`, lines 66 to 95).  It always appends `-L<stdlib> -lcompcert` (lines 21 to 30), but on AArch64 that library holds only the variadic-argument helpers, which no translation calls.  In the experiments, the object file of the translation of each of eight corpus modules had no undefined symbol, and only the test host's replacement for `printf` drew on CompCert's library, for the variadic-argument helpers.  The generated code runs from RAM: QEMU's ELF loader writes `.text`, `.rodata`, and `.data` at their link addresses, so the startup code copies nothing.

QEMU documents two fixed addresses of `virt` for bare-metal guests, flash at 0 and RAM at `0x4000_0000`, and places the device tree at the start of RAM.  Every other device address may change between QEMU versions and must come from the device tree.  The image is linked at `0x4010_0000`, above the device tree.  The UART address is fixed in the linker script, and the test harness compares it with the device tree that `-machine virt,dumpdtb=FILE` writes for the QEMU in use: QEMU 8.2.2 gives `pl011@9000000` with `reg = <0x00 0x9000000 0x00 0x1000>` and `stdout-path = "/pl011@9000000"`.  Reading the device tree at startup would avoid the check at the cost of a parser in the trusted startup code.

A board differs in four ways, each outside the proofs: the exception level at entry, the UART's address and setup, the RAM base, and the need for the MMU and caches, without which every data access is uncached.  QEMU 8.2.2 emulates the Raspberry Pi 3B (`raspi3b`, Cortex-A53) but not the 4B, which newer QEMU documentation lists.  The project has not chosen a board, and the board milestone starts with that choice.

## The generated main and its outputs

The translator writes `main` after the translation's functions, in the same C file, so that `ccomp` compiles one whole program and `transf_c_program` covers it in one run.  `main` never takes the address of a local, so SimplLocals turns its locals into temporaries, as it does for the translation's functions.  For an entry `run` with scalar parameters and an `Array UInt64` result, `main` is:

```c
extern volatile unsigned int lx_out;

int main(void) {
  unsigned long long r, n, i;
  lx_init();
  r = lxf_run(7ULL, 9ULL);                 /* the arguments fixed at build time */
  if (lx_status != 0U) return (int) lx_status;
  n = /* the word at r, by the translator's load64 code */;
  n = 8ULL * n + 8ULL;                     /* the length word and the elements */
  i = 0ULL;
  for (;;) {
    if (!(i < n)) break;
    lx_out = (unsigned int) ((unsigned char *) lx_mem)[r + i];
    i = i + 1ULL;
  }
  return 0;
}
```

For a `UInt64` result, eight stores `lx_out = (unsigned int) ((r >> 8k) & 255ULL)` replace the loop.  The output is the array's representation in `lx_mem`, the length word and then the elements, little-endian, which `Heap.Owned` and `MemRel` describe byte by byte.  Byte loads need no alignment fact about `r`.  Other result types reach this form through a Lean function that encodes them as an `Array UInt64`, compiled with the rest of the program, so that `main` and its proof stay the same for every program.

Arguments fixed in advance take two forms.  A scalar argument is a constant in the call.  A heap argument, such as an array or a byte string, is a constant inside a Lean definition without parameters, `def run : Array UInt64 := encode (f input)`, for which the reflector's theorems take the argument type `Unit` (`Verified/README.md`, lines 772 and 773).  The verified compiler compiles the constant with the rest of the definition, and `p.run.implements` covers the construction of the value.  `main` therefore places nothing in `lx_mem` before the call, and no theorem about a sequence of host calls is needed.  Whether the reflector accepts every such definition is checked in milestone B4.

The program can report results in four ways, and CompCert's semantics observes two of them:

| Channel | In CompCert's behaviour | Use |
| --- | --- | --- |
| The `int` that `main` returns | yes: `Terminates t r` carries `r` | 0, or the trap code of `lx_status`.  The startup code passes `w0` to QEMU's exit status through semihosting |
| Volatile stores to a volatile global | yes: each is an event `Event_vstore chunk id ofs v` of the trace, which every pass preserves | the result's bytes, through `lx_out` at the UART's data register |
| A memory region read after the program halts, by a debugger or QEMU's monitor | no: `program_behaves` records only the trace and the result, so CompCert's theorem says nothing about final memory | none |
| Semihosting calls from C, such as `SYS_WRITEC` | only as an external call, whose event and result come from `external_functions_sem`, a parameter of CompCert.  The Lean theorems hold for every such semantics and so conclude nothing about a call to one | the startup code's exit call, outside the proofs |

A volatile store reaches the trace as follows.  C2C gives an `extern volatile` declaration an empty initializer and `gvar_volatile = true` (`cfrontend/C2C.ml`, lines 1278, 1279, and 1305 to 1307).  SimplExpr turns an assignment to a volatile lvalue into `Sbuiltin None (EF_vstore chunk)` with the lvalue's address and the value (`cfrontend/SimplExpr.v`, lines 184 to 226), and the experiment's `clightgen` output shows this form for a store to `lx_out`.  `volatile_store` of a block that `Senv.block_is_volatile` marks emits `Event_vstore` and leaves memory unchanged, with no permission check (`common/Events.v`, lines 571 to 583).  The assembler and linker resolve `lx_out` by name to the address in the linker script, so the event means a 32-bit store to that address.

On QEMU, the PL011 model passed every byte to its output in the experiments.  On hardware the transmitter can be busy when `main` writes, and `main` cannot wait for it: a volatile read of the UART's flag register is an input event whose value the theorem would have to quantify over, and a loop that waits on it has no termination proof.  The board milestone has to settle how output reaches a device that may not accept every write.

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

The program is `bareProgram pre T args`: CompCert's external declarations `pre`, the translation's definitions in the order of the C text, the declaration of `lx_out`, and `main`, with `prog_main` naming `main`.  `clightgen` puts its declarations of CompCert's built-in and run-time functions first, among them `__builtin_fsqrt`, which the translation now places between `lx_pun` and the result globals, so that declaration moves into `pre`.  The theorem holds for every `pre` of external function declarations whose identifiers are distinct from the program's and which declares `__builtin_fsqrt` at its signature, and the per-build check confirms that the program `clightgen` reads has that shape.

```lean
theorem p.run.program (A : Archi) (X : ExtSem) (pre) (hpre : PrefixOk pre) :
    bigstep_program_terminates A X (bareProgram pre p.translation args)
        (outTrace (encode (run args))) 0 ∨
      (aborts = true ∧ bigstep_program_terminates A X (bareProgram pre p.translation args) E0 1)
```

`encode xs` is the eight bytes of `xs.size` followed by the eight bytes of each element, and `outTrace` maps each byte `b` to `Event_vstore Mint32 outId 0 (EVint b)`.  The proof follows `main`'s body: `init_mem` of the whole program, with the prefix and `lx_out` before and after the translation's blocks; `lx_init_correct` for the call of `lx_init`; `p.run.native` for the call of the entry, with the premises that `start` already proves for the state after `lx_init`; the test of `lx_status`; a loop lemma that produces one event per byte from `Heap.Owned` and `MemRel`; and `outcome_result_value` for the returned `int`.

### What the Lean copy must add

| Addition | CompCert 3.18 source |
| --- | --- |
| `bigstep_program_terminates` and `type_int32s` | `cfrontend/ClightBigstep.v`, lines 252 to 260; `cfrontend/Ctypes.v`, line 259 |
| `Genv.find_var_info` and `Genv.block_is_volatile` | `common/Globalenvs.v`, lines 211 and 217 |
| `eventval_match` for `EVint` and `EVlong` | `common/Events.v`, line 270 |
| `Val.load_result` | `common/Values.v`, line 1069 |
| `volatile_store`, `volatile_store_sem`, and the case `EF_vstore` of `external_call` | `common/Events.v`, lines 571 to 583, 820 to 824, and 1530 |
| for inputs only: `volatile_load`, `volatile_load_sem`, and the case `EF_vload` | `common/Events.v`, lines 557 to 569, 709 to 713, and 1529 |
| a renaming lemma: `bigstep_program_terminates A X p t r` implies the same of `p.rename ρ` with the trace renamed, for every injective `ρ` | none |

`external_call` passes `ExtSem` the symbol table alone today, and the volatile cases also need the volatility of blocks, so it gains the global environment's variable information while `ExtSem` keeps its type.  The differential test of the copy gains volatile stores and loads, compared with `ccomp -interp -trace 1`, which prints each volatile event (`driver/Interp.ml`, lines 62 to 68).  The interpreter treats a volatile variable as memory (lines 568 to 582), so the test programs define `lx_out` instead of declaring it `extern`, which leaves the semantics of the store unchanged.

### From the Lean theorem to the machine code

**The program `clightgen` reads.**  The per-build check compares the whole program, prefix and `main` included, with `bareProgram`, up to an injective renaming of identifiers, and the renaming lemma moves the theorem across it.  The check's current rule, which ignores CompCert's external declarations, changes accordingly.

**The program `ccomp` compiles.**  `clightgen` numbers identifiers by a canonical encoding of their names (`export/ExportDriver.ml`, line 207, and `lib/Camlcoq.ml`, lines 288 to 301 and 337 to 345), and SimplExpr's temporaries then start at 128.  `ccomp` numbers names from 1 in the order it meets them, and its temporaries start after the last name (`lib/Camlcoq.ml`, lines 374 to 377).  The Clight program that `clightgen` prints and the one inside `ccomp` therefore differ by a renaming of identifiers, if the two front ends otherwise agree.  The renaming lemma holds for every injective renaming, so the trusted assumption shrinks to this: for the same C text, the Csyntax program `p` inside `ccomp` is the one inside `clightgen` with its identifiers renamed injectively.

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

**Uniqueness.**  `clight2_bigstep_to_asm` shows that the Asm program can terminate with `t` and `r`, not that it cannot do something else.  Asm's semantics is determinate (`aarch64/Asm.v`, line 1282): two steps from one state match in their events and, with equal events, reach one state.  For a trace of volatile stores, `match_traces` holds only between equal events (`common/Events.v`, lines 505 to 517), so every run from the initial state follows the terminating run, and a planned Rocq lemma, an estimated 150 lines, concludes that every behaviour of `Asm.semantics tp` is `Terminates t r`.  With the volatile loads of the section on arguments not fixed in advance, runs differ only in the values read, and the lemma states the behaviour for each sequence of values.

**What the Asm behaviour says.**  The initial state has the memory of `Genv.init_mem tp`, the program counter at `main`, the return address and stack pointer null, and every other register undefined (`aarch64/Asm.v`, lines 1238 to 1247).  A final state has the program counter null and `X0` holding `Vint r` (lines 1249 to 1253), the low 32 bits of the register.  Each stack frame is a fresh block of unbounded memory, so the semantics has no stack size.  Under the assumptions that the section on the trusted base lists, the processor that runs `main` performs exactly the stores of `t` to the address of `lx_out`, in order, and returns to the startup code with `r` in `w0`.  Nothing follows about time, about memory outside the trace, or about a run whose stack overflows.

## Startup code

The startup code is GNU assembly, about fifty instructions and a table of exception vectors, linked first:

| Step | Instructions | Reason |
| --- | --- | --- |
| Check the exception level | `mrs CurrentEL` | QEMU enters the image at EL1, as the experiment found.  At another level the code stops with a message |
| Mask interrupts | `msr daifset, #0xf` | DAIF was `0x3c0`, all masked, at entry under QEMU.  A board's firmware may differ |
| Install the vectors | `msr VBAR_EL1` | 16 entries of 128 bytes at a 2 KiB boundary.  Each reports `ESR_EL1`, `ELR_EL1`, and `FAR_EL1` and exits with status 255 |
| Enable floating point | `CPACR_EL1.FPEN = 0b11`, then `isb` | FPEN's reset value is unknown.  Without this step `main` trapped at its third instruction with exception class `0x07` |
| Set the stack | `mov sp, __stack_top` | `SCTLR_EL1.SA` was 1 at entry, so the stack pointer must stay 16-byte aligned |
| Clear `.bss` | a loop of `stp xzr, xzr` | `lx_mem` and the uninitialized globals lie in `.bss`, and `init_mem` gives them zeros |
| Fill the stack with a pattern | test builds only | the high-water mark that the section on the stack uses |
| Call `main` | `bl main` | |
| Exit | semihosting `SYS_EXIT` with `ADP_Stopped_ApplicationExit` and `w0` | QEMU exits with `main`'s result.  A board waits in a loop of `wfe` after writing the result to the UART |

The MMU and the caches stay off on QEMU: `SCTLR_EL1` was `0x00c50838` at entry, with `M`, `C`, and `I` clear.  With stage 1 translation off, the architecture gives every data access the memory type Device-nGnRnE, which allows no unaligned access, as QEMU issue 1204 quotes from section D8.2.10 of the Arm Architecture Reference Manual, issue I.a.  The translator issues an 8-byte access only at a multiple of 8 and byte accesses otherwise, and CompCert's frames are aligned, but QEMU 8.2.2 did not fault on an unaligned 8-byte load with the MMU off, so tests on QEMU cannot find such an access.  On a board the MMU must be on for speed, with an identity map of RAM as normal write-back memory and of the UART as device memory, and with an unmapped page below the stack.  That adds page tables and their setup, an estimated eighty instructions, to the trusted code.

Outside every proof stay the startup code, the vectors and their reporting code, the linker script with its addresses and stack size, and, in test builds, a reporting routine in C that runs only after `main` returns or after an exception.  That routine is a second compilation unit outside the program of the theorem.  It shares only the UART's symbol with that program and runs only after `main` returns or after an exception has stopped it, so the deployment build replaces it with assembly.

## Arguments not fixed in advance

A loader that writes input into a C global before the start makes the theorem's premise false.  CompCert's semantics starts from `init_mem`, which fixes the initial contents of every global, so a machine whose memory holds loaded bytes in a global starts from a state that no theorem describes.  Input must therefore come through volatile reads.  `volatile_load` of a volatile block returns an arbitrary value of the access's type and records it in the trace as `Event_vload` (`common/Events.v`, lines 557 to 565).

The design for inputs, milestone B7, places an `extern volatile const unsigned char lx_in[]` at a fixed address in the linker script, which QEMU's generic loader fills with `-device loader,file=FILE,addr=ADDR,force-raw=on`.  `main` reads a length and the bytes with volatile loads, allocates an array through the module's `alloc`, stores the bytes into it, and calls an entry whose parameter is `LeanExe.Bytes`.  The theorem then quantifies over the input: for every sequence of bytes up to a bound, the program terminates with a trace of the loads of those bytes followed by the stores of the output of `run` on the decoded input.  Three pieces are new: (a) `EF_vload` in the Lean copy; (b) a theorem that `alloc` followed by byte stores gives a store in which `Represent.borrowed` of the bytes holds, the theorem about a sequence of host calls that the translator's notes list as missing; and (c) the uniqueness lemma for traces with input events.  The physical assumption is that each volatile read of the region returns the byte the loader placed there.  The plan defers inputs until the fixed-argument path works end to end.

## The stack

CompCert's Asm semantics gives each frame a fresh block, so its theorem assumes that the stack never overflows.  The verified compiler bounds the nesting of calls: a guarded recursive function, and every function that calls one, takes the call depth, traps at `unreachable` when the depth reaches 1,000, and passes the depth plus one to the functions of this kind that it calls (`Verified/README.md`, lines 322 to 326).  The test comes after the callee's prologue, so at most 1,001 such frames nest below an entry.  Apart from the entries, which call such a function with depth 0, a function that does not take the depth calls none that does, since it would have no depth to pass, so those functions form an acyclic call graph below each chain.

A static bound follows from the assembly that `ccomp` prints.  `aarch64/Asmexpand.ml` emits a `.cfi_adjust_cfa_offset` for each part of a frame's allocation (lines 491 to 516), so a function's frame is the sum of its adjustments, and its callees are the targets of its `bl` and `b` instructions.  A function takes the depth when it reaches a cycle of the call graph, and the bound of a function is its deepest chain of calls with at most 1,001 frames of functions that take the depth.  The tool must also check, against the translator's list of functions that take the depth, that every function on a cycle takes it, since recursion without the depth would have no bound.  The build fails when the bound of `main`, which covers every chain of calls from it, exceeds the stack size in the linker script.

| Module | Largest frame | Largest bound of a function | High-water mark under QEMU, with the test host |
| --- | --- | --- | --- |
| `recursion` | 224 bytes | 224,544 bytes | 230,128 bytes |
| `listrecursion` | 32 bytes | 32,048 bytes | 37,840 bytes |
| `sha256` | 368 bytes | 816 bytes | 6,608 bytes |
| `crc` | 16 bytes | 48 bytes | 6,112 bytes |
| `euler` | 352 bytes | 1,760 bytes | 7,552 bytes |
| `gpt` | 368 bytes | 944 bytes | not measured |

The test host's frames on the path to an exported function take 5,792 bytes: 2,448 for the replacement `main`, 3,296 for the host's `main` with its argument and result arrays, 16 for `invoke`, and 32 for the glue function.  For three modules the high-water mark equals that sum plus the bound of the export that the deepest case calls: 230,128 bytes is 5,792 plus the 224,336 of `deep` at depth 0, 37,840 bytes is 5,792 plus 32,048, and 7,552 bytes is 5,792 plus the 1,760 of the Euler solver.  For `sha256` and `crc` the high-water mark lies in the host's own code.  The bound tool is unverified, so it joins the trusted base, and two checks back it: in test builds the startup code fills the stack with a pattern and reports the high-water mark, and a run whose mark exceeds the bound fails the test.  A stack of 1 MiB holds more than four times the largest bound in the sample, and on a board with the MMU on, an unmapped page below the stack turns an overflow into a fault.

## Trusted base

After the change, the trusted base is:

1. Lean's kernel, with `propext`, `Classical.choice`, and `Quot.sound`.
2. The Lean copy of the Clight subset, with the program-level judgment and volatile accesses, checked by review and by differential tests against `ccomp -interp`.
3. The C printer and the front end that `ccomp` and `clightgen` share, checked per build up to a renaming of identifiers, and the assumption that `ccomp`'s numbering of identifiers is an injective renaming of `clightgen`'s.
4. CompCert's Rocq proofs of the passes from Cshmgen to Asmgen, of `bigstep_semantics_sound`, and of Asm's determinacy, with CompCert's parameters and Coq's classical axioms, and Coq's kernel, which checks the composition and the uniqueness lemma.
5. CompCert's extraction to OCaml and its printer of assembly.
6. The GNU assembler and linker, and the linker script.
7. The startup code, the exception vectors, and the reporting code of test builds.
8. The static stack bound, its tool, and the stack size.
9. CompCert's model of AArch64 in `aarch64/Asm.v` as a description of the processor.
10. QEMU, or the board: the ELF loader, the processor, and the UART's acceptance of each store to its data register.
11. QEMU's semihosting, for the exit status in tests.

Compared with the translator's design, libc, the operating system, and the C host leave the trusted base, and `main` enters the proofs.  The startup code, the linker script, and the device's behaviour enter the trusted base.  The stack, an assumption about the size of a thread's stack in the translator's design, becomes a bound that a tool computes and the build compares with the stack it reserves.

## Test plan

1. **The corpus under QEMU.**  A freestanding build of `tools/native-host.c`, with small replacements for the parts of libc it uses, reads its command line from a block that QEMU's generic loader places in RAM and runs each case of `tests/native/verified.sh` in its own QEMU process.  Each case must give the line that the Wasmtime host and the native host give, under the same rules for traps and allocation counters.  In the experiment, all 1,463 cases of six modules, `libsort`, `crc`, `sha256`, `recursion`, `listrecursion`, and `calls`, passed in 292 seconds, and all 3,322 module cases of `euler` and of `shapes` on `sums` passed in 643 seconds, about 0.2 seconds per case.  The test host lies outside the proofs, as the native host does.
2. **Programs with generated `main`.**  GCD on constants, CRC-32 of `123456789`, SHA-256 of `abc`, an Euler solve, and a recursion that reaches the depth limit run under QEMU.  The UART's bytes and the exit status must equal `encode` of the Lean result, which `#eval` computes, and the Wasmtime result of the same entry, and each program's theorem must check with the three standard axioms.
3. **Stack.**  For every corpus module, the static bound must exceed the high-water mark of every case, the deep recursion cases at depths 999 and 1,000 included.
4. **The Lean copy.**  The differential tests gain volatile stores and, for inputs, volatile loads, against `ccomp -interp -trace 1` on AArch64 and x86-64.
5. **The per-build check.**  `clightgen` reads the whole program, CompCert's declarations and `main` included, and the check compares it with `bareProgram` up to renaming.
6. **The checks themselves.**  A build without the FP enable, a stack below the bound, and a UART address that differs from the device tree must each fail visibly.

## Milestones and exit criteria

| Milestone | Work | Exit criterion |
| --- | --- | --- |
| B0 · Toolchain | `tools/baremetal/`: startup code, linker script, build script, the device-tree check | the experiment's programs build from the repository and run under QEMU |
| B1 · Corpus under QEMU | the freestanding test host and a driver beside `tests/native/verified.sh` | every translated case of the corpus and every module case passes under QEMU |
| B2 · Lean copy | the program-level judgment, volatile stores, their differential tests | no difference from `ccomp -interp` in either CompCert configuration |
| B3 · Whole program | `bareProgram`, the prefix of external declarations, `init_mem` and `start` for it, the renaming lemma, the check on the whole program | `start` holds for `bareProgram` of every corpus module, and the check passes for all of them |
| B4 · Generated `main` | the `main` writer, its proof, and `p.run.program` from a command | the programs of test 2 run under QEMU with their theorems |
| B5 · Rocq | `clight2_bigstep_to_asm` and the uniqueness lemma, built against CompCert 3.18's proofs | both check with the assumptions recorded |
| B6 · Stack bound | the bound tool, its cross-check with the translator, and the build's test | test 3 passes for every corpus module |
| B7 · Inputs (optional) | volatile loads, the theorem about `alloc` and stores, the quantified theorem | SHA-256 of a loaded message, with its theorem |
| B8 · Board (optional) | MMU, guard page, the board's entry and UART, the output question of the section on `main` | the programs of test 2 on a board |

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
| How does output reach a device on a board, where `main` cannot wait for the UART? | Decide at B8, with the board in hand. |
| Are inputs not fixed in advance (B7) in scope? | Yes, after B4, as designed. |
| The MMU on QEMU: off, or on, which would give QEMU's runs a board's memory types? | Off on QEMU, on for a board. |
| The entry's form: scalar constants in `main`, heap constants inside a Lean definition without parameters, and a result of type `UInt64` or `Array UInt64` | As designed, with other result types encoded in Lean. |
| The UART's address: fixed in the linker script and checked against QEMU's device tree by the test harness, or read from the device tree at startup? | The linker script and the harness's check. |

## Sources

- CompCert 3.18, the release archive whose digests the translator's notes record: `configure`; `runtime/Makefile`; `driver/Compiler.v`, `Complements.v`, `Linker.ml`, `Interp.ml`; `cfrontend/Clight.v`, `ClightBigstep.v`, `Cshmgenproof.v`, `SimplExpr.v`, `C2C.ml`, `Ctypes.v`; `common/Events.v`, `Globalenvs.v`, `Values.v`, `Behaviors.v`, `Smallstep.v`; `aarch64/Asm.v`, `Asmexpand.ml`, `SelectLong.vp`; `x86/SelectLong.vp`; `backend/SplitLong.vp`; `lib/Camlcoq.ml`; `export/ExportDriver.ml`
- QEMU, the `virt` machine: https://www.qemu.org/docs/master/system/arm/virt.html
- QEMU, the generic loader: https://www.qemu.org/docs/master/system/generic-loader.html
- QEMU, semihosting: https://www.qemu.org/docs/master/about/emulation.html
- QEMU, Raspberry Pi machines: https://www.qemu.org/docs/master/system/arm/raspi.html
- Arm, semihosting specification (`HLT #0xF000`, `SYS_EXIT`, `ADP_Stopped_ApplicationExit`): https://github.com/ARM-software/abi-aa/blob/main/semihosting/semihosting.rst
- Arm, `CPACR_EL1`: https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/CPACR-EL1--Architectural-Feature-Access-Control-Register
- Arm Architecture Reference Manual, DDI 0487, the section on the effects of disabling a stage of address translation (D8.2.10 in issue I.a): https://developer.arm.com/documentation/ddi0487/latest
- QEMU issue 1204, unaligned accesses with the MMU off: https://gitlab.com/qemu-project/qemu/-/issues/1204
- Multiboot specification, the machine state at entry: https://www.gnu.org/software/grub/manual/multiboot/multiboot.html
