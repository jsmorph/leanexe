# Review of the third iteration's statements

The reviews below were written when the library was developed in another repository.  This copy gives the present paths and names of the library and of the calculator, and the request and the design that the reviews cite stayed in that repository.

Two independent agents reviewed the statements: the first the WebAssembly statements, the second the C form's.

## The WebAssembly statements

An independent agent received the request and [the statements](statements.md), with the definitions that they use (the first iteration's `Spec.lean`, `Program.lean`, and `Types.lean`, the second iteration's `segVal` and `SegDigits`, the third iteration's `Program.lean` and `Compiled.lean`, and leanexe's `Verified/Call.lean` and `docs/verified-manual.md`), and not the proofs.  It wrote its own reading of what the request requires, compared each statement with it, and named the wrong programs that each statement still accepts.  This file records its findings and the answers.

### The reviewer's reading of the request

1. For every canonical natural, the new division returns the first iteration's `natDivMod` and `natDivModChecked` quotient and remainder, the status 1 and two zeros for a zero divisor included, and canonical results.
2. The truncated and Euclidean integer divisions equal `intTDivModChecked` and `intEDivModChecked`, for every combination of signs and for zero divisors.
3. The natural and integer printers write exactly `intToText`'s text, `printSpec`, for every integer, so that the equality with `toString` and read-after-print hold.
4. Each of the five new exports has a `Verified.Call` theorem over every argument, against the first iteration's specification functions, with no premise on the depth.
5. Each export has a closed-form allocation bound linear in the lengths, valid at the frame count of the call theorems, 1,000.
6. The entries with thresholds as arguments are correct and bounded for every value of the thresholds.
7. The rest, the earlier exports unchanged, the algorithms of decisions 1 and 2, the C form, the tests, the figure, and the absence of project-specific names, is not stated by theorems.

### The comparison

| Statements | Verdict | Wrong programs still accepted |
|---|---|---|
| `DivPost`, `baseDiv_spec`, `rdiv_spec`, `tdiv_spec`, `udiv_spec`, `divSeg_spec` | Helpers, strong for their role: exact frame conditions, a top word of the quotient at most 1, and premises that are the algorithms' own preconditions on the layout, the normalization, and `m ≤ n`. | Behavior outside those layouts, which no caller uses.  The docstring of `divSeg` in `Program.lean` gave `14 n + lx + 10` words of scratch, where the theorem states `13 N + LX + 10`, the layout of the normalized divisor, the normalized dividend, and the scratch of `udiv`; the docstring now states `13 n + lx + 10`. |
| `natDivModBZWith_eq`, `natDivModBZ_eq_natDivMod`, `natDivModCheckedBZWith_eq`, `natDivModCheckedBZ_eq`, `natDivModCheckedBZ_eq_natDivModChecked` | As strong as needed; the forms with thresholds hold for every `t`, `T`, and `D`; the specifications are the first iteration's; `Canonical` and fewer than `2^32` limbs are the first iteration's premises. | Any result or a trap on arrays that are not canonical, outside the library's domain. |
| `intTDivModCheckedBZ_eq_intTDivModChecked`, `intEDivModCheckedBZ_eq_intEDivModChecked` | Stronger than needed: only the magnitudes must be canonical. | Magnitudes that are not canonical. |
| `intTDivModCheckedBZ_eq`, `intEDivModCheckedBZ_eq` | As needed, for every `a` and `b`, signs and zero divisors through the specifications. | None. |
| `natDivModBZ_canonical`, `intDivModCheckedBZ_canonical` | Correct, and implied by the equations. | None. |
| `PowOK`, `ChunksPost`, `toChunks_spec`, `chunksDC_spec` | Helpers; `chunksDC_spec` needs only `Digits`.  The first version of `statements.md` used `PowOK` without its definition, which is now listed. | None. |
| `natToTextDCWith_eq`, `natToTextDC_eq`, `natToTextDC_eq_intToText`, `intToTextDC_eq`, `intToTextDC_eq_intToText` | As needed: exactly the first iteration's text for every integer whose magnitude has fewer than `2^32` limbs; a printer that added leading zeros fails them. | A different text for a `BigInt` that is not canonical. |
| `intToTextDC_toString`, `readSpec_intToTextDC`, `intOfText_intToTextDC` | The carry-over: `toString`, `readSpec`, and the first iteration's reader, with the first iteration's premise on the text's size. | None. |
| `rdiv_fits_all`, `chunksDC_fits`, `natDivModCheckedBZWith_fits`, `natToTextDCWith_fits` | Stronger than a bound from the sizes: each holds for every argument and every threshold, at 135, 180, 139, and 181 frames. | A module that traps from depth is excluded. |
| `*_bound_le`, `*_room` | Linear closed forms for every `k`, so at 1,000 frames, with premises on the sizes alone and for every threshold. | Any allocation up to the bound. |
| The seven call theorems | As needed: every argument, canonical arguments and room for the generated bound as the precondition, no premise on the depth, every threshold for the entries with parameters; the indices agree with the manual's numbering of the entries that take the depth. | Any behavior on arguments that are not canonical; an entry with parameters that ignored its thresholds. |
| `rdiv_trapFree`, `divSeg_trapFree`, `chunksDC_call` | Extra: every argument, no allocation for the two in place, no premise on the depth. | None. |

The reviewer compared the bounds with the first iteration's: the natural and truncated divisions have the same bound, `128 m + 144 n + 824`; the Euclidean division has `248 (m + n) + 1472` against `232 (m + n) + 1440`; and the printer `438 n + 1968` against `94 n + 424`.

### What no statement covers

- The first iteration's own quadratic code would meet every statement of the interface: its results are the same, its division's bound is the same number, and its printer's bound is below `438 n`.  The statements prove correctness, frames, and allocation, and the request asks for no proof of the running time; the subquadratic algorithms are in `Program.lean`, and the timings show their growth.
- Below the threshold, the division calls the second iteration's `divideS`, MultiPrecision's Algorithm D with the carries by shift and mask, where decision 1 names the first iteration's Algorithm D.  The second iteration's `natDivModCheckedS_eq_natDivModChecked`, `natDivModCheckedS = natDivModChecked`, from `divideS_eq_divide`, proves that it returns the first iteration's results for every input, so the results are the same; the README states the choice.
- The integer divisions with Lean's convention at a zero divisor, `intTDivMod` and `intEDivMod`, have no counterpart in the new code; the request names the exports with a status.
- The C form had no statements at the time of the review; `Native.lean` and `NativeRuntime.lean` add them.
- No single theorem states a call with room for the closed form: a caller combines the call theorem, the room theorem, and `Heap.Within.mono`, as for the second iteration.

### The reviewer's ranking and the answers

1. The new algorithms are indistinguishable from the old in the statements (low to medium).  Answer: as above; the README says so.
2. The variant of Algorithm D below the threshold (low, design).  Answer: the user chose on 2026-11-27 to keep the second iteration's Algorithm D, since `natDivModCheckedS_eq_natDivModChecked` proves that it returns the first iteration's results, so the request's claims hold unchanged, and it is the faster fallback.
3. No C statements yet (low).  Answer: stage 5 adds them.
4. `PowOK` undefined in `statements.md` (low, documentation).  Answer: added.
5. The call and room theorems are separate (low).  Answer: kept, as in the second iteration.
6. Name resolution unchecked (residual).  Answer: printing the call theorems with `pp.fullNames` shows `Library.Numerics.Bignum.natDivModCheckedSpec`, `Library.Numerics.Bignum.intEDivModCheckedSpec`, `Library.Numerics.Bignum.printSpec`, `Library.Numerics.Bignum.Canonical`, and `Library.Numerics.Bignum.BigInt.Canonical`, the first iteration's definitions.

## The C form's statements

A second agent received the request, the C form's statements of `Native.lean` and `NativeRuntime.lean` in `statements.md`, the WebAssembly statements they build on, the second iteration's C form as the pattern that decision 6 names, leanexe's definitions of `LeanExe.Native.NativeImpl` and `LeanExe.Native.NativeA`, and the host and the script, and not the proofs.

Its reading: for each of the seven exports, the C function `lxf_f` is `funId k` of the translation, with `k` the index of the call theorem; under every `Archi` and every semantics of external functions, from a C memory related to a store whose heap meets the allocator invariant, with canonical arguments and `top` plus the closed form at most `2^28`, the call terminates with `lx_status` 0, its results represent the Lean function's value, which equals the first iteration's specification, and `top` rises by at most the closed form, at every threshold for the entries 64 and 71; and the names of every symbol a host uses, five result positions, the start by `lx_init`, and the theorems of `alloc` and `release`.

Its findings: every `_native_size` theorem names the right index, function, specification, and closed form, and the memory premise is right, since `Heap.Within` with the cap of `nativeCap = 4096` pages is the bound of `2^28` bytes; the premise of fewer than `2^32` limbs is implied by it and harmless.  The existential over the C function is not weak, since `native_start`'s environment condition forces each function at `funId k` to be the one its symbol resolves to, and it shows that the premises on the environment can be met.  `native_names` lists every symbol that `host/bignum3.c` uses, and its two `Nodup` conditions make names and identifiers correspond one to one; `native_start`, `alloc_room_native`, and `release_native` are the second iteration's.  The wrong C programs that the statements still accept are those of the second iteration's pattern: a function that also wrote a global outside `StoreRel`'s footprint, another run under a semantics of external functions that is not deterministic, code that overflows the machine stack, an entry with parameters that ignored its thresholds, and code with the same results and a quadratic time.

Its ranking, all documentation or shared with the second iteration, and the answers:

1. `statements.md` showed `_spec_trapFree` and `_native_spec` only for `natDivModCheckedBZ` and did not list the helpers' C theorems.  Answer: a paragraph now states that each export has the three theorems and lists the helpers' theorems.
2. The C prototypes and result types are existential and not displayed, so the host's declarations rest on the tests (shared).  Answer: kept, as in the second iteration.
3. The README dropped the second iteration's sentence on `StoreRel`'s footprint.  Answer: restored.
4. The README's bound of 182 counts frames of the depth guard, not bytes of the stack.  Answer: the README now says so.
5. The C form runs only the 1,120 cases of up to 2,000 limbs (shared).  Answer: the README states it.
6. Name resolution of the C statements.  Answer: printing `intEDivModCheckedBZ_native_size` and `natToTextDC_native_size` with `pp.fullNames` shows `Library.Numerics.Bignum.Canonical`, `Library.Numerics.Bignum.intEDivModCheckedSpec`, and `Library.Numerics.Bignum.printSpec`.
