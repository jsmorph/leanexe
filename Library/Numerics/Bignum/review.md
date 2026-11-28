# Review of the specification

The reviews below were written when the library was developed in another repository.  This copy gives the present paths and names of the library and of the calculator, and the request and the design that the reviews cite stayed in that repository.

A fresh agent reviewed [the specification](Spec.lean), [the record type](Types.lean), and the planned statements against the request and the design, from the files alone.  It wrote its own reading of the request before it studied the specification, built an executable model in Node's `BigInt` from the request, and compared it with the specification's values on 3,277 cases: 2,470 text-export cases, among them random and special texts, words with 256 or `2^32` added to a digit, all four sign combinations, and zero divisors, 407 pairs of naturals and 400 pairs of integers, with operands of up to about 3,000 digits and near the limb boundaries.  Every value agreed.  The comparison caught each of three wrong models that the reviewer seeded: one that accepted `-0` gave 66 mismatches, one with the truncated remainder for `%` gave 149, and one with a sign on zero gave 280.  It found no wrong program that a planned statement accepts on canonical arguments within the size premises, and it checked an untrimmed result, a negative zero, `a ≤ b` as the subtraction's flag, `(#[], #[])` for a zero divisor, a remainder with the divisor's sign, words read modulo 256, acceptance of `-0` or `+1`, and the other order of statuses.

It reported these points, and the specification now answers each.

| Point | Response |
|---|---|
| The planned statements spoke of "each export `f` above", which included the divisions of Lean's convention, whose export would break decision 2, and `natTrim`, whose call theorem needs `Digits` and not `Canonical`. | The header lists the exports.  `natDivMod`, `intTDivMod`, and `intEDivMod`, with the program's other helpers, are `@[inline]`, so the compiler expands them into their callers and does not export them.  `natTrim`'s call theorem takes `Digits`. |
| The bounds of the call theorems had no stated constants. | Each export has a closed form, stated with its call theorem and in the README. |
| The header called the Euclidean remainder never negative, which fails at a zero divisor: `(-5) % 0 = -5`. | The header says "for a nonzero divisor" and states the remainder at a zero divisor.  The tests call the library's divisions at `(-5, 0)`. |
| Non-canonical arguments get no guarantee, and the header did not say so. | The header says that results on other arguments have no meaning. |
| `intOfText` returns `true` for success where the other exports return the status 0. | Recorded in the header. |
| Decision 3's words also admit `["-"] ("0" / nonzero *digit)`, which accepts `-0`. | The header records the reading and that the design's grammar, which rejects `-0` and lists it among the rejections to test, settles it. |
| The reading of "exports for each operation" was not stated. | The header states it: one text export per integer operation, in place of `calc`, with the exports over limbs and records. |
| An export that finds no memory traps, with no status. | Recorded in the header, with the call theorems' room premise that excludes the trap. |
| `BigInt.Canonical` had no readable form. | `BigInt.canonical_iff` states it as a canonical magnitude and a sign that is false when the magnitude is empty. |

The reviewer named other readings of decision 3: exports over limbs and records with `intOfText` and `intToText` alone; one text export per row of the design's table, with a status and two texts for each division; text exports alone; and a status word from every export.  The specification keeps its reading and states it, and [the README](README.md) names the choice for the user.

## Review of the statements

A second fresh agent reviewed the final statements, with their proofs omitted, against the request and the design, after writing its own reading of the request.  It found no wrong program that the equations and call theorems of the 24 exports of the interface accept on canonical arguments: the mutations of the design, a trim that leaves a zero limb, a sign left on zero, and a remainder with the divisor's sign, are each excluded, the call theorems' specifications and preconditions match the equations, the room of each call theorem is the generated bound that its closed form bounds, and the closed forms' premises hold for every input that the call theorem covers.

| Finding | Response |
|---|---|
| The module also exports the 18 reused functions of MultiPrecision, Uscale, and Int64Text, functions 2 to 19, which had no call theorem, and `divide`, `shortDiv`, and `longDiv` among them return no error status for a zero divisor, against decision 2. | `Reused.lean` states a call theorem for each of the 18, with the bounds of `Bound.lean` and `reused_bounds_zero`.  The three divisions keep MultiPrecision's conventions.  The user decided to keep them as exports outside the interface, unchanged. |
| Decision 3 also admits a grammar that accepts `-0`, and the specification's choice was not put to the user. | The user decided to keep `-0` rejected, so that reading and printing are exact inverses, and confirmed one text export per integer operation. |
| A zero divisor that is not canonical, such as `#[0]`, has no guaranteed status. | Consistent with decision 4; the README states that results on arguments that are not canonical have no meaning. |
| No theorem stated print after read on the program. | `intToText_of_read` states it. |
| `eq_limbsOf`'s docstring said "exactly when" for one direction. | Corrected. |
| `intOfText` signals success with `true`, and `textCmp` returns the code 0 with an error status. | Both are recorded in the specification's header. |

## Review of the C form

A fresh agent reviewed the statements of [`Native.lean`](Native.lean), with their proofs omitted, against the request for the C form, after writing its own reading of it: a Clight theorem for the C function of every export that has a main claim, from a C memory related to a store that meets the call theorem's precondition with room in 256 MiB of `lx_mem`, with the specification's value and status and the closed form of the bound, together with a proof that the premises can be met from the program's start and a tie from each theorem to the symbol that the host calls.  It found that the 24 statements of the interface's exports state this: their preconditions, specifications, and closed forms match the call theorems, `ImplementsA.strengthen` is the rule of consequence, `NativeImpl` carries the postcondition of the strengthened theorem to the C function, the size forms' premise is the room premise of WebAssembly with the closed form in place of the generated bound, and the comparisons need no size form.

| Finding | Response |
|---|---|
| Exports 2 to 19 had only the generic `compiled.f.native`, which admits a trap and states no specification, and `lxf_alloc` and `lxf_release`, through which the host places and releases arguments, had no C theorem at this translation. | [`NativeRuntime.lean`](NativeRuntime.lean) states `add`, `sub`, `mul`, `divide`, and `le` with MultiPrecision's and Uscale's specifications, the other 13 from their generated theorems without a trap, and `alloc_room_native` and `release_native` from leanexe's `alloc_native_room` and `release_native`. |
| No statement showed that the premises can be met: every C theorem is an implication over an arbitrary environment, memory, and heap. | `native_start` states that `init_mem` and `lx_init` give a memory related to the module's initial store with `lx_status` 0, in the program's own environment, which meets every hypothesis of `NativeA` on the environment, and an initial heap that meets the allocator invariant with `top` at 4,096 bytes. |
| The theorems name `funId k`, and a swap of the names of two functions of one signature, such as `lxf_natAdd` and `lxf_natMul`, would escape every statement. | `native_names` states the C name of each of the module's functions, by evaluation in the kernel. |
| The C theorems cover less than the WebAssembly theorems, since `lx_mem` has 256 MiB where the module can grow to 65,535 pages; the docstring gave texts of fewer than `2^30` words where `intOfText_native_size` takes `2^32`; and the website's sentence did not state the limit. | The README and the docstring state the limit with an example, the docstring and the README give `2^32` for `intOfText`, and the website's sentence names the 256 MiB. |
| The theorems state that a terminating run exists, and leanexe's `NativeA.unique` is not instantiated. | The README says so; the translation calls no external function. |
| A call without room is left to the generic `compiled.f.native`. | Accepted by the reviewer and kept. |

The link from `bignum.c` to `compiled.translation` remains the comparison of `clightgen`'s reading in `host/EmitNative.lean check`, as leanexe's trusted base states.

A third fresh agent reviewed the statements of `NativeRuntime.lean`, with their proofs omitted, against the same request and the three findings above, after writing its own reading of what each statement must say.  It found that the five specification theorems of the reused exports match the call theorems of `Reused.lean` and MultiPrecision's specifications, that the generic theorems state the absence of a trap within the generated bound, that `native_start` gives every premise of `NativeA` on the environment, the memory, and the heap against the module's own initial store, and that the 44 names match the exports.  It found no wrong C function that a statement accepts, and it reported these points.

| Finding | Response |
|---|---|
| `lx_init`, `lx_status`, `lx_mem`, and the result globals, which the host uses, had no stated names, so a translation that printed the second result's global as `lx_r0_l` would meet every statement. | `native_names` states those names, five result positions, and that no two identifiers and no two names coincide. |
| `native_start` closes the gap only for the environment, the memory, and the heap: the host's writes of the arguments have no theorem, and the README said that the premises can be met. | The README and the docstring name the premises that `native_start` covers and state that the arguments' premises rest on the host's code. |
| `native_start` omitted the premise `memoryCap ≤ 65535` of `NativeA`. | It states that the cap is `nativeCap`. |
| `alloc_native` and `release_native` stopped at the store, without the heap after the call, and `alloc_native` took the name of leanexe's theorem with a trap. | `alloc_room_native` states the allocator invariant after the allocation and the fresh block, and `release_native` the invariant after the release. |
| `native_names` states membership and not that a name has one identifier. | It states that neither the identifiers nor the names repeat. |
| The reused exports have no C closed forms. | The README points to `Bound.lean`'s closed forms of their generated bounds. |
| The docstrings of the `*_spec_trapFree` theorems called them C functions, and the generic theorems' indices were implicit. | The docstrings name the module's function and its index. |
| The theorems state that a run exists, and `StoreRel` relates only the translation's globals and `lx_mem`. | The README states both. |
