# Sail's Lean back end on the floating-point functions

These scripts translate the floating-point functions of the Armv9.4-A Sail model into Lean with
Sail's Lean back end, elaborate the output, test it against Talos's binary64 functions, and prove
equations that the A64 Isla check assumes.  The modules of [`F7/`](F7/) prove that the
translated `FPAdd`, `FPSub`, `FPMul`, and `FPDiv` of `(a, b, 0x02000000)` at 64 bits return
`f64Add a b`, `f64Sub a b`, `f64Mul a b`, and `f64Div a b` for every pair of words, that
`FPSqrt(a, 0x02000000)` returns `f64Sqrt a`,
`FixedToFP(a, 0, TRUE, 0x02000000, FPRounding_TIEEVEN, 64)` returns `f64ConvertI64U a`, and
`FPToFixed(a, 0, TRUE, 0x02000000, FPRounding_ZERO, 64)` returns `i64TruncSatF64U a` for every
word, and that `FPCompare(a, b, FALSE, 0x02000000)` returns the flags `fcmpNZCV a b` that the
model's FCMP sets, for every pair of words.  The modules `F7/*32.lean` prove the equations of the
single-precision forms other than FRINTN's against Talos's binary32 functions (The binary32
proofs), and [`check.sh`](check.sh) regenerates the translation and checks the proofs.  Sail's C
emulator of the same slice tests the arithmetic functions and FixedToFP with exact rationals
([`emu/`](emu/)).  Nothing in the A64 model or its proofs depends on these files.

## Versions and installation

| Component | Version | Source |
|---|---|---|
| Sail | 0.20.3, the latest release (the Lean back end first appeared in 0.19) | opam package `sail.0.20.3`, tag `0.20.3` (`3df54034`) of [rems-project/sail](https://github.com/rems-project/sail/releases/tag/0.20.3) |
| OCaml | 5.4.1 | opam switch `sail-0.20.3` |
| opam | 2.1.5 | Ubuntu package `opam` |
| Sail model | arm-v9.4-a at `7d0581642` | [rems-project/sail-arm](https://github.com/rems-project/sail-arm) |
| Lean support library | lean-sail `v6` (`c816ea7a`), which the back end names | [rems-project/lean-sail](https://github.com/rems-project/lean-sail) |
| Lean | v4.29.0, which the back end names, and the repository's v4.34.0-rc2 | elan |

[`install.sh`](install.sh) creates the opam root and the switch and installs Sail, in 3.5 min
with 6 jobs and 1.1 GB.  Sail's installation guide names the Debian packages
`build-essential`, `libgmp-dev`, `z3`, and `pkg-config`.  Sail calls Z3 to check constraints.
[`run.sh`](run.sh) runs a command in a new session under a user scope with a memory cap, a CPU
quota, and a timeout, with GNU `time -v` reporting elapsed time and peak memory.

## Sources

The Isla traces of the A64 check come from the IR of isla-snapshots, which sail-arm `111345b`
generated (isla-snapshots commit `9591cbb`); the translation reads sail-arm `7d0581642`.  Of the
files that `translate.sh` reads, `decode_start.sail`, `builtins.sail`, `interrupts.sail`,
`devices.sail`, `mem.sail`, and `decode_end.sail` are identical in the two commits.
`prelude.sail` differs only in the `lean:` names of external functions, which `111345b` lacks;
`termination_measures.sail` is `111345b`'s `coq_termination.sail` with the Rocq measures inside
`$iftarget coq`.  The other changes lie in `v8_base.sail` (202 lines), `interface.sail`,
`stubs.sail`, `impdefs.sail` (a blank line), and `fetch.sail`, in exception entry, address
translation, the instruction fetch, and the announcements of the concurrency interface.

| Changed definition in the slice | Where `FPAdd` and the other roots reach it |
|---|---|
| `AArch64_FPTrappedException` (an announcement removed) | through `FPProcessException` when FPCR enables the exception's trap |
| `ExceptionSyndrome`, `BranchTo`, `FloorPow2` | only through `AArch64_FPTrappedException` |

`fp-slice.isail` therefore cuts the slice at `AArch64_FPTrappedException` and
`AArch32_FPTrappedException`, after which no definition of the translation differs between the
commits: [`srcdiff.py`](srcdiff.py) maps every changed line to its top-level definition, and of
those only `AArch64_FPTrappedException` occurs in the translation, as the name that the cut keeps.  Sail 0.20.3 does not check `111345b`'s
`v8_base.sail`: the type of `FloorPow2`'s `n`, `{'n, 'n >= 0. int('n)}`, fails at
`2 ^ (n - 1)`, which `7d0581642` fixes with `'n > 0`.

The translation reads Sail 0.20.3's library, and the IR the library of Sail commit `f3da8185`.
isla-sail is a Sail plugin, so an IR takes the library of the Sail that ran the plugin, and the
346 source locations that the IR records in its 38 library functions fit `f3da8185` and its two
successors on the main branch before the snapshot, which change no `.sail` file of the library,
and fit no release.  For every library function, extern, and built-in declaration that FPAdd,
FPSub, FPMul, FPDiv, FPSqrt, and FixedToFP reach in the IR or in the translation, the two
libraries agree in meaning: they differ in the `lean:` names of externs, in declarations that
0.20.3 moves to `corelib.sail` with the same text, and in a name reservation for the C back end.
The IR also calls `slice_mask`, `sail_mask`, `__id`, and `neq_int`, where isla-sail's
`-mono_rewrites` and Sail's `sizeof` rewrite changed the code, and each gives on its arguments the
value of the expression that the translation computes in its place.  Compared by name rather than
by line, every model definition that the IR reaches below the cut is identical in the two sail-arm
commits, except `AArch64_FPTrappedException` and the `lean:` name of `neq_any`.

## Translation

[`translate.sh`](translate.sh) type-checks the model, runs the REPL commands of
[`fp-slice.isail`](fp-slice.isail), and writes a Lake project.  The commands keep the definitions
that FPAdd, FPSub, FPMul, FPDiv, FPSqrt, FixedToFP, FPRoundInt, FPToFixed, FPCompare, and
`initialize_registers` reach, with the standard library, up to the two cut trap functions, and
apply the Lean rewrites.
The slice keeps `initialize_registers` because the back end's rewrite `add_register_init_function`
calls it, and `:rewrite move_termination_measures` runs before the slice, which would otherwise drop
the loop measures.  [`fp-measures.sail`](fp-measures.sail) gives FPRoundBase__1's loops the measures
that `termination_measures.sail` gives the Rocq target only, so the back end writes them with
lean-sail's `whileFuelM`.  The model's files after `mem.sail` other than `decode_end.sail` and
`fetch.sail` are left out: Sail parses and checks every file before the slice, and the whole model
exceeded a 7 GiB cap after 7 min.  The options are `--lean-real-numbers` (Mathlib's ℝ for the
specification's reals), `--lean-noncomputable`, and `--lean-single-file`, without which the back end
fails on the slice with `Invalid_argument("List.combine")`.

The cut keeps the declarations of the two trap functions and drops their bodies, and the back
end calls each as a pure function that returns `Unit`.  [`ArmExtras.lean`](ArmExtras.lean)
supplies them as functions that return `()`, so in the translation a trapped floating-point
exception returns to its caller, and it supplies `sign_extend`, as sail-arm's own
`lean/ArmExtras.lean` does for a later Sail.

| Measure | Value |
|---|---|
| Time | about 20 s a translation, with Sail's cache of Z3 results (`sail_smt_cache`); four in 87 s |
| Peak memory | 1.6 GB |
| Output | 7,528 lines with 926 definitions, and 4,168 lines of types |
| Loops | the two `whileFuelM` loops of FPRoundBase__1, and no other loop |

The output is monadic.  Each function runs in `SailM`, an `EStateM` over a state whose map holds
the model's registers, and reads the registers it needs.  FPAdd has the type
`BitVec k_N → BitVec k_N → BitVec 64 → SailM (BitVec k_N)`.  Unpacking yields a real number,
the arithmetic is on ℝ, and FPRoundBase__1 normalizes with the two loops, rounds with `Int.floor`,
and compares the error with 1/2.  The back end fixes the choice source of unspecified values in
the type of `SailM` to lean-sail's `trivialChoiceSource`.

## Elaboration

The back end's output does not elaborate as written.  [`fix-output.sh`](fix-output.sh) makes the
edits below and prints how many rewrites each makes, and [`lean-sail-v6.diff`](lean-sail-v6.diff)
applies to lean-sail the fix of `ArchSemSequential.lean` that its tag `v9` carries and deletes its
coercion `CoeT Int x Nat`.

| Failure | Lean versions | Edit | Rewrites | Check that the edit changes nothing else |
|---|---|---|---|---|
| `Real.lean` opens a namespace `Defs` that no output declares | both, with reals | delete the line | 1 | the deleted command declares nothing |
| `assert` at the start of a do element parses as Lean's assert element | v4.34.0-rc2 | qualify every call as `LIB.assert` | 41 | on v4.29.0 the 6,457 constants of the output of the six-function slice hash identically with and without the edit |
| Sail prints a real literal as `N/D` or `-N/D` without parentheses, so `gt_real e 1/2` parses as `(gt_real e 1) / 2` | both | parenthesize every `N/D`, `-N/D`, and bare `-N` outside strings and comments; fail on a decimal or exponent literal | 14 fractions, no negative | each changed line has a `1/2` that becomes `(1/2)`; without the edit the output does not elaborate |
| The back end writes an integer of the model where Lean expects a natural number, as a width, an index, a shift, or a fuel, and lean-sail's coercion `CoeT Int x Nat` converts it with `x.toNat`, which maps a negative integer to 0.  `asl_Int`'s `result` takes the type Nat from its first branch, so the translation's SInt, and FixedToFP of a signed operand, gave 0 for every negative value | both | delete the coercion (`lean-sail-v6.diff`); type `asl_Int`'s `result` as Int, and write `.toNat` at each other place, with the model's guarantee that the value is nonnegative in a comment of the script | 30 | on v4.34.0-rc2 the 6,456 constants of the output hash identically with the coercion and without it after the edit, except `asl_Int` |
| `sign_extend` and the cut functions are unknown | both | `ArmExtras.lean` | | the cut changes FPProcessException and no other function: against the uncut slice on v4.29.0, the 6,457 constants of the cut output differ only in FPProcessException, `sail_model_init`, and constants that Lean derives for the inductive types |
| lean-sail's `ArchSemSequential.lean`: `Decidable (0 < choice)` | v4.34.0-rc2 | `lean-sail-v6.diff` | | the edited `interpretSailEffects` belongs to the version-2 interface, which the output does not name |

Lean's coercion of a type's arithmetic converts each operand, so the coercion gave the width
`hi - lo + 1` of `integer_subrange` as `hi.toNat - lo.toNat + 1`, and the script writes that form,
which equals `hi - lo + 1` for the `lo = 0` of every call.  Without the coercion every place that
used it fails to elaborate, so the 30 conversions are all of them; the comparison of constants
shows that each reproduces the coercion's term, and that only `asl_Int` changes, its unsigned
branch to `pure ↑x.toNat` and its signed branch to `pure x.toInt`.

The literal rewrite follows `doc_lit` of the back end's `pretty_print_lean.ml`, which prints an
`L_real` with Zarith's `Q.to_string`, so every real literal has one of the forms `N`, `-N`,
`N/D`, and `-N/D`; a negative integer literal prints as `(-N)` (`doc_big_int`).  [`ConstDump.lean`](ConstDump.lean) writes the hashes that the
comparisons use: each constant's type and value, with the module name and the numbering of
matchers normalized, from builds of the Float-valued output with `probe429.sh`.  The derived constants
that differ between the cut and the uncut output are the eliminators and recursors of
`Register`, whose constructors differ with the register set, and the `noConfusion` and `Repr`
definitions of the enumerations, whose difference was not traced.  The uncut slice also needed
two edits that the cut makes unnecessary, since both functions lie on exception paths: a
comparison of two `BitVec.join1 [b]` in IncrementInstructionCounter that runs in `whnf` without
end, and the do elaborator's failure on MaybeZeroSVEUppers on v4.34.0-rc2.

The comparisons of constants on v4.29.0 ran on the slice without the roots FPRoundInt, FPToFixed,
and FPCompare and were not repeated on the output with them.  The three roots add the definitions
FPRoundInt, SatQ, SignedSatQ, UnsignedSatQ, FPCompare, and FPToFixed and change the text of no
other definition: the two outputs differ elsewhere only in the generated names of two type
quantifiers in a comment.  The nine `assert` calls and the eight fractions of the added
definitions take the same edits as the others.

[`elaborate.sh`](elaborate.sh) builds the real-number output with the repository's toolchain and
Mathlib in a scratch copy of the repository in 162 s, and its rational counterpart (below) in
167 s, at a peak of 4.1 GB, with only Mathlib's naming warnings.  [`probe429.sh`](probe429.sh)
builds the Float-valued output with Lean v4.29.0 and lean-sail v6 unchanged in 226 s and 4.3 GB.
[`Check.lean`](Check.lean) prints the types and axioms of the six functions.

## Loops

FPRoundBase__1 doubles a mantissa `M` below 1 while it is below 1, with fuel `⌈1/M⌉`, and then
halves it while it is at least 2, with fuel `⌈M'⌉`.  lean-sail's `whileFuelM` returns the current
value when its fuel runs out, so a short measure would change a result without an error.
[`F7/Base.lean`](F7/Base.lean) proves that both loops exit by their conditions within their fuel
for every positive real mantissa, the only inputs that FPRoundBase__1's assertion `op != 0` admits:
`loop1_exit` gives the number `k` of doublings, with `k < ⌈1/M⌉`, `M·2^i < 1` for `i < k`, and
`1 ≤ M·2^k`, and `loop2_exit` gives the number of halvings likewise.  `whileFuelM_pure` and
`loopP_of_exit` turn the loops into iterations of their bodies, and `loops_eq` gives their result
`(e, M·2^-e)` with `1 ≤ M·2^-e < 2`.

## The state hypothesis

`Hyp` states what the theorems assume of the state: the register map holds FeatureImpl, PSTATE,
FPSR, SCR_EL3, HCR_EL2, and SMCR_EL1 to SMCR_EL3; one of FEAT_AA64EL0 to FEAT_AA64EL3 is
implemented; and PSTATE.nRW is 0.  The other features, among them FEAT_AFP, FEAT_SME, and
FEAT_SME_FA64, the other fields of PSTATE, the values of FPSR and of the five system registers, the
other registers, the memory, and the choice state are free; FPCR is the functions' argument,
0x02000000.  Each theorem holds for every state that satisfies `Hyp`.

The Isla profiles meet the hypothesis.  `isla_footprint_no_init` (sail-arm's `isla_main.sail`)
runs `InitFeatureImpl`, which sets FeatureImpl from the registers `FEAT_*_IMPLEMENTED` that
`tests/isla/traces.sh` sets with `-I` from each profile's `features` file, as
`LeanExe/A64/Isla/Profile.lean` states.  Every file sets FEAT_AA64EL0 and FEAT_AA64EL1.  FEAT_AFP
is clear under `tcg` and set under `kvm` and `sme`, and FEAT_SME and FEAT_SME_FA64 are set under
`sme` only (`tests/isla/sme/features` lines 234 and 236).  The reset of Isla's `armv9p4.toml`
sets PSTATE.nRW to 0, which the traces record as `assume-reg`, and Isla's state holds every
register.  FPCR comes from the F2 traces, which fix it to 0x02000000 (`tests/isla/traces.sh`).

The Lean back end evaluates both operands of `&&` and `||`.  It writes each monadic operand as
`(← …)`, which Lean's `do` notation runs before the test, while Sail's rewrites leave such operands
in place for short-circuiting (Sail 0.20.3 `src/lib/rewrites.ml`) and the IR that Isla runs
evaluates them only when the first operand does not decide the result (`AE_short_circuit`,
`src/lib/anf.ml`).  A translated function therefore runs calls that Sail's function skips.  On
the paths of FPAdd, FPSub, FPMul, FPDiv, FPSqrt, FixedToFP, FPToFixed, and FPCompare at 64 bits
under FPCR 0x02000000, the eagerly evaluated operands are these:

| Function | Expression | Operands that run although Sail skips them |
|---|---|---|
| FPUnpackBase__1, FPProcessNaNs__1, FPDefaultNaN__1, FPRoundBase__1, FPProcessDenorms, FPProcessDenorm, FPToFixed | `HaveAltFP() && !UsingAArch32()`, with `&& FPCR.AH == 1` in all but the first and FPDefaultNaN__1 | UsingAArch32, which reads PSTATE and FeatureImpl |
| FPRoundBase__1 | `FPCR.UFE == 1 && (!InStreamingMode() \|\| IsFullA64Enabled())` | InStreamingMode, which reads FeatureImpl and PSTATE, and IsFullA64Enabled |
| FPProcessException | `FPCR<enable> == 1 && (!HaveSME() \|\| PSTATE.SM == 0 \|\| IsFullA64Enabled())` | HaveSME, a read of PSTATE, and IsFullA64Enabled |
| HaveAArch64 | the four tests of FEAT_AA64EL0 to FEAT_AA64EL3 | reads of FeatureImpl |
| IsFullA64Enabled | `(PSTATE.EL == EL0 \|\| PSTATE.EL == EL1) && !IsInHost()`, `(PSTATE.EL == EL0 \|\| PSTATE.EL == EL1 \|\| PSTATE.EL == EL2) && EL2Enabled()` | reads of PSTATE, IsInHost, and EL2Enabled |
| ELIsInHost | `!HaveVirtHostExt() \|\| ELUsingAArch32(EL2)` | ELUsingAArch32(EL2) |
| EL2Enabled | `HaveEL(EL2) && (!HaveEL(EL3) \|\| SCR.NS == 1 \|\| IsSecureEL2Enabled())` | SCR_GEN_read and IsSecureEL2Enabled |
| IsSecureEL2Enabled | `HaveEL(EL2) && HaveSecureEL2Ext()`, `!ELUsingAArch32(EL3) && SCR_EL3.EEL2 == 1` | HaveSecureEL2Ext, ELUsingAArch32(EL3), and a read of SCR_EL3 |

Under FPCR 0x02000000 the first operand of the tests in FPProcessException and FPRoundBase__1 is
false, so the value of IsFullA64Enabled plays no part, and its call matters only through its
effects.  `ro_fullA64` in [`F7/Base.lean`](F7/Base.lean) proves that IsFullA64Enabled returns
without an error and changes nothing but the choice state from every state whose register map
satisfies `FARegs`: FeatureImpl with an implemented AArch64 exception level, PSTATE, SCR_EL3,
HCR_EL2, and SMCR_EL1 to SMCR_EL3 present, for every setting of the features and every exception
level and register value.  It composes the same statement for IsInHost, ELIsInHost, EL2Enabled,
IsSecureEL2Enabled, ELUsingAArch32 at EL2 and EL3, IsSecureBelowEL3, and SCR_GEN_read, whose
assertions hold because the configuration's `HaveEL` is true for every level and `HaveAArch32EL`
only for EL0.  `bind_fa` then lets `sail_simp` step over each call.  The other eager operands read
FeatureImpl and PSTATE; the proofs unfold them, and each theorem's statement that only FPSR
changes excludes a write.

## Unspecified values

The ASL declares variables without initial values, sail-arm gives them `undefined`, and the
translation draws each at the start of its function: Booleans, bit vectors, integers, and
enumeration members from the choice source, and reals from `undefined_real`, which returns
`default` (`Armv9fp/Real.lean`) and does not consult the choice source.  The type `SailM` fixes
the choice source to lean-sail's `trivialChoiceSource`, which answers `false` and 0, and Mathlib's
`default : ℝ` is 0, so each theorem speaks of the translation with these values.  The proofs keep
`trivialChoiceSource`, the instance `Real.instInhabited`, and `unspecReal`, the real that
`undefined_real` returns, irreducible, and `sail_simp` steps over each draw with `bind_choose` and
`bind_undefined_real`, never unfolding `undefined_real`.  Every drawn value thus stays a term that
no step evaluates, and each proof ends with a result and a register map free of such terms.  That
a theorem would hold for another choice source is a property of how its proof was built, which the
kernel's check of the statement does not establish.  For the reals the check below establishes
more: it also elaborates the proofs against a variant of the translation whose `undefined_real`
returns `opaqueReal`, an `opaque` constant whose value the kernel cannot unfold.  The theorems
check there with the same statements, so their proofs use no property of the unspecified real,
and they hold for every value of it.  FPSqrt draws the real `value_name` before FPUnpack assigns
it, and FPRoundBase__1, which FPSqrt and FixedToFP reach, draws `mantissa` before the loops assign
it; FPToFixed draws `value_name`, and FPCompare `value1_name` and `value2_name`, before FPUnpack
assigns them.  The variant checks `fpSqrt_eq_f64Sqrt`, `fixedToFP_eq_f64ConvertI64U`,
`fpToFixed_eq_i64TruncSatF64U`, and `fpCompare_eq_fcmpNZCV` with the others.

## Tests

[`RatReal.lean`](RatReal.lean) replaces the back end's Float-valued reals with Lean's exact `Rat`,
which holds every value that FPAdd, FPSub, FPMul, FPDiv, and FixedToFP compute; FPSqrt has no
rational evaluation.  [`Vectors.lean`](Vectors.lean) draws the vectors of the A64 vector test
(`tests/TestSupport/A64/FpVectors.lean`) with `vectors 3 200000`, the operands of
`a64-fpvectors gen 3 200000`, runs the rational translation from the registers that
`sail_model_init` sets with FEAT_AA64EL0 and FEAT_AA64EL1 added, under FPCR 0x02000000, and
compares each result with Talos's function.  [`emu/`](emu/) builds Sail's C emulator of the same
slice, whose runtime computes reals as GMP rationals, and runs it on the vectors that
`Vectors.lean` writes.  FPSqrt's `sqrt_real` in Sail's `sail.c` stops Newton's iteration when two
iterates differ by less than `c`, 10^-30 for an argument of at least 1 and 10^-30 times the
argument below 1, so its result lies within `c` above the root; `emu/fpemu.c` counts a vector as
resolved when GMP's integer square root places the root at least `c` from every rounding
boundary.

| Test | Vectors | Result | Time, peak memory |
|---|---|---|---|
| Rational translation against Talos | 200,000 of each of FPAdd, FPSub, FPMul, FPDiv, FixedToFP | every result equal | 15 min 48 s, 1.8 GB |
| C emulator against Talos and the rational translation | the same, and 200,000 FPSqrt | every result equal to both | 396 s; generation 52 s and 2.0 GB, build 4 s |
| FPSqrt margin | 153,948 that reach `sqrt_real` | none unresolved; the smallest margin is 55 times `c` | |

Every class of every form agrees, among them the vector test's ties, near ties, overflows,
underflows, cancellations, and special values.  Neither test runs FPToFixed or FPCompare.
[`Eval.lean`](Eval.lean), the probe's first evaluation, compares 10,484 operand pairs per binary
function and 10,086 integers.

## The proofs

`fpAdd_eq_f64Add` in [`F7/FPAdd.lean`](F7/FPAdd.lean) states that for every pair of words `a`,
`b` and every state `s` with `Hyp s.regs fi ps fpsr`, the translated `FPAdd a b 0x02000000` at 64
bits returns `(f64Add a b).toBitVec` and a state whose registers are `s.regs` with FPSR set to
`fpsr ||| addMask a b`, and whose memory, tags, cycle count, and output are `s`'s.  `addMask`
sets IOC for a signaling NaN operand and for the sum of opposite infinities, OFC and IXC on
overflow, and IXC on an inexact sum (`roundMask`).  `fpMul_eq_f64Mul` in
[`F7/FPMul.lean`](F7/FPMul.lean) states the same of FPMul and Talos's `f64Mul`, with `mulMask`:
IOC for a signaling NaN operand and for an infinity times a zero, OFC and IXC on overflow, IXC on
an inexact product, and UFC and IXC on an inexact subnormal product.  `fpDiv_eq_f64Div` in
[`F7/FPDiv.lean`](F7/FPDiv.lean) states the same of FPDiv and Talos's `f64Div`, with `divMask`: IOC
for a signaling NaN operand and for the quotients of two infinities and of two zeros, DZC for a
finite nonzero dividend over a zero, OFC and IXC on overflow, IXC on an inexact quotient, and UFC
and IXC on an inexact subnormal quotient.  `fpSub_eq_f64Sub` in [`F7/FPSub.lean`](F7/FPSub.lean)
states the same of FPSub and `f64Sub`, with `subMask`: IOC for a signaling NaN operand and for the
difference of equal infinities, and the bits of `roundMask` for the exact difference.
`fpSqrt_eq_f64Sqrt` in [`F7/FPSqrt.lean`](F7/FPSqrt.lean) states it of FPSqrt and `f64Sqrt` for
every word, with `sqrtMask`: IOC for a signaling NaN and for a negative operand other than a zero
or a NaN, and IXC for an inexact root.  `fixedToFP_eq_f64ConvertI64U` in
[`F7/FixedToFP.lean`](F7/FixedToFP.lean) states it of
`FixedToFP a 0 true 0x02000000 FPRounding_TIEEVEN 64`, the call of the wrapper FixedToFP64 that
UCVTF D←X uses, and `f64ConvertI64U`, with `cvtMask`: IXC for an inexact result.
`fpToFixed_eq_i64TruncSatF64U` in [`F7/FPToFixed.lean`](F7/FPToFixed.lean) states it of
`FPToFixed a 0 true 0x02000000 FPRounding_ZERO 64`, the call of the wrapper FPToFixed64 that
FCVTZU X←D uses, and `i64TruncSatF64U`, with `fixMask`: IOC for a NaN, an infinity, or a
truncation outside `[0, 2^64)`, and IXC for an inexact truncation inside it.
`fpCompare_eq_fcmpNZCV` in [`F7/FPCompare.lean`](F7/FPCompare.lean) states it of
`FPCompare a b false 0x02000000`, the call that FCMP D makes, and the 4-bit word of
`fcmpNZCV a b`, the flags of the model's `State.fcmp`, with `cmpMask`: IOC for a signaling NaN
operand.  Each theorem depends on `propext`, `Classical.choice`, and `Quot.sound` only.

The proofs follow the translated code.  `sail_simp` rewrites a run of the monadic code step by
step with lemmas for register reads and writes, the choice source, the exception monad of
`SailME.run`, and the FPCR fields; the state hypothesis resolves the reads of `UsingAArch32`,
`HaveAltFP`, and `FPProcessException`, and `bind_fa` the calls of `IsFullA64Enabled`.
`fpUnpack_run` gives the type, sign, and value of an operand, its value `scaledValue a · 2^-1074`
for a finite one, and `fpProcessNaNs_run` the default NaN under FPCR.DN.  `fpRound_dy` in
[`F7/Round.lean`](F7/Round.lean) gives the result of FPRound__2 on `±N · 2^-(1074 + X)` for every
`X`: Talos's `roundDyadicMagnitude neg N X`, the two-stage rounder of `IEEE64.mul`, with the FPSR
bits of `maskDy N X`.  It splits the normal results (`round_normalG`) from the subnormal ones
(`round_subG`).  For a normal result the loops give the exponent `log2 N − 1074 − X`, the integer
mantissa is the quotient `q` of `N` by `2^(X + j)` with `j = log2 N − 52 − X`, and the error is
the remainder over `2^(X + j)`; for a subnormal one the divisor is `2^X`.  `tDy_normal` and
`tDy_sub` state Talos's two stages over the same quotient and remainder: `roundShift` rounds `N`
over the divisor to the nearest integer, ties to even, and `roundScaledMagnitude` of that integer
times `2^j` is exact (`rsm_exact`, `rsm_carry`), so the two-stage rounding equals
FPRoundBase__1's single rounding in every case of rounding, carry, and overflow.  FPRoundBase__1 detects tininess before rounding, so
an inexact subnormal result sets UFC even when it rounds up to the smallest normal number.  The
exact sum of FPAdd is `X = 0`, where `tDy_zero` gives `roundScaledMagnitude`; FPMul's exact
product of the magnitudes `A` and `B` is `±(A · B) · 2^-2148` (`mul_val`), `X = 1074`.

FPDiv's exact quotient `±(A / B)` is a rational, `±((A · 2^1074) / B) · 2^-1074` (`div_val`).
`fpRound_q` in [`F7/RoundQ.lean`](F7/RoundQ.lean) gives the result of FPRound__2 on
`±(P/Q) · 2^-1074` for all positive `P` and `Q`: Talos's `roundRationalMagnitude neg P Q`, the
two-stage rounder of `IEEE64.div`, with the FPSR bits of `maskQ P Q`.  For a normal result with
`log2 ⌊P/Q⌋ = 52 + j`, the bounds `2^(52+j) ≤ P/Q < 2^(53+j)` give the exponent `j − 1022`
(`exp_eqR`), the integer mantissa is the quotient of `P` by `Q · 2^j`, and the error is the
remainder over `Q · 2^j`.  For a subnormal one the divisor is `Q`.  `rq_normal` and `rq_sub` state
Talos's two stages over the same quotient and remainder: `roundQuotient_eq` gives the first, and
`rsm_exact` and `rsm_carry` of `F7/Round.lean` the second.  The statements write Talos's word as
`(roundRationalMagnitude neg P Q).toBitVec`, where `F7/Round.lean` uses the definition `tDy`: with
a definition in its place, the kernel's check of the word against that of `f64Div` at
`P = A · 2^1074` reached a 2 GB cap and was stopped after 43 s.  `fpAdd_run`, `fpMul_run`, and
`fpDiv_run` take the 36 pairs of operand types and the signs of infinities and zeros, and
`fpAdd_run` the sign of a nonzero exact sum.

Talos's `sub a b` is `add a (negate b)`.  `negW b`, the word of `negate b`, has the type and the
magnitude of `b` and the opposite sign (`ty_negW`, `sv_negW`, `sg_negW`), so Talos's side of FPSub
becomes FPAdd's with the sign of `b` inverted, and FPSub__1 differs from FPAdd__1 only in its tests
of the signs and in `sub_real`.  `fpSub_run` follows `fpAdd_run` with the exact difference
`(sv a − sv b) · 2^-1074` (`sub_diff`) and `fpRound_run`.

FixedToFP reads the word as the natural `n`, returns +0 for `n = 0`, and otherwise rounds the real
`n / 2^0`.  That real is the magnitude `n · 2^1074` in units of 2^-1074 (`cvt_val`), so
`fpRound_run` gives `roundScaledMagnitude` of `n · 2^1074`.  `fromInt_nat` identifies that word
with Talos's `fromInt n`, which `f64ConvertI64U` computes.

For a positive finite operand of magnitude `N`, FPSqrt rounds `√R · 2^-1074` with the radicand
`R = N · 2^1074`.  Talos's `roundSqrtMagnitude` takes `r = Nat.sqrt R`, the shift
`k = log2 r − 52`, and `l = r / 2^k`, rounds `l` up when `4 · R` exceeds `(2 · l + 1)^2 · 2^(2k)` or
equals it with `l` odd, and packs the result times `2^k` with `roundScaledMagnitude`.  Every such
result is normal: `2^(k+52) ≤ r < 2^(k+53)` and `k + 2 < 2047` for `R` in `[2^1074, 2^3172)`
(`root_facts`).  `round_normalR` in [`F7/RoundR.lean`](F7/RoundR.lean) states FPRoundBase__1's
normal case for a positive real `M` over the exponent of `M`, the scaled mantissa, its floor, and
the decisions of its error against 1/2 and 0, and gives Talos's `roundScaledMagnitude` of the
rounded mantissa times `2^j`; its proof is `round_normalG`'s with these in place of a quotient and
a remainder.  For FPSqrt the scaled mantissa is `√R / 2^k`, whose floor is `l` by Mathlib's
`Real.floor_real_sqrt_eq_nat_sqrt`, and the comparisons of its error become Talos's comparisons of
`4 · R` with `(2 · l + 1)^2 · 2^(2k)` and of `R` with `l^2 · 2^(2k)` (`round_root`).  The tie
`4 · R = (2 · l + 1)^2 · 2^(2k)` cannot occur, since the odd part of `R` has at most 53 bits and
`(2 · l + 1)^2` is odd and above 2^106, but the proof does not use this: both sides round a tie to
even.

FPToFixed unpacks its operand with FPUnpack__1, which gives a NaN the value 0 and an infinity
±2^1000000, signals Invalid Operation for a NaN, and takes the floor of the value and the error
between the value and its floor.  Under FPRounding_ZERO it adds 1 to the floor of a negative value
with a nonzero error, and SatQ clamps the integer to `[0, 2^64 − 1]`.  FPToFixed then signals
Invalid Operation when SatQ clamps, and Inexact when SatQ does not clamp and the error is nonzero.
`bind_satQ` gives SatQ's word and its flag of saturation for every integer.  For a finite word of
magnitude `m` in units of 2^-1074, `fix_pos`, `fix_neg0`, and `fix_neg1` give the floor and the test
of a zero error through the quotient `q` and the remainder `r` of `m` by 2^1074: the floor is `q`
for a word with a clear sign bit, and `−q` or `−q − 1` for a negative one as `r` is 0 or not, so the integer that
SatQ receives is `±q`, the value of Talos's `truncatedInt` (`trunc_fin`).  The value of an infinity
is a natural number of at least 2^64 (`inf_val_nat`), which SatQ clamps, and Talos's `truncatedInt`
gives an infinity and a NaN no value (`trunc_none`).  After these lemmas the proof keeps `q`, `r`,
and the infinity's value as variables, so no step evaluates 2^1074 or 2^1000000.

FPCompare with `signal_nans` false unpacks both operands, returns 0011 when either is a NaN, and
otherwise compares the real values with `eq_real` and `lt_real`.  FPUnpack's value of a word that
is not a NaN is `extV` of Talos's `scaledValue` (`val_extV`): `scaledValue · 2^-1074` for a finite
word, whose `scaledValue` lies strictly between −2^2098 and 2^2098 (`mag_fin_lt`), and ±2^1000000
for an infinity, whose `scaledValue` is ±2^2098 (`mag_inf_eq`).  Every finite value lies strictly
between −2^1024 and 2^1024, so `extV` is strictly increasing on `[−2^2098, 2^2098]`
(`extV_strictMonoOn`), and `eq_real` and `lt_real` of the values equal Talos's `eq` and `lt`, which
compare `scaledValue` (`val_eq_sv`, `val_lt_sv`).  `fpCompare_run` takes the NaN case, with or
without a signaling NaN, and the case of two ordered operands, whose result is the number that
`fcmpNZCV` gives for equal, smaller, and greater values.

Lean's core library, in which Talos is written, and Mathlib elaborate `2 ^ 1074 : ℕ` with
different instances of `Pow`.  When the kernel compares the bit vectors of two words that differ
syntactically, it reduces each projection by evaluating its word, and the evaluation unfolds
`N * 2 ^ 1074` with `N` a variable one successor at a time: a test of such a comparison reached
9.7 GB before the kernel stopped at its recursion limit.  FPDiv's check with a definition in
place of the written-out word, above, also stopped; whether its cause is the same was not tested.
`fromInt_nat` and `tSqrtU` therefore state Talos's side as an equation of words, whose two sides
the kernel compares argument by argument, and the proofs reach each bit vector by rewriting.

| Module | Lines | Contents |
|---|---|---|
| `F7/Base.lean` | 878 | the monad lemmas, the state hypothesis, the read-only lemmas of IsFullA64Enabled (about 250), the FPCR fields, the 72 comparisons of enumeration constants, unpacking and NaNs (about 130), and the loops (about 130) |
| `F7/Round.lean` | 778 | lemmas on words and bit vectors (about 320), Talos's two stages (about 275), and FPRoundBase__1 (about 185) |
| `F7/RoundQ.lean` | 397 | Talos's rounder of a quotient and `maskQ` (about 110), the exponent and mantissa of a rational in FPRoundBase__1 (about 80), and FPRoundBase__1 (about 175) |
| `F7/RoundR.lean` | 137 | FPRoundBase__1's normal case over a real scaled mantissa |
| `F7/FPAdd.lean` | 158 | FPAdd's cases |
| `F7/FPSub.lean` | 212 | the negation of a word and FPSub's cases |
| `F7/FPMul.lean` | 147 | FPMul's cases |
| `F7/FPDiv.lean` | 133 | the exact quotient and FPDiv's cases |
| `F7/FPSqrt.lean` | 343 | the square root on the reals, Talos's rounding of a root, FPRound__2 on a root, and FPSqrt's cases |
| `F7/FixedToFP.lean` | 85 | Talos's conversion and FixedToFP |
| `F7/FPToFixed.lean` | 336 | SatQ, the floor and the error of a word's value (about 120), Talos's truncation, and FPToFixed's cases |
| `F7/FPCompare.lean` | 234 | the bounds of `scaledValue`, `extV` and its monotonicity (about 130), and FPCompare's cases |
| `F7/Isla.lean` | 300 | the join with the Isla equations and the profile witnesses |
| `F7/Round32.lean` | 756 | binary32 fields, unpacking, and NaNs (about 225), the result words and Talos's binary32 rounders with their rational form (about 290), and FPRoundBase__1 at 32 bits on a rational (about 210) |
| `F7/FPAdd32.lean` | 164 | FPAdd's cases at 32 bits |
| `F7/FPSub32.lean` | 200 | the negation of a single and FPSub's cases |
| `F7/FPMul32.lean` | 126 | the exact product and FPMul's cases |
| `F7/FPDiv32.lean` | 130 | the exact quotient and FPDiv's cases |
| `F7/FPSqrt32.lean` | 397 | FPRoundBase__1's normal case at 32 bits over a real mantissa, the root, and FPSqrt's cases |
| `F7/FixedToFP32.lean` | 174 | UCVTF S←X's and SCVTF S←W's FixedToFP |
| `F7/FPToFixed32.lean` | 451 | FCVTZU X←S's and FCVTZS W←S's FPToFixed, with SignedSatQ at 32 bits |
| `F7/FPCompare32.lean` | 217 | FPCompare's cases at 32 bits |
| `F7/Isla32.lean` | 213 | the join with the 32-bit Isla equations |

`lake build F7` on edgexpert-18ff under `tools/leanrun --cpus 2`, after the translation is built,
takes `F7.Base` 47 to 51 s, `F7.Round` 48 to 60 s, `F7.FPAdd` 35 to 38 s, `F7.FPMul` 42 to 43 s,
`F7.RoundQ` 43 to 48 s, `F7.FPDiv` 37 to 38 s, and `F7.Isla` 2 to 3 s, at a peak of 2.9 GB.
In separate builds with 1 or 2 CPUs, `F7.FPSub` takes 39 s, `F7.RoundR` 29 s, `F7.FPSqrt` 10 to
13 s, `F7.FixedToFP` 2 to 3 s, `F7.FPToFixed` 8 to 10 s, and `F7.FPCompare` 3 to 5 s.  The heartbeat limits are about twice the measured use: 406,886
thousand heartbeats for `fpProcessNaNs_run`, 649,219 for `round_normalG`, 182,938 for
`round_subG`, 653,810 for `round_normalQ`, 182,566 for `round_subQ`, 401,760 for `round_normalR`,
442,830 for `fpAdd_run`, 448,450 for `fpSub_run`, 488,265 for `fpMul_run`, and 451,965 for
`fpDiv_run`.  `fixedToFP_run` (3,308), `round_root` (17,241), and `fpSqrt_run` (92,831) check
under the default limit of 200,000, and `fpToFixed_run` (81,332) and `fpCompare_run` (18,072)
under limits of 160,000 and 40,000.  In separate builds with 2 CPUs, `F7.Round32` takes 60 s,
`F7.FPAdd32` 37 s, `F7.FPSub32` 42 s, `F7.FPMul32` 58 s and `F7.FPDiv32` 46 s side by side,
`F7.FPSqrt32` 30 s, `F7.FPToFixed32` 14 s, `F7.FPCompare32` 3 s, `F7.FixedToFP32` 2 s, and
`F7.Isla32` 1 to 2 s, at a peak of 3.2 GB.  Their limits are about twice the measured use: 411,630
thousand heartbeats for `fpProcessNaNs_run32`, 656,024 for `round_normalQ32`, 183,392 for
`round_subQ32`, 402,941 for `round_normalR32`, 457,325 for `fpAdd32_run`, 455,960 for
`fpSub32_run`, 501,100 for `fpMul32_run`, 458,462 for `fpDiv32_run`, 82,021 for `fpToFixed32_run`,
84,840 for `fpToFixed32S_run`, and 18,268 for `fpCompare32_run`; `fpUnpack_run32` (55,145),
`round_root32` (17,875), `fpSqrt32_run` (90,718), `fixedToFP32_run` (3,454), and `fixedToFP32S_run`
(3,500) check under the default limit.

FPMul cost 147 lines of its own and about 200 lines of the rounding's generalization: the pilot's
rounding at the fixed scale 2^-1074 took about 500 lines, and its generalization over `X`, which
also serves FPAdd, about 700.  FPDiv cost 133 lines of its own and 397 lines of the rational
rounding, 530 in all, against an estimate of 650 to 700 from FPMul's measures.  The rational
rounding takes from `F7/Round.lean` the lemmas on words and bit vectors, `rsm_exact`, `rsm_carry`,
and the lemmas `floor_div_nat`, `err_div`, `gt_half`, and `eq_half`, which hold for every natural
divisor, and its proofs of FPRoundBase__1 follow `round_normalG` and `round_subG` step by step,
with the divisor `Q · 2^j` or `Q` in place of `2^(X + j)` or `2^X`.  FPSub took 212 lines,
FixedToFP 85, FPSqrt 343 with the 137 of `RoundR.lean`, FPToFixed 336, and FPCompare 234.

## The binary32 proofs

The translated functions take the width of their operands as an implicit argument, so `FPAdd a b
0x02000000` on 32-bit words is FPAdd at 32 bits, and each root of the slice serves both widths.
The modules `F7/*32.lean` prove the 32-bit counterparts of the 64-bit theorems for every pair of
words, or every word, from every state that satisfies `Hyp`, with FPSR's update and the frame:
`fpAdd32_eq_f32Add`, `fpSub32_eq_f32Sub`, `fpMul32_eq_f32Mul`, `fpDiv32_eq_f32Div`, and
`fpSqrt32_eq_f32Sqrt` give Talos's `f32Add`, `f32Sub`, `f32Mul`, `f32Div`, and `f32Sqrt` with the
masks `addMask32`, `subMask32`, `mulMask32`, `divMask32`, and `sqrtMask32`, whose bits are those of
the 64-bit masks; `fixedToFP32_eq_f32ConvertI64U` gives `f32ConvertI64U` for
`FixedToFP a 0 true 0x02000000 FPRounding_TIEEVEN 32` on a 64-bit word, the call of UCVTF S←X,
and `fixedToFP32_eq_f32ConvertI32S` gives `f32ConvertI32S` for
`FixedToFP a 0 false 0x02000000 FPRounding_TIEEVEN 32` on a 32-bit word, the call of SCVTF S←W,
with `cvtMask32` and `cvtMask32S`.  The signed conversion holds for the translation with the
explicit conversions of `fix-output.sh` (Elaboration), and it fails for the translation with
lean-sail's coercion, whose SInt maps every negative operand to 0.
`fpToFixed32_eq_i64TruncSatF32U` gives `i64TruncSatF32U` for
`FPToFixed a 0 true 0x02000000 FPRounding_ZERO 64` on a 32-bit word, the call of FCVTZU X←S, and
`fpToFixed32S_eq_i32TruncSatF32S` gives `i32TruncSatF32S` for
`FPToFixed a 0 false 0x02000000 FPRounding_ZERO 32`, the call of FCVTZS W←S, with `fixMask32` and
`fixMask32S`: IOC for a NaN, an infinity, or a truncation outside the integer range, and IXC for
an inexact truncation inside it.  `fpCompare32_eq_fcmpNZCV32` gives the flags `fcmpNZCV32` of
`State.fcmpS` for `FPCompare a b false 0x02000000` on 32-bit words, the call of FCMP S, with
`cmpMask32`: IOC for a signaling NaN operand.

[`F7/Round32.lean`](F7/Round32.lean) holds the 32-bit unpacking (`fpUnpack_run32`), the processing
of NaNs (`fpProcessNaNs_run32`), and one rounding lemma.  `fpRound32_q` gives the result of
FPRound__2 at 32 bits on `±(P/Q) · 2^-149` for all positive `P` and `Q`: Talos's
`IEEE32.roundRationalMagnitude neg P Q` with the FPSR bits of `maskQ32 P Q`.  Its proof is
`fpRound_q`'s with the binary32 constants: for `log2 ⌊P/Q⌋ = 23 + j` the loops give the exponent
`j − 126`, the integer mantissa is the quotient of `P` by `Q · 2^j`, and the error is the remainder
over `Q · 2^j`; for a subnormal result the divisor is `Q`.  Talos's binary32 rounders encode a
normal result directly where the binary64 ones pass it to `roundScaledMagnitude`, so `rq_normal32`
unfolds `roundRationalMagnitude` for `j ≥ 1` and uses `rsm_exact32` and `rsm_carry32` for `j = 0`.
The other rounders are instances of the rational one: `rsm_eq_rrm32` states that
`roundScaledMagnitude neg N`, the rounder of a sum and of an integer, is
`roundRationalMagnitude neg N 1`, and `rdm_eq_rrm32` that `roundDyadicMagnitude neg N X`, the
rounder of a product, is `roundRationalMagnitude neg N (2^X)`.  The exact sum or difference of two
finite operands is an integer `z` times 2^-149, the rational `|z| / 1`; the exact product of the
magnitudes `A` and `B` in units of 2^-149 is `(A · B) / 2^149`, the exact quotient
`(A · 2^149) / B`, and the converted integer `z` is `(|z| · 2^149) / 1`.  FPSqrt's root is irrational
in general, and `round_normalR32` in [`F7/FPSqrt32.lean`](F7/FPSqrt32.lean) states FPRoundBase__1's
normal case at 32 bits over the scaled mantissa, as `round_normalR` does at 64 bits; the radicand
`N · 2^149` of a positive finite single lies in `[2^149, 2^426)`, so every root is normal, with the
shift `log2 (Nat.sqrt R) − 23` below 253 (`root_facts32`).  FPToFixed and FPCompare at 32 bits
follow `F7/FPToFixed.lean` and `F7/FPCompare.lean` with the binary32 unpacking: the truncation of a
finite single is the quotient of its magnitude by 2^149, and FPUnpack's value of a single that is
not a NaN is strictly increasing in Talos's `scaledValue`, which lies in `[-2^277, 2^277]`
(`extV32_strictMonoOn`).  SignedSatQ at 32 bits returns the low 32 bits of the saturated integer,
`BitVec.ofInt 32` (`bind_satQS`), which is Talos's `intToUInt32` inside `(-2^31, 2^31 - 1)`.  The
statements write Talos's words without a definition in between, and `tSqrtU32`, `fromInt32`, and
`fromInt32_nat` state Talos's side as equations of words, for the reason above.

`F7/Isla32.lean` joins each theorem to its 32-bit Isla equation in the pattern of `F7/Isla.lean`:
`fpAdd32Eq_of_sail`, `fpSub32Eq_of_sail`, `fpMul32Eq_of_sail`, `fpDiv32Eq_of_sail`,
`fpSqrt32Eq_of_sail`, `fixedToFP64_32Eq_of_sail`, `fixedToFP32_32Eq_of_sail`,
`fpToFixed32_64Eq_of_sail`, `fpToFixed32_32Eq_of_sail`, and `fpCompare32Eq_of_sail` derive
`FPAdd32Eq`, `FPSub32Eq`, `FPMul32Eq`, `FPDiv32Eq`, `FPSqrt32Eq`, `FixedToFP64_32Eq`,
`FixedToFP32_32Eq`, `FPToFixed32_64Eq`, `FPToFixed32_32Eq`, and `FPCompare32Eq` from the links
`SailFPAdd32` and the others, each the claim of its 64-bit counterpart with the 32-bit wrapper of
`tests/isla/armv9p4-checked-fp.diff`, or, for FCMP S, with the call of FPCompare on two 32-bit
operands.  FRINTN's equation `FPRoundInt32Eq` has no proof: FPRoundInt rounds the signed value to
an integer and passes the result to FPRound__1 with `FPRounding_ZERO`, a rounding mode that no
lemma here covers.

## The join with the Isla equations

`FPAddEq A` (`LeanExe/A64/Isla/Float.lean`) constrains the meaning `A` that Isla's semantics gives
the abstract call `FPAdd64`, on Isla's values: two 64-bit vectors and the struct of FPCR whose one
field `bits` holds 0x02000000.  The theorems here speak of the translation's functions on
`BitVec 64`, with FPCR a `BitVec 64`, from a state that satisfies `Hyp`.  `SailFPAdd A` in
[`F7/Isla.lean`](F7/Isla.lean) states the link between the two: from every state that satisfies
`Hyp`, whatever the translation's `FPAdd a b 0x02000000` returns, `A` returns on the same words and
on `islaFPCR fpcrV`, the struct whose `bits` holds FPCR.  Lean does not check the link.  It rests on
three claims that review supports: the IR's `zFPAdd64` returns `zFPAdd`'s result at 64 bits
(`tests/isla/armv9p4-checked-fp.diff`); the IR's `zFPAdd`, which isla-sail compiled from sail-arm
`111345b`, computes what the translation's FPAdd, from `7d0581642`, computes (Sources); and Isla's
state at each abstract call, read as a register map of the translation, satisfies `Hyp`.  Since
the pilot's result is the same from every state that satisfies `Hyp`, quantifying the link over all
of them asks of Isla only what holds at the state of the call.  `fpAddEq_of_sail` derives
`FPAddEq A` from `SailFPAdd A` and `fpAdd_eq_f64Add`, converting between `UInt64` and `BitVec 64`,
and `fpSubEq_of_sail`, `fpMulEq_of_sail`, `fpDivEq_of_sail`, `fpSqrtEq_of_sail`, and
`fixedToFPEq_of_sail` derive `FPSubEq`, `FPMulEq`, `FPDivEq`, `FPSqrtEq`, and `FixedToFPEq` from
the links `SailFPSub`, `SailFPMul`, `SailFPDiv`, `SailFPSqrt`, and `SailFixedToFP` likewise.
`SailFixedToFP` also identifies two of Isla's argument values with the translation's: the integer
`fbits` 0, which Isla passes as the 128-bit vector 0, as it passes every integer of the model, and
the rounding mode, which Isla passes as the enumeration member `FPRounding_TIEEVEN` by name.
`fpToFixedEq_of_sail` derives `FPToFixedEq` from `SailFPToFixed` in the same way, with the rounding
mode `FPRounding_ZERO`.  FCMP calls FPCompare without a wrapper, so `SailFPCompare` links the
abstract call `FPCompare` on two 64-bit operands, `signal_nans` false, and FPCR to the
translation's FPCompare, and `fpCompareEq_of_sail` derives `FPCompareEq` from it and
`fpCompare_eq_fcmpNZCV`, reading the 4-bit result as the number `fcmpNZCV`.

The derivation needs a state that satisfies `Hyp`, and the witness comes from the profiles.
`islaState p u` builds the registers that `Hyp` names from the profile `p` of
`LeanExe/A64/Isla/Profile.lean` and its unknown values `u`: FeatureImpl from the values of the
`features` file's lines in order, with `u.feature` last, as `InitFeatureImpl` builds it; PSTATE
with the fields that `Profile.sys` sets and those of `u`; SCR_EL3, HCR_EL2, and SMCR_EL3 as the
profile sets them; SMCR_EL1 and SMCR_EL2 from `u`; and FPSR 0.  `hyp_tcg`, `hyp_kvm`, and
`hyp_sme` prove `Hyp` for every `u` under each profile, reading FEAT_AA64EL0 to FEAT_AA64EL3
through the translation's `num_of_Feature`, and `names_tcg`, `names_kvm`, and `names_sme` prove
that the line of each `features` file at the index `num_of_Feature F` names `F`, for the features
that the proofs read: FEAT_AA64EL0 to FEAT_AA64EL3, FEAT_AFP, FEAT_SME, FEAT_SME_FA64, FEAT_VHE,
and FEAT_SEL2.  The theorems depend on `propext`, `Classical.choice`, and `Quot.sound` only.

## The check

[`check.sh`](check.sh) regenerates the translation from pinned inputs and checks the proofs
against it, on a host with Sail 0.20.3 in the opam switch `sail-0.20.3`, a scratch copy of the
repository whose `.lake/packages` are built, sail-arm at `7d0581642`, and lean-sail at `v6`.  It
copies the model files that `translate.sh` reads and lean-sail's sources into a new work
directory, applies `lean-sail-v6.diff`, and translates the slice with the options of the
real-number translation.  It compares the SHA-256 hashes of the model files, of lean-sail's
sources after the patch, of every generated file, and of the files after `fix-output.sh` with
[`check.sha256`](check.sha256), and fails on a difference; `--record` writes the file instead.
It then builds the translation and the library `F7` of [`F7/`](F7/) in the copy, whose lakefile
gains the libraries `Sail`, `Armv9fp`, and `F7`, first with `undefined_real` returning the
opaque constant `opaqueReal` and then as generated.  After each build it prints the axioms of
the theorems that [`Axioms.lean`](Axioms.lean) names and fails on any axiom besides `propext`,
`Classical.choice`, and `Quot.sound`.  The repository's own build takes neither Sail nor
lean-sail: whether it should is a decision on dependencies that remains open.

A run with `--record` wrote `check.sha256`, and a second run, which compared the hashes with it,
found every hash equal, so the translation is reproducible from the pinned inputs.

| Measure | Value |
|---|---|
| A run on edgexpert-18ff under `tools/leanrun --cpus 2`, with FPAdd and FPMul | 11 min 30 s, peak 4.1 GB |
| Its parts | translation about 30 s; each of the two builds `Armv9fp` 149 to 159 s, `F7.Base` 47 to 48 s, `F7.Round` 50 to 66 s, `F7.FPAdd` 38 to 44 s, `F7.FPMul` 42 to 48 s, `F7.Isla` 2 s |
| A run under `tools/leanrun --cpus 3`, with FPAdd, FPMul, and FPDiv | 13 min 16 s, peak 4.1 GB |
| Its parts | each of the two builds `Armv9fp` 157 to 162 s, `F7.Base` 45 to 46 s, `F7.Round` 47 s, then `F7.FPAdd`, `F7.FPMul`, and `F7.RoundQ` side by side in 62 to 82 s each, `F7.FPDiv` 37 to 39 s, `F7.Isla` 2 to 3 s |
| A run under `tools/leanrun --cpus 3`, with the six functions | 12 min 48 s, peak 4.2 GB |
| Its parts | each of the two builds `Armv9fp` 137 to 144 s, `F7.Base` 43 to 48 s, `F7.Round` 43 to 48 s, then the other modules side by side: `F7.FPAdd` 41 to 51 s, `F7.FPSub` 38 to 39 s, `F7.FPMul` 42 to 44 s, `F7.RoundQ` 50 to 55 s, `F7.RoundR` 32 to 43 s, `F7.FPDiv` 37 to 40 s, `F7.FPSqrt` 10 s, `F7.FixedToFP` 2 to 3 s, `F7.Isla` 2 s |
| A run under `tools/leanrun --cpus 4` without lean-sail's coercion `CoeT Int x Nat`, with the slice of nine roots, the 64-bit functions, FPToFixed and FPCompare at 64 bits, and the 32-bit FPAdd, FPSub, FPMul, FPDiv, FPSqrt, and UCVTF S←X | 14 min 23 s, peak 4.1 GB |
| A run under `tools/leanrun --cpus 4` with every theorem of `Axioms.lean`, the 32-bit conversions and FPCompare among them | 13 min 58 s, peak 4.1 GB, every hash equal to `check.sha256` |
| Its parts | each of the two builds `Armv9fp` 118 to 140 s, `F7.Base` 41 s, `F7.Round` 42 s, then the other modules side by side, among them `F7.Round32` 53 to 54 s, `F7.FPAdd32` 35 s, `F7.FPSub32` 38 s, `F7.FPMul32` 40 s, `F7.FPDiv32` 39 s, `F7.FPSqrt32` 28 to 29 s, `F7.FPToFixed32` 16 s, `F7.FPCompare32` 3 s, `F7.FixedToFP32` 2 s, and `F7.Isla32` 1 s |

## What the proofs trust

A theorem of `F7/` speaks about the Lean translation; it states Arm's functions only as far as
the chain below translates the ASL faithfully.

| Item | Role |
|---|---|
| Arm's ASL and its translation into Sail by sail-arm | the specification that the Isla check also trusts |
| Sail 0.20.3's front end, rewrites, and Lean back end, which its authors call experimental, with its eager `&&` and `\|\|` | the translation of the Sail slice into Lean |
| lean-sail v6 with `lean-sail-v6.diff` | the monad, register map, bit-vector operations, and `whileFuelM`.  v6 has two defects: the coercion `CoeT Int x Nat`, which the diff deletes, and `set_slice_int`, which computes `toInt (updateSubrange' (ofInt len n) lo len x)` and so gives −1 for `[int_mant with 0 .. 0 = 0b1]`; the translation reaches `set_slice_int` only in FPRoundBase__1's `FPRounding_ODD` branch, which no theorem of `F7/` enters.  lean-sail `v9` fixes `set_slice_int` and keeps the coercion |
| The back end's reliance on lean-sail's coercion `CoeT Int x Nat`, which maps a negative integer to 0 | removed: the translation elaborates without the coercion after the conversions below |
| The explicit conversions of `fix-output.sh`: the type Int of `asl_Int`'s `result`, and `.toNat` in `integer_subrange` (the width from `hi` and `lo`, and `lo`), `integer_update_subrange` (the width), FPInfinity, FPMaxNormal, FPZero, and FPDefaultNaN__1 (the widths `E`, `F`, `E − 1`, and `F − 1`), FPProcessException (`enable` and `cumul`), FPRoundBase__1 (the fuel of each loop and the widths `N − (E + F + 1)` and `N − 1`), and FPProcessNaN__1 (`topfrac`), and in `to_bytes_le`, `from_bytes_le`, `slice_zeros_concat`, `subrange_zeros_concat`, `sext_slice`, `unsigned_subrange`, and `vector_update_subrange_from_integer_subrange`, which no theorem of `F7/` reaches | each value is nonnegative by the guarantee of the model that the script's comment cites, except in `sext_slice`, `slice_zeros_concat`, and `subrange_zeros_concat`, whose types do not bound each operand; each conversion other than `asl_Int`'s elaborates to the coercion's term |
| The back end's `Real.lean` | the real-number primitives on Mathlib's ℝ, and `Int.floor` for `round_down` |
| `ArmExtras.lean` | `sign_extend`, and the stand-ins of the two cut trap functions |
| The slice: the files that `translate.sh` omits and the cut at the trap functions | the definitions that the translation contains |
| `fp-measures.sail` | the loop measures, whose sufficiency `loop1_exit` and `loop2_exit` prove |
| `fix-output.sh` | the textual edits above |
| The sources: sail-arm `7d0581642` in place of the IR's `111345b`, and Sail 0.20.3's library in place of `f3da8185`'s | the comparisons in Sources |
| `armv9p4-checked-fp.diff`: `FPAdd64`, `FPSub64`, `FPMul64`, `FPDiv64`, and `FPSqrt64` return `FPAdd`, `FPSub`, `FPMul`, `FPDiv`, and `FPSqrt` at 64 bits, `FixedToFP64` returns `FixedToFP` at N = 64, and `FPToFixed64` returns `FPToFixed` at M = 64 | in the Isla row |
| `armv9p4-checked-fp.diff`: `FPAdd32`, `FPSub32`, `FPMul32`, `FPDiv32`, and `FPSqrt32` return `FPAdd`, `FPSub`, `FPMul`, `FPDiv`, and `FPSqrt` at 32 bits, `FixedToFP64_32` and `FixedToFP32_32` return `FixedToFP` at N = 32, and `FPToFixed32_64` and `FPToFixed32_32` return `FPToFixed` of a 32-bit operand at M = 64 and M = 32 | in the Isla row |
| The links `SailFPAdd`, `SailFPSub`, `SailFPMul`, `SailFPDiv`, `SailFPSqrt`, `SailFixedToFP`, `SailFPToFixed`, and `SailFPCompare`: each IR function and the translation's function compute the same function, Isla's values correspond to the translation's, among them the 128-bit integers and the enumeration members of `FixedToFP64` and `FPToFixed64` and the Boolean `signal_nans` of `FPCompare`, and Isla's state at each abstract call satisfies `Hyp` | the join of the section above; `hyp_tcg`, `hyp_kvm`, `hyp_sme`, and the `names_` theorems check the profile part |
| The links `SailFPAdd32`, `SailFPSub32`, `SailFPMul32`, `SailFPDiv32`, `SailFPSqrt32`, `SailFixedToFP64_32`, `SailFixedToFP32_32`, `SailFPToFixed32_64`, `SailFPToFixed32_32`, and `SailFPCompare32`: the claims of the 64-bit links for the 32-bit wrappers and for FPCompare on 32-bit operands | the join of `F7/Isla32.lean` |

## Commands

On a host with the Debian packages, with `$S` sail-arm at `7d0581642`, `$M` its arm-v9.4-a
directory, `$L` lean-sail v6, `$T` this directory, `$O` an output directory, `$W` a new work
directory, and `$R` a scratch copy of the repository whose `.lake/packages` are built:

```sh
sh $T/install.sh
sh $T/check.sh $S $L $R $W
opam exec --switch sail-0.20.3 -- sh $T/translate.sh $M $O/real armv9fp $T/fp-slice.isail \
  --lean-real-numbers --lean-noncomputable --lean-single-file
opam exec --switch sail-0.20.3 -- sh $T/translate.sh $M $O/float armv9float $T/fp-slice.isail \
  --lean-single-file
opam exec --switch sail-0.20.3 -- sh $T/translate.sh $M $O/rat armv9rat $T/fp-slice.isail \
  --lean-single-file
cp -R $L $L-lean434 && patch -d $L-lean434 -p1 < $T/lean-sail-v6.diff
sh $T/probe429.sh $O/float/armv9float $O/v429
sh $T/probe434.sh $R $L-lean434 $O
sh $T/lean-file.sh $R $T/Check.lean
sh $T/lean-file.sh $R $T/Vectors.lean
opam exec --switch sail-0.20.3 -- sh $T/emu/build.sh $M $O/emu
sh $T/emu/check.sh $O/emu/fpemu $R/tmp/sail/vectors.txt $O/emu/vectors.out
```

`probe434.sh` elaborates both translations in `$R` and runs `Eval.lean`; `Vectors.lean` needs
`lake build TestSupport.A64.FpVectors` in `$R` first.  With `$A` and `$B` the `src` directories
of sail-arm `111345b` and `7d0581642`, `uv run $T/srcdiff.py $A $B
$O/real/armv9fp/Armv9fp.lean prelude.sail v8_base.sail stubs.sail interface.sail impdefs.sail
fetch.sail` lists the changed definitions, and `ConstDump.lean`, with the module name
substituted, writes `consts.txt` in a project that `probe429.sh` built.
