# Sail's Lean back end on the floating-point functions

These scripts translate the floating-point functions of the Armv9.4-A Sail model into Lean with
Sail's Lean back end, elaborate the output, and evaluate it against Talos's binary64 functions.
They measure whether the equations that the A64 Isla check assumes, such as
`FPAdd(a, b, 0x02000000) = f64Add a b`, can be proved from a mechanical translation of Arm's
pseudocode.  Nothing in the model or its proofs depends on them.

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

## Translation

[`translate.sh`](translate.sh) type-checks the model, runs the REPL commands of
[`fp-slice.isail`](fp-slice.isail), and writes a Lake project.  The commands keep the definitions
that FPAdd, FPSub, FPMul, FPDiv, FPSqrt, FixedToFP, and `initialize_registers` reach, with the
standard library, and apply the Lean rewrites.  The slice keeps `initialize_registers` because
the back end's rewrite `add_register_init_function` calls it.  `:rewrite move_termination_measures`
runs before the slice, which would otherwise drop the loop measures.  The model's files after
`mem.sail` other than `decode_end.sail` and `fetch.sail` are left out: Sail parses and checks
every file before the slice, and the whole model exceeded a 7 GiB cap after 7 min.  The options
are `--lean-real-numbers` (Mathlib's ℝ for the specification's reals), `--lean-noncomputable`,
and `--lean-single-file`, without which the back end fails on the slice with
`Invalid_argument("List.combine")`.  [`ArmExtras.lean`](ArmExtras.lean) supplies
`sign_extend`, as sail-arm's own `lean/ArmExtras.lean` does for a later Sail.

| Measure | Value |
|---|---|
| Time | 31 s, with Sail's cache of Z3 results (`sail_smt_cache`) |
| Peak memory | 1.4 GB |
| Output | 13,233 lines (1.58 MB) with 1,385 definitions, and 4,262 lines (103 KB) of types |
| Floating-point definitions | 1,209 lines, of which FPRoundBase__1 has 292 and FPUnpackBase__1 223 |

The output is monadic.  Each function runs in `SailM`, an `EStateM` over a map from the
model's registers to their values, and reads the registers it needs.  FPAdd has the type
`BitVec k_N → BitVec k_N → BitVec 64 → SailM (BitVec k_N)`.  Unpacking yields a real number,
the arithmetic is on ℝ, and FPRoundBase__1 normalizes with two `while` loops over ℝ and rounds
with `Int.floor` and comparisons with 1/2.  `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for the six functions ([`Check.lean`](Check.lean)).

## Elaboration

The back end's output does not elaborate as written, on either Lean version.
[`fix-output.sh`](fix-output.sh) makes the edits below, each of which keeps the meaning of the
definitions, and [`lean-sail-v6.diff`](lean-sail-v6.diff) applies to lean-sail the fix that its
tag `v9` carries.

| Failure | v4.29.0 | v4.34.0-rc2 | Edit |
|---|---|---|---|
| Generated `lakefile.toml` lacks a newline before Mathlib's `rev` | with reals | with reals | none (the scripts do not use it) |
| `Real.lean` opens a namespace `Defs` that no output declares | with reals | with reals | delete the line |
| `sign_extend` unknown | yes | yes | ArmExtras.lean |
| `ThisInstrLength` unknown without `fetch.sail` | yes | yes | add `fetch.sail` |
| FPRoundBase__1 writes the real 0.5 as `1/2` unparenthesized, so `gt_real e 1/2` parses as `(gt_real e 1) / 2` | yes | yes | `(1/2)` |
| A comparison of two `BitVec.join1 [b]` in IncrementInstructionCounter does not finish (`whnf`) | yes | yes | compare the bits |
| lean-sail `ArchSemSequential.lean`: `Decidable (0 < choice)` | no | yes | lean-sail-v6.diff |
| `assert` at the start of a do element parses as Lean's assert element | no | yes | qualify the 119 calls |
| The do elaborator fails on MaybeZeroSVEUppers ("Failed to assign join point RHS") | no | yes | `backward.do.legacy` for that definition |

With the edits, [`probe429.sh`](probe429.sh) builds the Float-valued output (no Mathlib) with
Lean v4.29.0 in 235 s and 4.1 GB, and [`probe434.sh`](probe434.sh) builds the real-number
output with the repository's toolchain and Mathlib in [`elaborate.sh`](elaborate.sh)'s scratch
copy of the repository in 187 s and 4.1 GB.  The first build reports no warning and the second
only Mathlib's naming warnings.

## Evaluation

The real-number output is noncomputable.  [`RatReal.lean`](RatReal.lean) replaces the back end's
Float-valued reals with Lean's exact `Rat`, which holds every value that FPAdd, FPSub, FPMul,
FPDiv, and FixedToFP compute.  The definitions are otherwise the same text as the real-number
output.  [`Eval.lean`](Eval.lean) runs each function at 64 bits under FPCR `0x02000000` from
the registers that `sail_model_init` sets, with Sail's fixed choice for unspecified values and
with AArch64 implemented at EL0 and EL1, and compares the result
with Talos's `f64Add`, `f64Sub`, `f64Mul`, `f64Div`, and `f64ConvertI64U`.  On 10,484 operand
pairs per binary operation (all pairs of 22 special values, 5,000 pairs with exponents within 2
of each other, and 5,000 random bit patterns) and 10,086 integers for FixedToFP, every result
agrees, in 29 s.  FPSqrt has no rational evaluation and is not tested.

## Loops

Lean's `while` is `repeatM`, whose unfolding lemma `Lean.Loop.forIn_eq_of_monadTail` needs a
`Lean.Order.MonadTail` instance.  Lean v4.34.0-rc2 has none for `EStateM` and so none for
`SailM`.  [`fp-measures.sail`](fp-measures.sail) gives the back end the loop measures of
FPRoundBase__1 that sail-arm writes for Rocq only, and the back end then writes the loops with
lean-sail's `whileFuelM`, which recurses on its fuel.  That output elaborates with the
repository's toolchain in 181 s.  The fuel, ⌈1/m⌉ for the loop that doubles a mantissa m below
1 and ⌈m⌉ for the loop that halves one at or above 2, is at least 2^(k-1) for a loop of k
iterations, and so at least k.

## Commands

On a host with the Debian packages, with `$M` sail-arm's arm-v9.4-a directory, `$L` lean-sail v6,
`$T` this directory, `$O` an output directory, and `$R` a scratch copy of the repository whose
`.lake/packages` are built:

```sh
sh $T/install.sh
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
```

Adding `$T/fp-measures.sail` at the end of the first command gives the fuel-bounded loops.
