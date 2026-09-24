# Certified scalar compilation: working agenda

## Authorization and branch

Work on `correct`, created from `typesafety` at
`834ba204d84720e00deef9b4ce476d4a04e55ff4` on 2026-09-24.
The user's spelling `typesatefy` means the reviewed `typesafety` branch.
The user approved the whole agenda below, allowed appropriate changes to the
existing type work, explicitly authorized direct Lean execution here, and
requested continued work, frequent commits/pushes, and an updated `task.md`
until the entire plan is complete.

The preceding working state is preserved in
`plans/typesafety-working-state-2026-09-24.md`.

## Current checkpoint

- Branch created and cloned at the base commit.
- Pinned Lean 4.34.0-rc2 / 6a10ac8c22beadecabdbb0919c2b50214762f91d is installed and checked.
- Independent scalar grammar/admission and affine/choose source certificates pass; audits use only propext.
- The GCD loop feasibility gate passes against the unchanged TalosGcd.gcd.
- All five pilot source certificates pass, including Prng.mix and ScalarHelper.caller.
- Next: generic lowering and exact bytes.
- Talos dependencies are cloned; targeted Mathlib cache acquisition is in progress.

## Objective and precise claim

Implement `scalar64` with a proved backend and checked certificates connecting
the original Lean declaration to exact emitted WASM bytes. The first release
covers arithmetic, branching, scalar helper calls, and terminating loops.
Generation success or differential testing is not certification.

A certified binary must be valid and, for every source input, terminate with
the corresponding source result and preserve surrounding state, subject to the
explicit ABI and model assumptions. General simulation may assume a terminating
source execution; each certified package supplies the necessary evidence.
The original Lean declaration and exact byte value must occur in the checked
dependency chain. A hand-reconstructed source specification is insufficient.

The compiler and certificate generator can remain untrusted. The guarantee
covers every compilation accepted by the independent certificate checker.
Generic backend theorems must cover the admitted profile, not only the pilots.

## First profile

| Part | Initial scope |
|------|---------------|
| Interface | Any fixed number of UInt64 arguments; one UInt64 result. |
| Values | 64-bit words and Boolean conditions. |
| Arithmetic | Modular add/sub/mul; unsigned div/rem/comparisons; bitwise operations and masked shifts. |
| Control | Constants, variables, strict lets, conditionals. |
| Calls | Direct scalar helpers with an acyclic call graph. |
| Iteration | Structured loops with scalar carried values; selected tail recursion through proved conversion to loops. |
| Runtime | No heap, memory access, mutable globals, imports, or host effects in the certified module. |

WASM i64 represents words; instruction selection supplies unsigned semantics.
Other widths and signed operators are later extensions. Nat may occur in proofs
and termination measures without being an admitted runtime type. Preserve
modular arithmetic, division by zero returning zero, remainder by zero returning
the dividend, and shift counts modulo 64.

## Complete agreed plan

### 1. Profile and theorem statement

- [x] Independent scalar admission judgment and terminating checker.
- [x] Checker soundness and completeness.
- [ ] Explicit ABI, core execution contract, value representation, source
      certificate, and final artifact contract.
- [ ] Well-formed locals, calls, indices, signatures, exports, and result arities.
- [ ] Explicit numeric behavior and termination premises.

### 2. Existing type work

- [ ] Reuse word w64, arithmetic laws, typing, machine semantics, renaming,
      and sequencing.
- [x] Use ordinary typing and strict evaluation; relevance is separate.
- [ ] Allow unused scalar parameters/bindings and justify discarded evaluation.
- [ ] Specify loops independently, directly or by proved recursive expansion.
- [ ] Relate the profile to the independent language; do not substitute the
      diagnostic compiler IR evaluator as its semantics.

### 3. Source certificates: early feasibility gate

- [ ] Freeze scalar-core representations and prove certificates naming the
      original Lean functions.
- [ ] Reusable arithmetic, binding, branch, call, and iteration certificate rules.
- [x] Arithmetic.affine certificate.
- [x] Arithmetic.choose certificate.
- [x] Loop certificate before large backend work.
- [ ] Certificate generation with explicit rejection of unsupported source forms.

### 4. Verified scalar backend

- [ ] Total scalar lowering used by the actual certified compiler path.
- [ ] Explicit semantics and well-formedness for any intervening IR.
- [x] Primitive lowering, including guarded division and remainder.
- [ ] Locals, strict staging, scratch noninterference, and branches.
- [ ] Helper calls, arguments, and returns.
- [ ] Loops, simultaneous carried updates, and termination transfer.
- [ ] Module validity and function/type/export indexing.
- [ ] Scalar-only module assembly without unused allocator machinery.
- [ ] Generic correctness for every admitted well-formed program, without
      handwritten per-program WASM instruction proofs.

### 5. Exact bytes and certified compilation

- [ ] Independent artifact decoding and validation.
- [ ] Full decoded-module equality with verified lowering.
- [ ] Composition of source correspondence, lowering, and byte equality.
- [ ] Explicit compile-certified --profile scalar64 command or equivalent.
- [ ] Fail closed on unsupported source, stale evidence, or failed checking.
- [ ] Portable package recording source, core/IR, ABI, export, bytes, certificates,
      theorem names, and pinned dependencies.
- [ ] Independent verification without running the compiler or proof generator.

### 6. Acceptance and reproducibility

- [ ] Arithmetic.affine: multiple inputs and modular arithmetic.
- [ ] Arithmetic.choose: both branches.
- [ ] Prng.mix: bitwise arithmetic, shifts, and large constants.
- [ ] Helper-call fixture: call graph, staging, and return convention.
- [ ] TalosGcd.gcd: carried loop state, remainder, and termination.
- [ ] All pilots share compiler theorems; program-specific work is source
      correspondence and termination.
- [ ] Dependency audits retaining the type-safety policy: no proof holes, added
      axioms, or native-evaluation proof shortcuts.
- [ ] Mutation rejection for source linkage, operations, calls, bytes, exports,
      ABI, and manifest declarations.
- [ ] One passing clean-checkout independent verification command.
- [ ] Record exact commands, pins, successes, failures, and limits.
- [ ] Update maintained documentation and this task; commit and push.

## Execution policy

The user explicitly permits direct Lean execution here, overriding the local
runner-only instruction for this session. Keep Lean execution serial, use the
pinned toolchain and one Lean thread, and bound diagnostic runtimes. Reduce a
timed-out proof before retrying. Authorized branch edits, checks, commits, and
pushes require no further permission. Do not modify main or typesafety.

Audit scopes: the existing TypeSafety library and its admission proofs retain
the propext-only policy. The source-loop bridge and Talos backend may inherit
Lean's standard propext, Quot.sound, and Classical.choice axioms. Lean's own
repeatM definition already uses choice. No newly declared axioms, sorryAx, or
native-evaluation proof shortcuts are permitted in either scope.

Never mark unchecked work proved or incomplete gates complete. Keep the original
source and exact-byte trust boundaries. The reviewed specifications, Lean proof
checker, pinned Talos semantics, and stated host assumptions remain explicit.

## Journal

### 2026-09-24: initialization

Created correct from the reviewed typesafety head and cloned it. The workspace
had no Lean installation, so the pinned release is being downloaded. Preserved
the old independent-language agenda and recorded this complete plan before
implementation.

### 2026-09-24: first checked source certificates

Added Correct/Scalar64/Profile, Source, and Arithmetic. Admission is an independent
inductive grammar plus the existing sound ordinary type checker. It allows strict
unused lets/arguments and rejects non-word runtime families. Source certificates
name the actual Arithmetic.affine/choose definitions and prove independent-machine
execution for every scalar input. Branches and modular boundaries are included.

Passed: lake build LeanExe.Correct.Scalar64.Arithmetic; lake env lean
test/scalar64_profile.lean. The test includes 13 admission/execution cases and
six dependency audits, all with only propext. Initial generic simp proofs pulled
in Quot.sound via predicate/function congruence; replaced them with constructive
pointwise list proofs rather than widening the audit policy.

Source certificate generation, loop certificates, verified lowering, and byte
closure are not complete. The source grammar currently permits direct calls;
acyclic helper admission and the separate iteration boundary remain open.

The shell has no GitHub push credential. Commits are published through the
connected GitHub Git-data interface, then the local branch is synchronized to
that exact remote commit. No changes are made to main or typesafety.

### 2026-09-24: source loop feasibility completed

Added an independent terminating iteration relation, a checked bridge to Lean's
actual repeatM/Loop.forIn, a reusable two-argument call execution rule, and a GCD
source certificate. The original TalosGcd.gcd source remains unchanged. The proof
connects its actual while loop to the carried-state iteration and then to the
independent core's recursive execution, for all UInt64 inputs. Remainder strictly
decreases the second word's natural measure until zero; zero input is covered.

Passed: lake build LeanExe.Correct.Scalar64.Gcd; lake env lean
test/scalar64_gcd.lean. Audits report only Lean's three standard logical axioms.
Lean 4.34 hides generated matchers across module boundaries: exported an explicit
Loop.forIn unfolding lemma and used full-transparency rewriting for the final
source equality. No source replacement or computational axiom was introduced.

### 2026-09-24: all pilot source certificates checked

Added constructive bridges from the independent arithmetic bit specification to
Lean UInt64 AND, OR, XOR, and masked shifts. Prng.mix now has a universal strict-let
source certificate with the original large constants. Added a scalar helper-call
fixture and certificate covering left-to-right argument staging, a fresh callee
environment, and restoration of caller bindings after the call.

Passed: lake build LeanExe.Correct.Scalar64.Prng; lake build
LeanExe.Correct.Scalar64.Helper; lake env lean test/scalar64_sources.lean.
Eleven dependency audits contain only the declared standard logical axioms;
affine, choose, helper calls, and shifts still use propext alone. The independent
TypeSafety files have not been changed.

Backend work is in progress: typed expression lowering and a scalar IR with
explicit assignment, calls, structured conditionals, and terminating loops.
These drafts are not yet counted as checked. Mathlib cache acquisition is being
kept in the workspace so interrupted downloads can resume without losing archives.

### 2026-09-24: generic expression lowering checked

The typed scalar expression lowerer and its structural correctness theorem pass
Lean. The theorem covers every expression constructor and arbitrary input/local
states and stack continuations, preserving the surrounding store. It reuses the
existing ScalarTransition expression semantics and scratch noninterference proof,
while retaining explicit WASM control result types for later exact module equality.

Passed: lake build Project.Correct.Scalar64.Model in proofs/talos/lean; lake env
lean Project/Correct/Scalar64/ExpressionTests.lean. The latter checks zero-divisor
division/remainder and masking a shift count of 65, and audits the generic lowering
and scratch preservation theorems. Only the declared standard axioms occur.

The scalar command IR and total execution rules are defined and kernel checked.
Its loop rule states an invariant and decreasing measure entirely in IR semantics.
Call/loop lowering correctness, module checking, byte closure, and the command-line
gates remain unfinished. The independent binary validator's legacy one-memory
requirement is being extended, with a soundness proof, to permit scalar modules
with zero memories while still rejecting memory operations in those modules.
