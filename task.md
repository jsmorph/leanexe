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
- Generic expression/command/call/loop lowering and all five source/IR certificates pass.
- All five exact-byte closures pass, including independent grammar and validity.
- Next: portable packages, independent CLI verification, mutations, and cold gate.
- Pinned Talos/Mathlib dependencies and required caches are available.

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
- [x] Explicit ABI, core execution contract, value representation, source
      certificate, and final artifact contract.
- [x] Well-formed locals, calls, indices, signatures, exports, and result arities.
- [x] Explicit numeric behavior and termination premises.

### 2. Existing type work

- [x] Reuse word w64, arithmetic laws, typing, machine semantics, renaming,
      and sequencing.
- [x] Use ordinary typing and strict evaluation; relevance is separate.
- [x] Allow unused scalar parameters/bindings and justify discarded evaluation.
- [x] Specify loops independently, directly or by proved recursive expansion.
- [x] Relate the profile to the independent language; do not substitute the
      diagnostic compiler IR evaluator as its semantics.

### 3. Source certificates: early feasibility gate

- [x] Freeze scalar-core representations and prove certificates naming the
      original Lean functions.
- [x] Reusable arithmetic, binding, branch, call, and iteration certificate rules.
- [x] Arithmetic.affine certificate.
- [x] Arithmetic.choose certificate.
- [x] Loop certificate before large backend work.
- [x] Certificate generation with explicit rejection of unsupported source forms.

### 4. Verified scalar backend

- [x] Total scalar lowering used by the actual certified compiler path.
- [x] Explicit semantics and well-formedness for any intervening IR.
- [x] Primitive lowering, including guarded division and remainder.
- [x] Locals, strict staging, scratch noninterference, and branches.
- [x] Helper calls, arguments, and returns.
- [x] Loops, simultaneous carried updates, and termination transfer.
- [x] Module validity and function/type/export indexing.
- [x] Scalar-only module assembly without unused allocator machinery.
- [x] Generic correctness for every admitted well-formed program, without
      handwritten per-program WASM instruction proofs.

### 5. Exact bytes and certified compilation

- [x] Independent artifact decoding and validation.
- [x] Full decoded-module equality with verified lowering.
- [x] Composition of source correspondence, lowering, and byte equality.
- [x] Explicit compile-certified --profile scalar64 command or equivalent.
- [x] Fail closed on unsupported source, stale evidence, or failed checking.
- [x] Portable package recording source, core/IR, ABI, export, bytes, certificates,
      theorem names, and pinned dependencies.
- [x] Independent verification without running the compiler or proof generator.

### 6. Acceptance and reproducibility

- [x] Arithmetic.affine: multiple inputs and modular arithmetic.
- [x] Arithmetic.choose: both branches.
- [x] Prng.mix: bitwise arithmetic, shifts, and large constants.
- [x] Helper-call fixture: call graph, staging, and return convention.
- [x] TalosGcd.gcd: carried loop state, remainder, and termination.
- [x] All pilots share compiler theorems; program-specific work is source
      correspondence and termination.
- [x] Dependency audits retaining the type-safety policy: no proof holes, added
      axioms, or native-evaluation proof shortcuts.
- [x] Mutation rejection for source linkage, operations, calls, bytes, exports,
      ABI, and manifest declarations.
- [x] One passing clean-checkout independent verification command.
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

### 2026-09-24: generic backend and all source/IR pilots checked

Added the total command lowerer, explicit IR total-execution semantics, argument
staging proof, store-preserving function/call theorem, structured loop proof,
scalar-only module assembly, and local/scratch/signature/DAG admission checks.
Executes.lower_spec is generic across commands, functions, inputs, surrounding
stacks, stores, and host environments. Termination is a semantic premise of the
IR execution evidence; each pilot supplies it. The loop invariant/measure is
stated entirely in IR semantics and transferred through the shared backend theorem.

Added Certificate.correct and Artifact.valid_and_correct, composing the original
source declaration, independent core execution, IR evidence, full-module byte
closure, formal decoder grammar, independent validity, and WASM termination with
the source result and unchanged store. This is certificate-checked compilation:
source/IR correspondence is checked per accepted translation; generation itself
is untrusted. No correctness claim is made for the ordinary uncertified compiler.

All five pilot source/IR certificates pass. GCD stages carried updates and uses
the generic loop lowering theorem; it contains no WASM instruction proof. Added
the encoder, which consumes the actual proved lowerer. Exact-byte equalities are
now being checked; they are not yet marked complete.

The binary validator now accepts zero or one memory, with its soundness theorem
updated. The prior one-memory composition helper remains checked. ValidationTests
passes acceptance and formal validity for zero/one memory and rejects a memory
load without memory, an invalid local, an invalid callee, and two memories.
Backend and validator dependency audits contain only the declared standard axioms.

Passed in proofs/talos/lean: lake build Project.Correct.Scalar64.Backend;
lake build Project.Correct.Scalar64.Encode; lake build
Project.Correct.Scalar64.Pilots; lake build Project.Correct.Scalar64.Gcd;
lake build Project.Correct.Scalar64.ValidationTests. Module/byte closure packages,
CLI rejection gates, mutation tests, and clean verification remain open.

### 2026-09-24: exact emitted bytes checked for every pilot

All five encoder outputs now have kernel-checked decode, validation, and complete
Talos module equalities. Artifact.of_parts composes these facts into the exact
byte contract. The naive monolithic `rfl` closure exceeded 90 seconds; splitting
it and using proof-producing `cbv` for decoding reduced each proof to 3–8 seconds.
No native-decide or compiler-trust axiom is used. All five closures audit to only
propext, Classical.choice, and Quot.sound. The original timeout is preserved in
the work journal rather than retried unchanged.

Passed: lake build Project.Correct.Scalar64.Artifacts (all five); lake build
Project.Correct.Scalar64.Package (untrusted scalar data serialization). The byte
sizes are affine 53, choose 58, mix 89, helper 78, and gcd 90. Portable CLI packages
and mutation/cold verification are still in progress.

### 2026-09-24: independent package CLI implemented

Added compile-certified and verify-certified with strict JSON data schemas,
canonical checking text, source/core/IR/ABI/export bindings, source snapshots,
SHA-256 file identities, theorem names, repository revision, and dependency pins.
Compilation selects a checked source/IR certificate or accepts an explicitly named
custom certificate; it does not infer proofs for arbitrary Lean. The generic
backend still covers every Certificate accepted by the checker. Unsupported
profiles, absent source certificates, malformed data, and failed equalities stop
publication. The generator's binary reader only supplies an untrusted witness;
the independent Lean decoder proves its equality to the actual byte array.

The affine CLI package has passed end to end. The verifier builds only the
certificate dependencies and canonical checking module, with no call to the
encoder or package emitter. Final correctness and equality dependencies are
audited against the three standard axioms. The remaining pilot CLI runs,
mutations, and clean-checkout gate are pending.

### 2026-09-24: acceptance gate and documentation checkpoint

Added the repeatable check-correct driver, adversarial package mutations with
recomputed hashes, clean-checkout verification, engine smoke cases, and a
namespace-wide axiom audit. Added the scalar correctness guide and README entry.
The affine portable package passes against published revision 44e9c7ab. The new
full acceptance driver is being run next; this checkpoint does not yet claim that
all mutations or the cold gate have passed.

The new namespace audit passed: 494 scalar declarations use only the three
standard axioms, and 2,181 independent TypeSafety declarations use propext alone.

### 2026-09-24: all five portable packages accepted

At published revision 9c0975a2, compile-certified and independent verification
passed for affine, choose, mix, helper, and gcd. Node's WASM engine accepted every
binary, exposed exactly its intended export with no imports, and passed 333
boundary/branch/modular/call/loop cases. These tests supplement the universal
Lean theorems. The three source/admission test modules and the full namespace
axiom audit also passed. Mutation checks are in progress; source linkage and IR
arithmetic mutations already fail their Lean obligations with recomputed hashes.
The cold gate has not yet finished.

### 2026-09-24: mutation results and package review

All 13 initial adversarial mutations were rejected with recomputed checksums:
source declaration, core/IR operation, call target/argument order, WASM opcode
with matching decoder witness, metadata/binary exports, ABI order/arity,
certificate declaration, dependency pin, and theorem declaration. Unsupported
source/profile checks also passed. The cold checkout is rebuilding project proofs.

Review found two packaging refinements: reject placeholder declaration names
and mismatched source namespaces, and limit revision comparisons to actual source,
proof, and configuration paths so bundled review copies do not invalidate their
own recorded revision. Added regression cases for both names and independent
module admission (cycles, arity, bounds, and division scratch capacity).


The complete gate passed at 9c0975a254daaeb91c1bddc3d0e2ea7c4841f573:
`tools/check-correct --packages tmp/certified-acceptance --mutations --cold`.
All five clean-checkout verifications succeeded. Only pinned external dependency
caches were shared; the source and project proof caches started empty. Generation
was not invoked in the detached checkout. The final package-name refinements and
bundled-package checkpoint will receive a final independent verification run.

The module-admission regressions passed, including explicit rejection of a
self-call at the encoder boundary and insufficient division scratch space.
