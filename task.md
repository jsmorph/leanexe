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
- Pinned Lean 4.34.0-rc2 is being installed into workspace-local tooling.
- No scalar correctness milestone has passed yet.
- Next: profile, admission checker, source-certificate interface, and choose.

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

- [ ] Independent scalar admission judgment and terminating checker.
- [ ] Checker soundness and completeness.
- [ ] Explicit ABI, core execution contract, value representation, source
      certificate, and final artifact contract.
- [ ] Well-formed locals, calls, indices, signatures, exports, and result arities.
- [ ] Explicit numeric behavior and termination premises.

### 2. Existing type work

- [ ] Reuse word w64, arithmetic laws, typing, machine semantics, renaming,
      and sequencing.
- [ ] Use ordinary typing and strict evaluation; relevance is separate.
- [ ] Allow unused scalar parameters/bindings and justify discarded evaluation.
- [ ] Specify loops independently, directly or by proved recursive expansion.
- [ ] Relate the profile to the independent language; do not substitute the
      diagnostic compiler IR evaluator as its semantics.

### 3. Source certificates: early feasibility gate

- [ ] Freeze scalar-core representations and prove certificates naming the
      original Lean functions.
- [ ] Reusable arithmetic, binding, branch, call, and iteration certificate rules.
- [ ] Arithmetic.affine certificate.
- [ ] Arithmetic.choose certificate.
- [ ] Loop certificate before large backend work.
- [ ] Certificate generation with explicit rejection of unsupported source forms.

### 4. Verified scalar backend

- [ ] Total scalar lowering used by the actual certified compiler path.
- [ ] Explicit semantics and well-formedness for any intervening IR.
- [ ] Primitive lowering, including guarded division and remainder.
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

Never mark unchecked work proved or incomplete gates complete. Keep the original
source and exact-byte trust boundaries. The reviewed specifications, Lean proof
checker, pinned Talos semantics, and stated host assumptions remain explicit.

## Journal

### 2026-09-24: initialization

Created correct from the reviewed typesafety head and cloned it. The workspace
had no Lean installation, so the pinned release is being downloaded. Preserved
the old independent-language agenda and recorded this complete plan before
implementation.
