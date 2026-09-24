# Scalar compiler correctness: restarted, INCOMPLETE

## Correction and authorization

The prior completion reports were false. They covered a separate backend and
five manually supplied source/IR certificates. They did not establish a usable
certified Lean-source compiler. The user has explicitly instructed removal of
that implementation and completion of the actual job. Those changes are removed
from the working tree; Git history preserves what happened. Work remains on
`correct`, with the reviewed `typesafety` source restored from
834ba204d84720e00deef9b4ce476d4a04e55ff4. Main and typesafety are untouched.

Do not mark this agenda complete because examples or backend proofs pass.
Completion requires the source-declaration compiler interface below.

## Required result

Prove the actual compiler correct once for every program in a precisely defined
scalar source subset. The general theorem must connect the original checked Lean
source declaration, the actual extraction and lowering functions, and the exact
emitted WebAssembly bytes. It must quantify over every valid input. In addition
to preservation on successful compilations, prove compilation succeeds for the
defined supported subset. Define support from source syntax and types, not from
whether an output happens to satisfy correctness.

The executable must call the functions covered by these proofs. Source meaning
must be independent of compilation and connected to Lean's operations. Each new
supported program inherits correctness from the general compiler theorem. A
separate backend, a registry of examples, or individual generated correspondence
proofs does not fulfill this task. No handwritten IR or compiler-correctness
certificate is required from the user.

The profile uses concrete WASM values: UInt64 arguments/results, internal Bool,
modular arithmetic, unsigned comparisons, bit operations and masked shifts,
strict bindings, branches, acyclic scalar helper calls, and supported terminating
structured iteration. Division by zero returns zero and remainder by zero the
dividend. Runtime Nat, heap objects, imports, mutable globals, and allocation are
excluded. Proof-level Nat and explicit termination arguments are permitted.

## Completion gates

- [x] Read and identify the actual existing extraction, IR, lowering, and emission paths.
- [ ] Define independent scalar semantics and precise source/ABI/termination contracts.
- [ ] Implement source-only certified entry admission with explicit errors.
- [ ] Prove general original-Lean-source to actual extracted-IR semantic preservation.
- [ ] Prove extraction succeeds for the defined source subset.
- [ ] Prove every scalar lowering pass used by the accepted subset.
- [ ] Compose a general theorem for the actual compiler entry point and emitted bytes.
- [ ] Cover strict bindings, branching, numeric boundaries, and acyclic helper calls.
- [ ] Cover the agreed structured-loop/termination cases without per-program WASM proofs.
- [ ] Use actual compiler emission and prove full decoded-module equality for exact bytes.
- [ ] Produce portable proof packages independently checkable without compiler/generator execution.
- [ ] Compile and certify unseen source functions with no registration, handwritten IR, or correctness certificates.
- [ ] Check deliberate source/extractor/IR/opcode/call/export/ABI/manifest mutations.
- [ ] Audit final theorem dependencies: no holes, fresh axioms, or native-evaluation shortcuts.
- [ ] Preserve the independent TypeSafety propext-only policy.
- [ ] Pass a clean-checkout gate starting from source declarations and a separate package-only gate.
- [ ] Update documentation with actual scope, exact commands, limitations, and remaining obligations.

## Work policy

Commit and push frequently; explicitly announce every successful push. Keep Lean
processes serial under the pinned toolchain. The user explicitly authorized direct
local Lean execution; tools/leanrun with LEANRUN_LOCAL=1 retains locking and
bounded execution. Split a timed-out diagnostic before retrying it. Do not spawn
other agents without authorization. No status statement can exceed its evidence.

## Journal

### Restart

Inspected the real path: LeanExe.Extract.compileEnvironment uses the existing
extractor to produce LeanExe.IR.Module; LeanExe.Wasm.Binary.CoreWasm emits it.
ScalarDescriptor and ScalarCertificate already connect parts of actual lowering
to reusable descriptor code. The typesafety base also contains the Talos
ScalarTransition proof library. The previous separate Correct/Scalar64 path,
manual-certificate CLI, bundled pilot packages, and false completion report have
been removed. The required source-only frontend is currently UNIMPLEMENTED.

### Source traversal refactor (checked)

The previous task text still allowed individual proof-producing compilation as
the final result. Corrected it to the requested general compiler theorem and
added a separate acceptance theorem to rule out vacuous success-by-rejection.

The production source traversal used opaque partial definitions for application
decomposition, lambda collection, forall collection, application reconstruction,
and a fuel-bounded beta reducer. Moved the first four into Extract.Syntax as
total functions, with reconstruction and metadata invariance proofs; made the
existing beta reducer total on its fuel. This is source traversal infrastructure,
not a source-to-IR semantics proof. No end-to-end theorem exists yet.

Validation: `lake build LeanExe.Extract.Syntax LeanExe.Extract.Types` and
`lake build LeanExe.Extract.Core` passed through tools/leanrun. The application
spine reconstruction and metadata invariance proofs were checked by Lean.

### Native scalar operations (checked)

Added independent relational semantics over the existing IR for finite locals,
strict bindings, arithmetic, branches, and short-circuit conditions. Unsupported
operators and out-of-range locals have no evaluation rule. This semantics is not
the diagnostic partial evaluator. Calls and loops still need semantic rules.

Refactored the ten direct UInt64 primitive branches in the production extractor
to call ScalarPrimitive.lower. Proved ofName_sound, ofName_name, denote_toIR, and
lower_correct against Lean's native UInt64 operations and the IR relation for
arbitrary operands. The extractor rebuild passes. This proves the primitive
lowering step only, not the enclosing opaque recursive extractor or WebAssembly.

Identified that overloaded arithmetic dispatch ignores its typeclass evidence;
checking a concrete custom-instance counterexample before changing that boundary.

### Source instance dispatch regression (checked)

Reproduced a real mismatch through compileEnvironment: a custom HAdd UInt64
instance implementing subtraction evaluated to 7 on (10,3), while extracted IR
returned 13. Removed the bypass that skipped class-evidence normalization for
arithmetic projections. The same source now extracts subtraction and returns 7.
Made the existing fuel-bounded class normalizer total. Its semantic preservation
has not yet been proved.

Added test/scalar_class_evidence.lean: 48 source-versus-extracted-IR comparisons
cover custom HAdd/HSub/HMul/OfNat, standard arithmetic, bit operations, shifts,
and branching, including zero and overflow inputs. All passed via tools/leanrun.
These are regression checks, not a substitute for the general compiler theorem.

### Recursive primitive-expression extraction (checked)

Added an independent source relation over actual Lean.Expr syntax. Its primitive
constants are explicitly paired with their native Lean definitions, separately
from the compiler's operator table. Added total extractScalarExpr and wired it
into both production extractExprFrom and extractValueFrom for materialized
scalar slots.

Proved preservation for arbitrary expression trees and inputs; support implies
compilation success; compilation success implies syntactic support; and a
combined total-correctness theorem for this extraction fragment. No examples or
per-function proof certificates occur in these proofs. Current fragment: direct
UInt64 primitives, UInt64.ofNat literals, variables, and metadata. The actual
extractor rebuild and the 48 class-evidence regression checks pass.

These theorems do NOT cover complete declarations, overloaded-source
normalization, strict bindings, branches, helpers, loops, WASM lowering, or bytes.
The full agreed subset and source-to-bytes theorem remain incomplete. Auditing
current theorem dependencies in test/scalar_expr_axioms.lean.

### Canonical elaborated scalar expressions (checked)

Extended the same production traversal and general proofs to the canonical
HAdd/HSub/HMul/HDiv/HMod/HAnd/HOr/HXor/HShiftLeft/HShiftRight applications emitted
by Lean, including exact instance evidence, and canonical OfNat UInt64 literals.
Custom instances are excluded from this proved traversal and continue through
the existing evidence-normalizing path. A class recognizer soundness theorem
connects accepted heads to the independent native-operation source relation.

The 56 regression comparisons pass. They now also assert raw-source admission
before any normalization: ordinary arithmetic, affine arithmetic with literals,
bits, shifts, and a literal above 2^64 are accepted; custom instances and the
still-unproved branch fragment are excluded. The extractor rebuild passes.

Updated axiom audit: preservation/acceptance/combined extraction theorems now
use propext, Quot.sound, and Classical.choice; recognizer soundness uses propext
and Quot.sound. These are standard Lean axioms, with no sorryAx, fresh axioms,
or native-decide shortcut. The independent TypeSafety policy is unchanged.
Declaration application and source-to-bytes composition are still unproved.

### Production entry point to IR (checked)

Added scalar function application semantics over the original elaborated lambda
term, argument-order and finite-local-slot proofs, and scalar IR statement and
single-result function semantics. Proved extractScalarFunc_correct for every
successful declaration extraction and every argument list of the declared arity,
and extractScalarFunc_accepts for the independent source support predicate.

The normal compileEnvironmentWithEntryModeDetailed now handles the proved scalar
declaration case before the general opaque recursive extractor. It uses the same
IR and result-slot ABI and continues into the existing emitter. The generic
compileEnvironment_scalar_total_correct theorem references that actual entry
point, the original environment declaration/body, syntactic source support, and
all inputs. Its endpoint is IR.Func.ScalarEval. Native scalar constants have
explicit meanings in the independent source grammar; arbitrary Lean syntax is
not included. Existing unsafe/partial and reserved-export exclusions remain.

The proof and production extractor build pass. The 56 regression checks pass
through the changed entry point. This is NOT the end-to-end compiler theorem:
WASM lowering/encoding and the rest of the agreed language features remain open.

### Production emitter transparency (checked)

Made the existing expression/condition/local-let/statement scratch calculators
and annotated statement emitter total. The nested-list termination obligation
uses element membership and structural size; their equations and emitted code
were not replaced by a separate backend. Existing ScalarCertificate proofs pass.

Proved scalarFunc_emit for the normal emitFuncInstrs function: the exact emitted
instruction list is the recognized descriptor's code followed by the actual
result-slot store/load. Added descriptor scalar evaluation and operator meaning
lemmas as preparation for the IR-to-WASM semantic proof. The descriptor evaluator
alone is not a WebAssembly execution theorem. Talos semantics, scratch bounds,
module assembly, and exact binary correspondence still need to be connected.
