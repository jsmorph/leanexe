# Source-Theorem Transport Plan

**Status:** Deferred.  Exact-artifact decoding, validation, translation, and behavioral proof are implemented for twenty-one artifacts.  The current project plan first tests smaller compiler-theorem-directed regions before committing to this general refinement boundary.

## Goal

The target workflow starts with a Lean function, a theorem about that function, and an exact WebAssembly artifact compiled from it.  For the first profile, the function has type `UInt64 → UInt64`, and its theorem has the form `∀ x, Pre x → P x (f x)`.  The final proof applies the same precondition `Pre` and predicate `P` to the value returned by the artifact, with an ABI wrapper that connects a Lean `UInt64` to a WebAssembly `i64`.

The proof will establish functional refinement on the source theorem's domain before it transports `P`.  For every input admitted by the ABI that satisfies `Pre`, the exported function must terminate without a trap, return the representation of `f x`, and satisfy the scalar profile's state-frame condition.  A generic transport theorem then derives the artifact statement from that refinement theorem and the user's source theorem.

The compiler remains an untrusted producer of candidate evidence.  Lean checks a source-to-IR certificate, a generic IR-to-WASM theorem, and equality between the verified lowering and the module decoded from the exact artifact bytes.  A compiler error causes one of those checks to fail rather than changing the theorem's subject.

```text
f : UInt64 → UInt64 ── source certificate ──► frozen scalar IR
                                                    │
                                                    │ proved lowerScalar
                                                    ▼
                                            expected Talos module
                                                    ▲
                                                    │ full equality
artifact bytes ── decode ── validate ──► decoded Talos module

sourceSpec : ∀ x, Pre x → P x (f x) ── transport ──► artifact satisfies P
```

## Meaning of the Same Theorem

The propositions `Pre` and `P` and their source proof remain unchanged.  The artifact theorem has a different outer form because machine execution takes encoded arguments, starts in a machine state, and returns encoded results.  The transport theorem removes that execution wrapper and applies `sourceSpec` to the decoded result.

```lean
theorem sourceSpec : ∀ x, Pre x → P x (f x)

theorem artifactSpec :
  ∀ initial x,
    ScalarInitialState initial →
    Pre x →
    TerminatesWith artifactModule initial exportIndex [.i64 x]
      (fun final results =>
        ScalarFrame initial final ∧
        ∃ y, results = [.i64 y] ∧ P x y)
```

The artifact statement proves both existence of the result and the source property on `Pre`.  A separate refinement theorem identifies the result as `f x` for every input in that domain, which prevents a weak predicate `P` from concealing incorrect compilation.  Determinism of the accepted Talos profile then gives uniqueness where a caller needs it.

## Definition of Completion

The work is complete for an accepted scalar function when one command checks the source theorem against a frozen IR value and an exact `.wasm` file.  The command must prove the source-to-IR certificate, decode and validate the embedded bytes, check full-module equality with the verified scalar lowering, and build the transported theorem.  Removing the compiler executable after evidence generation must not prevent the proof package from building.

Adding another function inside the accepted profile must require no function-specific WebAssembly proof.  The package may contain a generated source certificate whose proof term depends on the function's definition, but the Lean kernel must check it through reusable certificate lemmas.  Unsupported source forms, IR forms, ABI types, or WebAssembly features must stop with a named boundary and no correctness claim.

The first completion claim covers `UInt64 → UInt64` functions with scalar locals, calls within the checked module, structured conditionals, and loops whose source certificate proves termination.  Multi-argument scalar functions follow after the one-argument path, using the existing `gcd` artifact as the first extension case.  Heap values, arbitrary-precision `Nat` and `Int`, callbacks, imports, and host effects require representation and state-relation work outside the first claim.

The initial transport interface covers extensional input/output propositions with source preconditions.  Cost, execution-trace, allocation, and noninterference theorems require corresponding observables in `ArtifactComputes` before they can use the same composition.  The plan therefore establishes functional theorem transport first and leaves room to strengthen the execution relation without changing exact-byte identity.

## Trust Boundary

This plan inherits the Lean kernel, exact-byte grammar, validator specification, Talos semantics, and Talos fidelity assumption recorded by the artifact plan.  It adds the scalar ABI, proof-level IR semantics, and source predicate to the formal statement that a reviewer must assess.  The kernel checks the source definition and theorem as ordinary Lean declarations.

The compiler, extractor, optimizer, certificate generator, serializer, Wasmtime, and hash implementation remain outside the proof's logical premises.  They may produce candidates, identifiers, and test evidence, while kernel-checked certificates connect the source declaration, frozen IR, and decoded bytes.  A defect in a formal specification remains a specification-review risk, so manifests must pin those definitions as well as their completed proofs.

## Formal Interfaces

### Scalar ABI

Define one proof-level ABI record that specifies source types, WebAssembly parameter and result types, value encoding, result decoding, admissible initial states, and the observable frame condition.  The first instance maps `UInt64` bit patterns bijectively to `i64` values and requires one result.  The entry function must preserve the memory and globals named by the scalar frame or restore any temporary changes before it returns.

```lean
structure ScalarABI (α β : Type) where
  encodeArgs : α → List Wasm.Value
  resultRep : β → List Wasm.Value → Prop
  admissible : α → Prop
  initial : Wasm.Store → Prop
  frame : Wasm.Store → Wasm.Store → Prop
  params : List Wasm.ValType
  results : List Wasm.ValType
```

Keep ABI representation separate from mathematical predicates such as `Pre` and `P`.  Separating those definitions allows the generic transport theorem to apply to any proposition over source values.  Later ABI instances can add signed interpretation, several arguments, bounded natural numbers, or heap representations without changing the theorem's composition.

### Proof-Grade IR Semantics

The current scalar IR evaluator uses partial definitions and caps each `while` execution at 1,000,000 iterations.  When the cap expires, it returns the current store, making fuel exhaustion indistinguishable from normal termination.  Add an inductive or fuel-indexed `IRTerminatesWith` relation that records argument and result values, call behavior, and loop termination.  Add a checked evaluator that reports fuel exhaustion, and prove it sound with respect to the relation so computation can discharge closed certificate obligations.

Define `ScalarIRWellFormed` as a proposition and a sound decidable checker.  It must cover function and local indices, call signatures, scalar constructor restrictions, result arity, branch result agreement, and every evaluator premise used by lowering.  The existing Boolean fragment classifier can contribute to the decision procedure after a theorem connects successful classification to the proof-level proposition.

```lean
def SourceRefinesIR
    (Pre : UInt64 → Prop)
    (f : UInt64 → UInt64)
    (ir : IR.Module)
    (entry : Nat) : Prop :=
  ∀ x, Pre x → IRTerminatesWith ir entry [x] [f x]
```

The concrete relation should quantify over a derivation or a sufficient execution budget rather than use an evaluator equality that can diverge.  A theorem should hide that budget from clients once the certificate establishes termination.  Loop and recursive-call certificates must therefore contain termination evidence instead of relying on a test timeout.

### Source-to-IR Certificate

For each function, freeze the extracted IR as a Lean value and prove a theorem that names both that value and the original Lean constant.  The useful certificate statement is `∀ x, Pre x → IRTerminatesWith ir entry [encode x] [encode (f x)]`.  Because the theorem mentions `f` directly, a bug in parsing, extraction, optimization, or IR serialization cannot survive kernel checking.

The current extractor can produce the candidate IR and candidate proof, but its implementation remains outside the trusted base.  The certificate generator should reduce source constructs through reusable congruence, arithmetic, branch, call, recursion, and loop lemmas, then let Lean elaborate and check the resulting proof term.  Differential execution can test the generator, but it cannot substitute for a certificate when proof generation fails.

The initial feasibility work must determine how much of the accepted source subset can use generated proof terms without a formal Lean AST semantics.  Straight-line definitions and conditionals should close by unfolding and compositional lemmas, while recursive definitions will require induction over the source termination argument or a relation between source recursion and IR loops.  If that method does not support the intended loop cases, the design review must choose between a proof-producing reifier and a small formal source language with a proved translation to IR.

### Verified Scalar Lowering

Define `lowerScalar` as a total Lean function from well-formed scalar IR modules and their ABI metadata to complete Talos modules.  Its output must include function types, function bodies, runtime support selected by the profile, globals, memory, and exports, because the artifact link will compare full modules.  Splitting body construction from binary serialization remains useful, but this theorem concerns the structured Talos module produced by lowering.

```lean
theorem lowerScalar_correct
    (abi : ScalarABI UInt64 UInt64)
    (hwf : ScalarIRWellFormed ir entry abi)
    (hadmissible : abi.admissible x)
    (hinitial : abi.initial initial)
    (hir : IRTerminatesWith ir entry [x] [y]) :
    TalosTerminatesWith
      (lowerScalar ir entry abi)
      initial
      (abi.encodeArgs x)
      (fun final wasmResults =>
        abi.frame initial final ∧
        abi.resultRep y wasmResults)
```

Prove this theorem by reusable cases for each accepted IR expression, condition, and statement constructor.  Function calls require an induction principle over the checked call graph or a step-indexed simulation that supports recursion.  Loops require a simulation lemma driven by the `IRTerminatesWith` derivation, so no program-specific WebAssembly loop invariant remains in the final package.

Arithmetic theorems must state the selected fixed-width behavior.  The `UInt64` profile uses source operations modulo `2^64` and corresponding `i64` instructions, while division, shifts, and conversions require explicit treatment of traps and operand interpretation.  Lowering must implement the source result for every input in `Pre`, or the source certificate must prove that `Pre` excludes each trapping case.

### Exact Artifact Link

The [Artifact Verification Format](../docs/artifact-format.md) supplies embedded bytes, a sound decoder, complete validation for the accepted profile, and translation to Talos.  Each transport package must prove that the translated validated module equals `lowerScalar` applied to the frozen IR and ABI metadata.  Full-module equality covers helper functions, indices, exports, globals, memory declarations, and function bodies, avoiding an unchecked correspondence between entry points.

```lean
theorem artifact_equals_lowering :
  ∃ raw validated,
    Wasm.Binary.decode artifactBytes = .ok raw ∧
    Wasm.Binary.validate raw = .ok validated ∧
    ValidatedModule.toTalos validated = lowerScalar ir entry abi
```

Lean should decide this equality by reduction or check a generated equality certificate.  The external SHA-256 identifies the proof package, while the embedded byte array remains the formal subject.  Serialization correctness can make this equality easier to generate, but theorem transport does not assume that the compiler's serializer or emitter is correct.

### Composition and Transport

Define `ArtifactComputes` in terms of `Pre`, the decoded and validated exact artifact, the selected export, the ABI initial-state predicate, termination, result representation, and frame condition.  Compose the source certificate, `lowerScalar_correct`, and `artifact_equals_lowering` into one refinement theorem.  The composition must expose no compiler premise and no generated Talos module that lacks an equality proof to decoded bytes.

```lean
theorem artifact_refines_source
    (hsource : SourceRefinesIR Pre f ir entry)
    (hwf : ScalarIRWellFormed ir entry abi)
    (hbytes : ArtifactEqualsLowering artifactBytes ir entry abi) :
    ArtifactComputes artifactBytes abi Pre f

theorem transport_source_theorem
    (hrefines : ArtifactComputes artifactBytes abi Pre f)
    (hsourceSpec : ∀ x, Pre x → P x (f x)) :
    ArtifactSatisfies artifactBytes abi Pre P
```

The second theorem should be short and independent of compiler structure.  Its proof obtains the represented return value from `hrefines`, rewrites it to `f x`, and applies `hsourceSpec`.  All substantial work belongs in the refinement theorem and its three checked inputs.

## Evidence Package

Store the source link, frozen IR, exact artifact, and proof targets in one content-addressed package.  The source module remains an imported Lean dependency because the certificate and theorem name its constant and proof.  The compiler may regenerate candidate files, but the checked package must remain buildable without it.

```text
proofs/transport/<case>/<sha256>/
  program.wasm
  manifest.json
  ArtifactBytes.lean
  IRProgram.lean
  SourceCertificate.lean
  ArtifactEquality.lean
  TransportedSpec.lean
```

The manifest should record the source module, declaration, theorem, ABI profile, IR entry, artifact digest, decoder profile, equality theorem, refinement theorem, and transported theorem.  It should also identify the Lean release, Talos revision, and artifact-verification package on which the proof depends.  Generated file headers should record commands and input digests without treating generator output as trusted evidence.

## Work Plan

| Phase | Implementation | Acceptance gate | Dependency |
|-------|----------------|-----------------|------------|
| 0. Statement and ABI | Define the `UInt64 → UInt64` ABI, domain-qualified `ArtifactComputes`, `ArtifactSatisfies`, and the generic transport lemma. | A hand-constructed model and refinement theorem transport an existing source proposition without changing `Pre` or `P`. | None |
| 1. IR semantics | Add `IRTerminatesWith`, `ScalarIRWellFormed`, a decision procedure, and evaluator-soundness theorems. | Straight-line, branch, call, and loop fixtures have checked derivations, and malformed modules reject. | None |
| 2. Source-certificate feasibility | Generate certificates for one straight-line definition, one conditional definition, and one terminating loop or recursive definition. | Each theorem directly names the Lean function and frozen IR, builds without `sorry` or axioms, and fails after a semantic IR mutation. | Phase 1 |
| 3. Certificate design review | Measure proof size and check time, review recursion coverage, and choose proof-producing unfolding or a formal source reifier. | The review records one certificate architecture and the accepted Lean source subset. | Phase 2 |
| 4. Scalar lowering | Define complete Talos-module lowering and normalize its module layout against current scalar artifacts. | Decidable equality holds for the selected straight-line, conditional, and loop artifacts. | Phase 1 and emitter restructuring |
| 5. Constructor simulations | Prove lowering theorems for scalar expressions, conditions, local bindings, statements, structured control, and calls. | Every accepted constructor has a theorem whose premises come from IR well-formedness or execution evidence. | Phase 4 |
| 6. Back-end theorem | Compose constructor results into `lowerScalar_correct`, including recursion, loop termination, trap freedom, and frame preservation. | The theorem builds for every well-formed module in the first profile without a program-specific WebAssembly proof. | Phase 5 |
| 7. Exact-byte composition | Add `ArtifactEqualsLowering` and compose it with decoding, validation, and Talos translation. | Each pilot artifact proves full-module equality from its exact embedded bytes. | Artifact plan phases 1–6 and phase 4 |
| 8. Evidence generator | Generate the IR literal, certificate candidate, ABI metadata, artifact manifest, and equality candidate. | Deleting the compiler executable after generation does not prevent all package targets from rebuilding. | Phases 2, 3, and 7 |
| 9. End-to-end pilot | Build refinement and transported theorems for the three one-input fixtures. | One command rejects mutations to source linkage, IR, bytes, ABI, export, or theorem names and accepts the unchanged packages. | Phases 6–8 |
| 10. Multi-argument extension | Generalize scalar tuples and transport the existing `gcd` source theorem to its exact artifact. | The `gcd` package uses the same back-end and transport theorems with no handwritten instruction proof. | Phase 9 |
| 11. Aggregate gate | Register transport packages, check manifests, and run the source, IR, artifact, equality, refinement, and transported theorem targets serially. | A clean checkout reproduces every registered theorem under the repository resource policy. | Artifact plan phase 7 and phase 10 |

The artifact plan now supplies exact-byte identity, sound decoding, sound validation, Talos translation, and an aggregate checker for all twenty-one registered binaries.  The refreshed 2026-09-04 twenty-one-package aggregate result passes for release-input digest `bbc645be04edcae73d6d36958a01b85bfa0a24f7660fc0ccb801ac6e133711a3`.  Phases 0 through 6 of this plan may start without further artifact-verifier work, while Phase 7 can use the implemented artifact boundary directly.  The first end-to-end transport claim still requires the source certificate and verified scalar-lowering lines to meet at full-module equality.

## Pilot Sequence

The first fixture should be a one-input straight-line `UInt64` function with a source theorem that requires more than definitional reduction.  The second should introduce a conditional whose theorem covers both branches.  The third should contain a terminating loop or recursion so the certificate and simulation architectures demonstrate their termination arguments.

After those fixtures pass, extend the ABI to two `UInt64` arguments and reuse the existing `gcd` artifact and theorem.  The fixture order separates ABI tuple work from the harder loop and recursion work.  A source theorem that succeeds only because its predicate ignores the return value does not satisfy a pilot gate, since the separate `ArtifactComputes` theorem must still identify the exact result.

## Verification Command

Add a command that takes a registered transport package rather than an arbitrary source path and compiler invocation.  Generation and checking may be separate modes, allowing developers to refresh candidates while artifact recipients run only the checker.  Both modes must run Lean children serially under the repository's cgroup, CPU, priority, I/O, and timeout policy.

```sh
tools/theorem-transport.js check proofs/transport/example/<sha256>
```

The checker should verify manifest consistency, source declaration and theorem names, IR well-formedness, the source certificate, artifact identity, decoding, validation, full-module equality, the back-end refinement theorem, and the transported theorem.  It should report the first failed boundary and the relevant declaration or byte offset.  It must reject missing certificates, stale generated files, unsupported ABI profiles, and any package whose decoded export differs from the recorded entry.

## Tests and Failure Evidence

Mutation tests should alter one source-linked IR operation, branch target, call index, artifact opcode, function type, export index, and manifest field.  Each mutation must fail at the expected certificate, validation, equality, or registry boundary.  The mutation suite checks that no cache or generated declaration bypasses the intended dependency chain.

The source-certificate suite should include arithmetic boundaries, division and shift side conditions, nested conditionals, local reuse, direct calls, recursive calls, zero-iteration loops, and multi-iteration loops.  The back-end suite should exercise each accepted IR constructor and each emitted WebAssembly instruction form.  Test execution under the IR evaluator and Wasmtime remains diagnostic evidence alongside the formal proofs.

Record certificate size, elaboration time, peak memory, and equality-check time for every pilot.  A proof that exceeds the repository limits should prompt a smaller reusable lemma or a divided elaboration boundary before another unchanged run.  Release evidence should name the exact source theorem, IR digest, artifact digest, equality theorem, refinement theorem, and transported theorem.

## Relationship to Existing Plans

The [Artifact Verification Format](../docs/artifact-format.md) owns byte identity, decoding, validation, and the Talos translation.  This plan consumes those results and adds the source certificate, verified scalar lowering, exact equality to that lowering, and theorem transport.  Artifact-only proofs therefore remain independent of source and compiler claims.

The [Compiler Architecture](../docs/compiler.md) records the present extraction, IR, emitter, annotation, and scalar-certificate boundaries.  This plan takes a translation-validation path for scalar functions: every artifact carries checked evidence that its frozen IR computes the source function and that its decoded module equals a proved lowering of that IR.  The scalar backend theorems can later become components of a broader compiler proof.

The compiler already lowers function bodies through `LeanExe.Wasm.Instr`, and `LeanExe.Wasm.ScalarCertificate` proves selected descriptor-emitter equalities.  This plan still requires a proof-grade module lowering and a connection from that lowering to independently decoded bytes.  The exact artifact remains the subject of the transported theorem regardless of how the emitter produced its candidate certificate.

## References

Repository context appears in [Artifact Proving](../docs/artifact-proving.md), [Compiler Architecture](../docs/compiler.md), [Verifying a Program](../docs/verifying.md), and [Talos Proofs](../proofs/talos/README.md).  The scalar IR definitions and evaluator live in `LeanExe/IR/Core.lean`, while scalar extraction and execution support live in `LeanExe/Extract/Eval.lean`.  Decisions, failed certificate approaches, and completed acceptance gates belong in `devnotes.md` as implementation proceeds.
