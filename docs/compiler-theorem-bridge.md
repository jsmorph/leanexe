# Compiler Theorems as Artifact-Proof Inputs

Date: 2026-08-07

## Purpose

Compiler theorems can reduce artifact-proof generation time without becoming premises of the retained artifact theorem.  The compiler can produce a typed description of a generated region and prove that its emitter constructs the corresponding instruction template.  The artifact package can then parse the description as untrusted data, compare the template with the region decoded from the exact WASM bytes, and apply a generic Talos theorem only after that comparison succeeds.

This division assigns different work to the compiler and the artifact verifier.  The compiler explains its output and checks that its explanation follows from the emitter.  The artifact verifier establishes that the explanation describes the distributed bytes, so deleting the source, compiler, compiler theorem, and sidecar after proof generation does not invalidate the retained proof.

The immediate application is Demo 1's scalar trial-division loop.  Its annotation names the IR condition, body, and scratch window, but the proof agent still reconstructs the transition from instructions and numeric local updates.  A compiler theorem can support a canonical scalar-transition descriptor that the current `Project.ProofKit.ScalarTransition` work proves directly against Talos.

## Current theorem inventory

The production compiler has no theorem relating extraction, `LeanExe.IR`, or `LeanExe.Wasm.Binary.CoreWasm.emitExpr` and `emitStmt` to WebAssembly behavior.  `LeanExe.Core.lower_correct` proves equality for the separate one-constructor ASCII-digit example in `LeanExe/Core.lean`.  `LeanExe/Examples/Correctness.lean` contains compiler execution cases and no compiler-correctness theorem, despite the filename.

`LeanExe/IR/Core.lean` supplies executable scalar semantics, but those definitions cannot support a general compiler theorem in their present form.  Heap expressions use placeholder results such as zero or the original pointer, releases are no-ops, and loops stop after 1,000,000 iterations while returning the current state as though execution had terminated.  The scalar fragment remains useful for theorem development after restricting the syntax and stating termination separately.

The emitter already has the structure needed for a narrow proof.  `LeanExe/Wasm/Binary.lean` lowers `Expr`, `Cond`, and `Stmt` values to `List Instr`, and `emitStmtAnnotated` constructs code and relative region locations together.  The current annotation recognizers and their JavaScript consumers check selected shapes computationally, but the compiler contains no theorem that connects a successful recognition or annotation to `emitStmt`.

The artifact side has the stronger semantic foundation.  The binary decoder and validator have soundness theorems, each generated package connects exact embedded bytes to the translated Talos module, and the proof kit contains semantic results for fixed-array wrappers, searches, allocation, and control flow.  `Project.ProofKit.ScalarTransition` now defines a typed scalar expression and statement language, an evaluator, a canonical Talos program, and weakest-precondition theorems for expressions, statements, and block-wrapped while loops.

## Logical boundary

The proposed path has two independent checks.  The compiler-side theorem establishes that the descriptor generator agrees with the compiler emitter for every supported IR term.  The artifact-side equality establishes that one descriptor's canonical Talos program equals the selected region in the module decoded from the exact WASM bytes.

Agreement at either boundary cannot substitute for agreement at the other.  A correct compiler theorem says nothing about a stale or unrelated binary presented to the artifact verifier.  An exact artifact equality proves the selected region but does not establish that the compiler will issue a correct descriptor for future outputs.

```text
                         compiler workspace

IR statement ---- reifyScalar ----> scalar descriptor ----> sidecar JSON
      |                                  |
      +---- emitStmt --------------------+
               emission theorem

                         artifact workspace

exact WASM bytes ---- decode and translate ----> exact Talos Program region
                                                    |
sidecar JSON ---- parse ----> neutral descriptor ---+--- checked equality
                                                    |
                                      descriptor semantic theorem
                                                    |
                                         application invariant
                                                    |
                                           artifact theorem
```

The retained artifact theorem should import the exact decoded `Program`, the neutral descriptor definitions, the descriptor semantic theorem, and application mathematics.  It should not import `LeanExe.IR`, `LeanExe.Wasm.Binary`, the source module, or the compiler-side emission theorem.  The compiler theorem strengthens annotation generation and detects emitter drift, while the exact region equality supplies the logical connection used by the artifact proof.

The separation also supports a distinct theorem-transport result.  A later proof may retain a source theorem, source-to-IR certificate, and compiler simulation theorem to derive an artifact theorem directly.  That result has a larger stated dependency boundary and should remain separate from artifact-only verification.

## Proposed increments

| Rank | Increment | Implementation effort | Retained assumptions | Generality | Expected proof-time effect |
|------|-----------|-----------------------|----------------------|------------|----------------------------|
| 1 | Scalar reification and emission theorem | Small to medium | None: the retained proof uses exact artifact equality | Scalar expressions, conditions, assignments, sequences, branches, and while-loop bodies | High for Demo 1 if it removes transition reconstruction |
| 2 | Certified read, write, and scratch effects | Small after scalar reification | None: the artifact-side checker recomputes effects from the descriptor | Every scalar descriptor and later descriptor families | Medium: removes local-frame and noninterference proof search |
| 3 | Theorem-backed annotation locations | Medium | None: the artifact-side checker validates locations against the decoded program | Calls, branches, loops, and nested regions | Low direct effect: prevents annotation drift and permits more aggressive recipes |
| 4 | Proof-producing region certificate checker | Medium to high | The neutral checker soundness theorem | Every region with a registered descriptor | High: replaces generated decomposition scripts with checked certificate evaluation |
| 5 | Scalar IR-to-descriptor semantic correspondence | Medium | None in artifact-only mode: the theorem may guide certificate generation | The scalar IR fragment with explicit termination | Medium to high when IR invariants or source proofs already exist |
| 6 | Source and local provenance hints | Small to medium | None: names and source paths remain guidance | Any extracted term for which storage provenance survives | Unknown: may reduce invariant discovery without shortening Lean checks |
| 7 | Serializer round-trip theorems | Medium | None for the artifact behavior theorem | All emitted modules | Low for Stage 5: useful for compiler assurance and artifact production |
| 8 | General back-end simulation | Large | Explicit compiler theorem if retained | The supported compiler profile | High eventual value, but unsuitable as the next proof-time experiment |

The first two increments share one descriptor and one structural induction.  The emission theorem proves syntactic agreement with the compiler, while the effect theorem proves which combined locals an evaluation may change.  Their artifact-side counterparts use the same descriptor to prove Talos execution and frame preservation, avoiding two unrelated analyses of a loop body.

The third and fourth increments address the sidecar as a proof-producing interface.  A location theorem ensures that composing annotated fragments preserves each region's path and interval, while a neutral certificate checker converts a decoded instruction region and descriptor into a proved equality or semantic summary.  These results permit the proof agent to start from checked region theorems instead of reconstructing nested lists with `change`, `rfl`, and repeated weakest-precondition steps.

The later increments should depend on measurements from the scalar pilot.  A source-proven invariant can guide an artifact proof, but an invariant copied into a retained module still needs a compiler-free proof over the neutral transition system.  A full compiler simulation solves a broader theorem-transport problem and should not delay the smaller descriptor experiment.

## Increment 1: scalar reification and emission

The compiler-side typed descriptor should cover the scalar subset used by Demo 1.  The subset includes local reads, `UInt64` constants, wrapping addition, subtraction, multiplication, checked unsigned division and remainder, bit operations, shifts, equality, unsigned comparisons, Boolean negation and short-circuit operations, scalar conditionals, assignment, sequence, and statement conditionals.  Reification returns `none` for unsupported IR constructors, preserving a precise descriptor language.

The compiler-side declarations belong in `LeanExe/Wasm/ScalarCertificate.lean`.  They use the compiler's `Instr` type and have no dependency on Talos or the artifact proof workspace.  Separate signatures for plain and release-aware emission expose the theorem boundary required by `emitStmt`.

```lean
def ScalarExpr.ofIR : LeanExe.IR.Expr → Option ScalarExpr
def ScalarCond.ofIR : LeanExe.IR.Cond → Option ScalarCond
def ScalarStmt.ofIR : LeanExe.IR.Stmt → Option ScalarStmt

def ScalarExpr.emit (scratch : Nat) : ScalarExpr → List LeanExe.Wasm.Instr
def ScalarCond.emit (scratch : Nat) : ScalarCond → List LeanExe.Wasm.Instr
def ScalarStmt.emit (scratch : Nat) : ScalarStmt → List LeanExe.Wasm.Instr

theorem ScalarExpr.ofIR_emit
    (h : ScalarExpr.ofIR expression = some descriptor) :
    CoreWasm.emitExprWithRelease releaseIndex scratch expression =
      descriptor.emit scratch

theorem ScalarExpr.ofIR_emitPlain
    (h : ScalarExpr.ofIR expression = some descriptor) :
    CoreWasm.emitExpr scratch expression = descriptor.emit scratch

theorem ScalarCond.ofIR_emit
    (h : ScalarCond.ofIR condition = some descriptor) :
    CoreWasm.emitCond scratch condition =
      descriptor.emit scratch

theorem ScalarCond.ofIR_emitWithRelease
    (h : ScalarCond.ofIR condition = some descriptor) :
    CoreWasm.emitCondWithRelease releaseIndex scratch condition =
      descriptor.emit scratch

theorem ScalarStmt.ofIR_emit
    (h : ScalarStmt.ofIR statement = some descriptor) :
    CoreWasm.emitStmt releaseIndex scratch statement =
      descriptor.emit scratch

theorem ScalarStmt.ofIR_while_emit
    (hCondition : ScalarCond.ofIR condition = some conditionDescriptor)
    (hBody : ScalarStmt.ofIR body = some bodyDescriptor) :
    CoreWasm.emitStmt releaseIndex scratch (.while condition body) =
      ScalarWhile.emit scratch conditionDescriptor bodyDescriptor
```

The plain and release-aware expression and condition emitters need separate agreement theorems because `emitStmt` uses them in different positions.  The `releaseIndex` parameter should disappear from each conclusion whose accepted syntax contains no release or call.  Checked division and remainder require the same scratch-local saves and zero-divisor branches used by `emitCheckedDivModWithRelease`, preventing a descriptor from stating ordinary WebAssembly trapping division when the compiler implements Lean's zero-divisor results.

`emitStmtAnnotated` should call `ScalarStmt.ofIR` when it constructs a while annotation.  On success, the sidecar should contain tagged JSON for the condition and body rather than `reprStr` strings, along with the scratch start and a descriptor version.  The old strings may remain as human diagnostics during migration, but no proof recipe should parse or trust them.

## Increment 2: checked effects and local roles

Structural `reads`, `writes`, and `scratchWidth` functions should accompany the scalar descriptor.  Their preservation theorem states that successful descriptor evaluation preserves every local outside `writes` and the descriptor's scratch interval.  Combined local indices in the statement match Talos's parameter-plus-local numbering.

```lean
theorem ScalarExpr.eval_preserves
    (hEval : expression.eval scratch state = some (value, next))
    (hOutside : index ∉ expression.writes scratch) :
    next.get index = state.get index

theorem ScalarStmt.eval_preserves
    (hEval : statement.eval scratch state = some next)
    (hOutside : index ∉ statement.writes scratch) :
    next.get index = state.get index
```

The compiler can export the computed sets as diagnostics, while the artifact package recomputes them from the parsed descriptor.  A sidecar mismatch should fail strict annotation validation, and the retained theorem should refer only to the recomputed value.  This gives the proof agent named frame facts at each branch and back edge without trusting compiler-provided local roles.

Source-local names can accompany these numeric facts as guidance.  The extraction layer knows storage slots while it compiles lets and parameters, so it can retain a name or expression path where one exists.  Those labels need no theorem and should never determine a proof step.  They help the agent formulate an invariant over a descriptor whose numeric behavior the neutral semantics and exact region equality establish.

## Increment 3: annotation composition theorems

The compiler should prove a restricted code-projection theorem for annotated scalar statements.  For the supported subset, `(emitStmtAnnotated releaseIndex scratch statement).code` should equal `emitStmt releaseIndex scratch statement`, and every reported scalar region should select the descriptor's emitted code from that result.  A theorem over a total scalar annotation function is preferable to forcing induction over the current broad `partial` emitter.

The general `Annotations.Emitted.append` and branch-prefix operations should acquire small preservation lemmas.  These lemmas should state how an empty relative path shifts during concatenation, how an existing nested path keeps its inner indices, and how an `if`, block, or loop prefixes a field path.  They make annotation coordinates an emitter invariant rather than parallel bookkeeping that only example tests exercise.

These compiler theorems should not replace artifact-side region selection.  The retained package continues to evaluate `Project.ProofKit.Annotation.region` over the exact decoded function and prove equality with the neutral descriptor program.  Compiler-side location theorems instead guarantee that normal compiler changes fail near the emitter when they make the sidecar stale.

## Increment 4: a neutral certificate checker

Generated `AnnotationMatches` files currently contain artifact-specific declarations ending in `by rfl`.  That method is sound because Lean checks equality with the decoded `Program`, but a growing descriptor vocabulary will produce large generated expressions and difficult diagnostics.  A neutral checker can accept an exact region and a descriptor, return success only when the region equals the descriptor program, and expose one soundness theorem.

```lean
def checkScalarRegion
    (program : Wasm.Program) (descriptor : ScalarRegion) : Bool

theorem checkScalarRegion_sound
    (h : checkScalarRegion program descriptor = true) :
    program = descriptor.program
```

The package can discharge a closed check by reduction and use `checkScalarRegion_sound` to obtain the equality.  Mutation tests should alter one opcode, constant, local index, branch arm, scratch index, path step, and interval endpoint, requiring each changed package to fail before the behavioral theorem begins.  The checker belongs in the artifact proof workspace and imports no compiler definitions.

A later certificate can contain a composition tree rather than one equality.  Each node can identify a scalar transition, fixed-array load, allocator region, call, or loop, and the checker can establish coverage and non-overlap against the exact structured program.  The semantic theorem then composes registered proof-kit results according to the checked tree, leaving only application predicates, invariants, and termination arguments.

## Increment 5: semantic use of IR theorems

Once scalar reification exists, prove that reification preserves scalar evaluation.  The theorem should cover only successful reification and should use a termination relation for loops instead of the current evaluator's silent fuel cutoff.  This theorem lets compiler-side analyses and source-certificate experiments reason about the same transition descriptor used by artifact proofs.

An artifact-only proof cannot retain this IR correspondence theorem under the current dependency policy.  The compiler may use it to generate candidate invariants, transition equations, or a source-free semantic capsule, but the final package must check those claims again over the neutral descriptor.  If a user chooses theorem transport, the final theorem may name the IR correspondence explicitly and disclose the larger dependency boundary.

A useful intermediate result is a theorem about one loop step rather than whole-function compilation.  When scalar reification succeeds, the IR body's next store and the neutral descriptor's next state should agree on represented locals.  This result can validate generated loop equations and reveal errors in local numbering before Codex starts, while the retained Talos descriptor theorem independently proves the same equations for the exact artifact.

## Smallest useful proof of concept

The first proof of concept should cover Demo 1 function zero's while condition and body.  The completed `Project.ProofKit.ScalarTransition` expression, statement, and while theorems supply the neutral artifact-side semantics, while the remaining compiler work adds scalar reification and its emission theorem, emits a structured descriptor in the while annotation, and generates one exact `AnnotationMatches` equality for the frozen decoded function.  The artifact behavior proof should use the descriptor theorem for the complete loop transition while leaving the prime-factor invariant, decrease proof, and terminal number-theoretic equality in the artifact-specific module.

The implementation touches six existing areas and one new compiler module.  `LeanExe/Wasm/ScalarCertificate.lean` defines compiler-side reification, emission, effects, and the plain, release-aware, and while-composition agreement theorems.  `LeanExe/Wasm/Annotations.lean` and `LeanExe/Wasm/Binary.lean` carry the structured descriptor, while `proofs/talos/lean/Project/ProofKit/ScalarTransition.lean` supplies neutral semantics and Talos weakest-precondition results.  `tools/leanexegen-annotations.js` parses the descriptor and generates the exact match and recipe, and `test/leanexegen.js` covers validation and mutations.

The proof data should flow through four checked boundaries.  Successful compiler reification proves agreement with the emitter and writes a descriptor.  Leanexegen parses that descriptor, the generated package proves equality with the exact decoded loop region, the generic descriptor theorem proves its Talos transition, and the application proof supplies the invariant and termination facts.

Demo 1 supplies the in-sample performance test.  Its isolated scalar-loop baseline has three retained proof-generation times of approximately 436, 490, and 680 seconds, while the annotation-only screen produced no proof after approximately 1,082 seconds.  Three fixed reproofs with the descriptor should use the same WASM, formal specification, model, reasoning level, cache policy, and proof-isolation rules.  Failures and timeouts remain part of the result.

Demos 2 through 5 should run their existing annotation and package tests to detect parser or emitter regressions.  They do not provide an independent scalar-loop performance sample because their current gains come from array search, map, and filter composition theorems.  Before promoting scalar certificates as a general proof-time method, freeze a held-out Demo 6 such as a two-element input array whose scalar helper computes Euclid's algorithm and returns a singleton result, record its annotation-free baseline, and then expose the scalar descriptor without changing its source, specification, or WASM.

The proof of concept succeeds only if the descriptor remains generic and lowers median Stage 5 time.  A shorter proof, a better journal, or successful first-check elaboration does not compensate for a slower complete proving session under the project's current objective.  Demo 6 should confirm that any improvement survives a different loop invariant, branch shape, and arithmetic operation before the method expands to array-loop bodies.

## Implemented first increment

The production emitter now uses `LeanExe.Wasm.ScalarDescriptor` for every expression, condition, statement, or while loop that reifies into the supported scalar subset.  Its former partial definitions remain fallback emitters for unsupported syntax, while the total public entry points select descriptor emission after successful reification.  `LeanExe.Wasm.ScalarCertificate` proves agreement for expressions, conditions, statements, and complete while loops by reducing those public entry points through the successful reification equation.

Version-one while annotations contain the neutral syntax tree in JSON, with `UInt64` constants encoded as decimal strings.  The consumer validates the complete tree, renders it as `Project.ProofKit.ScalarTransition` data, and generates an exact theorem over the selected decoded instruction interval.  Recipe validation accepts the scalar-loop theorem only when the descriptor exists and the recipe names both that exact equality and the generated program.

The current array-wrapper Demo 1 passed the production `leanexegen annotate` path without changing its 1,938-byte WASM artifact.  Lean checked the generated equality for function zero's top-level interval two through three, and package verification accepted the resulting exact-artifact theorem.  This completes the structural bridge while leaving the proof-generation timing experiment and held-out scalar demo open.

## Further experiments

A compiler-generated cut-point graph can divide one function into transitions at loop heads, calls, allocation boundaries, and returns.  The compiler can prove that its graph covers the emitted structured code, while an artifact-side checker independently reconstructs coverage from exact regions.  Codex would then prove relations between cut-point states instead of discovering the graph and instruction boundaries.

Abstract-interpretation certificates can add range and representation facts to those cut points.  The compiler computes intervals, nonzero divisors, unchanged-local sets, or scratch freshness, and a small neutral checker validates each fact over descriptor transfer functions.  Each successfully checked fact replaces the corresponding repeated `omega`, fixed-width normalization, or local-frame search without embedding application-specific behavior in the proof kit.

The compiler can also emit proof obligations rather than conclusions.  For a loop, the descriptor generator can name initialization, preservation, exit, and decrease formulas over a typed state record, with no proposed invariant.  This gives Codex a standard goal and allows proof telemetry to attribute time to application mathematics rather than instruction reconstruction.

A source theorem may help generate an invariant candidate through local provenance and cut-point correspondence.  The candidate should enter the artifact task as prose or a source-free proposition, and the exact descriptor proof must establish it without importing the source theorem.  This experiment measures whether compiler structure and source mathematics together reduce invariant discovery while preserving artifact-only verification.

## Work that should wait

A full correctness theorem for `Extract` cannot be a modest next step.  It requires a semantics for the supported elaborated Lean fragment or per-program extraction certificates, and heap-typed programs require an IR value semantics and ownership model that the current evaluator lacks.  The existing compiler-verification and theorem-transport plans remain the appropriate home for that work.

A whole-back-end simulation should also wait for evidence from the scalar descriptor pilot.  The pilot proves many of the same scalar emitter cases and reveals the usable state relation, scratch discipline, and theorem decomposition at a smaller boundary.  If the pilot reduces proof time on Demo 1 and the held-out scalar demo, its theorems can form the scalar portion of the later simulation.

Serializer correctness has value for compiler assurance and artifact production, but it does not address the measured Stage 5 bottleneck.  The current exact-byte decoder, validator, translation, and package equality already establish the retained artifact identity.  Serializer work should proceed when it supports theorem transport or eliminates production cost, rather than displace the transition-certificate experiment.

## Decision after the pilot

The measured pilot determines the next compiler-theorem investment.  A substantial reduction on Demo 1 and the held-out demo justifies extending the descriptor and certificate checker to array-loop scalar bodies, calls, and allocation cut points.  A neutral or slower result means the remaining time lies in invariant mathematics, agent planning, or Lean elaboration, and telemetry should identify which part before adding more compiler theorems.

Both outcomes preserve the artifact boundary.  Compiler theorems may explain emission, validate certificate generation, and provide candidate mathematics.  The retained proof rests on exact decoded-region checks and neutral semantic theorems when it establishes that the WASM satisfies its specification.
