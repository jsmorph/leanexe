# Faster Direct WASM Proof Generation

| Field | Value |
|---|---|
| Date | 2026-08-05 |
| Primary metric | Wall-clock time to generate an accepted artifact proof |
| Required result | A theorem over the exact module decoded from the frozen WASM bytes |
| Reference case | `.lake/leanexegen-runs/demo1-timing-1` |

## Result to preserve

The final theorem must continue to concern the exact WAT-derived Talos `Program`, and the package theorem must continue to connect that `Program` to the module decoded and validated from the embedded WASM bytes.  The accepted demo-1 package establishes this boundary through `Behavior.artifact_behavior : FormalSpec.ArtifactSpec module`, followed by `Artifact.artifact_correct` over `decode artifactBytes`.  Any source file, compiler trace, language model, tactic, certificate generator, or proof planner may propose evidence, but Lean must check the retained evidence against those exact definitions.

Artifact-only verification and artifact-only proof generation are separate properties.  A proof agent may use source material as untrusted guidance and still produce a package whose theorem and import closure contain no Source module or compiler theorem.  Such a package remains independently verifiable after deleting the source, compiler, guidance, and generator, although the history of its construction used information from them.

A transported theorem has a different dependency boundary.  If the final derivation composes a source theorem with a proved lowering or simulation theorem, the theorem still concerns exact bytes when the derivation includes checked equality with the decoded artifact.  It then depends logically on the source definition, source theorem, proof-level lowering, and their specifications, so it does not replace the direct artifact-only result required here.

## Current evidence

The accepted array-based demo-1 proof at `.lake/leanexegen-runs/demo1-timing-1` took 58 minutes 36.775 seconds in stage 5.  An earlier 48-minute 32-second package concerned a different 1,954-byte WASM and disappeared when `/tmp` was cleared, so it cannot serve as the fixed comparison case.  The retained interval includes the headless Codex session, its file inspection and Lean iterations, and the independent outer checks, while the stage report records neither internal command counts, failed candidate hashes, nor command durations.

The final `Behavior.lean` contains 579 lines and 23,233 bytes.  Lines 11 through 364 define the prime-factor mathematics, the generated local frame, the loop invariant, and the 160-instruction scalar helper proof; lines 423 through 578 prove the 263-instruction exported array wrapper and its allocation result.  The middle wrapper around the scalar helper occupies 34 lines, so proof length does not distribute evenly across semantic difficulty.

A controlled reproof added `BumpFacts.wordAddress` and `wordAddress_toNat` to the checked proof kit while holding the formal specification, Source, WASM, `Program`, support modules, Codex version, and Lean toolchain fixed.  Stage five fell from 3,516.775 seconds to 1,964.130 seconds, a reduction of 44.15 percent, and independent verification accepted the result.  The faster proof contains 591 lines and 22,760 bytes, so this single run demonstrates a timing possibility rather than a relationship between proof size and proving time.

Two unchanged word-address reproofs took 360.144 and 2,249.443 seconds.  Together with the 1,964.130-second run, they establish a median of 1,964.130 seconds and a range of 1,889.300 seconds.  The outer-acceptance intervals stayed between 33.573 and 41.742 seconds, placing nearly all observed variance in the Codex proof session.

`Project.ProofKit.FixedArrayAllocator.region_spec` now proves the complete emitted empty-free-list search and no-growth bump path, including capacity normalization, six header stores, global updates, and returned-root assignment.  Three fixed-artifact proofs applied that theorem and independently verified in 2,556.812, 1,134.008, and 941.494 seconds.  Their 1,134.008-second median is 42.3 percent below the word-address median, although their 1,615.319-second range shows that model search remains unstable.

`Project.ProofKit.FixedArraySingleton.region_result_spec` composes that allocator theorem with the emitted singleton-result suffix.  It proves the length and payload stores, result-local assignments, address bounds, and final `UInt64Array.At` predicate for an arbitrary scalar value, leaving the artifact proof to connect that value to the formal specification.  Three accepted uses took 680.396, 436.403, and 489.993 seconds, giving a 489.993-second median and a 243.993-second range.

The [current proof kit](proofs/talos/lean/Project/ProofKit/README.md) removes repeated leaf obligations and two complete runtime regions.  `Project.ProofKit.Array` supplies the public array representation and load facts, `Project.ProofKit.Allocation` supplies bump-allocation arithmetic, `Project.ProofKit.Memory` supplies read-over-write facts, `Project.ProofKit.FixedArrayAllocator` proves the emitted allocator region, `Project.ProofKit.FixedArraySingleton` proves the singleton allocation and result region, and `Project.ProofKit.Control` supplies entry and wrapper tactics.  The accepted proofs still discover the scalar loop invariant, prove the application lemmas, symbolically execute the scalar loop branches, and process the input-array wrapper.

The current `Project.ProofKit.Allocation` exposes `BumpFacts.wordAddress` and `wordAddress_toNat`, which replaced the proof's local root and payload address derivations in the faster controlled reproof.  The run reached its first complete candidate about eight minutes earlier than the retained baseline.  These theorems still leave the search for a function summary, loop invariant, branch semantics, and allocator control-flow proof.

Earlier control-tactic experiments establish an important negative result.  The first proof-kit run reduced the behavior proof from 329 to 321 lines while stage 5 increased from 238.557 to 253.925 seconds, and the later loop-tactic reproof reduced it to 316 lines while stage 5 increased to 390.849 seconds.  These runs had different artifacts from the current array case, but they show that fewer lines and faster generation are independent measurements.

One result in the [proof-engineering notes](docs/plan-notes.md) shows where abstraction can change elaboration cost.  `Project.WpScaffold.wp_run_folded` and generated frame facts reduced `Project.Validate.Loop` from 1,560 seconds to 15 seconds by preventing repeated reduction of a large literal local frame.  This result concerns Lean elaboration rather than model search, but repeated Lean checks form part of proof-generation time and can dominate an iterative session.

The current proof task receives a 24,862-byte selection from the [strategy guide](docs/proof-strategies.md) and a 5,961-byte proof-library catalog.  Demo-1's coarse feature classifier selects all ten strategy sections because its three reachable functions contain calls, loops, arithmetic, memory, allocation, and a function longer than 200 instructions.  The guide describes useful proof shapes, but it does not identify exact regions, local meanings, runtime templates, or theorem applications for this `Program`.

## Where stage 5 spends effort

The present data supports a list of plausible costs, not a ranked attribution.  The agent must infer a semantic decomposition from a literal `Program`, choose statements for each helper, recover application mathematics from the formal result, and discover a loop invariant that matches generated locals.  It then writes one module and repeatedly builds the final artifact target, so a late change can force Lean to elaborate all earlier material again.

The proof kit currently operates mostly below the semantic boundaries that organize the program.  `bumpFacts` proves address and page arithmetic, but the proof still steps through the allocator's branches and stores; `word_reads` normalizes finished memory expressions, but the proof still constructs those expressions; and entry tactics open the same weakest-precondition goal that follows their use.  These declarations are useful, but a major time reduction requires checked results at function, region, loop-transition, and ABI-wrapper boundaries.

The guidance also asks the model to perform repository archaeology inside a time-sensitive proof task.  Its examples cite successful CLOB, validator, LEB128, frame, and allocator modules, while the isolated task permits only the curated proof-kit imports.  A model can learn a pattern from those descriptions, but it must translate the pattern into the current names, local indices, and instruction slices before Lean supplies useful feedback.

The single candidate module obscures progress.  A failed edit to the exported wrapper can cause Lean to revisit the already accepted scalar loop proof, while a changed invariant can invalidate hundreds of following lines.  The orchestrator retains no accepted submodule or theorem checkpoint from an interrupted session, so another reproof begins the same discovery work unless the model reconstructs it from the fixed context.

## Sound acceleration boundaries

The checker boundary determines whether an acceleration affects the logical dependency of the result.  Proof-producing automation and untrusted hints can save generation time without becoming assumptions.  Direct theorem transport can establish an exact-byte theorem, but it carries the source and lowering results into the derivation.

| Mechanism | Retained logical dependency | Must its generator be trusted? | Artifact-only final proof? |
|---|---|---|---|
| Checked proof-kit theorem | Talos semantics and the theorem's import closure | No | Yes |
| Lean tactic that emits a proof term | The declarations referenced by the emitted term | No | Yes |
| Generated region equality or local-frame lemma proved by `rfl` | Exact `Program` and neutral support declarations | No | Yes |
| External source, proof, or compiler trace used only as prose guidance | None | No | Yes |
| Source-derived Lean module containing only independently proved mathematics over the formal specification | That mathematical module | No | Yes, if its import closure excludes Source and lowering claims |
| Target certificate checked directly against the exact `Program` | The certificate checker and checked certificate theorem | No | Yes |
| Source theorem composed with a checked source-to-target refinement theorem | Source, refinement, ABI, and exact-artifact equality | No, if all evidence is checked | No |

The import and axiom audits should enforce these distinctions rather than rely on prompt language.  A hint-assisted run may package the hint digest for reproducibility while omitting the hint from the proof import closure.  An artifact-only verifier should rebuild from the retained Lean sources without requiring the hint, Source module, compiler, or certificate producer.

## Artifact-derived proof workbench

### Exact structural map

Leanexegen should derive a detailed proof map from the frozen `Program` before starting Codex.  The current feature file records function-level counts and Boolean features, while a useful map would name every reachable call, structured-control path, branch continuation, instruction range, local initialization, load and store address expression, and recognized runtime region.  The map is untrusted planning data because the final Lean proof still checks the exact program.

The same pass can emit checked structural declarations.  It can define named instruction slices, prove their concatenation equals each generated function by `rfl`, generate folded local-frame access and update lemmas, and prove exact equalities between recognized regions and canonical templates.  A faulty pass then produces a declaration that Lean rejects instead of directing the proof toward a different program.

For demo-1, the map should identify three semantic units before model inference: the scalar factor loop in function 0, the conditional one-call wrapper in function 1, and the singleton-array ABI wrapper with an inlined empty-free-list bump allocation in function 2.  It should also identify the exported function and exclude unreachable retain, release, and allocator exports from the proof plan.  This information currently exists only after the model reads and interprets hundreds of instruction constructors.

### Generated proof scaffold

The structural pass can generate a Lean scaffold with definitions and named target propositions but no unproved declarations.  It can supply `factorFrame`-style folded frames, exact region definitions, call-site facts, entry reductions, and expected signatures for function summaries, leaving candidate modules to prove those propositions from an application relation and loop invariant.  Lean checks every completed module, while the generator remains outside the trusted base.

A scaffold should expose semantic holes at stable boundaries rather than create one goal per instruction.  For a loop it should request an invariant, a measure, initialization, one theorem per branch transition, and an exit theorem; for a call it should request one callee summary; for the allocator it should request a capacity and result representation.  The model then chooses mathematical content without spending tokens and Lean iterations reconstructing target syntax.

The scaffold also provides a place to select proof-kit declarations mechanically.  If the `Program` matches the fixed-array bump template, the generated module can import the allocation facade and state the exact application of its region theorem.  If no template matches, the scaffold should retain the raw region and report that classification rather than choose a superficially similar theorem.

### Target verification-condition generator

A larger step is a verification-condition generator over `Wasm.Program`.  The generator symbolically executes straight-line instructions, converts structured branches into separate obligations, replaces proved calls with summaries, and stops at loops for caller-supplied invariants and measures.  Its output should be a theorem whose conclusion is a weakest-precondition or `TerminatesWith` statement over the exact program.

The sound implementation can take either of two forms.  A Lean metaprogram can construct proof terms from existing weakest-precondition lemmas, leaving every term to kernel checking; alternatively, a verified Lean function can consume annotations and return a derivation whose soundness theorem yields the target result.  An external model or compiler may propose annotations, because neither form trusts their producer.

The verification-condition language should describe locals by symbolic expressions and memory by named regions.  Machine arithmetic, load bounds, and read-over-write results can become side conditions handled by the proof kit, while the application-specific obligations state relations such as factor-count preservation.  This division gives source proofs and proof agents a stable place to contribute semantic facts without exposing the full instruction interpreter.

### Proof-producing target normalization

A proof-producing decompiler offers a more ambitious artifact-only route.  It can translate the exact structured WASM program into a small SSA or control-flow language and prove that executions of the normalized program correspond to Talos executions of the original.  The behavior proof then targets the smaller language, while the checked correspondence restores the exact-program theorem.

This approach differs from compiler verification because it starts from the decoded artifact.  The decompiler and optimizer remain untrusted when they emit a candidate normalized program plus a checked equivalence certificate.  The hard work lies in calls, loops, memory, traps, and state framing, but the current structured Talos `Program` avoids arbitrary control-flow recovery.

The first target-normalization pilot should cover scalar functions with locals, arithmetic, conditionals, and one loop.  Demo-1 function 0 fits that profile and isolates the difficult semantic loop from the array allocator.  A successful pilot would replace a 250-line instruction proof with a target-equivalence theorem plus an invariant proof over a compact transition system.

## Higher semantic lemmas and tactics

The next proof-kit work should raise the abstraction from arithmetic facts to region semantics.  Existing CLOB and fixed-array proofs already contain parameterized instruction theorems for empty free-list search, bump allocation, fixed-array memory construction, copy loops, and representation framing.  The task is to distill neutral statements with small premises and exact region-matching requirements, rather than import application modules into leanexegen.

| Boundary | Current support | Higher semantic result |
|---|---|---|
| Large local frame | Generic folded-frame machinery exists outside the leanexegen facade | Generated `frame_step` facts and a proof-kit facade exposing the checked `wp_run_folded` tactic |
| Straight-line region | `wp_run` and manual simplification | A proof-producing `wp_region` that stops at calls, branches, and loops |
| Empty free-list search | Demo proof uses a zero-measure loop directly | A parameterized region theorem returning the no-fit frame |
| Bump allocation | `BumpFacts` proves arithmetic | A `wp` theorem for the exact allocator region returning the modeled store, pointer, pages, globals, and frame |
| Array result construction | Singleton and pair representation constructors | A theorem for writing a length-prefixed vector of words into a fresh region |
| Singleton array wrapper | Manual ABI loads, scalar call, allocation, stores, and result reconstruction | A theorem parameterized by the scalar callee summary and expected-value equation |
| Application loop | Raw `wp_loop_cons` plus a caller-written invariant | A relational loop scaffold that asks for abstract transitions, rank decrease, and terminal interpretation |
| Repeated helper region | Function summaries remain artifact-local | Transport through checked function-region renaming or a structural template equality |

The inlined allocator offers the best near-term semantic target.  The accepted public proof spends substantial effort executing a runtime implementation whose behavior is stable across generated array programs.  A theorem over the exact allocator instruction region can absorb that execution while retaining explicit premises for memory fit, page limits, globals, and returned ownership.

The singleton-array wrapper offers the next composition boundary.  A generic theorem can accept a scalar `TerminatesWith` result, the input array representation, and a proof that the scalar result equals the formal expected element, then establish the ABI postcondition after allocation.  Its structural premise must prove that the concrete entry body matches the wrapper template, so the theorem cannot apply to a changed artifact by heuristic recognition.

The scalar loop needs a different abstraction because its mathematics changes by program.  A relational loop theorem can separate target mechanics from semantic choice: the caller supplies an abstract state relation, a representation of that state in generated locals, a well-founded rank, one target-to-abstract transition theorem for each branch, and a terminal-result theorem.  The theorem can handle Talos block, loop, repeat, fallthrough, and done-flag administration once for every consumer.

Tactics should produce small, predictable goals and fail at the first unmatched structure.  Broad simplification over a long program can consume more time than explicit region theorems and can leave a goal whose origin is hard to determine.  Each tactic needs focused timing on at least two consumers, because shorter proof text has already failed to predict generation time.

## Guidance and proof-search interfaces

More prose will not fix discovery when the task already selects every section.  The proof agent needs exact declarations, exact program facts, and small examples chosen for the current goal.  A catalog generator should obtain declaration names and signatures from Lean, associate each with structural tags and representative consumers, and fail its test when a signature or import changes.

A goal-directed query tool can search that catalog without running Lean.  Inputs can include the active theorem shape, instruction constructors in the current region, memory representation, and desired postcondition; output can contain a ranked list of declarations, exact `#check` text, required premises, and one compact application.  The search result remains advice, while Lean resolves all names and checks the application.

The generated proof map should select examples by structural fingerprint rather than repository prominence.  A demo-1 allocator goal should receive the nearest empty-free-list bump theorem, not general discussions of retain, release, ownership trees, or LEB128 copies.  A scalar loop should receive one invariant scaffold and one folded-frame example whose locals and control shape resemble the target.

Accepted artifact proofs can form a retrieval corpus after normalization.  Index a region by instruction-tree hash, call-renaming-normalized hash, local count, memory operations, and theorem shape, then return a checked reusable theorem when the region matches or a prose example when it does not.  `Project.FunctionRegion.terminatesWith` already transports a closed portable function region across direct-call index renaming, which provides a checked first mechanism for exact reuse.

Guidance should distinguish facts that the structural pass established from suggestions that a source or model proposed.  `PROGRAM_FACTS.json` can contain exact artifact-derived data, while `SEMANTIC_HINTS.md` can contain untrusted function names, variable meanings, invariants, and proof ideas.  This separation prevents a compiler mapping from appearing to carry the same status as a checked function-body equality.

## Information from a Lean source proof

A theorem proof term does not contain the tactic narrative that produced it.  Lean retains constants, recursors, applications, and proof arguments, so a tool can inspect dependencies and induction structure, but recovering the author's intended loop invariant or compilation mapping from an arbitrary elaborated term is unreliable.  A source-proof interface should therefore request useful annotations explicitly or derive them from a structured proof language.

The source theorem may also state less than artifact functional correctness.  A theorem `P x (f x)` can transport `P` only after another result proves that the artifact returns `f x`; a weak `P` cannot identify the artifact result.  The source side therefore needs a functional source-to-model certificate or a semantic relation strong enough to determine the returned value.

### Untrusted source-proof guidance

The cheapest experiment is to let the artifact proof agent inspect the Source definition and its proof while continuing to prohibit Source imports.  The agent can copy the recursive state relation, induction parameters, branch facts, and mathematical lemmas into a direct proof, then Lean checks the result against the exact target.  This mode changes the construction history but leaves the final package source-free.

A narrower variant exports a structured hint file before deleting Source from the proof workspace.  The file can name candidate function summaries, source variables, loop state, ranking functions, branch meanings, mathematical dependencies, and a tentative source-to-target local map.  Compiler debug information can fill the map as untrusted data, while the target proof verifies each claimed correspondence through symbolic execution.

Demo-1 provides a direct test.  A source proof of `Source.compute input = FormalSpec.expected input` would naturally expose `countFactorsFuel`, the decreasing fuel, the remaining value, divisor, accumulated count, and the prime-factor invariant.  Supplying those facts should remove much of the semantic discovery in `func0_correct` even though the finished target proof cannot apply the source theorem.

### Source-derived semantic capsule

A stronger interface asks the source proof task to emit a source-free semantic capsule.  The capsule contains a small abstract state, an inductive or functional transition relation, initialization and terminal theorems, application mathematics, and a proof that every terminal state yields the formal expected value.  Its imports may include the formal specification and neutral mathematics, but they must exclude Source, compiler IR, and lowering claims.

For demo-1, the capsule could define a state containing remaining value, divisor, count, and fuel.  It could prove the factorization lemmas now located at the start of `Behavior.lean`, state the two forms of progress, and prove that the terminal count equals `primeFactorsList.length`.  The artifact proof would then prove that each branch of function 0 implements one capsule transition and that the generated measure decreases.

This capsule transports useful proof content without transporting a source theorem as a premise.  A source-aware generator can propose its declarations and proofs, but Lean checks them as independent mathematics, and the target simulation remains direct.  The capsule may be program-specific because artifact-only verification constrains dependencies and theorem subjects rather than requiring every supporting lemma to be reusable.

### Target annotations synthesized from source proofs

Source recursion and induction hypotheses can supply target loop annotations.  An emission trace can map source parameters and local bindings to target function parameters and local slots, map recursive calls to loop back edges, and map source base cases to target exits.  The trace remains untrusted when a target verification-condition generator checks every annotated region against `Program`.

This method resembles translation validation at the proof-obligation level.  The source proof supplies candidate invariants and summaries, the compiler supplies candidate correspondence metadata, and the target checker produces an artifact-only theorem.  A mismatch causes an unproved verification condition rather than a false artifact result.

The source proof can also guide lemma selection.  Its constant dependencies identify arithmetic, list, array, and number-theoretic results likely to recur in the target proof, while its induction arguments identify likely ranks and preserved relations.  The proof planner can translate those dependencies into exact catalog queries without importing the source theorem.

### Target certificates

A target certificate can contain the region decomposition, symbolic states, function summaries, loop invariants, ranks, branch transitions, and memory frames needed by the verification-condition generator.  A source proof and compiler trace can produce the certificate, but the checked conclusion mentions only the exact `Program`, formal specification, and neutral library.  This is the most promising route from source proof content to a direct artifact proof.

Certificate checking should use small declarative records rather than generated tactic scripts when possible.  The checker can report which region, annotation, or side condition failed, and a language model can revise that component without rewriting the complete behavior module.  The final package retains the certificate value or generated proof modules and rebuilds them under the same import and axiom audits.

### Direct theorem transport

The existing [source-theorem transport plan](plans/theorem-transport.md) proves a source-to-IR certificate, a generic IR lowering theorem, and full equality between the lowering and the exact decoded artifact.  It can eliminate handwritten target proofs for an accepted source and compiler profile.  Its final result depends on source semantics and proved lowering, so it complements the direct artifact-proof line rather than replacing it.

The verified lowering can still improve the direct line without becoming a final dependency.  Its proof architecture can define the target certificate language and generate candidate annotations, while the artifact-only checker replays those annotations against the target.  Erasing source dependencies requires generating a new target proof; proof irrelevance or runtime erasure does not remove imported constants from Lean's logical dependency graph.

## Decomposition and caching

The generated proof should use several case-local modules.  A practical demo-1 division is `Behavior.Math`, `Behavior.Func0`, `Behavior.Func1`, `Behavior.Entry`, and a short `Behavior` composition module.  Each module can be accepted and cached before the model proceeds, while the final verifier rebuilds all source modules from the package.

This division changes both model search and Lean cost.  The scalar loop task sees its formal mathematics and function body without the allocator, while the entry task sees the accepted scalar summary without the loop implementation.  Editing the entry proof no longer forces Lean to elaborate the loop source, because Lake can reuse the checked `.olean` during generation.

The orchestrator can run a sequence of headless tasks with explicit theorem outputs instead of one task that owns the whole file.  It should derive that sequence from the checked call graph and region map, retain accepted modules after a later task fails, and present the next task with theorem signatures rather than prior conversation.  Lean commands remain serial under `tools/leanrun`, while independent model planning could run concurrently only when the theorem interfaces are already fixed.

Cross-artifact caching requires a checked correspondence.  A content-addressed entry can key on the normalized region, theorem statement, Talos and proof-kit identities, and all imported source digests; reuse then supplies a proof module plus a region equality or function-transport theorem.  A structural similarity score may retrieve an example, but it cannot authorize theorem reuse.

A persistent Lean process may reduce repeated startup and import costs, but it requires integration with the machine-wide lock and cgroup policy.  Module division and focused targets offer a lower-risk first experiment because they use the current runner unchanged.  The generation workflow should build the active helper target after an edit and reserve `ArtifactResult`, embedded-byte comparison, and declaration audit for accepted checkpoints and the final outer check.

## Measurement

Stage 5 needs structured telemetry before another optimization comparison.  The orchestrator should record the start and end of the Codex task, every prescribed Lean command, candidate source hash, target, exit status, elapsed time, timeout, and final outer checks.  It should record enough information to separate model work from Lean without retaining complete model conversations or large terminal transcripts.

The fixed comparison case should remain the exact package at `.lake/leanexegen-runs/demo1-timing-1`: the same request, formal specification, source artifact, WASM bytes, Talos `Program`, Codex version, model settings, Lean toolchain, and machine resource limits.  `leanexegen reprove` already holds the frozen modules and artifact fixed while allowing proof-kit changes.  Proof guidance, proof-kit identity, scaffold identity, and source-hint identity must appear in each result.

| Metric | Reason |
|---|---|
| Stage-5 wall time | Primary user-visible generation cost |
| Codex-task wall time | Separates generation from outer verification |
| Time to first Lean check | Measures structural and semantic planning delay |
| Lean check count and cumulative time | Measures iteration and elaboration cost |
| Failed candidate count by diagnostic class | Identifies discovery, API, arithmetic, and elaboration failures |
| Final outer-check time | Measures retained proof cost independently of search |
| Peak memory and timeout count | Detects tactics or theorem boundaries that do not scale |
| Success rate over repeated fixed runs | Prevents one fast failure-prone method from appearing better |
| Accepted proof structure | Secondary evidence from lines, syntax volume, local scaffolding, and shared theorem use |

One run can reject an approach that fails or becomes much slower, but it cannot establish a stable timing improvement.  Promising variants should receive at least three fixed reproofs with the same cache policy, followed by comparison of their medians and ranges.  Cold verifier time should be measured separately from warm proof-generation time because they answer different questions.

Accepted proof structure is a secondary optimization objective.  Fewer proof steps, less local scaffolding, and greater use of shared theorems can justify refinement even when the first timing screen regresses, while proving time remains primary.  Raw source bytes and identifier length do not measure proof complexity, and a proof may contain longer names because it applies more shared declarations.

## Concrete experiments

The experiments below hold the exact artifact and formal statement fixed.  Each experiment should preserve the source-free import audit for the final artifact-only package.  An experiment that uses source hints must also prove that deleting those hints does not prevent independent verification of the published package.

| Order | Experiment | Mechanism | Acceptance evidence |
|---|---|---|---|
| 0 | Telemetry baseline | Instrument internal Codex and Lean actions, then reprove with the current kit | Reproduce an accepted theorem and attribute stage-5 time |
| 1 | Exact proof map and split scaffold | Generate checked regions, folded frames, and separate helper modules from `Program` | Lower median generation time with no source context |
| 2 | Semantic allocator and singleton-wrapper theorem | Distill a neutral `wp` result for the recognized runtime region and compose it around the scalar callee | Entry proof uses the region theorem and exact structural equality |
| 3 | Source-guided invariant | Supply a structured, untrusted summary of the source proof's state, rank, branches, and mathematics | Final package omits Source and verifies after deleting the hint |
| 4 | Source-free semantic capsule | Generate checked program-specific mathematics and an abstract transition system from the source proof | Target proof imports the capsule but no Source or lowering module |
| 5 | Annotated target certificate | Have the source proof and compiler trace propose VCG annotations checked against `Program` | Checker produces `artifact_behavior` from the exact certificate |
| 6 | Scalar target normalization | Prove demo-1 function 0 equivalent to a compact artifact-derived transition system | Replace most instruction-level scalar proof while preserving exact target composition |
| 7 | Fixed association-list demo | Apply the winning artifact-only method to demo-2's array loads, fixed search, pair result, and allocation | Confirm that the improvement extends beyond prime-factor mathematics |

Experiments 1 and 2 address costs visible in the accepted proof without changing the source boundary.  Experiment 3 tests how much time comes from recovering semantic intent, while experiment 4 tests whether source proof content can become checked source-free mathematics.  Experiments 5 and 6 require more implementation, but they can change proof generation from free-form script synthesis into annotation and certificate synthesis.

The first semantic theorem should target the inlined bump allocator and singleton output construction, not another entry macro.  Existing proof-kit additions already cover the remaining leaf address expressions, and prior entry macros reduced text without reducing time.  A region theorem removes a complete instruction proof and gives the model a function-level postcondition it can compose.

The first source-assisted comparison should use explicit ideal annotations written from a real source proof.  It should not include the accepted target proof or target-specific tactic sequence, because that would measure reproduction from an answer rather than transport of source reasoning.  If ideal annotations reduce time, the next work concerns extracting them; if they do not, source-proof mining should not displace target VCG and runtime theorem work.

## Recommended sequence

Instrumentation comes first because the 58-minute aggregate cannot identify the limiting component.  The exact proof map, generated folded frames, focused targets, and module checkpoints follow because they improve every proof mode and preserve the current boundary.  These changes also create the interfaces needed by semantic runtime theorems and target certificates.

The next abstraction should prove the semantics of the fixed-array allocator region and singleton-array wrapper.  Demo-1 and demo-2 both need array allocation and output representation, and the repository contains established allocator results from which to distill the theorem.  The result should accept an explicit scalar or fixed-search summary and should require checked equality with the concrete instruction region.

Source-proof assistance should then begin with an optional hint mode and a source-free semantic capsule.  Those experiments can determine whether the model's long delay comes from rediscovering application invariants and mathematics.  Their final proof packages must pass the same source import rejection as artifact-only generation.

An annotated target VCG is the largest likely improvement that retains direct artifact verification.  It turns the model's task into supplying function summaries, invariants, ranks, and side-condition proofs, while deterministic target machinery handles instruction execution and control plumbing.  Proof-producing target normalization becomes worthwhile if the VCG still exposes too much generated local and stack structure.

The direct source-theorem transport plan should proceed as a separate result.  It can eventually avoid case-specific target proofs for supported compiler profiles and can supply annotation machinery to the direct line.  Its success does not remove the need for artifact-only proofs when source, compiler evidence, or an accepted lowering profile is unavailable.

## Failure modes

| Failure | Consequence | Detection or response |
|---|---|---|
| Catalog and guidance growth | The model spends more time selecting among irrelevant facts | Measure context size and queries; select exact signatures and examples by region |
| A theorem has many abstract premises | Applying it costs more search than replaying the concrete proof | Test the complete application on two artifacts and simplify its interface |
| A tactic performs broad reduction | Lean checks become slow or fail without a useful goal | Bound the tactic to named regions and record per-command time |
| A runtime recognizer accepts a near match | The structural equality fails, wasting the attempt | Check equality before Codex starts and report the first differing instruction |
| Source hints describe optimized-away or reordered state | The proposed invariant does not match target locals | Treat mappings as candidates and validate them through target symbolic execution |
| A source theorem proves only a weak property | The artifact result remains unidentified | Require a functional source-to-model result or target summary before transporting the property |
| Proof modules are divided at weak interfaces | Later modules replay earlier instruction details | Strengthen summaries to include stores, frames, globals, and representation facts used by callers |
| Cached proof reuse lacks exact correspondence | A theorem about another region enters the candidate | Require checked region equality or function transport before reuse |
| Timing uses different artifacts or cache states | Apparent improvement reflects another workload | Freeze package, model, tool pins, and cache policy in the result record |
| A hint-assisted proof imports Source accidentally | The final result loses artifact-only independence | Keep import rejection and transitive closure audit as hard verifier gates |

Library generalization can also consume substantial development time without improving model behavior.  A candidate theorem should first replace a complete repeated semantic region, then receive a small catalog entry and focused example.  The existing two-consumer rule remains useful, with a temporary exception for a direct theorem about a stable emitted runtime template that demo-2 will exercise next.

## Success criteria

The primary result is a lower median stage-5 wall time for fixed reproofs of the exact demo-1 package.  The proof must still build `Behavior.artifact_behavior`, `Artifact.artifact_correct`, the embedded-byte comparison, and the declaration and axiom audits.  The published artifact-only package must verify without Source, compiler, source hints, generator state, or a prior Lake cache.

The work should also explain the reduction.  Telemetry should show whether the winning method reduced planning delay, Lean invocation count, cumulative Lean time, failed candidates, or several of those quantities.  A shorter proof without a measured reduction does not satisfy the optimization goal.

A result generalizes after it reduces proof-generation time on demo-2 or another structurally distinct array artifact.  Runtime and ABI abstractions should transfer directly, while the application invariant and mathematics may remain specific to each program.  Target certificates and source-derived capsules should require new annotations rather than new instruction-level proof architectures.
