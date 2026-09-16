# Full Lean Kernel Typechecker Implemented in LeanExe

Prepared and consolidated: 2026-09-16  
Status: executable milestones M0.0–M0.11 and M1.0 complete on 2026-09-16. P0/P1 now prove source-level sort and concrete universe operations for all UInt64 inputs. Graph/binding/checker and exact-WASM correctness remain unproved. The user clarified that this remains a PoC: defer larger source proofs and do no WASM proof work now. Work is committed and published on branch lean-kernel-checker after each increment.

Review decision: start with M0.0, a single executable sort-typing rule intended to fit a few hours with a working toolchain. Grow through M0.1, M0.2, and subsequent small checkpoints. M1 is an integration target, not the first implementation task. Every M0 checkpoint has a runnable WASM artifact and a precise, limited claim; real Lean export checking arrives at M0.11.

## Start here in a new session

This is the consolidated handoff for the whole planning conversation. It preserves the final objective, the feasibility assessment, the user's corrections, the small executable checkpoints, and the longer-term architecture and verification discussion. Earlier proposals are historical where the latest M0 sequence supersedes them.

- **Final product:** a full pinned-version Lean kernel typechecker implemented in leanexe's executable Lean subset and compiled to WASM.
- **Next task:** M1.1: extend the export adapter to let expressions, preserving annotations and checking an unused invalid value. M0.0–M0.11 and M1.0 are complete. P0/P1 source proofs are complete; larger source proofs are deferred, and WASM proofs are outside current work.
- **First closed proof:** M0.6, using caller-supplied encoded syntax.
- **First actual Lean export:** M0.11 complete: pinned lean4export output for implicationIdentity is accepted in WASM; a well-scoped corrupted body is rejected through the same path. No globals, universe parameters or axioms enter that package.
- **M1:** integration of the small checkpoints, not the first work unit.
- **M2–M5:** longer-term targets to subdivide before implementation; no full-project schedule has been established.
- **Current evidence:** each completed checkpoint has focused source checks, generated-WASM execution, and standard-Lean comparison; commands and counts are in the checker README and journal. Ten universal source theorems now cover sort typing and concrete max/imax, with an axiom audit. No overall checker soundness or exact-WASM theorem is claimed.
- **Current action scope:** the user authorized continued implementation, local Lean execution, and a commit and push after each increment on lean-kernel-checker. Preserve the existing roadmap and unrelated work.

Read sections 1–2 for the goal and claim boundaries, section 5.0 for exact M0 checkpoints, and section 8 for the first-session procedure. Sections 3–4 and 6–10 retain the design constraints, coverage requirements, trust discussion, and pinned evidence needed later; they are not all prerequisites for M0.0.

## 1. Mandate and background

The user examined [Tenet](https://github.com/keithadler/tenet), an independent Lean 4 kernel implementation in C#, and asked whether its core could be implemented in [leanexe](https://github.com/jsmorph/leanexe). The user then clarified the intended result:

> I want a typechecker for full lean but the typechecker is implemented in leanexe.

This clarification is authoritative. The deliverable is a full Lean kernel typechecker written in the executable Lean subset accepted by leanexe and compiled to standalone WebAssembly. A restricted object language is not the final product. Small fragments are implementation milestones only.

The implementation language and the language being checked are different layers. The checker can use monomorphic first-order functions, arrays, tagged records, explicit stacks, and machine integers while checking dependent functions, universe-polymorphic declarations, indexed inductives, quotients, and proof terms represented as syntax data. LeanExe does not need to execute those object-language features directly.

Here, full Lean means the kernel language of elaborated declarations for an explicitly pinned Lean 4 version. It does not initially mean implementing Lean's parser, elaborator, macro system, tactic engine, typeclass search, compiler, or editor services. Existing Lean tooling may produce the input terms; the new checker must make its own judgments about them.

Tenet is a reference implementation, compatibility oracle, and source of test ideas. A literal C# translation is not required. The intended architecture must fit leanexe's execution and verification model. If code or fixtures are copied, preserve applicable licenses and attribution, and describe implementation independence accurately.

### Discussion record and decision priority

| Discussion point | Consolidated decision |
|---|---|
| Could Tenet's core be implemented through leanexe? | No fundamental expressiveness barrier was identified in source inspection. A working port and full-scale performance remain unproven. |
| “I want a typechecker for full lean but the typechecker is implemented in leanexe.” | The object language is the complete pinned Lean kernel language. Restricting the implementation language must not silently restrict the eventual checking goal. |
| Request for a plan a new session can use | Preserve background, architecture, risks, source references, commands, exit gates, and the exact next task in this document. |
| Request for clean milestones and command-line artifacts that check something real | Every checkpoint delivers an executable rule check or kernel operation with concrete examples; later checkpoints check complete proofs and exported declarations. |
| “M1 is far too big. Need M0.1, M0.2, ... First M0.0 should be feasible in a few hours.” | M0.0 is one scalar rule; M0.1–M0.11 grow incrementally. M1 is an integration target. The earlier large first milestone no longer governs the next session. |
| “Commit there and push with each increment (starting with M0.0).” | Publish each tested/proved increment on lean-kernel-checker; preserve local commits and verify the fetched remote tree. |
| “You are proving correctness as you go, yes?” | Tests had not established formal correctness. Add useful small source proofs and make coverage explicit; later clarification permits deferring larger source proofs. |
| “Good, no WASM proofs now. It's also okay to defer some source-level proofs. We're still in PoC territory…” | Prioritize showing that LeanExe can execute the required checker operations. Keep P0/P1 proofs, defer larger source obligations, and resume M0.10/M0.11. No WASM proof work now. |
| Request to contain everything discussed so far | This document consolidates the whole discussion; a new session should not need to recover earlier chat messages. |

The user requirements above are firm. Names such as LeanExe.KernelCheck and leancheck-wasm, the .lxk file extension, the eventual byte protocol, storage representations, and exact later fixture selection are implementation proposals. Resolve them using the actual checkout and measurements. Do not let a provisional naming or architecture choice enlarge M0.0.

The few-hour target for M0.0 is a scope decision, conditional on working tools. It is not a claim that the artifact already exists, nor an estimate for every later checkpoint. Runnable intermediate artifacts are useful even while full kernel coverage is unfinished, provided their limitations are stated precisely.

### Feasibility review and corrections to the original sequencing

The project is technically plausible, with different confidence levels at different scales:

- High confidence in a small independently executing checker for the dependent-function fragment, subject to the incremental leanexe compilation checks. M0.0 establishes the scalar execution path; it does not require an explicit-machine framework.
- Moderate confidence in full pinned-version kernel coverage. The difficult work is conversion behavior, inductive validation/recursor synthesis, and fitting the implementation to leanexe's subset. This is substantial implementation work, not a mechanical port.
- Unproven practicality for full Mathlib throughput and memory usage. Array copying, term lifetimes, and the available WASM memory model require measurement and may justify focused leanexe improvements.
- Full checker soundness and exact-binary refinement remain separate substantial workstreams. The user expects correctness proofs as work progresses; source-level proof increments are now active, and tested executable milestones must not be called proved.

The original plan delayed the first proof check behind a complete primitive layer and a storage bake-off. A subsequent revision still made the first executable too large by requiring dependent functions, conversion, export ingestion, and packaging together. The user explicitly rejected that granularity and asked for M0.0 to be feasible in a few hours. Start with one typing rule, add one operation or syntax form at a time, and retain a replaceable representation. Optimize only after an executable provides a workload. Add arbitrary-precision literal reductions and Unicode-literal semantics when milestones first need them. Earlier releases must report those missing features as unsupported, never silently truncate or reinterpret them.

Full Lean remains the final goal. The earliest M0 checkpoints implement documented rules and syntax operations on caller-supplied scalars or graphs; they do not yet check exports. M0.6 checks a closed proof, M0.11 checks an actual exported proof, and subsequent releases expand the supported kernel fragment. These are progressively stronger claims, not different definitions of the final goal.

### Evidence used for this plan

The planning session inspected these repository revisions through GitHub:

| Repository | Revision |
|---|---|
| Tenet | 1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657 |
| leanexe | 2430ffcc3382d29db0b466b8ea595962b817e2d1 |

The assessment included Tenet's expression, universe, environment, typechecker, and inductive sources; leanexe's language specification, structural-recursion extractor, array emitter, IntMap example, artifact format, development guide, and repository instructions. Feasibility is an engineering judgment from this inspection, not a demonstrated working port or performance result.

At the inspected leanexe revision, both compiler and proof workspaces pin Lean 4.34.0-rc2, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d. Use the actual checkout's pins at implementation time; record deliberate changes. Start compatibility work against one exact kernel version rather than mixing behavior from several releases.

## 2. Goals and completion criteria

### Required executable product

1. All semantic checking runs in leanexe-generated WASM. No call to Lean's native kernel, C# Tenet, a host-side typechecker, or native reduction may decide acceptance.
2. Cover the complete supported-version kernel: universes, dependent functions, definitions and theorem bodies, reduction and conversion, inductive families, recursor derivation, quotients, literals, and declaration safety rules.
3. Check the complete dependency closure when claiming independent verification. Any explicitly trusted-import mode must report those assumptions and must not make the same claim.
4. Represent object-language naturals exactly using arbitrary-precision arithmetic within available memory. Machine-word overflow must never silently change an object-language value.
5. Validate input structure and references, reject malformed data, and never install a failed declaration into the accepted environment.
6. Report accepted, rejected, unsupported, and resource-exhausted outcomes distinctly. An unsupported feature is an unfinished compatibility item; exhaustion is inconclusive. Neither is evidence of an invalid theorem.
7. Produce a reproducible WASM artifact, an input-format specification, a runtime interface, diagnostics, a compatibility matrix, and recorded positive and negative test evidence.

Full coverage is version-specific. Resource bounds are unavoidable for any executable checker, but must not become silent semantic restrictions. Define workload targets using Init, selected dependent libraries, and eventually a full pinned Mathlib closure. Do not promise Tenet's throughput before measuring this implementation.

### Verification objectives

Keep three claims separate:

| Claim | Evidence required |
|---|---|
| The implementation behaves like the reference checkers on tested inputs | Differential tests, including deliberately invalid inputs |
| The checking algorithm is sound | A formal connection from successful checking to specified typing and declaration judgments |
| The distributed WASM executes that checking algorithm correctly | Exact-byte identity, decoding/validation evidence, and a behavioral/refinement theorem |

The user requested the executable full checker and subsequently asked whether correctness was being proved as work progressed. The implementation had reached M0.9 with tests only. P0/P1 now establish universal source properties for the sort and concrete universe primitives. Graph, binding, inference, conversion, and exact-artifact proofs remain outstanding and have explicit small proof checkpoints. A compiler-correctness assumption or successful test corpus does not establish either source soundness or binary refinement.

### Initially out of scope

- Source elaboration, tactic execution, macro expansion, and source-to-source compatibility.
- Direct .olean loading, multi-version readers, project discovery, and parallel checking.
- Reproducing Lean's error messages verbatim.
- Native-code evaluation as a trusted conversion rule.
- Claims of eliminating all bootstrap trust or proving Lean's consistency by self-checking.

These exclusions concern tooling and trust, not omission of kernel typing rules.

## 3. Architectural decisions and constraints

### 3.1 Pure checker with explicit state

Implement a pure first-order checker with explicit environments, local contexts, temporary terms, caches, work stacks, and resource accounting. Use data tags for continuations and operations instead of runtime closures or function-valued fields.

M0.0 and M0.1 use the existing scalar ABI. M0.2 introduces a small Array UInt64 graph format through the existing array ABI. For integrated export checking, a candidate public boundary is a checked byte protocol consumed by an import-free library entry, returning encoded results and diagnostics. If artifact-generation tools require Array UInt64 -> Array UInt64, provide a lossless adapter and verify its encoding. This later wire/ABI design is provisional and must not delay the first scalar artifact.

WASI, filesystem access, export production, and process orchestration can remain host adapters. Host code must not supply unchecked semantic verdicts, prevalidated recursors, trusted cache entries, or unchecked summaries that determine acceptance.

### 3.2 Syntax and identity

Represent names, universe levels, expressions, and declarations independently of Lean's runtime Expr/Environment objects. Use locally nameless syntax with de Bruijn indices for bound variables and explicitly fresh local identities, following the kernel semantics.

Consider compact node identifiers and shared expression DAGs. M0.2 may use simple flat storage; choose a large-library storage strategy after measuring actual checker workloads. An interned identifier is an implementation identity, not automatically evidence of definitional equality. Hashes are accelerators: collisions require full key comparison. Never accept equality solely because hashes match.

Track metadata such as loose-bound-variable range, free-variable occurrence, universe-parameter occurrence, and structural hashes where useful. Recompute or validate metadata at the input boundary. It must not be possible to bypass checking by supplying false metadata.

Object-language indexed types remain ordinary syntax nodes; leanexe's restriction on executable indexed inductives is not a restriction on what those nodes can describe.

### 3.3 Storage is the main scaling risk

Tenet uses append-only environments plus mutable dictionaries and sets for type inference, reduction, and equality caches. The inspected leanexe backend allocates and copies arrays for set and push operations. Its IntMap example demonstrates expressibility, not scalable constant-time mutation.

Repeatedly pushing into a flat term arena or updating a large array-backed hash table can produce quadratic copying. Reference counting alone does not remove that cost. Recursive temporary cleanup is also conservative in some current leanexe paths.

M0.0 and M0.1 use only scalar inputs and need no term store. From M0.2, use the simplest representation that can execute the tiny corpus, behind a narrow interface. Record allocation behavior when relevant, but do not require a final large-library storage choice before checking the first theorem. Before advancing to substantially larger closures, measure candidate representations with the operations the checker needs:

- Persistent tree/trie or carefully structured segmented storage using the current subset.
- A focused ownership-aware runtime/compiler improvement if measurements show that the existing representations cannot scale.

Segmenting storage is not automatically a solution: account for updates to the segment index and copying at every level. If introducing in-place updates, prove or enforce the ownership condition that preserves pure Lean alias semantics, and include meaningful alias-preservation regressions. Do not add unsafe mutation simply to obtain a fast prototype.

Separate persistent accepted declarations from per-declaration temporary expressions and caches. Specify cache lifetime and context keys. Do not reset linear memory while retained environment pointers still reference it.

### 3.4 Recursion and work budgets

Tenet's inference, weak-head normalization, conversion, and recursor reduction call one another on generated terms. General mutual nonstructural recursion is not guaranteed to fit leanexe's accepted source shapes.

Prefer an explicit evaluator/checker machine with tagged continuation frames and a fuel-controlled loop when the mutually recursive core needs it. M0.0 and M0.1 need no machine or stack at all. Introduce recursive helpers or explicit frames only at the checkpoint that requires them; do not build a generalized virtual machine first. Simple structural helpers may use the supported structural-recursion forms.

Account for work in every potentially unbounded path, including substitution, large-number operations, input parsing, and conversion retries. Make budget counters overflow-safe. A bounded call that runs out of fuel returns exhausted; it must not feed a false conversion result into a logically definitive rejection or populate a negative cache entry.

### 3.5 Numbers and text

LeanExe's bounded runtime Nat is suitable for validated indices, lengths, and budgets. It is not the representation of object-language Nat literals.

Implement nonnegative big integers using supported word arrays or another measured representation, with canonical zero and no redundant high limbs. Include the arithmetic and bit operations required by the pinned kernel's literal reductions. Use exact intermediate carry/borrow handling; test values across limb boundaries and well above 2^64.

Use bytes for names and string payloads. Implement the necessary UTF-8 validation and Unicode-scalar decoding explicitly. LeanExe's limited ASCII JSON parser is not a complete reader for arbitrary Lean export names or string literals. Define embedded NUL, escaping, invalid encoding, and canonicalization behavior. Match the pinned kernel's string-constructor expansion.

### 3.6 Input and provenance

Begin M0 with direct scalar and graph inputs. At M0.11, ingest lean4export declarations through the narrow documented adapter; later expand its supported forms and integrated byte format. Defer .olean parsing. Tenet reads dependency-ordered tables of names, levels, expressions, and declarations and regenerates inductive metadata rather than trusting it.

An external export converter may simplify the initial prototype, but its fidelity is a separate boundary: a checker can correctly verify the wrong statement if a reader drops a hypothesis. Preserve exact source/export identity, declaration names, theorem statements, axiom dependencies, and conversion provenance. Cross-check decoded declarations against an independent reader.

Validate table ordering, reference bounds, declaration uniqueness, constructor shapes, universe parameters, complete record consumption, and size limits. Reject cycles or forward references wherever the format prohibits them. If a format permits references requiring graph validation, validate them before traversal.

Treat an axiom as an explicitly reported assumption. Checking that an axiom has a well-formed type does not prove it. Make sorryAx and nonstandard axioms visible; a configurable axiom policy is distinct from kernel well-formedness.

## 4. Kernel coverage checklist

Maintain a versioned matrix linking every rule to its implementation, positive tests, negative tests, differential evidence, and proof status.

| Area | Required behavior |
|---|---|
| Universes | zero, successor, parameters, max, imax, normalization/equivalence, constraint checks, parameter substitution and validation |
| Expressions | variables, sorts, constants with level arguments, application, lambda, Pi, let, projection, literals, treatment of irrelevant metadata |
| Binding | capture-avoiding substitution, instantiation, abstraction/lifting where used, local declaration scope, fresh identifiers |
| Inference/checking | well-formed sorts and types, full validation of applications and binders, constant instantiation, projection legality, separate unchecked-inference optimizations where justified |
| Reduction | beta, zeta, delta, iota, projections, quotient rules, recursors, and native literal arithmetic implemented inside the checker |
| Conversion | proof irrelevance, function and structure eta, unit-like cases, universe equivalence, reducibility hints, literal expansion and kernel-specific conversion behavior |
| Declarations | axioms, definitions, theorems, opaque declarations, supported mutual blocks, duplicate checks, universe closure, free-variable closure, safety restrictions |
| Inductives | indexed families, mutual blocks, strict positivity, parameter uniformity, universe restrictions, elimination restrictions, nested inductives |
| Recursors | independently derive types, metadata and computation rules; validate supplied claims; handle required K-like and structure reductions |
| Quotients | validate prerequisites, derive quotient constants, validate their types and reduction behavior |
| Environment | dependency order, scoped staging, atomic commit/rollback, no leakage of rejected declarations |

Executable unsafe/partial declaration metadata must follow the pinned kernel's rules, including restrictions preventing unsafe terms from proving safe propositions. Distinguish the checked object's safety metadata from the implementation language: the checker itself must remain accepted safe, non-partial leanexe source.

Do not confuse mathematical definitional equality with the operational comparison algorithm. Reduction order, hints, limits, and cache behavior can affect compatibility. Begin with a conservative reference-compatible algorithm. Tenet's broader failure caching and faithful retry are optional optimizations to investigate later, not a shortcut for the first implementation.

## 5. Runnable milestones and exit gates

The immediate work sequence is M0.0 through M0.11 below. Each checkpoint produces a runnable WASM artifact that checks a stated rule or performs one specified kernel operation. It need not already check an entire proof. M1 is the integration acceptance target reached by these increments. M2 through M5 are longer-range objectives; subdivide them into similarly small checkpoints before implementation, rather than treating each as one task. Preserve earlier commands or supply a trivial compatibility wrapper when interfaces evolve.

Fragments restrict checking rules as well as syntax. A failed early conversion procedure is not automatically evidence that full Lean rejects the terms: missing eta or proof-irrelevance behavior can matter even on familiar syntax. Declare these completeness limits. Report unsupported/inconclusive when an unimplemented rule may be needed, and reserve definitive rejection for established errors. Every milestone must still include clear invalid examples that it can genuinely reject.

### 5.0 Immediate sequence: small executable M0 checkpoints

M0.0 is deliberately tiny. Target roughly two to four hours of implementation and focused checking on an already working leanexe checkout. This estimate excludes installing toolchains or repairing the execution environment. If basic compilation is blocked, record that blocker instead of silently expanding the milestone into toolchain work.

Each subsequent checkpoint should add one kernel capability or one boundary adapter, with a focused command and test set. They are not all promised to fit the same two-to-four-hour window. If one requires multiple new subsystems, split it further before starting. Initial storage can be naive; no cache framework, compiler optimization, or general exporter is a prerequisite. Following the later correctness discussion, pair implementation changes with their scoped proof obligations; the user permits deferring larger source proofs while the PoC establishes feasibility.

#### M0.0 — One rule: the type of a concrete sort

Deliver one scalar source function, compiled by leanexe, with the provisional signature:

~~~lean
checkSort (level claimedLevel : UInt64) : UInt64
~~~

The two inputs represent the judgment Sort level : Sort claimedLevel for concrete natural-number universe levels. The function returns:

- 0 when claimedLevel is exactly level + 1;
- 1 when the claimed level is wrong;
- 2 when level + 1 cannot be represented in this initial machine-word encoding.

Check the representation limit before addition. This bounded encoding is an explicit initial profile, not Lean's final universe semantics. Symbolic universe parameters, max/imax expressions, term graphs, contexts, and declarations are outside this checkpoint.

Proposed direct runtime commands, to become actual copy-pastable commands in the implementation receipt:

~~~sh
wasmtime run --invoke checkSort checker-m0-0.wasm 0 1
wasmtime run --invoke checkSort checker-m0-0.wasm 0 0
wasmtime run --invoke checkSort checker-m0-0.wasm 1 2
~~~

Expected returned words are 0, 1, and 0 respectively. They check Prop : Type, reject Prop : Prop, and check Type : Type 1. Wasmtime's process exit is separate from the function's returned word; do not claim that returning 1 automatically makes the shell command fail. The tiny regression driver must inspect the returned value and fail on a mismatch.

Scope is one Lean source module, its generated WASM, and a small existing-style test driver or command receipt. Reuse the current scalar compilation and Wasmtime invocation paths; no new launcher. Include several caller-supplied levels, both sides of the representation boundary, and a source-side check against the pinned Lean interpretation of sorts. Native Lean is used only during development, not by the resulting function.

**Done means:** generated WASM runs on caller-supplied scalar inputs, the three examples and boundary checks produce the expected words, and the artifact/commands are recorded. It is a real implementation of one kernel typing rule. It does not parse a theorem or check a proof, and should not be advertised as doing so.

#### M0.1 — Concrete universe operations

Add scalar checks for max and imax over concrete universe levels, especially imax u 0 = 0 and imax u (v + 1) = max u (v + 1). These support the eventual Pi formation rule and exercise Prop's impredicativity. Use expected-result inputs so the same simple scalar command path can test correct and incorrect claims. No symbolic normalization yet.

**Done means:** callers can check concrete max/imax claims in WASM, including zero-codomain cases, unequal levels, and wrong expected results. Keep M0.0 regression commands passing.

#### M0.2 — A tiny encoded term graph

Introduce a documented fixed-width Array UInt64 representation for Sort, bound variable, Pi, and lambda nodes, using validated node identifiers. Use the existing array ABI host support. Define roots, permitted tags, child-reference ordering, and field bounds. Validate structure and references only; validate lexical scope at the traversal checkpoint below.

**Done means:** a command accepts several externally supplied well-formed graphs and rejects an unknown tag, a missing child, and a prohibited cycle/forward reference. This is syntax validation, not type checking. Do not add JSON, NDJSON, .olean, names, or a new general CLI here.

#### M0.3 — Bound-variable scope and shifting

Implement binder-aware scope checking and shifting for the four admitted node forms. A binder applies to the body, not its domain; shifting must preserve variables bound inside the shifted term. Keep indices checked against overflow. If scope and shift together exceed one focused session, split into M0.3a and M0.3b.

**Done means:** runnable operations correctly handle variables immediately inside/outside scope, nested binders, shifts under binders, and malformed indices. Test expected output graphs, not only a success flag. These operations will be reused directly by typing.

#### M0.4 — Local contexts and variable typing

Add inference for Sort and bound variables in an explicitly represented local context. Implement context lookup with the required lifting when reading stored types. Begin with contexts that can be checked using the currently implemented forms, such as A : Sort 1 followed by x : A; arbitrary unchecked local-context entries are not accepted as established facts.

**Done means:** a command infers the correctly lifted type of x, validates admitted context entries in order, and rejects an out-of-scope lookup. Report the local assumptions; this is an open judgment, not a closed theorem.

#### M0.5 — Pi formation

Add dependent function type formation using the existing context operations and concrete imax calculation. Check both the domain and codomain as types. Target the type forall p : Prop, p -> p and a concrete-universe polymorphic identity type.

**Done means:** WASM determines the sort of those types and rejects a body/domain that is not a type. This verifies a proposition's formation, not a proof of it. Symbolic universes remain unsupported.

#### M0.6 — Lambda checking: the first closed proof

Add lambda inference/checking and structural type comparison for the admitted fragment. Target fun (p : Prop) (hp : p) => hp against forall p : Prop, p -> p. Input comes from the small graph format, supplied by the caller; no export parser is required yet.

**Done means:** a command checks that identity proof and rejects the same proof shape claimed to establish forall p q : Prop, p -> q by returning its p hypothesis. No trusted external declarations or axioms are needed. Do not reject a potentially convertible pair merely because general conversion is still missing; keep the supported fragment and inconclusive cases explicit.

#### M0.7 — Capture-avoiding substitution

Implement substitution/instantiation as a separately runnable operation over the admitted syntax. Use the existing shift operation; test substitution under nested binders, references to outer variables, unused variables, and index adjustment.

**Done means:** WASM returns the expected term graph for independently specified examples. Keep this milestone about substitution; do not also build a normalizer.

#### M0.8 — Application typing

Add the application node, validate it, and infer application types using Pi inspection and substitution. Initially require the function's inferred type to expose a Pi without reduction beyond the implemented subset.

**Done means:** check implication composition and dependent application on concrete-universe types, and reject an application with a demonstrably incompatible argument type. Cases needing unimplemented conversion return unsupported/inconclusive.

#### M0.9 — Beta reduction and a bounded conversion check

Add a capture-avoiding beta step, then the smallest fuel-bounded reduction/comparison loop needed for a case where a type-level identity application reduces to the expected type. Reuse substitution. If the loop and the beta step do not fit one focused checkpoint, split them into M0.9a and M0.9b.

**Done means:** a command accepts a typing example that structural comparison alone could not establish, rejects a clear nonconvertible case in the supported fragment, and reports exhaustion separately. Full Lean conversion, caches, eta, and proof irrelevance are not claimed yet.

#### M0.10 — Let expressions

Add a let node, validate its declared type and value, and implement its substitution/reduction behavior. Reuse existing checking and substitution operations; do not add an environment of global definitions here.

**Done means:** check one valid let-containing term and reject a let with an incorrect value type, including an unused let binding. This prevents checking only the eventual result while ignoring invalid subterms.

#### M0.11 — Read one actual Lean proof export

Freeze an actual pinned-Lean export of implicationIdentity from a minimal prelude module with its complete dependency closure. Add a narrow host-side adapter from the documented export representation to the already working graph input. Reject unhandled forms explicitly; no silent omission or host typechecking. Preserve the original export and test exact decoded structure.

Check the requested type and body in WASM. In this first package, require a closed single theorem with no referenced global declarations, universe parameters, or axiom assumptions; verify that restriction from the decoded content. If the exporter supplies extra dependencies, inspect them and refine the fixture instead of trusting them.

**Done means:** the executable accepts the actual exported Lean proof and rejects a well-formed corrupted export via the same path. It runs without Lean or Tenet after preparation. Adapter fidelity is explicitly documented as an operational boundary. If setting up an exporter and writing the adapter are separate substantial tasks, split this checkpoint; do not rebuild the exporter ecosystem as an incidental task.

### 5.0.1 What follows M0

The completed M0 PoC reaches actual export checking. Use these small next steps:

- **M1.0 — application exports (complete):** extend only the host adapter for `app` records;
  export implication composition from minimal Lean, preserve raw/decoded data,
  and accept it plus reject a scoped wrong-argument corruption in the existing
  WASM checker. No new kernel rule or symbolic-universe work is required.
- **M1.1 — let exports:** map `letE` records losslessly to the existing value/binder
  representation. Verify the raw fixture actually contains a let; accept it and
  reject a malformed or wrong-valued unused let through the same path.
- **M1.2 — symbolic-level syntax:** add a checked level table and references for
  zero, successor, parameter, max and imax. Deliver a syntax-validation artifact;
  do not also implement general universe comparison in this increment.
- **M1.3 — level parameter substitution:** implement separately runnable,
  capture-free parameter instantiation with concrete expected outputs. Keep
  symbolic comparison and global declaration admission as subsequent increments.

Subdivide symbolic comparison (including imax's zero cases) and global-environment
admission after inspecting those workloads. The larger M1 exit gate below remains
an integration target, not one implementation task. Keep cheap useful source
proofs; defer larger source obligations explicitly and do no WASM proof work now.


M1 integrates these small capabilities and adds symbolic universes, a minimal validated global declaration environment, and the fuller proof corpus described below. Break those additions into similarly scoped checkpoints when M0.11 is reached. M1 is not one few-hour task.

For each M0 checkpoint retain only the source, runnable WASM, exact command, tiny input/expected-output set, and a short scope note. Full release packaging, axiom reporting, memory benchmarks, and export provenance are required when applicable; they are not imposed on the scalar M0.0 function. Do not let a growing checklist prevent delivery of the next small executable.

### 5.1 Command-line contract and release bundle

For the integrated M1 release, use a provisional command name, leancheck-wasm. The following commands describe intended deliverables; none exists yet. M0 checkpoints use existing direct scalar/array invocation paths and do not wait for this launcher:

~~~sh
leancheck-wasm check fixtures/m1/logic.lxk
leancheck-wasm check fixtures/m1/logic-bad-body.lxk
leancheck-wasm show fixtures/m1/logic.lxk implicationIdentity
leancheck-wasm check fixtures/m1/logic.lxk --json
~~~

The .lxk suffix denotes a proposed versioned byte representation of Lean declarations. It is not an existing format. For an initial compact reader, provide an explicit preparation command:

~~~sh
leancheck-wasm pack exports/logic.ndjson --out fixtures/m1/logic.lxk
~~~

Packing may use host-side code to translate lean4export's syntax. It may not infer types, normalize terms, erase proof bodies, invent hypotheses, or preapprove declarations. Preserve the original NDJSON, validate the packed graph inside WASM, and record source/export identities. A converter's fidelity remains an operational assumption until independently established. Represent unsupported constructs faithfully or return an explicit unsupported result.

The final check command must run without Lean, Lake, .NET, Tenet, or a network connection. Producing a new export and rebuilding the checker may require development tools. Distinguish those preparation dependencies from runtime dependencies in the README.

At M1 packaging time, prefer an import-free library WASM plus a minimal Wasmtime C launcher using the existing repository host conventions. The launcher reads bytes, transfers them to WASM memory, invokes the checker, prints the WASM-produced result, and maps statuses to process exits. It must not make semantic judgments. This gives a normal executable command while keeping the checker itself wholly inside leanexe-generated WASM.

A small WASI stdin wrapper is optional. The inspected leanexe stdin adapter limits input to its initial 16-page memory, so it is not a ready-made transport for large exports. Do not promise that piping Mathlib into it will work. Likewise, the current exact-artifact profile excludes imports: retaining an import-free checker makes that proof path cleaner, while host I/O remains outside the checker theorem.

Every integrated release from M1 onward must contain:

- checker.wasm and the command-line launcher, with platform/runtime requirements and digests;
- source version, build instructions, tool pins, and a documented input schema;
- at least one original Lean source module, its frozen actual export, and its complete selected dependency closure;
- valid inputs, at least one well-formed but ill-typed input, and malformed/unsupported/exhaustion examples;
- a checkable expected-results manifest and a one-command regression runner;
- a support matrix, axiom report, known limits, and a measured runtime/memory receipt.

Proposed launcher statuses are 0 accepted under the reported axiom policy, 1 rejected proof/declaration, 2 malformed input, 3 unsupported feature, 4 exhausted resources, 5 host/internal failure, and 6 axiom-policy violation. These are checker CLI statuses, separate from leanexe's compiler exit codes. Traps and crashes never count as logical rejection. An unexpected trap must not be labeled exhausted unless the host has reliable evidence of the resource failure.

For check, print the requested theorem identity and statement (or an unambiguous canonical representation), declarations checked, imported declarations trusted, axiom dependencies, support profile, and status. The standard independent mode requires trusted imports = 0; explicitly allowed axioms remain separately reported. Pretty-printing can improve later.

### M1 — Check actual dependent-function proofs

**User-visible result:** run a WASM checker on a small module of ordinary Lean proofs and distinguish valid terms from incorrect proofs.

Prepare a minimal module using Lean's prelude directive if needed to avoid automatic library imports. Write direct proof terms instead of tactics so the dependency closure is small and inspectable. Candidate source examples, to elaborate and freeze during implementation, include:

~~~lean
prelude
universe u

theorem implicationIdentity : ∀ p : Prop, p → p :=
  fun p hp => hp

theorem implicationCompose :
    ∀ p q r : Prop, (p → q) → (q → r) → p → r :=
  fun p q r f g hp => g (f hp)

def polymorphicIdentity (A : Sort u) (x : A) : A := x

theorem dependentApply :
    ∀ (A : Sort u) (P : A → Prop), (∀ x, P x) → ∀ x, P x :=
  fun A P h x => h x
~~~

These examples are proposed fixtures, not statements that this session compiled them. Add a small definition/unfolding example that forces beta, let, and delta conversion; merely accepting syntactically identical types is insufficient. Export only the selected declarations and all their actual dependencies. If unexpected generated dependencies appear, inspect them rather than trusting or discarding them.

Implement the required universe rules, dependent Pi/lambda/application checking, constants and declaration scope, substitution, and limited reference-compatible conversion. Validate both types and bodies, including unused binders and subterms. Axioms in the positive M1 corpus should be absent; reject hidden assumptions under its empty axiom policy.

Create a well-formed negative export for the claimed type forall p q : Prop, p -> q using a body that returns the supplied proof of p. The parser should accept its syntax and the checker should reject the type mismatch. Corrupt a bound index and a universe argument separately. Confirm these are rejected by the pinned native kernel as well; native Lean is a development oracle, not a runtime dependency.

**Exit gate:** the same distributed command accepts the real positive export, rejects a semantically false proof, reports unsupported terms distinctly, and returns exhausted on a deliberately insufficient budget. It checks all dependencies and runs in a clean runtime-only environment. Parser success or hand-built internal terms alone do not complete M1.

**Feasibility:** an integration target after M0, not a single short implementation task. No object-language numeric literals, Unicode string reductions, arbitrary tactics, or full inductive machinery are necessary. Source names can deliberately be ASCII for this corpus. No requirement to finish a general big-number library or optimal cache implementation first.

### M2 — Check induction and equality proofs

**User-visible result:** check proofs of arithmetic and simple data-structure laws with their inductive foundations independently validated.

Start with a minimal actual Lean source module defining its own natural-number type, identity/equality family, and addition. Prove laws such as addition by zero and associativity using explicit recursors or ordinary structural proofs. After that works, freeze at least one selected theorem from the pinned Lean library, such as a suitable Nat addition theorem, together with its real dependency closure. Confirm the exact theorem and closure before making it a release gate.

Implement single inductive families, including the indexed identity family needed for equality, their positivity/universe/elimination checks, and recursor derivation and reduction. Equality must not be a host-provided trusted primitive. Derive the recursor from the checked declaration and compare exported metadata. A temporary version that assumes the recursor is useful for debugging but does not meet this milestone.

This is the first substantial difficulty increase. Split internal tasks into constructors and computation, indexed equality, induction, and arithmetic proofs, but retain one release claim: independent checking of the complete arithmetic proof package.

Introduce exact literal arithmetic when the selected library closure requires it. Pure constructor-encoded naturals can support the initial source-defined examples without implementing every arithmetic fast path. Never map unbounded checked values to wrapping machine words.

Negative cases must include a changed proof body, a wrong recursor computation rule, a non-positive declaration, and a disallowed elimination. Construct invalid declarations by mutating exports because Lean's frontend will correctly refuse to generate them.

**Exit gate:** the command checks a genuine induction proof, checks the types and constructors it depends on, derives the recursor, and rejects corrupted foundational declarations. Include a selected pinned-library proof once its complete closure is supported.

### M3 — Full pinned-version kernel and Lean's core library

**User-visible result:** check the complete pinned Init dependency closure, plus focused examples exercising every remaining kernel rule.

Complete mutual and nested inductives, structures/projections, quotient initialization and reduction, conversion/eta/proof-irrelevance edge cases, opaque/theorem/safety behavior, arbitrary-precision literal operations, and Unicode strings. Keep a versioned rule matrix; a green Init run alone does not prove coverage of rarely exercised rules.

Add nontrivial data examples, such as tree traversal properties and indexed-container proofs, when those features are introduced. Each addition should have a runnable exported proof package, rather than waiting for the aggregate Init run to supply all feedback.

Choose and measure scalable storage before accepting large closure workloads. Record term count, allocation and memory growth, cache behavior, work limits, and time. Failures of a large export should be minimized into focused fixtures.

**Exit gate:** complete implemented rule matrix for the pinned kernel version; a full recorded Init run with no unaccounted skips, trusted declarations, unsupported features, or exhausted checks; and positive/negative tests for features absent from that corpus. Audit axioms and native certificates explicitly. If an input closure needs a native assumption, name it and resolve the policy rather than silently accepting it under an ordinary-proof claim.

**Feasibility:** substantial kernel engineering. Full coverage remains plausible, but neither support nor speed is established by M1 or M2.

### M4 — Independently recheck a useful leanexe proof package

**User-visible result:** use the new command to check the proof behind an existing exact-WASM artifact, with the actual theorem dependency closure.

Select a small existing leanexe artifact package after inspecting its theorem dependencies and native certificate usage. Prefer a scalar or small array example before numerical solvers. Export its artifact-identity and behavioral theorems and their dependencies, replacing native computation certificates with kernel-checkable ones where required.

The command should identify the exact theorem statements, checked closure, permitted axioms, and artifact bytes or digest named by the theorem/package. Checking an exported theorem does not by itself compare a user's external binary to those bytes: retain an explicit byte-identity check for that external file and state the boundary.

This does not require a proof of the new checker first. It produces useful independent implementation evidence about the existing artifact proof, subject to the new checker being correct. It is not an independent proof of the checker's own soundness.

**Exit gate:** an ordinary command-line run rechecks a real artifact proof package without delegating kernel judgments or hiding native certificates. Record actual closure size and resource costs. A chosen small theorem may still import a large Mathlib subset; inspect before promising this milestone is cheaper than M5. M4 and M5 may be reordered if measured dependencies favor that.

### M5 — Full-library scale and reproducible distribution

**User-visible result:** check a complete pinned Mathlib closure and selected external projects using the same executable interface.

Add large-export handling, measured memory management, and targeted optimizations while preserving all earlier gates. Whole-input checking may be adequate initially; introduce a session/streaming protocol only when justified. Stateful sessions must retain validated environments inside WASM; never accept a host-reconstructed environment as already checked or reset storage beneath live terms.

Profile before adding parallelism or direct .olean readers. Preserve the exact imported versions of each tested project. Rechecking a different Mathlib checkout is not evidence about a project's dependency closure.

**Exit gate:** a complete reproducible run with explicit zero-skip coverage, no unexplained oracle disagreements, declared axioms and resource limits, and a runtime-only release bundle. Publish measured performance without borrowing Tenet's .NET timings as forecasts.

**Feasibility:** scaling is the largest unresolved implementation risk. This milestone may need focused leanexe runtime/compiler improvements; the earlier artifacts remain useful if that takes longer.

### Active proof track — Source refinement and exact artifacts

This track now starts immediately, rather than waiting for M1. The user asked
whether correctness was being proved as implementation progressed. The earlier
milestones had only tests and source/WASM comparisons. The detailed
[proof ledger](../LeanExe/KernelCheck/PROOFS.md) records the corrected status,
precise obligations, and small proof increments.

- **P0/P1 complete:** ten universal source theorems for sort acceptance,
  rejection and overflow, and concrete max/imax operations and claim checks.
  The specifications use unbounded natural numbers. Run `node test/kernel_proofs.js`;
  its transitive axiom audit permits only propext, Classical.choice and Quot.sound.
- **Deferred P2a:** node-address safety and validator entry checks under explicit ABI
  representation bounds. **P2b:** full graph-to-syntax refinement.
- **P3/P4:** scope, shifting and substitution invariants and their connection to
  the actual graph operations; split model laws and implementation refinement.
- **P5/P6:** admitted-context and inference-machine invariants, then acceptance
  implies declarative typing for the implemented fragment.
- **P7:** reducer correctness, typing preservation, and conversion-success soundness.
- **Exact-WASM proofs:** explicitly deferred outside current work by the user.

A separate model theorem or one successful fixture does not establish checker
soundness. A source theorem does not establish a WASM theorem. Keep both proof
coverage and missing cases visible, and keep executable regression evidence as
an additional gate. M0.10, M0.11 and M1.0 are complete; M1.1 is the next PoC increment. Larger source proofs may
be deferred explicitly; no WASM proofs are being attempted now. Self-checking cannot remove the logical bootstrap by assertion.

## 6. Native certificates and bootstrap trust

The inspected leanexe artifact generator defaults to native_decide, and its audit permits Lean.ofReduceBool and generated decision-certificate families. Tenet refuses Lean.reduceBool/Lean.reduceNat reductions because they depend on running compiled code.

For independently checking this project's own proofs, prefer kernel-checkable certificates. LeanExe already documents an artifact migration --kernel mode using decide +kernel. Inspect the actual theorem dependency closure; changing one generator flag is not proof that every dependency is free of native assumptions.

If a certificate appears as an axiom, report it as an assumption rather than treating it as a checked proof. Refuse native-reduction shortcuts unless their results are supplied with independently checkable proof evidence. This policy must not be described as arbitrary rejection of ordinary Lean proof terms: it identifies an extra trust mechanism outside independent kernel computation.

Writing and proving the checker in Lean still uses a Lean proof-checking bootstrap. Executing a separately implemented checker in WASM provides useful implementation diversity, but does not make that bootstrap logically disappear. Likewise, translating Tenet's algorithm preserves many of its design assumptions even if the implementation and runtime differ.

## 7. Validation discipline

Tests must distinguish parser validity, kernel acceptance, axiom policy, supported features, and resource limits. Report each category explicitly.

Required suites as the corresponding capabilities are implemented (not prerequisites for M0.0):

1. Primitive and representation tests: limb arithmetic, UTF-8, variable indices, substitution, level normalization, hash collisions, and malformed graph references.
2. Rule-focused tests: a valid and an invalid example for every matrix entry, including dependent and universe-sensitive cases.
3. Differential tests: the same declarations under the new checker, the pinned native Lean kernel, and a compatible pinned Tenet. Keep oracle configuration, imported assumptions, and budgets in the report.
4. Mutation and attack tests: false proofs, positivity violations, recursor tampering, duplicate/scope mistakes, and malformed cached metadata.
5. Runtime regressions: deterministic output, aliases preserved across updates, memory ownership, rollback after failures, and exhaustion at several budgets.
6. Corpus gates: complete declared dependency closures with explicit coverage accounting and reproducible inputs.

Do not trust future declarations after an earlier dependency has failed. A diagnostic mode that continues with unchecked declarations must be clearly separate from a successful verification run. Compare cache-enabled and conservative modes where optimizations could change outcomes. Treat any false acceptance as a correctness blocker.

For a full checker, differential agreement is compatibility evidence, not a proof of soundness. Tests on only well-typed declarations are especially insufficient.

## 8. M0.0 implementation-session procedure (completed)

The first implementation session completed M0.0 using this procedure. The next checkpoint is M0.1. Do not start a parser, expression representation, proof exporter, or general evaluator before shipping this checkpoint.

1. Read the current repository instructions, inspect working-tree changes, and verify the pinned compiler/runtime paths. Preserve existing work.
2. Integrate a focused subplan without replacing the active root roadmap. Record that the next acceptance target is M0.0.
3. Find the existing scalar Lean-to-WASM example and its test/runtime invocation. Reuse that path; do not design a launcher.
4. Add a small module containing checkSort with the semantics specified in M0.0, including the overflow guard and explicit numeric result codes.
5. Compile it through tools/leanrun using the repository's permitted execution mode. Run it with caller-supplied scalar inputs using Wasmtime.
6. Check the three documented examples, a few other levels, and the representation boundary. Compare against the pinned Lean interpretation of sorts during development.
7. Save checker-m0-0.wasm or the repository-conventional generated artifact, the exact build/run commands, and a short receipt identifying source revision, result meanings, limitations, and checks performed.
8. Update the checkpoint status. M0.1 is next; do not automatically expand M0.0 to include it.

The scope is deliberately compatible with a few hours of work once tools are available. If execution setup consumes that window, record the blocker and preserve the small implementation scope. A successful M0.0 checks one typing rule, not a theorem; say that plainly.

### End-of-checkpoint handoff

After each implemented checkpoint, record these facts in the project subplan or existing development journal:

- checkpoint completed or still open, exact scope, and any split into smaller tasks;
- source revision/files and generated WASM path, plus a digest when recording a distributable artifact;
- exact build and run commands, required runtime, input values/files, expected results, and observed results;
- what the result establishes: one rule, syntax validity, an open judgment, a closed proof, or an exported dependency closure;
- remaining unsupported features, explicit assumptions, resource failures, and the next small task.

For M0.0 this is a short receipt, not a new reporting framework. A returned status word is not a shell exit code; an execution trap is not a rejected proof; a source-only successful check is not a WASM run. M0.0 commands confirmed by section 12 are runnable; later checkpoint commands remain proposals until their own implementation receipts confirm them.

### Execution rules carried forward from the inspected repository

- Run every Lean/Lake/compiler invocation through tools/leanrun, with a reasonable timeout. Do not run Lean processes concurrently or bypass its shared lock.
- Standard Linux mode enforces the repository's CPU, memory, swap, and scheduling limits. Read the current instructions for exact values and platform handling.
- LEANRUN_LOCAL=1 requires explicit authorization for local execution without the standard cgroup controls. The user explicitly authorized direct/local Lean execution in this session on 2026-09-16. Use the existing runner in LEANRUN_LOCAL=1 mode to retain serialization, timeouts, and priority controls; no runner bypass is needed.
- Repository drivers that invoke the runner should be invoked as documented, without wrapping them in another runner and deadlocking the shared lock.
- After a timeout, diagnose or divide the target before repeating it unchanged.
- Follow current focused and aggregate test gates for the code actually changed. Keep compiler/runtime changes isolated enough to review and test independently.
- Preserve unrelated work, established artifacts, and the active project's existing verification evidence.

## 9. Open decisions and risks

| Decision/risk | Starting position | Evidence needed |
|---|---|---|
| Project location | Integrate under leanexe with a focused subplan; final namespace provisional | Current checkout conventions and accepted extraction boundary |
| Object kernel version | Start with leanexe's exact pinned Lean version | Versioned rule inventory and oracle compatibility |
| Storage | No heap design for M0.0/M0.1; simple graph storage from M0.2 | Actual checker workloads before large-closure redesign |
| Input encoding | Scalars first, graphs from M0.2, export adapter at M0.11 | Exact graph schema, adapter fidelity, eventual Unicode/big-number handling |
| Machine organization | Ordinary scalar functions first; add recursion/continuations only as needed | Compile each new control-flow shape at its owning M0 checkpoint |
| Full-library memory | Per-declaration temporary lifetimes and sharing | Measured Init/Mathlib growth; avoid assuming .NET memory figures transfer to WASM |
| Formal specification | Independent declarative judgments; investigate reusable theory work before committing | Compatibility, proof scope, dependency and license review |
| Direct .olean support | Defer | Stable checked input path and a clear reason to add reader complexity |
| Native assumptions | Explicit audit and kernel-checkable certificates | Complete theorem dependency inspection |

The M0.0 two-to-four-hour target is conditional on a working checkout and runtime, not a measured estimate. No full-project calendar estimate is justified yet. Full-kernel compatibility and a soundness proof are substantial separate efforts. M0 should build the executable path one small operation at a time; M1 integrates it. Use its measurements and subsequent inductive implementation to refine effort estimates before committing to full-library throughput or formal-proof schedules.

## 10. Source references

These links pin the inspected source state. Recheck current files when implementing.

### Tenet

- [Design and trust boundary](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/docs/design.md)
- [Expressions and literals](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/src/Tenet.Kernel/Expr.cs)
- [Universe levels](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/src/Tenet.Kernel/Level.cs)
- [Type checking, conversion, caches, and native-reduction policy](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/src/Tenet.Kernel/TypeChecker.cs)
- [Inductives and recursors](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/src/Tenet.Kernel/Inductive.cs)
- [Environment and transactional declaration checking](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/src/Tenet.Kernel/Environment.cs)
- [Export format](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/docs/format.md)
- [Testing and differential campaigns](https://github.com/keithadler/tenet/blob/1ff7bd6fb1df9d6b5bbce5159cbc8425792c0657/docs/testing.md)

### LeanExe

- [Language, recursion, numeric, ABI, and ownership specification](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/docs/spec.md)
- [Array allocation and copy emission](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/LeanExe/Wasm/Binary.lean)
- [Structural-recursion extraction](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/LeanExe/Extract/StructuralRec.lean)
- [Executable map example](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/LeanExe/Examples/IntMap.lean)
- [Exact-artifact verification and certificate modes](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/docs/artifact-format.md)
- [Verification workflow](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/docs/verifying.md)
- [Existing compiled byte-processing precedent: self-hosted emitter](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/docs/self-hosted-emitter.md)
- [Repository instructions](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/AGENTS.md)
- [Development guide](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/DEVELOPING.md)
- [Existing active roadmap; preserve when integrating](https://github.com/jsmorph/leanexe/blob/2430ffcc3382d29db0b466b8ea595962b817e2d1/plan.md)

## 11. Handoff checkpoint

- [x] Clarified that the object language is the full Lean kernel language.
- [x] Inspected both repositories and identified the main implementation constraints.
- [x] Recorded background, scope, architecture, checkpoints, gates, trust boundaries, and source references.
- [x] Consolidated all discussion and removed obsolete first-milestone prerequisites.
- [x] Integrate a scoped subplan into the actual leanexe checkout.
- [x] Reviewed feasibility and replaced horizontal implementation phases with runnable release milestones.
- [x] Incorporated the user's correction: M1 was too large; start with small M0 checkpoints.
- [x] M0.0: scalar concrete-sort typing rule and runnable WASM; source checks and 32 runtime judgments pass.
- [x] M0.1: concrete max/imax checks; 98 WASM/standard-Lean comparisons pass.
- [x] M0.2: validated encoded syntax; 17 WASM/standard-Lean cases pass.
- [x] M0.3: bound-variable scope and shifting; 13 scope and 12 exact-output cases pass.
- [x] M0.4: local contexts and variable inference; 14 exact-output cases pass.
- [x] M0.5: Pi formation; 10 WASM/standard-Lean cases and Lean universe judgments pass.
- [x] M0.6: lambda checking and the first closed proof; 12 WASM/standard-Lean judgments pass.
- [x] M0.7: substitution; 12 exact WASM/standard-Lean output cases pass.
- [x] M0.8: application typing; 7 WASM/standard-Lean cases pass.
- [x] M0.9: beta reduction and bounded conversion; 5 conversion and 4 reduction cases pass.
- [x] M0.10: let checking and reduction; 8 WASM/standard-Lean cases pass.
- [x] M0.11: actual Lean proof export through the checker; raw export reproduction, exact graph, corrupt proof, exhaustion and 14 adapter failure cases pass.
- [x] M1.0: actual composition export with two applications; raw reproduction, exact graph, scoped wrong-argument rejection, exhaustion and 19 adapter failure cases pass.
- [ ] M1: command-line checking of actual dependent-function proofs and meaningful corruptions.
- [ ] M2: independently checked induction/equality and arithmetic proofs.
- [ ] M3: complete pinned-version kernel and Init closure.
- [ ] M4: recheck a useful existing leanexe artifact proof package.
- [ ] M5: complete pinned Mathlib closure with measured resource use.
- [x] P0/P1: universal source proofs for sort typing and concrete max/imax; ten public theorems pass the axiom audit.
- [ ] P2a/P2b: address safety and full graph validation refinement.
- [ ] P3–P7: binding, substitution, inference and conversion correctness.
- [ ] Deferred beyond current PoC: exact-WASM verification, separate from source soundness.

Implementation began on 2026-09-16 on branch kernel-checker-m0-0. Source and focused tests are present in the working tree; see the execution receipt below for actual validation status. No M0 checkpoint is complete until its runtime gate passes.

## 12. Implementation receipt — 2026-09-16

M0.0 is complete. Base revision: d6511c65255aece97afa08dbfd994fb088f4ff6f.
Local branch: kernel-checker-m0-0.

### Source and artifact

- LeanExe/KernelCheck/Sort.lean: scalar checkSort, with overflow rejected before addition.
- LeanExe/KernelCheck/SortTest.lean: three actual Lean sort judgments and eleven focused source-function guards.
- test/kernel_sort.js: builds the source/compiler, emits WASM, and checks 32 caller-supplied input pairs against mathematical BigInt succession and standard Lean evaluation.
- LeanExe/KernelCheck/README.md: supported scope, result words, build and runtime commands.
- Generated artifact: .lake/build/kernel-check/checker-m0-0.wasm.
- Downloadable copy: build/kernel-check/checker-m0-0.wasm.
- Size: 1,116 bytes.
- SHA-256: 1ce9499a8f44633db3bd540d8b96e6d3ab389345cb99c5f745fc696154cff19b.

### Runtime evidence

The source module and tests built successfully under Lean 4.34.0-rc2, commit
6a10ac8c22beadecabdbb0919c2b50214762f91d. The focused driver passed all 32
WASM sort judgments and standard-Lean comparisons under Wasmtime 44.0.0 and
Node.js 24.13.0. Direct calls
returned 0 for (0,1), 1 for (0,0), 0 for (1,2), and 2 for (-1,0), where -1
encodes UInt64 maximum. The maintained Markdown gate passed, and git diff
whitespace validation passed. No aggregate compiler regression or formal
artifact proof is claimed for this isolated new entry.

### Session-local setup

The user explicitly authorized direct/local Lean execution. Standard systemd
scope creation failed with "Failed to connect to bus: No medium found".
The unchanged tools/leanrun runs with LEANRUN_LOCAL=1, preserving the lock,
priority controls, one Lean thread, and command timeouts. Cgroup CPU/memory/
swap limits are unavailable in this mode.

The toolchain is installed in build/tools/lean/lean-4.34.0-rc2-linux. The
official archive SHA-256 is
3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8.
An incomplete first download was resumed and verified before extraction.
Wasmtime archives were verified by the existing downloader; extraction used
TAR_OPTIONS=--no-same-owner for this container. Node.js 24.13.0 was verified
against its official SHASUMS256.txt because the preinstalled 24.19.0 failed
the repository's exact version check.

This container lacks both /proc/self/exe and /proc/<pid>/exe. The local,
ignored build/tools/work-mode/executable-path.c preload resolves only the
current process's executable link using AT_EXECFN and realpath; it preserves
other readlink calls. Explicit toolchain library paths repair shared-library
discovery. LEAN_SYSROOT selects the pinned toolchain. This environment shim
is not a source or runtime dependency of the WASM artifact.

The ignored build/tools/work-mode/env.sh records the current session paths.
Use it only in this authorized environment; do not copy its absolute paths
into portable repository configuration.

### Exact commands used

From this checkout, source build/tools/work-mode/env.sh for Lean-family work.
Then the following commands passed:

~~~sh
tools/leanrun --timeout 30s lean --version
tools/leanrun --timeout 120s lake build LeanExe.KernelCheck.SortTest
node test/kernel_sort.js
~~~

The focused test routes Lean/Lake/compiler children through tools/leanrun
itself, so do not wrap it in a second runner. It applies a 900-second cold
build timeout and 90-second compilation timeout. No Lean processes were
launched concurrently by separate orchestration calls.

Runtime-only invocation needs no Lean setup or preload:

~~~sh
build/tools/wasmtime/current/wasmtime run --invoke checkSort build/kernel-check/checker-m0-0.wasm 0 1
build/tools/wasmtime/current/wasmtime run --invoke checkSort build/kernel-check/checker-m0-0.wasm 0 0
build/tools/wasmtime/current/wasmtime run --invoke checkSort build/kernel-check/checker-m0-0.wasm 1 2
build/tools/wasmtime/current/wasmtime run --invoke checkSort build/kernel-check/checker-m0-0.wasm -1 0
~~~

Next: M0.1 only. M0.0 establishes executable concrete sort typing; it does
not check general Lean terms, declarations, proofs, or symbolic universes.


## 13. Current PoC receipt: M0.1–M0.11, M1.0 and P0/P1

All M0 increments are implemented and published on lean-kernel-checker. The
[checkpoint README](../LeanExe/KernelCheck/README.md) retains each command and
scope; the journal records failed approaches and gate results. The complete
focused command is `node test/kernel_all.js`.

M0.11 uses lean4export revision 483e011449cce37c3f8ad5e2aae434cbb1d2e53c,
matching Lean 4.34.0-rc2 / 6a10ac8c22beadecabdbb0919c2b50214762f91d. The minimal
prelude theorem's raw export has 17 records and zero constant references,
universe parameters, axioms, or other declarations. Fresh export bytes match
the frozen fixture exactly. The adapter's decoded graph is checked against a
separate exact fixture. A scoped corruption returns rejection (1); fuel 1
returns exhaustion (5); 14 unsupported/malformed adapter variants fail closed.

The generated import-free artifact is 2,429,809 bytes, SHA-256
`aa1353e70bdbf4a101efe57beb1220ca603820d19c0c7a767638a0bc1645350d`.
Actual accepted/rejected runtime commands also passed with Lean environment
variables and the Lean preload removed. This environment needs the Wasmtime
C API directory in LD_LIBRARY_PATH because its dynamic loader cannot resolve
its usual executable-relative path; that session setup is not a Lean runtime
dependency. Runtime commands and export reproduction instructions are in the
[fixture receipt](../test/fixtures/kernel-check/README.md).

P0/P1 add ten kernel-checked source theorems for all scalar sort/universe inputs.
The axiom audit permits only propext, Classical.choice and Quot.sound. Binding,
checker soundness, and adapter fidelity are not yet proved. Per the user's
clarification, larger source proofs may be deferred in this PoC and no WASM
proofs are being attempted. The [proof ledger](../LeanExe/KernelCheck/PROOFS.md)
keeps those boundaries explicit.

Implementation feasibility is materially better supported now: explicit first-
order machines in LeanExe perform binding, dependent-function typing, beta/zeta
conversion and an actual exported closed proof check. This does not establish
full Lean compatibility, inductive/recursor support, symbolic universe handling,
or large-library performance. The multi-megabyte artifact and naive graph copying
are remaining scale concerns. M1.1 is the next small task, not a full-kernel port.


### M1.0: exported applications

Complete: `node test/kernel_export.js composition` checks the pinned real
export of `(p q r : Prop) → (q → r) → (p → q) → p → r`, with proof
`fun p q r f g hp => f (g hp)`. The unchanged exporter output contains two
application records. The adapter maps their earlier function/argument references
to existing tag-4 nodes; no kernel rule changed. Replacing `g hp` with `g f`
changes one reference, remains well scoped, and is rejected by both ordinary
Lean execution of the checker and WASM. The exact decoded graph and provenance
hashes are committed alongside both raw inputs.

The focused gate covers acceptance, rejection, exhaustion, nineteen adapter
failure variants, and an import-free artifact. Its bytes and SHA-256 equal the
M0.11 artifact above: the existing checker handles the larger example unchanged.
Reproduce raw bytes with `node tools/kernel-export-fixture.js composition`.
The identity export remains a regression gate; the aggregate command includes
both exports. Source proof coverage is unchanged. Continue with M1.1 only.
