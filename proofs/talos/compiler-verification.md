# Compiler Verification Plan

This document assesses verifying the LeanExe compiler itself and lays out a staged plan.  It complements the [CLOB verification analysis](analysis.md): that document reviews the per-artifact proofs as they stand, while this one asks what replaces them.  Nothing here is committed work; the phases below are a proposal with named decision points.

## Current Trust Position

The compiler is a Lean program with a three-stage pipeline.  `LeanExe.Extract` (about 7,400 lines) consumes the elaborated Lean environment and recognizes a supported fragment.  It produces a deep-embedded typed `IRModule` (`LeanExe.IR.Core`, about 550 lines of syntax: 46 `Expr` constructors, 7 `Cond` constructors, and about 6 statement forms) with its own evaluator in `LeanExe.Extract.Eval`.  The WASM layer then emits the binary module.

None of this is trusted today.  The proof tool regenerates the WASM from source, Talos decodes it, and a handwritten input-generic theorem relates the decoded module to the source function.  That is translation validation performed by hand, per artifact.  Its cost is the instruction-proof effort; its benefit is that the compiler changes freely, paying a regeneration and sometimes a proof repair, never a compiler-proof repair.

## Architecture of a Verified Compiler

The pipeline splits into two problems with different characters.

The back end, IR to WASM, admits a once-and-for-all theorem: for every well-formed `IRModule` m, the decoded Talos semantics of the emitted module terminates under a compiler-computed budget and returns states related to the IR evaluation of m.  Everything needed to state this exists in per-artifact form and needs generalizing: the IR evaluator promoted to a specification, one representation relation defined by recursion on `Ty` in place of the handwritten `OrdersAt`, `LevelsAt`, and `TradesAt` predicates, the refcount and ownership discipline as one preserved invariant, and allocator correctness stated per emitter template.

The front end, Lean to IR, cannot receive a once-and-for-all proof, because that would require a formal semantics of the elaborated Lean fragment.  It does not need one.  Both sides live in Lean, so the per-program statement `evalIR (extract f) = f` is directly stateable and provable by reflection as a machine-checked certificate generated at compile time.  The existing IR comparison test gate is the empirical form of this statement.  A certifying front end plus a verified back end gives end-to-end machine-checked correctness for every compiled program with no handwritten WAT proofs.

## Feasibility

The estimate is one to two person-years for the qualified claim, with three scope qualifications: the theorem anchors at the IR; the first version excludes the `memoryGrow` path and uses coarse budgets, as every artifact proof does today; and the Talos model is the semantics, with fidelity to real WASM resting on differential execution.

The grounds: the IR is small in structure, and the shared proof assets built for the artifacts are the reusable half of the job.  The mass sits in roughly 18 loop-shaped fused intrinsics (`arrayMapSlots`, `arrayFoldMultiSlot`, `arrayFilterSlots`, the append, extract, and byte-array families).  Each compiles to a loop with allocation and needs an invariant and template theorem comparable to one depth branch phase, which with the shared library is days of work each.  Scalar and control constructors are cheap.  One known wrinkle: the IR represents `nat` in 64 bits (`natAdd` evaluates as `UInt64` addition), so front-end certificates for `Nat`-using programs carry no-overflow side conditions, matching the bounded-interpretation caveat the artifact proofs already state.

## Phases

Each phase pays on its own, and the project can stop after any of them.

| Phase | Work | Gate |
|-------|------|------|
| 0 | Finish the proof-infrastructure overhaul: shared instruction-theorem library, clone consolidation, slow-module divisions, all gates green. | Aggregate proof and execution gates. |
| 0.5 | Restructure the emitter: `emit : IR.Module → Wasm.Module` with serialization split off, validated by byte-identical output for all twenty cases; add the per-module `rfl` round-trip gate. | Byte-identical regeneration plus the new gate on all cases. |
| 1 | Author the IR semantics: keep the scalar evaluator, add the executable heap interpreter with the value domain, refcount ghost state, and per-constructor ownership conventions; add well-formedness; settle `nat`. | The 62 scalar comparisons as Lean examples, and the heap interpreter validated against the Wasmtime differential suite. |
| 2 | Define one `represents` relation by recursion on `Ty`, covering products, sums, structs, variants, and recursive variants; state the ownership discipline as one invariant.  The recursive case builds on the `RelTree` ownership-tree work. | Prove `OrdersAt`, `LevelsAt`, and `TradesAt` equivalent to instances of the generic relation. |
| 3 | Restate the shared theorems over IR constructors: allocator, copy loops, folds, searches, and the calling convention through `TerminatesWith`; one emitter template per constructor, scalars first, loop intrinsics in dependency order. | Focused warning-failing build per template. |
| 4 | The back-end theorem: structural induction over `Expr` and `Stmt` gluing the templates, with a module-level budget function.  Module division discipline applies from the first file, because the elaboration cost of the induction is the known engineering hazard. | Focused build of the induction modules; the theorem statement reviewed against the scope qualifications. |
| 5 | Front-end certificates: compile-time generation of `evalIR (extract f) = f` by reflection, wired into the Talos tools as a third gate, with a recorded fallback to differential testing where kernel reduction is too slow. | Certificates for all twenty registered cases. |
| 6 | Re-derive the twenty artifact theorems from the compiler theorem plus their source-property modules; retire the per-artifact instruction proofs. | Aggregate gate over the re-derived theorems. |

## Detailed Design Findings

Reading the pipeline in depth changes three parts of the plan.

### The IR has no heap semantics yet

The existing IR evaluator is scalar-only.  `LeanExe.Extract.Eval` gates evaluation behind `scalarModule`, and the evaluation state in `LeanExe.IR.Core` is `Store` over `Array UInt64` local slots.  The scalar constructs — arithmetic, conditionals, lets, calls, `while`, `seq`, and the range and loop folds — evaluate today, and the 62 IR comparison cases cover exactly this fragment.  Every heap construct (the array and byte-array families, `heapAllocSlots`, `release`) has no IR-level meaning.  Phase 1 is therefore authorship, and its content is larger than the original plan implied: an executable heap interpreter over a deep value domain (scalars, arrays, structs, variants), refcount ghost state, and the per-constructor ownership conventions — which values each construct consumes and which it borrows.  Those conventions exist operationally in `Extract.OwnershipReport` and `Extract.ReleaseCheck` and must be transcribed into the semantics.  The adequacy risk concentrates here: if a convention in the semantics disagrees with what the emitter implements, the mismatch surfaces late, in phase 3 templates.  Mitigation: run the heap interpreter against the Wasmtime differential suite as soon as it exists, before any proof depends on it.

### The emitter needs restructuring before proof

`LeanExe.Wasm.Binary.encode : IR.Module → Except String ByteArray` fuses code generation with binary serialization in 3,652 lines, and the verification pipeline reads the module back through `wasm-tools print` and the Talos decoder — an external tool inside the semantic path.  The back-end theorem should instead be stated over an explicit `emit : IR.Module → Wasm.Module` targeting the Talos module type, with `encode = serialize ∘ emit`.  The proof then lives inside Lean, and the external round trip becomes a per-module gate check: at artifact-generation time, compare the Talos-decoded model against `emit`'s output by `rfl`.  That check removes `wasm-tools` and the decoder from the semantic trusted base, leaving them only in the byte-serialization path.  The restructuring is a compiler refactor and must be validated the way the workflow migration was: byte-identical output for all twenty registered cases before any proof work starts.  This is a new phase between 0 and 1.

### Simulation shape

The IR statement layer is imperative (`assign`, `seq`, `ite`, `while`, fused fold-assigns), so the back-end proof is a forward simulation, and the simulation relation carries the compiler's slot map: IR local slot to WASM local index, plus the representation relation for heap slots and the allocator state.  Stating the IR semantics fuel-based and big-step, in the style of `TerminatesWith`, lets each template lemma discharge its obligation with the existing `wp` machinery — the loop templates are `wp_loop_cons` invariant proofs where the invariant is the simulation relation at the loop head, exactly the shape of the depth fold proof.  No per-program invariants appear anywhere; program-specific reasoning ends at phase 5 certificates.

### Template inventory

| Constructor class | Count | Proof shape | Existing asset |
|-------------------|-------|-------------|----------------|
| Scalar expressions and conditions (`u64Bin`, `ite`, `eqU64`, `ltU64`, `leU64`, `not`, `and`, `or`, literals, locals) | 15 | Direct `wp` stepping | The instruction simp set |
| Lets, calls, statements (`letE`, `letCall`, `letLets`, `assign`, `seq`, `ite`, `skip`, `call`) | 8 | Frame plumbing plus `wp_call_tw` | Function 3 and 6 call compositions |
| `while`, range and loop folds | 5 | Loop simulation invariant | The depth fold loop and copy loops |
| Allocation and release (`heapAllocSlots`, `arrayAllocSlots`, `release`, replicate) | 4 | Allocator templates | `FixedArrayAllocation`, the empty-allocation adapter, `release_frees_tree` |
| Array intrinsics (get, set, push, pop, append, extract, map, fold, find, filter, insert, erase, swap, reverse, eq, any, size, literal) | 18 | Loop simulation with allocation | Copy invariants, append and replace store facts |
| Byte-array intrinsics | 9 | Same, byte-granularity | `BytesAt`, validate and LEB proofs |

The array and byte-array rows are the mass, as estimated; the new information is that each fused intrinsic also fixes an ownership convention that phase 1 must state and phase 3 must match.

### Certificates for heap-typed entries

Scalar entries certify as `evalIR (extract f) args = f args` by reflection today.  Heap-typed entries need encode and decode functions per `Ty` between Lean values and the interpreter's value domain, and the certificate becomes `decode (evalIRHeap (extract f) (encode args)) = f args`.  Both sides stay executable, so `decide`-style checking remains available; kernel-reduction performance on large inputs is the open question, and the recorded fallback is the differential suite.  The `nat` overflow policy applies at the encode boundary: certificates for `Nat`-using entries state their no-overflow side conditions there, in one place.

### Budget function

Each allocating template contributes a byte cost; the budget is the composition over the program structure, computed by a total function `B : IRFunc → Nat → Nat` from input sizes.  The depth analysis shows what coarseness costs: bounding distinct-price counts by order counts made the artifact budget quadratic where the tight bound is data-dependent.  The compiler-level budget inherits this: budgets are worst-case over the type structure, and consumers needing tight bounds state them per program.  The `memoryGrow` path stays excluded until a consumer requires unbounded growth; the templates assert the fit premise exactly as the artifact proofs do.

## Decision Points

Four decisions belong to the project owner before or during the work: whether the `memoryGrow` path enters the first version (this plan defers it); budget precision (coarse first, sharpened only if a consumer needs it); the `Nat` overflow policy for certificates; and whether `Extract`'s fragment recognizer ever receives certificates or stays gated by differential tests.

## Implications and Costs

What the theorem buys: artifact proofs collapse to source-level reasoning plus a certificate, and each new export costs a source-property module instead of weeks of instruction proofs.  What it does not buy: the Lean elaborator and kernel remain trusted; Talos-model fidelity and host ABI conformance remain empirical; resource behavior and performance of generated code are untouched.

Two costs arrive with success.  The compiler ossifies: every emitter change reopens phase 3 or 4, and the current freedom to change the compiler against regeneration gates disappears.  Review concentrates: today a mistake in one artifact's predicates is contained to that artifact, while a mistake in the one generic representation relation would weaken every artifact claim at once.  The defensible claim after phase 6 is exactly: for every well-formed IR module, the emitted code's decoded Talos semantics terminates under the stated budget and returns states related to IR evaluation, and for each compiled program a reflection certificate ties the IR to the source function.
