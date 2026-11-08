# Verification knowledge base (VKB)

The VKB collects what agents and people learn while proving: lemmas, proof methods, worked examples, and the ways proofs fail.  It covers the obligations of end-to-end work for every artifact and property that [the index](../index.md) names by a code (WASM, SPEC, WASMF, WASI, C, CALIGN, METAL, A64, M7, WGSL, and PTX), the specification proofs of the library, and the proofs that check the back ends' models: the instruction forms against Isla's traces and the floating-point equations from Sail.  For a program of the verified compiler, the compiler's universal theorem gives the execution theorem, `p.f.implements`, so the work that remains comes after it: equality with an independent specification, call and file theorems, allocation bounds for `p.f.trapFree`, numerical error bounds, WASI totality, and the theorems of native code, bare-metal programs, images, boards, and GPU kernels.  The verified compiler, the runtime, and the trusted statements import no part of the VKB, so an entry can help a proof or fail its own check but cannot change a theorem.

## Entries

Each entry is a directory under [`entries/`](entries) with a `README.md` and an `entry.json`.  The README states when the entry applies, what to do, what fails, and where a worked example is, in prose that a prover can follow without other context.  `entry.json` names the modules to import, the declarations the entry relies on, the worked examples, and the goal shapes it addresses.  A search for a constant or a goal therefore finds the entry, and [the template](TEMPLATE.md) gives the form of both files.

An entry names existing declarations instead of restating them.  When several proofs repeat a lemma, the entry points to the copies, and replacing them with one shared lemma is a separate code change.  An entry may record a failure without a fix, because a recorded failure saves the next prover the same hours.

| Entry | Use |
|---|---|
| [Closed computations](entries/closed-computations/README.md) | Proves constants, table entries, exports, and other closed facts by kernel evaluation. |
| [Large folds and compiled terms](entries/large-term-unfolding/README.md) | Controls reductions that cause recursion-depth errors, timeouts, or excessive memory use. |
| [Loops and builds](entries/loop-combinators/README.md) | Proves invariants for `LeanExe.loop`, element equations for `LeanExe.build`, and equalities of loops that write into arrays of their state with the loops that build new arrays. |
| [Array folds by list induction](entries/array-fold-list-induction/README.md) | Proves that `xs.foldl step init` meets a specification stated by positions or lists, by induction on the array's list. |
| [Word identities](entries/word-bit-identities/README.md) | Relates shifts, masks, and packed words to bit-level specifications. |
| [Packed bytes](entries/packed-bytes/README.md) | Recovers a byte from an array that packs eight bytes into each word. |
| [Array layout across writes](entries/array-memory-framing/README.md) | Keeps `UInt64Array.At` and byte buffers across stores and memory growth, and proves loops that fill an array word by word. |
| [Write ranges](entries/memory-write-range/README.md) | Confines a sequence of stores to one interval of memory and keeps every other byte and field of the store. |
| [Binary64 error bounds](entries/float-error-tracking/README.md) | Propagates input and rounding errors through a chain of operations. |
| [Accuracy against real functions](entries/real-function-accuracy/README.md) | Bounds a binary64 function's distance from the rounding of a Mathlib function and transfers the bound to the module. |
| [Kernel checks over ℚ](entries/kernel-rational-checks/README.md) | Proves polynomial, series, and table bounds by evaluation in parts. |
| [Correct rounding](entries/correct-rounding/README.md) | Proves that software arithmetic returns the nearest-even rounding of an exact value. |
| [Decimal text](entries/decimal-conversions/README.md) | Proves parsers and printers of floating-point values against a grammar, rounding, and round trips. |
| [Transcriptions of standards](entries/spec-transcription/README.md) | Relates a program to a transcription of a published standard, its vectors, and its test references. |
| [Specification call theorems](entries/spec-call-theorem/README.md) | Combines a specification equality with generated execution and allocation theorems. |
| [Composed and appended programs](entries/module-composition/README.md) | Proves the theorems of functions added to or appended with a compiled program. |
| [Region frame of a call or a step](entries/region-frame/README.md) | Keeps the caller's arrays and trees across a call through the region clause, and composes the frames of steps. |
| [Explicit arguments before dependent proofs](entries/explicit-before-dependent-proof/README.md) | Avoids the unification failure of a proof argument about a value that a later argument fixes. |
| [File theorems](entries/file-theorems/README.md) | States that an emitted `.wasm` file holds the encoding of a module, through a file module outside the import graph. |
| [Closed-form allocation bounds](entries/verified-bound-closed-form/README.md) | Bounds the generated allocation term in input sizes or in counts of loop passes. |
| [Source forms and costs](entries/verified-source-costs/README.md) | Relates source choices, such as arrays kept in a loop's state, to allocation, generated bounds, and compilation cost. |
| [Array literals, proposition tests, and structure patterns](entries/reflector-forms/README.md) | Explains the reflected code and allocation charges of these forms, and the structure patterns that the reflector reads and those it rejects. |
| [Representations of structures and enumerations](entries/flat-instances/README.md) | Describes the `Flat` instances that the reflector needs for user types, and the module that holds them. |
| [Tail-termination cases](entries/tail-termination-cases/README.md) | Diagnoses remaining functional-induction cases in a tail-loop proof. |
| [Mutual execution induction](entries/mutual-relation-induction/README.md) | Proves statements over mutually inductive WASI or Clight executions. |
| [Partial loop correctness](entries/partial-wasm-loop/README.md) | States the result of a completed Wasm loop while its termination proof remains separate. |
| [Calls with operands below the arguments](entries/direct-call-stack-tail/README.md) | Extends a callee's theorem on its arguments to a call with more operands on the stack. |
| [Raw Wasm locals](entries/local-frame-projection/README.md) | Proves equalities of `Wasm.Locals` and reads parameters and locals in proofs of hand-written code. |
| [WASI host premises](entries/wasi-host-premise/README.md) | Identifies the satisfying-host premise needed to apply an execution theorem. |
| [WASI effect charges](entries/wasi-effect-charges/README.md) | Bounds allocation over complete command runs and their prefixes. |
| [WASI process totality](entries/wasi-process-total/README.md) | Combines progress, resource bounds, and accepted exit for an unbounded process. |
| [Line-oriented processes](entries/stream-fold/README.md) | Instantiates the shared line reader and output proof with an application kernel. |
| [GPU kernels](entries/verified-wgsl-kernel/README.md) | Proves WGSL dispatch and PTX launch theorems of verified builds and composes them into a host program. |
| [Native theorem conclusions](entries/native-conclusion-patterns/README.md) | Extracts result, heap, region, and postcondition facts from a native call theorem. |
| [Bare-metal C programs](entries/bare-metal-programs/README.md) | States whole-program theorems for fixed arguments, loaded inputs, request loops, and controllers. |
| [Clight determinism](entries/clight-determinism/README.md) | Compares two execution derivations and extends a proved result to every matching execution. |
| [AArch64 Image theorems](entries/a64-image-theorem/README.md) | Proves an A64 Image's run from boot from the compiler's theorems, and joins its output with a specification. |
| [Image files](entries/image-file-checks/README.md) | Checks a written A64 or M7 image against its generator in the kernel, in parts when it is large. |
| [Cortex-M7 board theorems](entries/m7-board-theorem/README.md) | Proves a step's run from reset through every window from its compiler theorem. |
| [Output of request programs](entries/request-output-prefix/README.md) | States the bytes written to the UART as a prefix of a specification's output for the bytes read. |
| [Instruction forms against Isla](entries/isla-form-proofs/README.md) | Proves an A64 or M7 form's agreement with Isla's traces of Arm's specification. |
| [Floating-point equations from Sail](entries/sail-fp-equations/README.md) | Derives an Isla theorem's floating-point hypothesis from Sail's Lean translation. |
| [Kernel evaluation costs](entries/kernel-evaluation-costs/README.md) | Finds the comparison that makes the kernel evaluate a large literal or a projected term. |
| [Generator orbits](entries/generator-orbits/README.md) | Proves periods, equidistribution, and jump-ahead of word generators. |

## Admission and growth

Every proof task ends with its lessons in the form of the template, as [the repository instructions](../AGENTS.md#verification-knowledge-base) require.  An agent that proves a program writes an entry, or a change to an entry, in its own branch when the lesson names existing declarations and applies to other programs, and it records a proposal in its journal or report when the lesson is uncertain or rests on one use.  The reviewer of the merge admits an entry when its guidance applies beyond the task, its declarations exist, and no entry already covers it, and otherwise merges it into an existing entry or declines it with a reason.  An entry does not state how often its lesson recurs, so the agent's report gives that evidence to the reviewer.  The verified-request skill ends its proofs in this way, and a brief for any other proof task ends with the same step.

A change that renames, removes, or restates a declaration that an entry names searches `VKB/entries` for the name and updates those entries in the same change.  A consolidation that replaces the copies an entry names by a shared lemma revises the entry, which then names the shared lemma and keeps one former copy as a worked example.  A proving run that finds an entry's guidance wrong or incomplete revises the entry, and so does a change after which a measurement that the entry cites no longer holds.

A change of its own retires an entry that is wrong beyond repair, whose code is gone, or whose lesson another entry holds, and its commit message gives the reason.  The `goals` of a retired entry move to the entry that absorbs it, so that a search for its goal shapes still finds the lesson.  The merge of two entries follows the same rules.

## Check

[`Check.lean`](Check.lean) imports the modules that the entries list.  It reports every listed declaration or example that does not exist and every entry whose directory name differs from its `id`, and it stops with an error at a listed module that does not exist or an entry without a `README.md`.  It needs the listed modules built, which the first step of the full check does.  Run the build and the check from the repository root:

```sh
tools/leanrun --timeout 12h lake build LeanExe Examples Demos Verified Library TestSupport \
  native-verified native-bare verified-cases native-module-cases
tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean VKB/entries
```

The check does not catch these defects, which the rules of [admission and growth](#admission-and-growth) leave to the changes that cause them:

- a name in an entry's README that its `entry.json` omits;
- an id in backticks that refers to a renamed or merged entry;
- guidance that a change to a declaration's statement, to the verified compiler, or to the library has made wrong;
- a measurement that a later change altered;
- a listed module that starts to read a file at elaboration.

A module that reads a file at elaboration, such as a file-theorem module, does not belong in `modules`, because the check would then depend on emitted files.  The README of an entry names a theorem of such a module together with the module's file.
