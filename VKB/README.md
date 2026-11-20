# Verification knowledge base (VKB)

The VKB collects what agents and people learn while proving: lemmas, proof methods, worked examples, and the ways proofs fail.  It covers the obligations of end-to-end work for every artifact and property that [the index](../index.md) names by a code (WASM, MASTER, SPEC, WASMF, C, CALIGN, METAL, A64, M7, WASI, WGSL, and PTX), the specification proofs of the library, and the proofs that check the back ends' models: the instruction forms against Isla's traces and the floating-point equations from Sail.  Entries also give guidelines for the work around a proof, such as testing a statement before its proof, reviewing a specification or a design, judging a run on a board or an emulator, and showing that a check can fail, and those entries cite the scripts, reviews, and documents that record each practice.  For a program of the verified compiler, the compiler's universal theorem gives the execution theorem, `p.f.implements`, so the work that remains comes after it: equality with an independent specification, call, master, and file theorems, allocation bounds for `p.f.trapFree`, numerical error bounds, WASI totality, and the theorems of native code, bare-metal programs, images, boards, and GPU kernels.  The verified compiler, the runtime, and the trusted statements import no part of the VKB, so an entry can help a proof or fail its own check but cannot change a theorem.

## Entries

Each entry is a directory under [`entries/`](entries) with a `README.md` and an `entry.json`.  The README states when the entry applies, what to do, what fails, and where a worked example is, in prose that a prover can follow without other context.  `entry.json` names the modules to import, the declarations the entry relies on, the worked examples, and the goal shapes it addresses.  A search for a constant or a goal therefore finds the entry, and [the template](TEMPLATE.md) gives the form of both files.

An entry names existing declarations instead of restating them.  When several proofs repeat a lemma, the entry points to the copies, and replacing them with one shared lemma is a separate code change.  An entry may record a failure without a fix, because a recorded failure saves the next prover the same hours.

| Entry | Use |
|---|---|
| [Closed computations](entries/closed-computations/README.md) | Proves constants, table entries, exports, and other closed facts by kernel evaluation. |
| [Large folds and compiled terms](entries/large-term-unfolding/README.md) | Controls reductions that cause recursion-depth errors, timeouts, or excessive memory use. |
| [Measuring Lean checks](entries/measuring-lean-checks/README.md) | Measures the time and peak memory of a check and locates the declaration that costs them. |
| [Diagnosing slow checks](entries/slow-check-diagnosis/README.md) | Finds the cause of a slow or failing check in order of measurement and links each cause to its remedy. |
| [Tactics whose failures mislead](entries/tactic-combinator-pitfalls/README.md) | Avoids combinators that report success on progress, miss errors, or fail on a goal that is type-correct only at the default transparency, rewrites and normal forms whose results make later steps fail, implicit binders that the elaborator fills, and parses and names that mislead. |
| [Types that elaboration chooses](entries/elaborated-types/README.md) | Types binders and literals so that statements and translations mean what they state. |
| [Lemmas that close goals of structure literals](entries/structure-update-lemmas/README.md) | States a lemma about an updated structure as one update of a variable, so that `exact` unifies its arguments with the flat literal that `simp` leaves, and names the updates of a proof that states many facts about them. |
| [One definition over ℤ and over words](entries/generic-algebra-transfer/README.md) | Defines an algorithm over generic operations, proves it over ℤ, and transfers it to wrapping words. |
| [Loops and builds](entries/loop-combinators/README.md) | Proves invariants for `LeanExe.loop`, element equations for `LeanExe.build`, and equalities of loops that write into arrays of their state with the loops that build new arrays. |
| [Array folds by list induction](entries/array-fold-list-induction/README.md) | Proves that `xs.foldl step init` meets a specification stated by positions or lists, by induction on the array's list. |
| [Word identities](entries/word-bit-identities/README.md) | Relates shifts, masks, and packed words to bit-level specifications. |
| [Programs over `Int64`](entries/signed-int64/README.md) | Proves `Int64` programs against specifications over the integers or WebAssembly's signed conversions, and runs them on the A64 and M7 back ends. |
| [Signed quantities as `Int64` values](entries/signed-integer-values/README.md) | Writes signed exponents and differences as `Int64` and proves their integers, comparisons, and exact conversions to binary64. |
| [Packed bytes](entries/packed-bytes/README.md) | Recovers a byte from an array that packs eight bytes into each word. |
| [Functions over `LeanExe.Bytes` as functions over lists](entries/bytes-as-lists/README.md) | States the bytes of a buffer as `Array.toList` of its array and proves reads and builds of literal buffers against lists. |
| [Byte buffers in words](entries/byte-buffer-passes/README.md) | Keeps a buffer of bytes in a step's words and proves straight-line passes over it, which a static cost bounds, against folds over lists. |
| [Bounds for a step's phases](entries/m7-phase-bounds/README.md) | Bounds the Cortex-M7 windows of a step's polling phases apart from its long window, by the cost of the path that the step's tests select, and compares each bound with half a byte time. |
| [Array layout across writes](entries/array-memory-framing/README.md) | Keeps `UInt64Array.At` and byte buffers across stores and memory growth, and proves loops that fill an array word by word. |
| [Write ranges](entries/memory-write-range/README.md) | Confines a sequence of stores to one interval of memory, keeps every other byte and field of the store, and states the bytes of a block whose zeroing and field stores overlap. |
| [Binary64 error bounds](entries/float-error-tracking/README.md) | Propagates input and rounding errors through a chain of operations. |
| [Interval inclusion proofs](entries/interval-enclosures/README.md) | Proves that an accepted result of an interval program contains a real quantity, with enclosures of monotone library functions and of integrals over panels. |
| [One source for a real formula and its interval program](entries/enclosure-def/README.md) | Declares a real function, its interval program, and the inclusion theorem from one body with `enclosure_def`, and proves what the statuses of the surrounding program imply. |
| [Searches over interval enclosures](entries/interval-searches/README.md) | Proves bracketing loops, bisections, marches, subdivisions, and queues of cells over interval evaluations once for any evaluator, and encloses roots from a residual and a bound on the slope. |
| [Accuracy against real functions](entries/real-function-accuracy/README.md) | Bounds a binary64 function's distance from the rounding of a Mathlib function and transfers the bound to the module. |
| [Accuracy of numerical functions applied in sequence](entries/composed-accuracy/README.md) | Composes the accuracy bounds of two compiled functions with an exact identity over the reals, as the round trip of the discrete Fourier transform does. |
| [Derivatives, inverse functions, and differential equations of real models](entries/real-model-calculus/README.md) | Combines Mathlib's derivatives, proves Taylor's theorem of order two from Rolle's theorem, differentiates inverse functions, proves the uniqueness of solutions of differential equations, and proves monotonicity and continuity through integrals with a parameter. |
| [Identities and certificates over the reals](entries/real-identities/README.md) | Finds the coefficients of `linear_combination` under constraints, removes a quadratic constraint by a rational parametrization, and certifies a matrix's single positive eigenvalue from the signs of pivots. |
| [Laws of random variables](entries/laws-of-random-variables/README.md) | Identifies the law of a real random variable with a named distribution from moment-generating functions on a half-line, and carries a function of a Gaussian vector to independent standard normal variables. |
| [Counts of words and of sequences of words](entries/word-counts/README.md) | States the bias of a random draw as counts of words and of sequences of words with Mathlib's finite sets, with a tail bound in counting form. |
| [Kernel checks over ℚ](entries/kernel-rational-checks/README.md) | Proves polynomial, series, and table bounds by evaluation in parts. |
| [Correct rounding](entries/correct-rounding/README.md) | Proves that software arithmetic returns the nearest-even rounding of an exact value. |
| [Decimal text](entries/decimal-conversions/README.md) | Proves parsers and printers of floating-point values against a grammar, rounding, and round trips, and printers and readers of integers against `toString`. |
| [Readers of line-oriented files](entries/line-readers/README.md) | Proves a reader over a byte buffer equal to a specification over `List.splitOn`, and its first error equal to a definition by line number. |
| [Transcriptions of standards](entries/spec-transcription/README.md) | Relates a program to a transcription of a published standard, its vectors, and its test references. |
| [Testing a statement before its proof](entries/statement-testing/README.md) | Evaluates a new theorem's statement on an executable model before proving it. |
| [Independent review of specifications and designs](entries/independent-review/README.md) | Reviews a specification against its request with the reviewer's own model and wrong programs, a premise on a host's replies with wrong premises, and a design note against the tree. |
| [Satisfiable hypotheses and complete conclusions](entries/non-vacuous-statements/README.md) | Shows each hypothesis satisfiable and makes a conclusion exclude the trivial run. |
| [Claims and the theorems that state them](entries/claims-and-theorems/README.md) | States each claim of a document as its theorem states it. |
| [Requirements for a safety theorem](entries/requirements-for-theorems/README.md) | Writes requirements whose terms, items, and margins a theorem can state. |
| [Compiled forms of list specifications](entries/linear-compiled-folds/README.md) | Makes native evaluation of a fold that appends to the end of a list linear by a `csimp` theorem, while the proofs keep the definition. |
| [Specification call theorems](entries/spec-call-theorem/README.md) | Combines a specification equality with generated execution and allocation theorems into call and master theorems. |
| [Composed and appended programs](entries/module-composition/README.md) | Proves the theorems of functions added to or appended with a compiled program. |
| [Region frame of a call or a step](entries/region-frame/README.md) | Keeps the caller's arrays, buffers, and trees across a call through the region clause, composes the frames of steps, among them a WASI command and the release of the variables that die after it. |
| [Explicit arguments before dependent proofs](entries/explicit-before-dependent-proof/README.md) | Avoids the unification failure of a proof argument about a value that a later argument fixes. |
| [File theorems](entries/file-theorems/README.md) | States that an emitted `.wasm` file holds the encoding of a module, through a file module outside the import graph. |
| [Checks that can fail](entries/discriminating-checks/README.md) | Shows that a check detects a seeded fault before its passes count as evidence, and fixes the random bytes of a run so that a driver compares its output byte for byte with the specification's. |
| [Executable mirrors of a specification](entries/mirror-cross-check/README.md) | Cross-checks a mirror that judges runs against a native replay of the specification. |
| [Theorems outside the full check](entries/out-of-build-checks/README.md) | Identifies theorems that the full check does not check and the driver that does, and elaborates a file against a module that no build has compiled. |
| [Results that show a check passed](entries/result-validity/README.md) | Takes a verdict from the check's own output on a known tree. |
| [Changes that keep statements and bytes](entries/unchanged-statements-and-bytes/README.md) | Shapes a change of a shared definition so that existing theorems and artifacts stay as they are, and shows it. |
| [Instructions that the encoder accepts](entries/encoder-domain/README.md) | Keeps emitted code within the verified encoder's instruction forms and builds missing loads from accepted ones. |
| [Closed-form allocation bounds](entries/verified-bound-closed-form/README.md) | Bounds the generated allocation term in input sizes or in counts of loop passes. |
| [Source forms and costs](entries/verified-source-costs/README.md) | Relates source choices, such as arrays kept in a loop's state, to allocation, generated bounds, and compilation cost. |
| [Owned tuple parameters and their theorem arguments](entries/owned-tuple-arguments/README.md) | States the argument of a function with an owned tuple or structure parameter as `Moved` of its Lean type, and the charge of a process step's call of such a function. |
| [Array literals, proposition tests, and structure patterns](entries/reflector-forms/README.md) | Explains the reflected code and allocation charges of these forms, and the structure patterns that the reflector reads and those it rejects. |
| [Representations of structures and enumerations](entries/flat-instances/README.md) | Describes the `Flat` instances that the reflector needs for user types, and the module that holds them. |
| [Tail-termination cases](entries/tail-termination-cases/README.md) | Diagnoses remaining functional-induction cases in a tail-loop proof. |
| [Mutual execution induction](entries/mutual-relation-induction/README.md) | Proves statements over mutually inductive WASI or Clight executions and inverts the runs of one program's action. |
| [Partial loop correctness](entries/partial-wasm-loop/README.md) | States the result of a completed Wasm loop while its termination proof remains separate. |
| [Calls with operands below the arguments](entries/direct-call-stack-tail/README.md) | Extends a callee's theorem on its arguments to a call with more operands on the stack. |
| [Raw Wasm locals](entries/local-frame-projection/README.md) | Proves equalities of `Wasm.Locals`, reads parameters and locals in proofs of hand-written code, and names the states of long proofs over generated code. |
| [WASI host premises](entries/wasi-host-premise/README.md) | Identifies the satisfying-host premise of an execution theorem, with or without flat calls, and what a new host specification must prove. |
| [WASI hosts built on a lower layer](entries/wasi-host-from-layer/README.md) | Defines a WASI host with stream functions and flat calls from the events of a lower layer such as the Linux call layer, implements its environment with the layer's rule, lifts the command theorem's runs to statements about the layer's events, carries runs without flat calls to other choices of the host's parameters, and states premises on the replies over a run's events or along its prefixes. |
| [Corollaries over the layer events of a WASI executable](entries/layer-event-corollaries/README.md) | States a command's request over the Linux calls of its executable under a condition on the layer events, excludes the trapped runs, mirrors the command's specification, and builds a witness. |
| [WASI effect charges](entries/wasi-effect-charges/README.md) | Bounds allocation over complete command runs and their prefixes, from one world when the charge depends on the host's replies, with the shared budget tactics and the rules of a pair's split. |
| [WASI process totality](entries/wasi-process-total/README.md) | Combines progress, resource bounds, and accepted exit for an unbounded process. |
| [Theorems over every run of a WASI command](entries/wasi-command-runs/README.md) | Proves what a command writes and with which status it exits for every host's replies, composes it with the generated `start` and `total` theorems, and states a property of the runs that trap. |
| [A new command of the WASI effect IR](entries/wasi-command-constructors/README.md) | Lists the definitions and proofs that a new constructor of the effect IR needs and proves the code of a pair's split. |
| [A new flat call on the native target](entries/native-flat-calls/README.md) | Lists the parts that a flat call needs in the Linux call layer, the shim, the AArch64 stub, and the documents before a command that imports it runs as an AArch64 Linux executable. |
| [Bytes that a trusted rule leaves free](entries/free-reply-bytes/README.md) | Gives a semantic rule a free value constrained by the host's guarantees and chooses it from the machine state in the compiler's proof. |
| [One buffer through a loop](entries/buffer-through-loop/README.md) | Keeps a buffer in a loop's state so that a read or a draw at each pass moves it and allocates nothing. |
| [Byte updates in place](entries/bytes-set-in-place/README.md) | Writes the bytes of a buffer with `LeanExe.Bytes.set` so that each update moves the buffer, and proves the result byte by byte. |
| [Line-oriented processes](entries/stream-fold/README.md) | Instantiates the shared line reader and output proof with an application kernel. |
| [Programs that read their whole input](entries/wasi-read-all/README.md) | Reads the whole standard input in `begin` with `readAll`, closes its charge, states the process theorem for inputs within and above the limit, and reads a named file whole into a buffer of its reported size. |
| [Handles and brackets](entries/wasi-handles/README.md) | Proves the discipline of `withOpen` from the handle check, stage by stage, states the close of each bracket that returns, reads descriptor numbers as open descriptors under the host's assumption, and reads the preopened handle alone or under `letPair` bindings. |
| [GPU kernels](entries/verified-wgsl-kernel/README.md) | Proves WGSL dispatch and PTX launch theorems of verified builds and composes them into a host program. |
| [Native theorem conclusions](entries/native-conclusion-patterns/README.md) | Extracts result, heap, region, and postcondition facts from a native call theorem. |
| [Bare-metal C programs](entries/bare-metal-programs/README.md) | States whole-program theorems for fixed arguments, loaded inputs, request loops, and controllers. |
| [Clight determinism](entries/clight-determinism/README.md) | Compares two execution derivations, extends a proved result to every matching execution, and states which semantics of external calls CompCert's theorem admits. |
| [Proofs of the Clight copy against N](entries/clight-n-proofs/README.md) | Proves the leaf forms of the reference semantics N for the Lean copy of Clight, and carries the copy's theorem of a program to an instance of N. |
| [Simulations over a machine](entries/simulation-over-a-machine/README.md) | States the A64 simulation over a model with more state or with imports, such as the process of the Linux call layer, carries the program model's lemmas to it, derives the model's theorems from the general ones, keeps the machine's facts by platforms and by checks in the generator, and proves the stubs of imports, for the process alone and on the machine. |
| [AArch64 Image theorems](entries/a64-image-theorem/README.md) | Proves an A64 Image's run from boot from the compiler's theorems, for fixed arguments, arguments read from the UART, or a message of bytes read from the UART, proves a Linux executable's run from its entry to `exit_group`, with calls through `Kernel.svc` or through the Linux call layer, a WASI command's executable and the check of descriptor 3 that starts it among them, and joins the output with a specification. |
| [Linux calls through the call layer](entries/linux-call-layer/README.md) | Describes what the Linux call layer's frame rule states and leaves to programs, the memory laws and the set of calls that the frame needs, the evaluation of a call in the A64 binding, and the buffers that replies write. |
| [Image files](entries/image-file-checks/README.md) | Checks a written A64 or M7 image against its generator in the kernel, in parts when it is large. |
| [Cortex-M7 board theorems](entries/m7-board-theorem/README.md) | Proves a step's run from reset through every window from its compiler theorem. |
| [Output of request programs](entries/request-output-prefix/README.md) | States the bytes written to the UART as a prefix of a specification's output for the bytes read. |
| [Instruction forms against Isla](entries/isla-form-proofs/README.md) | Proves an A64 or M7 form's agreement with Isla's traces of Arm's specification, including a load whose value a device gives. |
| [Isla traces with symbolic control registers](entries/isla-symbolic-configurations/README.md) | Traces a form under the control registers that a kernel or firmware sets, with symbolic registers, constrained bits, and the premises that such traces need. |
| [Floating-point equations from Sail](entries/sail-fp-equations/README.md) | Derives an Isla theorem's floating-point hypothesis from Sail's Lean translation. |
| [Code around an executable reference](entries/reference-harness-audit/README.md) | Audits the harnesses, configurations, patches, and edits around Isla, Sail's translation, a second implementation such as RCTab, or another reference. |
| [Encodings and co-simulation of machine forms](entries/machine-form-validation/README.md) | Validates a machine form's encoding against the assembler and its execution against processors and emulators. |
| [Runs on boards and emulators](entries/run-evidence/README.md) | States what a run on a board, under an emulator, or on a Linux host shows and the conditions under which it supports a theorem, and runs stubs at requests that compiled programs never make. |
| [Hardware facts and trusted assumptions](entries/hardware-facts/README.md) | Cites a primary source for each fact about the hardware, an engine, or the Linux kernel and keeps a trusted item's claim apart from its evidence. |
| [Kernel evaluation costs](entries/kernel-evaluation-costs/README.md) | Finds the comparison that makes the kernel evaluate a large literal or a projected term. |
| [Definitions that the kernel evaluates](entries/kernel-evaluated-definitions/README.md) | Gives an evaluated definition a form that computes each value once, or evaluates it natively and has the kernel check the literal. |
| [Generator orbits](entries/generator-orbits/README.md) | Proves periods, equidistribution, and jump-ahead of word generators. |
| [Sorting and selection](entries/sorted-permutation/README.md) | Proves a sort or a selection through the unique sorted permutation. |
| [Array heaps](entries/heap-sift-invariant/README.md) | Proves sift-down, sift-up, heapify, and removal through a heap order from a node on. |
| [Operation streams](entries/operation-stream-refinement/README.md) | Proves that a loop over operations refines a fold over an abstract value, with bounds on its counters. |
| [Safety theorems over a machine's history](entries/history-safety-theorems/README.md) | States safety theorems of a record machine over the records and answers before an answer, and relates the machine's state to the history terms. |
| [A machine over words against its specification](entries/word-machine-refinement/README.md) | Proves that a compiled machine over words in `Flat` structures computes a specification over numbers, check by check and transition by transition. |
| [Link-reversing tree updates](entries/tree-link-reversal/README.md) | Proves stackless tree updates equal to a structural recursion. |
| [Tail-recursive and fuel-bounded functions](entries/tail-recursive-spec/README.md) | Proves specifications by recursion on the program's measure, by fuel, or by a `repeatWhile` invariant. |
| [Traces of fuel-bounded runs](entries/run-traces/README.md) | Relates a run of rounds to an inductive trace and proves facts of every round, of the rounds from a given one, and of runs on changed inputs. |
| [Counts over nested sets](entries/nested-set-counts/README.md) | Compares counts of items under two classifications, such as the votes against a set and a subset, item by item through one `countP` for each set. |

## Admission and growth

Every proof task ends with its lessons in the form of the template, as [the repository instructions](../AGENTS.md#verification-knowledge-base) require.  An agent that proves a program writes an entry, or a change to an entry, in its own branch when the lesson names existing declarations and applies to other programs, and it records a proposal in its journal or report when the lesson is uncertain or rests on one use.  The reviewer of the merge admits an entry when its guidance applies beyond the task, its declarations exist, and no entry already covers it, and otherwise merges it into an existing entry or declines it with a reason.  An entry does not state how often its lesson recurs, so the agent's report gives that evidence to the reviewer.  The verified-request skill ends its proofs in this way, and a brief for any other proof task ends with the same step.

A change that renames, removes, or restates a declaration that an entry names searches `VKB/entries` for the name and updates those entries in the same change.  A consolidation that replaces the copies an entry names by a shared lemma revises the entry, which then names the shared lemma and keeps one former copy as a worked example.  A proving run that finds an entry's guidance wrong or incomplete revises the entry, and so does a change after which a measurement that the entry cites no longer holds.

A change of its own retires an entry that is wrong beyond repair, whose code is gone, or whose lesson another entry holds, and its commit message gives the reason.  The `goals` of a retired entry move to the entry that absorbs it, so that a search for its goal shapes still finds the lesson.  The merge of two entries follows the same rules.

## Check

[`Check.lean`](Check.lean) imports the modules that the entries list and reports these problems: a listed declaration or example that does not exist or that the entry's own modules do not import; a qualified name in a README's code spans that is no declaration, module, or namespace of the imported environment and no file at the repository's root, unless the entry's `unimported` lists it; a file of `unimported` that does not exist, or a name of it that an imported module declares; and an entry whose directory name differs from its `id`.  It stops with an error at a listed module that does not exist, an entry without a `README.md`, or an `entry.json` that does not parse.  [The template](TEMPLATE.md) states which code spans the check reads.  It needs the listed modules built, which the first step of the full check does.  Run the build and the check from the repository root:

```sh
tools/leanrun --timeout 12h lake build LeanExe Examples Demos Verified Library TestSupport \
  native-verified native-bare verified-cases native-module-cases
tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean VKB/entries
```

With `--changed`, the same program prints a report instead and exits with status 0: for each entry, the repository's files that hold the declarations it names, in `entry.json` or in its README, and the files of its `unimported`, which differ in the working tree from the last commit that changed the entry.  The report points a reviewer at guidance that may have gone stale, and it needs `git` and the same build:

```sh
tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean --changed VKB/entries
```

The check does not catch these defects, which the rules of [admission and growth](#admission-and-growth) leave to the changes that cause them:

- a name in an entry's README that its `entry.json` omits;
- a name in a code span that starts with a lower-case letter, such as a partial name;
- guidance that a change to a declaration's statement, to the verified compiler, or to the library has made wrong;
- a measurement that a later change altered;
- a listed module that starts to read a file at elaboration.

A link from one entry to another names the other's README, so the repository's link check fails when an entry is renamed or merged.  A module that reads a file at elaboration, such as a file-theorem module, does not belong in `modules`, because the check would then depend on emitted files, and the README names a theorem of such a module together with the module's file and lists it in `unimported`.
