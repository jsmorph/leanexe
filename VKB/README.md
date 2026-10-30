# Verification knowledge base (VKB)

The VKB collects what agents and people learn while proving properties of programs that the verified compiler compiles: lemmas, proof recipes, worked examples, and the ways proofs fail.  The compiler's universal theorem gives every accepted program its execution theorem, `p.f.implements`, so the work that remains comes after it.  That work includes equality with an independent specification, call and file theorems, allocation bounds for `p.f.trapFree`, numerical error bounds, WASI totality, and native and bare-metal results.  No compiler, runtime, or trusted statement imports the VKB, so an entry can help a proof or fail its own check but cannot change a theorem.

## Entries

Each entry is a directory under [`entries/`](entries) with a `README.md` and an `entry.json`.  The README states when the entry applies, what to do, what fails, and where a worked example lives, in prose that a prover can follow without other context.  `entry.json` names the modules to import, the declarations the entry relies on, the worked examples, the goal shapes it addresses, and the journal entries it comes from.  A search for a constant or a goal therefore finds the entry, and [the template](TEMPLATE.md) gives the form of both files.

An entry names existing declarations instead of restating them.  When several proofs repeat a lemma, the entry points to the copies, and replacing them with one shared lemma is a separate code change.  An entry may record a failure without a fix, because a recorded failure saves the next prover the same hours.

| Entry | Use |
|---|---|
| [Closed computations](entries/closed-computations/README.md) | Proves constants, table entries, exports, and other closed facts by kernel evaluation. |
| [Large folds and compiled terms](entries/large-term-unfolding/README.md) | Controls reductions that cause recursion-depth errors, timeouts, or excessive memory use. |
| [Loops and builds](entries/loop-combinators/README.md) | Proves invariants for `LeanExe.loop` and element equations for `LeanExe.build`. |
| [Array folds by list induction](entries/array-fold-list-induction/README.md) | Proves that `xs.foldl step init` meets a specification stated by positions or lists, by induction on the array's list. |
| [Word identities](entries/word-bit-identities/README.md) | Relates shifts, masks, and packed words to bit-level specifications. |
| [Packed bytes](entries/packed-bytes/README.md) | Recovers a byte from an array that packs eight bytes into each word. |
| [Array layout across writes](entries/array-memory-framing/README.md) | Keeps `UInt64Array.At` and byte buffers across stores and memory growth, and proves loops that fill an array word by word. |
| [Write ranges](entries/memory-write-range/README.md) | Confines a sequence of stores to one interval of memory and keeps every other byte and field of the store. |
| [Binary64 error bounds](entries/float-error-tracking/README.md) | Propagates input and rounding errors through a chain of operations. |
| [Specification call theorems](entries/spec-call-theorem/README.md) | Combines a specification equality with generated execution and allocation theorems. |
| [Region frame of a call or a step](entries/region-frame/README.md) | Keeps the caller's arrays and trees across a call through the region clause, and composes the frames of steps. |
| [Explicit arguments before dependent proofs](entries/explicit-before-dependent-proof/README.md) | Avoids the unification failure of a proof argument about a value that a later argument fixes. |
| [File theorems](entries/file-theorems/README.md) | States that an emitted `.wasm` file holds the encoding of a module, through a file module outside the import graph. |
| [Closed-form allocation bounds](entries/verified-bound-closed-form/README.md) | Bounds the generated allocation term in input sizes or in counts of loop passes. |
| [Source forms and costs](entries/verified-source-costs/README.md) | Relates source choices to allocation, generated bounds, and compilation cost. |
| [Array literals, proposition tests, and structure patterns](entries/reflector-forms/README.md) | Explains the reflected code and allocation charges of these forms, and the structure patterns that the reflector reads and those it rejects. |
| [Representations of structures and enumerations](entries/flat-instances/README.md) | Describes the `Flat` instances that the reflector needs for user types, and where a port of a LeanExe program puts them. |
| [Tail-termination cases](entries/tail-termination-cases/README.md) | Diagnoses remaining functional-induction cases in a tail-loop proof. |
| [Mutual execution induction](entries/mutual-relation-induction/README.md) | Proves statements over mutually inductive WASI or Clight executions. |
| [Partial loop correctness](entries/partial-wasm-loop/README.md) | States the result of a completed Wasm loop while its termination proof remains separate. |
| [Calls with operands below the arguments](entries/direct-call-stack-tail/README.md) | Extends a callee's theorem on its arguments to a call with more operands on the stack. |
| [Raw Wasm locals](entries/local-frame-projection/README.md) | Proves equalities of `Wasm.Locals` and reads parameters and locals in proofs of hand-written code. |
| [WASI host premises](entries/wasi-host-premise/README.md) | Identifies the satisfying-host premise needed to apply an execution theorem. |
| [WASI effect charges](entries/wasi-effect-charges/README.md) | Bounds allocation over complete command runs and their prefixes. |
| [WASI process totality](entries/wasi-process-total/README.md) | Combines progress, resource bounds, and accepted exit for an unbounded process. |
| [Line-oriented processes](entries/stream-fold/README.md) | Instantiates the shared line reader and output proof with an application kernel. |
| [Verified WGSL kernels](entries/verified-wgsl-kernel/README.md) | Proves dispatch of an accepted outer array build. |
| [Native theorem conclusions](entries/native-conclusion-patterns/README.md) | Extracts result, heap, region, and postcondition facts from a native call theorem. |
| [Clight determinism](entries/clight-determinism/README.md) | Compares two execution derivations and carries a proved result to every matching execution. |

## Admission and growth

Every proof task ends with proposals for new entries or changes to existing ones, in the form of the template, as [the repository instructions](../AGENTS.md#verification-knowledge-base) require.  A reviewer admits a proposal when its guidance applies beyond the task, its declarations exist, and no entry already covers it.  Otherwise the reviewer merges it into an existing entry or declines it with a reason.

The VKB has no fixed list of categories.  A prover finds an entry by the declarations and goals it names, so the scope grows with the work.  Entries that the work no longer needs leave only when they are wrong, stale, or duplicated without a distinct lesson.

## Check

[`Check.lean`](Check.lean) imports the modules that the entries list.  It reports every listed declaration or example that does not exist and every entry whose directory name differs from its `id`.  Run it from the repository root:

```sh
tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean VKB/entries
```

The check catches renamed and removed declarations, but not guidance that a change to the compiler or the library has made wrong.  After such a change, reread the entries that name the changed declarations.  A module that reads a file at elaboration, such as a file-theorem module, does not belong in `modules`, because the check would then depend on emitted files.

## Relation to LTG

[LTG](../ltg/README.md) serves the per-program proofs of the LeanExe compiler, whose hints name its rule lemmas.  The VKB serves programs of the verified compiler, which needs no per-program correctness proof.  The entries on array layout, write ranges, raw locals, calls with operands below the arguments, and region frames restate LTG's general entries of the same names without the LeanExe compiler's rules, and they name no declaration of `LeanExe/Compiler/` or `LeanExe/IR/`.
