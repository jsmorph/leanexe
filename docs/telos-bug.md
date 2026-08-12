# Talos Imported-Memory Instance Defect

This report records the defect first observed on 2026-08-02 and reproduced by the release gate on 2026-08-03.  The defect remains open in the pinned Talos dependency.  The current no-import artifact profile does not exercise it.

## Finding and Ownership

The implementation defect belongs to the pinned Talos repository, not to LeanExe's compiler, binary decoder, validator, artifact packages, or proof driver.  LeanExe obtains `CodeLib` from `https://github.com/cajal-technologies/talos` at revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`, as recorded by the [Talos dependency declaration](../proofs/talos/lean/lakefile.toml) and [conformance configuration](../proofs/talos/conformance.json).  The local dependency checkout is clean, so no LeanExe working-tree edit introduced the behavior.

Talos upstream commit [`07fe17b`](https://github.com/cajal-technologies/talos/commit/07fe17bba53861e7f21459d8eff325c4ab1037c9) added cross-module imports using snapshot semantics.  The commit and source state that imported globals, tables, and memories are copied into the importing instance, while imported functions close over an exporting-store snapshot.  The source also states that mutations through an import remain local and identifies shared-state linking as unsupported.

LeanExe owns the assurance consequence because this repository pins Talos, treats its semantics as a trusted component, and publishes claims based on it.  A release must qualify Talos fidelity, retain the failing comparison, and decide whether to wait for an upstream repair, maintain a pinned fork, or keep imports outside the verified profile.  The code defect is upstream.  The dependency and claim boundary are this project's responsibility.

## Reproduction

The repository command verifies the CodeLib and official testsuite revisions, checks `wasm-tools` 1.251.0 and Wasmtime 44.0.0, builds the Talos testsuite executable, and runs twenty-five exact official files.  The 2026-08-12 run produced 3,853 Talos passes, six known assertion failures, and 627 skipped commands, with no cascades, decoder errors, interpreter errors, or fuel exhaustion.  Wasmtime passed all twenty-five files with `function-references=y`.

```sh
tools/artifact-conformance.js check
```

All six failures occur in the official [`memory_grow.wast`](https://github.com/WebAssembly/testsuite/blob/9233a0a8d5920a8d32358ee915a3662ff3385029/memory_grow.wast) file.  Talos reports one incorrect growth followed by five observations of the resulting incorrect page count.  The gate accepts only these exact rows as a warning, removes the warning when no row remains, and rejects a changed, partial, or additional failure set.

```text
L49  expected [i32:-1], got [i32:5]
L50  expected [i32:5],  got [i32:6]
L56  expected [i32:5],  got [i32:6]
L62  expected [i32:5],  got [i32:6]
L68  expected [i32:5],  got [i32:6]
L75  expected [i32:5],  got [i32:6]
```

## Required WebAssembly Behavior

The first module defines and exports `mem1` with a minimum of two pages and a maximum of five.  The second module imports that memory through a declaration with minimum one and maximum six.  The provided `2 5` memory type satisfies the requested `1 6` import type because its permitted range is narrower, but importing it does not replace its five-page maximum.

The test grows the memory from two pages to three, then from three pages to five.  A further one-page growth must return `-1` and leave the memory at five pages.  Later assertions repeat the five-page observation after operations on other memories, which accounts for the five secondary failures.

The [WebAssembly matching rules](https://webassembly.github.io/spec/core/valid/matching.html) define compatibility between the provided and requested memory types.  The [runtime structure](https://webassembly.github.io/spec/core/exec/runtime.html) places memory instances in one shared store and gives module instances memory addresses that refer to those instances.  An import therefore receives the exported address and observes the same memory type, contents, page count, and later mutations.

## Talos Execution Path

Talos represents `Mem` with only `pages : Nat` and `bytes : Nat → UInt8`.  [`Mem.empty`](https://github.com/cajal-technologies/talos/blob/bb3277e21c9786e3133d5c1601e34ebdc0bea4df/interpreter/Interpreter/Wasm/Mem.lean#L22-L35) records neither the memory's maximum nor its runtime identity.  [`Mem.grow`](https://github.com/cajal-technologies/talos/blob/bb3277e21c9786e3133d5c1601e34ebdc0bea4df/interpreter/Interpreter/Wasm/Mem.lean#L141-L149) consequently accepts a separate `cap` argument.

At instantiation, the Talos testsuite harness copies the exporting module's `Mem` value into the importing module's local store.  The copy carries the current page count and byte function but cannot carry the exported five-page maximum because `Mem` has no such field.  The importer retains its static `1 6` declaration in its own `Module` value.

During `memory.grow`, [`execOne`](https://github.com/cajal-technologies/talos/blob/bb3277e21c9786e3133d5c1601e34ebdc0bea4df/interpreter/Interpreter/Wasm/Semantics.lean#L1560-L1588) calls `st.mem.grow delta m.memoryCap`.  `m.memoryCap` reads the executing module's declaration, which supplies six in the importer.  Talos therefore accepts growth from five pages to six and returns the previous size, five, where WebAssembly requires failure.

## Root Cause and Additional Exposure

The immediate root cause is a confusion between a static import declaration and a runtime memory instance.  The import declaration describes the range of external memories acceptable during instantiation, while the runtime instance retains the type and limit with which it was allocated.  Talos discards that distinction by storing the memory value in one module-local store and obtaining its limit from another module-local declaration.

The deeper defect is the absence of shared runtime identity for imported entities.  [`applyEntityImports`](https://github.com/cajal-technologies/talos/blob/bb3277e21c9786e3133d5c1601e34ebdc0bea4df/interpreter/Interpreter/Testsuite/Exec.lean#L459-L510) copies globals, tables, and memories, and the [cross-module resolution code](https://github.com/cajal-technologies/talos/blob/bb3277e21c9786e3133d5c1601e34ebdc0bea4df/interpreter/Interpreter/Testsuite/Exec.lean#L398-L450) captures exporting-store snapshots for imported functions.  This representation can also make writes, table changes, mutable-global updates, growth, and imported-function state diverge between an exporter and importer.

The selected test exposes only the lost memory maximum.  Adding a maximum to `Mem` would cause a copied memory to retain five and would repair these six assertions.  It would leave the copies independent, so it would not implement general WebAssembly linking semantics.

## Effect on LeanExe Artifact Verification

The current artifact profile rejects imports, tables, and multiple memories.  Each of the twenty frozen artifacts executes as one closed module whose static memory declaration and runtime memory correspond directly.  Under those conditions, Talos obtains the same limit from the module declaration that a memory-instance field would contain.

The defect therefore does not change the byte-identity, decoder-soundness, validator-soundness, exact-translation, or behavioral theorems already proved for those artifacts.  Those theorems continue to state behavior under the pinned Talos semantics, and their subjects contain no imported entity that can trigger the defect.  The failure limits the empirical evidence that connects Talos to general WebAssembly execution and blocks artifact claims for modules with imports.

The official `memory_grow.wast` file combines local memories with imported and multiple memories.  Its 45 passing Talos assertions supply useful evidence, while the six import-related failures lie outside the current artifact profile.  Release records must preserve both facts rather than reporting the entire file as either conforming or irrelevant.

## Repair Boundary

A narrow repair adds the effective maximum to each `Mem` instance, initializes it from the defining memory declaration, preserves it across imports, and makes the interpreter and weakest-precondition rules consult it.  That repair addresses the observed capacity error and forms part of a faithful memory-instance representation.  Its acceptance must state that shared mutation across module instances remains unsupported.

A complete repair introduces a shared runtime store containing addressable function, table, memory, and global instances.  A module instance maps its local indices to addresses in that store, imports reuse exported addresses, and invocation threads changes through the shared store.  This design follows the WebAssembly runtime structure and covers memory identity, mutation visibility, imported-function state, and the analogous table and global cases.

The existing twenty proofs can retain a compact closed-module interface if Talos supplies an embedding of closed modules into the shared runtime and proves an execution-equivalence theorem for modules without imports.  That separation preserves the current proof investment while giving conformance tests and future imported artifacts the general semantics.  Implementing the shared model in a maintained fork would require a new immutable Talos revision, proof updates, a complete artifact-gate rerun, and broader official linking tests before release.

## Disposition

The repository keeps the six-failure conformance result reproducible and visible through a machine-checked warning fingerprint.  An upstream issue should cite the pinned revision, upstream import commit, official test lines, Wasmtime comparison, and distinction between the capacity error and snapshot sharing.  Until an upstream or forked repair passes the relevant linking corpus, LeanExe's artifact claim should continue to exclude imports and describe Talos fidelity as profile-specific empirical evidence.
