# Artifact Proof Kit

Every `leanexegen` artifact-proof task receives this catalog and may import the modules below.  Each declaration is ordinary checked Lean, and the verifier includes the module sources in the proof-kit identity.  A generated proof should import the smallest module set that matches its artifact.

| Module | Checked support |
|---|---|
| `Project.ProofKit.Annotation` | Structured instruction-path resolution and exact half-open regions over a decoded Talos program. |
| `Project.ProofKit.Memory` | Word-read congruence, disjoint read-over-write facts, and the `word_reads` tactic for nested `write64` expressions. |
| `Project.ProofKit.Array` | The public `Array UInt64` representation, encoded-size and address normalization, load bounds, region preservation, and singleton or pair output construction. |
| `Project.ProofKit.Allocation` | Fixed-array bump-allocation addresses, header offsets, overflow exclusion, and the no-growth branch. |
| `Project.ProofKit.FixedArrayAllocator` | Complete empty-list search and bump-allocation semantics for the emitted one-parameter array-wrapper layout. |
| `Project.ProofKit.FixedArrayAllocatorWindow` | The fixed-array allocator semantics parameterized by a uniform shift of its combined-local operands. |
| `Project.ProofKit.FixedArrayEqNode` | One indexed array load, equality normalization, and two-way branch for an unrolled search. |
| `Project.ProofKit.FixedArrayInput` | The standard length-guarded indexed input loader parameterized by a uniform local-window shift. |
| `Project.ProofKit.FixedArrayLengthDispatch` | The standard fixed-array length comparison, Boolean normalization, and valid or invalid branch. |
| `Project.ProofKit.FixedArrayLtNode` | One key-first indexed array load, unsigned less-than comparison, and two-way branch for an unrolled search tree. |
| `Project.ProofKit.FixedArrayPairResult` | Complete allocation and two-word result semantics for the emitted twenty-four-local wrapper. |
| `Project.ProofKit.FixedArrayResult` | Continuation-generic length and payload stores plus singleton and pair representation theorems. |
| `Project.ProofKit.FixedArraySearch` | Nested search-branch composition for standard pair results. |
| `Project.ProofKit.FixedArraySingleton` | Complete allocation and singleton `Array UInt64` result semantics for the emitted one-parameter array-wrapper layout. |
| `Project.ProofKit.FixedArrayTraversalInput` | The checked indexed loader that leaves a traversal value on the operand stack. |
| `Project.ProofKit.Control` | Function entry, block-wrapped loop entry, and one-call wrapper tactics. |

## `Array UInt64` representations

`Project.ProofKit.UInt64Array.At` has the same definition as the generated `FormalSpec.UInt64ArrayAt` predicate.  A proof can change either a hypothesis or a goal to the shared predicate without adding an assumption.  Its projection lemmas expose the header read, an indexed element read, and the corresponding WebAssembly load bounds.

```lean
import Project.ProofKit.Array

change Project.ProofKit.UInt64Array.At initial inputPtr input at hArray
have hLength := hArray.lengthRead
have hLengthBound := hArray.lengthBound
have hInputAddress := hArray.pointerAddress_eq
have hSizeEncode := hArray.encodedSize_eq_one
have hValue := hArray.elementRead 0 hSingletonIndex
have hValueBound := hArray.elementBound 0 hSingletonIndex
have hValueAddress := hArray.elementAddress_eq 0 hSingletonIndex
have hGeneratedLengthBound := hArray.generatedLengthBound
have hGeneratedElement := hArray.generatedElement 0 hSingletonIndex
have hFirstRead := hArray.firstElementRead_add hSingletonIndex
```

`generatedLengthBound` and `generatedElement` expose the modulo-address forms produced by Talos symbolic execution of the emitted loader.  The element theorem returns both the checked eight-byte bound and the exact memory read for any logical index.  `firstElementRead_add` supplies the direct `ptr.toUInt32 + 8` read used when the wrapper first loads its query word.

Use `At.frameBefore` when the artifact writes only at or above a cutoff after reading its input.  The theorem needs the complete represented input below that cutoff, unchanged page count, and byte equality below the cutoff.  `At.write64After` handles one word write and can preserve the predicate through a short sequence of stores.

```lean
have hArrayFinal := hArray.frameBefore hInputBelowHeap hPages hBytesBeforeHeap
```

Use `uint64_array_singleton` or `uint64_array_pair` after changing a generated output goal to `Project.ProofKit.UInt64Array.At`.  The tactics reduce the representation goal to region bounds and the required header or payload reads.  `word_reads` then resolves nested word writes when their address separation follows from arithmetic facts already in the context.

```lean
change Project.ProofKit.UInt64Array.At final outputPtr #[value]
uint64_array_singleton
· omega
· omega
· word_reads
· word_reads
```

```lean
change Project.ProofKit.UInt64Array.At final outputPtr #[value, found]
uint64_array_pair
· omega
· omega
· word_reads
· word_reads
· word_reads
```

## Fixed-array bump allocation

Import `Project.ProofKit.Allocation` when the reachable program contains LeanExe's fixed-array allocator.  The current `RuntimeReady` precondition fixes an empty free list and supplies enough existing memory, so `bumpFacts` packages the arithmetic for the bump and no-growth path.  Its fields cover the 48-byte header root, the post-allocation top, unsigned-overflow exclusion, the page comparison, and all five header subtraction addresses.

```lean
import Project.ProofKit.Allocation

have hBump := Project.ProofKit.Allocation.bumpFacts
  heapTop capacity initial.mem.pages hFitMemory hPages
rw [hBump.rootToNat]
rw [if_neg (by simpa using hBump.noGrow)]
rcases hBump.headerOffsets with
  ⟨hsub40, hsub32, hsub24, hsub16, hsub8⟩
```

Use `BumpFacts.wordAddress` and `BumpFacts.wordAddress_toNat` for the returned array's length word and payload words.  The index counts words from the returned pointer, so word zero is the length and word one is the first element; the premise states that the complete word fits within the allocation capacity.  These theorems match the nested modulo expression emitted for a fixed-array payload store and avoid reconstructing its `UInt64` and `UInt32` normalization.

```lean
have hRootAddress := hBump.wordAddress 0 (by norm_num)
have hPayloadAddress := hBump.wordAddress 1 (by norm_num)
have hRootAddressNat := hBump.wordAddress_toNat 0 (by norm_num)
have hPayloadAddressNat := hBump.wordAddress_toNat 1 (by norm_num)
```

The projections `header40ToNat`, `header32ToNat`, `header24ToNat`, `header16ToNat`, and `header8ToNat` expose individual header addresses without destructuring `headerOffsets`.  `root_toNat`, `top_toNat`, `root_toUInt32`, `top_toUInt32`, `top_not_lt_base`, `headerOffsets`, and `bump_no_grow` remain available separately when a proof needs one fact.  Each statement depends on the fixed 48-byte LeanExe array header rather than a generated function or local-frame layout.

## Complete fixed-array allocator region

Import `Project.ProofKit.FixedArrayAllocator` when an emitted entry wrapper has one parameter, fourteen locals, the capacity in local 9, allocator temporaries in locals 10 through 14, and the returned root in local 5.  `region stride` starts with empty-free-list initialization after capacity normalization and ends after updating globals 0 and 2 and assigning the returned root.  `region_spec` proves that complete instruction region and continues from the named `allocStore` and `allocFrame` states.

The theorem takes the current capacity-local value, existing-memory fit, page limit, 32-bit-memory mode, empty free-list global, heap top, and allocation count.  A generated proof must first establish exact equality between its instruction suffix and `region stride`; definitional equality or a checked list decomposition suffices.  The theorem then removes the free-list loop, overflow branch, page-growth branch, six header stores, allocator-global updates, and root assignment from the case proof.

```lean
import Project.ProofKit.FixedArrayAllocator

change wp module_ (Project.ProofKit.FixedArrayAllocator.region stride ++ rest)
  Q initial frame env
apply Project.ProofKit.FixedArrayAllocator.region_spec
  module_ env initial frame heapTop capacity stride allocs
· exact hParams
· exact hLocals
· exact hValues
· exact hCapacityLocal
· omega
· exact hFitMemory
· exact hPages
· exact hMemory32
· exact hHeapTop
· exact hFreeList
· exact hAllocs
· exact hNext
```

## Shifted fixed-array allocator region

Import `Project.ProofKit.FixedArrayAllocatorWindow` when the same allocator instruction region appears after a uniform shift of its combined-local operands.  `region offset stride` uses combined locals `offset + 5`, `offset + 9`, and `offset + 10` through `offset + 14`; `region_spec` requires `offset + 14` internal locals and the capacity in internal local `offset + 8`.  Offset zero covers the fourteen-local wrapper, while offset ten covers the twenty-four-local wrappers in Demos 2 and 3.

The theorem produces `FixedArrayAllocator.allocStore` and `FixedArrayAllocatorWindow.allocFrame`, preserving the semantic memory and global-state definitions used by the canonical allocator theorem.  The caller proves an exact instruction-suffix equality before applying the theorem and supplies the shifted capacity-local fact.  The continuation receives the state after the allocator-global updates and the shifted returned-root assignment.

```lean
import Project.ProofKit.FixedArrayAllocatorWindow

change wp module_
  (Project.ProofKit.FixedArrayAllocatorWindow.region offset stride ++ rest)
  Q initial frame env
apply Project.ProofKit.FixedArrayAllocatorWindow.region_spec
  offset module_ env initial frame heapTop capacity stride allocs
· exact hParams
· exact hLocals
· exact hValues
· exact hCapacityLocal
· exact hCapacity
· exact hFitMemory
· exact hPages
· exact hMemory32
· exact hHeapTop
· exact hFreeList
· exact hAllocs
· exact hNext
```

## Indexed fixed-array input loader

Import `Project.ProofKit.FixedArrayInput` when the artifact copies its input pointer to combined local `offset + 9`, stores an encoded element index in `offset + 10`, and leaves the loaded value in `offset + 8`.  `program offset index` includes the emitted length load, unsigned index comparison, payload-address calculation, checked element load, and unreachable failure arm.  `program_spec` proves the complete region for any valid logical element and any following program or postcondition.

The theorem requires one input parameter, `offset + 14` internal locals, an empty operand stack, and a checked `UInt64Array.At` representation.  Its `resultFrame` records the input pointer, encoded index, and loaded value in the three internal local slots selected by the offset.  Offset ten matches the twenty-four-local wrappers used by Demos 2 and 3.

```lean
import Project.ProofKit.FixedArrayInput

change wp module_
  (Project.ProofKit.FixedArrayInput.program offset index ++ rest)
  Q st frame env
apply Project.ProofKit.FixedArrayInput.program_spec
  offset module_ env st frame inputPtr input index
· exact hParamsValue
· exact hLocals
· exact hValues
· exact hInput
· exact hIndex
· exact hNext
```

## Traversal input loader

Import `Project.ProofKit.FixedArrayTraversalInput` when an unrolled search loads an indexed input element for an immediate comparison.  `program offset index` stores the input pointer and encoded index in combined locals `offset + 5` and `offset + 6`, checks the index against the represented length, and leaves the loaded word on the operand stack.  `program_spec` proves that region for an arbitrary valid index and following program.

The result frame preserves the one input parameter, updates the two internal scratch locals, and sets the operand stack to the loaded `UInt64` value.  `program_stacked_spec` preserves an arbitrary operand-stack tail below that loaded value, supporting comparisons whose other operand was pushed before the load.  Offset ten matches the twenty-four-local search traversals in Demos 2 and 3, while `FixedArrayInput.program_spec` covers the result-wrapper region that stores the loaded word in combined local `offset + 8` and leaves an empty stack.

```lean
import Project.ProofKit.FixedArrayTraversalInput

change wp module_
  (Project.ProofKit.FixedArrayTraversalInput.program offset index ++ rest)
  Q st frame env
apply Project.ProofKit.FixedArrayTraversalInput.program_spec
  offset module_ env st frame inputPtr input index
· exact hParamsValue
· exact hLocals
· exact hValues
· exact hInput
· exact hIndex
· exact hNext
```

## Fixed-length dispatch

Import `Project.ProofKit.FixedArrayLengthDispatch` when a wrapper begins by storing its input pointer, reading the represented array length, comparing that length with a fixed size, and passing the result through emitted Boolean-normalization instructions.  `program inputLocal expectedSize invalidBranch validBranch` matches the normalized inequality encoding, while `eqProgram` matches the shorter normalized equality encoding.  `program_spec` and `eqProgram_spec` prove the length read, memory bound, encoded-size equivalence, normalization, and final branch selection for their respective encodings.

The valid and invalid premises use `FixedArrayEqNode.branchPost`, preserving the enclosing `if` behavior for fallthrough and break continuations.  `branchFrame` records the stored input pointer and empty operand stack at either branch entry.  Use `wp_fixed_array_length_dispatch inputLocal, expectedSize` for an inequality recipe and `wp_fixed_array_length_eq_dispatch inputLocal, expectedSize` for an equality recipe; both tactics infer the branch programs and remainder from the current goal.

```lean
import Project.ProofKit.FixedArrayLengthDispatch

wp_fixed_array_length_dispatch inputLocal, expectedSize
· exact hParams
· exact hValues
· exact hInputLocalPositive
· exact hInputLocalBound
· exact hExpectedSizeBound
· exact hInput
· intro hInvalidSize
  exact hInvalidBranch
· intro hValidSize
  exact hValidBranch
```

The equality tactic presents the same premises in the same order.  Its program boundary places the valid branch first in the final WebAssembly `if`, matching the compiler's equality encoding.  The checked annotation recipe identifies the encoding and names the corresponding tactic.

## Equality search node

Import `Project.ProofKit.FixedArrayEqNode` when an unrolled search node uses the traversal loader, compares its result with a saved `UInt64` key, normalizes the comparison through the emitted Boolean instructions, and enters one of two branches.  `program` and `program_spec` cover the loaded-first instruction order used by Demo 2, while `keyFirstProgram` and `keyFirstProgram_spec` cover Demo 3's key-first order through the stack-preserving loader theorem.  Both forms retain the artifact's branch programs and search order as parameters, proving the load, address bounds, comparison, Boolean normalization, and branch selection.

The branch obligations use `branchPost module_ env rest Q`, which implements the break and fallthrough behavior of the enclosing WebAssembly `if`.  The initial frame for either obligation is `branchFrame`, containing the traversal loader's scratch-local updates and an empty operand stack.  `wp_fixed_array_eq_node offset, index, keyLocal` handles loaded-first code, and `wp_fixed_array_key_eq_node offset, index, keyLocal` handles key-first code.  Each tactic infers the branch programs and remainder, leaving the semantic array and frame facts followed by the equal and unequal branch proofs.

`loadKeyProgram offset index keyLocal` covers the checked load that initializes a saved search key before the first comparison node.  Its theorem produces `keyFrame`, and `keyFrame_get_key` exposes the saved value through `Locals.get`.  `wp_fixed_array_search_key offset, index, keyLocal` infers the following search program and applies this theorem.

`SearchFrame offset keyLocal frame inputPtr key` records the four facts shared by every node: the input parameter, local-list length, empty operand stack, and saved key.  `SearchFrame.afterLoad` discharges a node's saved-key premise when the key local precedes the traversal scratch window, while `SearchFrame.branch` produces the same invariant for either branch frame.  These lemmas replace a program-specific frame predicate and its two preservation proofs.

`branchN module_ env count Q` represents `count` enclosing equality-node continuations without spelling out nested `branchPost` expressions.  Import `Project.ProofKit.FixedArraySearch` when those branches end in a standard pair result; `pairPost_branchN_conseq` composes `FixedArrayPairResult.pairPost` through the remaining count into the public pair-result continuation.  A compiler recipe orders the search-key and equality-node regions and supplies the exact offset, index, key local, and operand order for each tactic.

```lean
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArraySearch

wp_fixed_array_search_key 10, 0, keyLocal

wp_fixed_array_eq_node 10, index, keyLocal
· exact hParamsValue
· exact hLocals
· exact hValues
· exact hInput
· exact hIndex
· exact hKeyLocal
· intro hEqual
  exact hEqualBranch
· intro hUnequal
  exact hUnequalBranch
```

## Less-than search node

Import `Project.ProofKit.FixedArrayLtNode` when a search tree pushes its saved key, loads an indexed array element through the traversal loader, performs an unsigned less-than comparison, and selects two branch programs.  `program offset index keyLocal lessBranch notLessBranch` preserves both branch programs and the following continuation as parameters.  `program_spec` proves the checked load, memory bounds, comparison, and branch selection while retaining `FixedArrayEqNode.SearchFrame` across either child.

Use `wp_fixed_array_lt_node offset, index, keyLocal` after the preceding equality node has established inequality.  The tactic leaves separate obligations under `key < input[index]` and `¬ key < input[index]`, allowing the application proof to select the left or right subtree.  Checked recipes interleave equality and less-than nodes in their structured instruction order, so a proof follows the generated tree without reconstructing its traversal from the complete function.

```lean
import Project.ProofKit.FixedArrayLtNode

wp_fixed_array_lt_node 10, index, keyLocal
· exact hSearch
· exact hInput
· exact hIndex
· intro hLess
  exact hLessBranch
· intro hNotLess
  exact hNotLessBranch
```

## Complete pair-result wrapper

Import `Project.ProofKit.FixedArrayPairResult` when a twenty-four-local wrapper uses the offset-ten fixed-array allocator and returns two words.  `constResultProgram first second destination` covers a pair of computed constants, while `inputResultProgram index destination` reloads `input[index]` after allocation and returns `[input[index], 1]`.  Their semantic theorems finish at `pairPost`, which exposes the returned pointer and `UInt64Array.At` representation without referring to an application specification.

The input theorem transports the original array representation across the allocator header writes and output-length store before it invokes `FixedArrayInput.program_spec`.  Both theorems prove capacity normalization, empty-list allocation, result bounds, both payload stores, destination-local assignment, and the returned-root assignment.  `constResultProgram_result_spec` and `inputResultProgram_result_spec` compose those results with `pairPost_conseq`, producing the generic `resultContinuation` for a caller-supplied expected array.

`publicPost` states the returned-array condition for fallthrough and return continuations, while `fallthroughPost` and `resultContinuation` handle the generated local-14 return and surrounding block depths.  An artifact proof can use `publicPost (FormalSpec.expected input)` as its public assertion and prove one equality between the formal result and the pair at each semantic branch.  The composed theorem removes `pairPost` elimination when the current continuation already matches `resultContinuation`; forcing the entry proof into that shape can increase branch-discovery time.

```lean
import Project.ProofKit.FixedArrayPairResult

change wp module_
  (Project.ProofKit.FixedArrayPairResult.inputResultProgram index destination)
  (Project.ProofKit.FixedArrayPairResult.pairPost input[index] 1)
  initial frame env
exact Project.ProofKit.FixedArrayPairResult.inputResultProgram_result_spec
  module_ env initial frame heapTop allocs inputPtr input index destination
  hIndex expected hExpected hParamsValue hLocals hValues
  hDestinationPositive hDestination
  hInput hInputBelow hFitMemory hPages hMemory32
  hHeapTop hFreeList hAllocs
```

## Fixed-array result stores

Import `Project.ProofKit.FixedArrayResult` for the standard fixed-array length store and payload-address sequence.  `lengthStore_spec` and `payloadStore_spec` accept arbitrary combined-local indices, remaining programs, and postconditions, which lets an artifact proof place application-specific value computation between shared store proofs.  The definitions `writeLength` and `writePayload` name the resulting stores so later obligations do not expand a nested byte-write term.

`singletonStore_at` and `pairStore_at` reconstruct the public `UInt64Array.At` representation from those named memory transformers.  Their premises require the complete result region to fit in 32-bit address space and current memory.  The theorems cover arrays of one and two `UInt64` values without fixing an allocator layout or an application function.

```lean
import Project.ProofKit.FixedArrayResult

apply Project.ProofKit.FixedArrayResult.lengthStore_spec
  module_ env st frame root 2 rootLocal hValues hRoot hLengthBound
apply Project.ProofKit.FixedArrayResult.payloadStore_spec
  module_ env _ _ root first rootLocal scratchLocal 0
  hRoot hFirst hFirstBound
apply Project.ProofKit.FixedArrayResult.payloadStore_spec
  module_ env _ _ root second rootLocal scratchLocal 1
  hRoot hSecond hSecondBound

have hResult := Project.ProofKit.FixedArrayResult.pairStore_at
  st root first second hFit32 hFitMemory
```

## Complete singleton-array result region

Import `Project.ProofKit.FixedArraySingleton` when the fixed allocator region is followed by the standard singleton `Array UInt64` result suffix.  `resultSuffix` writes length one, moves the scalar value from combined local 2 through scratch local 8, writes it at the first payload word, and copies the returned root through combined locals 3 and 4.  `region_result_spec` proves the allocator and suffix together for any scalar result value and any following program.

The theorem requires the same one-parameter and fourteen-local layout as `FixedArrayAllocator.region_spec`, with capacity 16 in internal local 8 and the scalar result in internal local 1.  It constructs the two-word result memory, final local frame, and `UInt64Array.At` fact internally.  Its continuation receives that array fact, leaving the generated proof to relate the arbitrary scalar value to its formal specification and continue after the recognized instruction region.

```lean
import Project.ProofKit.FixedArraySingleton

change wp module_
  (Project.ProofKit.FixedArrayAllocator.region 1 ++
    Project.ProofKit.FixedArraySingleton.resultSuffix ++ rest)
  Q initial frame env
apply Project.ProofKit.FixedArraySingleton.region_result_spec
  module_ env initial frame heapTop allocs value
· exact hParams
· exact hLocals
· exact hValues
· exact hCapacityLocal
· exact hValueLocal
· exact hFitMemory
· exact hPages
· exact hMemory32
· exact hHeapTop
· exact hFreeList
· exact hAllocs
· intro hResultArray
  exact hNext hResultArray
```

## Function entry and loops

Import `Project.ProofKit.Control` when a theorem proves `Wasm.TerminatesWith` for a generated function definition that is definitionally equal to the selected module function.  The tactic `wp_entry functionDef as initial'` applies `Wasm.TerminatesWith.of_wp_entry` with `rfl` and introduces the initial local frame under the supplied name.  It leaves the function-body weakest-precondition goal visible.

```lean
import Project.ProofKit.Control

theorem example : Wasm.TerminatesWith env module_ index initial arguments post := by
  wp_entry Generated.funcDef as initial'
  unfold Generated.funcDef Generated.func
  wp_run
```

Use `wp_block_loop invariant inv decreasing measure` after symbolic execution reaches a WebAssembly `block` whose first instruction is a `loop`.  Use `wp_entry_to_loop functionDef unfolding functionBody as initial'` when function entry reaches that shape directly.  Both tactics leave the invariant, measure, preservation, decrease, and exit arguments in the generated proof.

```lean
theorem loop_correct : Wasm.TerminatesWith env module_ index initial arguments post := by
  wp_entry_to_loop Generated.func0Def
    unfolding Generated.func0
    as initial'
  apply Wasm.wp_loop_cons
    (Inv := loopInvariant initial' input)
    (μ := loopMeasure)
  · exact invariant_initial
  · exact invariant_preserved_and_measure_decreases
```

Use `wp_entry_single_call functionDef unfolding functionBody as initial' using callProof` when an entry function performs straight-line setup, calls one proved function, and returns its result.  The tactic applies `Wasm.wp_call_tw` to the supplied theorem and executes the return continuation.  Lean rejects the tactic when the generated control flow has another shape.

```lean
theorem wrapper_correct : Wasm.TerminatesWith env module_ index initial args post := by
  wp_entry_single_call Generated.funcDef
    unfolding Generated.func
    as initial'
    using callee_correct env initial' input
```
