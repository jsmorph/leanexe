# Artifact Proof Kit

Every `leanexegen` artifact-proof task receives this catalog and may import the modules below.  Each declaration is ordinary checked Lean, and the verifier includes the module sources in the proof-kit identity.  A generated proof should import the smallest module set that matches its artifact.

| Module | Checked support |
|---|---|
| `Project.ProofKit.Memory` | Word-read congruence, disjoint read-over-write facts, and the `word_reads` tactic for nested `write64` expressions. |
| `Project.ProofKit.Array` | The public `Array UInt64` representation, encoded-size and address normalization, load bounds, region preservation, and singleton or pair output construction. |
| `Project.ProofKit.Allocation` | Fixed-array bump-allocation addresses, header offsets, overflow exclusion, and the no-growth branch. |
| `Project.ProofKit.FixedArrayAllocator` | Complete empty-list search and bump-allocation semantics for the emitted one-parameter array-wrapper layout. |
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
```

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
