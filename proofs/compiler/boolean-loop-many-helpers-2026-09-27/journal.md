# Multiple word arguments on helpers before Boolean loops

Helpers before Boolean-result loops now accept two or more UInt64 arguments and
return a word, optionally retaining standard Id result annotations. The binary
case uses a two-argument closure. Larger functions use the existing ManyFunction
shape, whose arity and parameter syntax are independently checked. Body checks
run even when the helper is unused.

The source constructors and totality arguments reuse the established word-loop
helper semantics. The extraction acceptance and correctness proofs preserve
argument order, arity and captured values for every loop state. List-based
matching supplies the larger closure proof, rather than a separate theorem per
arity. Existing unary equations explicitly exclude the binary arrow shape.
The source, extraction and invariant proofs pass on the first build, followed
by public extraction and WASM admission without changing lowering.

Ten native declarations pass 240 comparisons. They cover two, three and five
arguments, repeated calls, bounds, initialization, nested captures, public flags,
break/continue, stride, retained Id results and shadowing. Raw syntax tests pass
24,192 comparisons, 20,736 invalid-input checks and 1,728 unused-helper controls.
Each parameter has a distinct arithmetic weight so reversed arguments produce a
different result. Nested helpers transform each parameter separately. Tests also
vary binder forms, source annotations, public parameter order, loop forms and
Boolean tails. All new execution tests pass on the first attempt.

Selected preceding unary-helper, predicate-helper and input-annotation tests are
rerun. The complete compiler proof and native Lean/V8 checks follow this
candidate. Unit-prefixed helpers, loop-containing continuations, broader helper
and proposition bodies and full-dialect compiler correctness remain open.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1206 declarations.
