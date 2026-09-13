# Checked lookup for embedded binary literals

Closed parser proofs can exceed the kernel's computation limit when
each byte read reduces an indexed lookup through a long list literal.
Lean's checked `cbv` evaluator creates proof terms for those computations.
Dividing a parser proof at function or instruction-sequence boundaries
limits each certificate, but repeated literal lookup can still dominate
checking.

The kernel mode of the [artifact generator](../../../tools/artifact-migrate.js)
emits a balanced list-concatenation representation with leaves of at most
256 bytes.  A reflexive equality checks the complete list against the
embedded array.  `List.getElem?_append` then proves each internal lookup
step, and a universal theorem equates the original array lookup with the
generated representation.  These equalities include out-of-range indices.

During `cbv`, the byte-array and array constants remain opaque.  Checked
data-projection and size equalities expose their required observations.
Each internal list node also remains opaque, with a `cbv_eval` lookup
theorem selecting its child.  The decoder definition, parser cursor,
returned value, and byte contents remain the subjects of the proof.

The Riemann artifact has 21,767 bytes.  A proof starting at instruction
333 of its largest function failed at the kernel limit after 108 seconds.
Keeping the byte-array constant shared still failed after 112 seconds.
The same statement passed with the lookup equalities and its original
heartbeat allowance.  The final 14-instruction suffix also passed, and
its compiled proof module decreased from 8,857,744 to 4,678,256 bytes.
All accepted lookup and suffix theorems used only `propext`.

Suffix reuse requires a separate dependency check.  The first registered
suffix equations were absent from the accepted proof's dependencies.
`cbv` processed `instructionSequence fuel allowElse` before applying
its cursor.  The [parser evaluation support](../../../proofs/talos/lean/Project/Artifact/Binary/Evaluate.lean)
adds a definitionally equal form with an explicit cursor parameter and
an `Except` result type.  Its eta equality preserves the original
parser, and a proof-producing simproc tries closed sequence equations
before the generic step equation.  The corrected consumer's dependency
audit confirms use of the earlier suffix and byte-lookup theorems.

The complete largest-function check still timed out after its sequence
proof passed.  `code_eq_of_parts` now composes the size-prefix result,
local declarations, explicit-cursor sequence theorem, and bounds.  The
[full function theorem](../../../proofs/talos/lean/Project/EulerRiemann/ArtifactCode99.lean)
passed with only `propext`, and its dependency audit confirms the earlier
sequence and byte-lookup certificates.  An array-size observation covers
the implicitly reducible `ByteArray.size` projection while keeping the
embedded array opaque to evaluation.

Large structured instructions require internal sequence boundaries.
The [offset utility](../../../proofs/talos/lean/Project/Artifact/Binary/CodeOffsets.lean)
uses the normative decoder to record nested cursors, fuel, terminators,
and paths into the cached instruction tree.  The
[nested-function example](../../../proofs/talos/lean/Project/EulerRiemann/ArtifactCode95.lean)
checks eighteen sequence certificates and its complete code result.
Its dependency audit confirms reuse across five nesting levels.
[Parser composition lemmas](../../../proofs/talos/lean/Project/Artifact/Binary/CodeParts.lean)
combine vector items, length prefixes, and bounded payloads.  The
metadata selects proof statements, while the kernel checks their equality
to the original decoder applications.

The [complete code section](../../../proofs/talos/lean/Project/EulerRiemann/ArtifactCodeVector.lean)
composes all 108 body results through `vectorLoop_eq_cons`, then checks
the item-count and byte-count prefixes.  Its axiom audit reports only
`propext`.

The other vector sections use individual entry certificates and the same
vector and bounded-parser lemmas.  The complete type-section evaluation
timed out before this decomposition passed.  Generic
[section-result lemmas](../../../proofs/talos/lean/Project/Artifact/Binary/SectionParts.lean)
preserve an already checked payload result when updating a raw module.
The [complete binary decoder](../../../proofs/talos/lean/Project/EulerRiemann/ArtifactParsed.lean)
then composes the six sections and header.  Its audit contains only the
three accepted logical axioms.  Supplying section-loop fuel explicitly
and replacing concrete simplification with the generic result lemma
resolved a separate composition timeout.  That iteration changed both
factors and does not distinguish their contributions.  Complete Riemann
validation also passes with checked cbv and only propext.  Translation
equality and explicit transfer of the complete behavioral specifications
to the frozen bytes pass with the accepted logical axioms.

The [checked lookup module](../../../proofs/talos/lean/Project/EulerRiemann/ArtifactByteLookup.lean)
and [suffix consumer](../../../proofs/talos/lean/Project/EulerRiemann/ArtifactCode99Part333.lean)
record the application.  Complete Riemann artifact verification and a
held-out measurement remain open.  This entry records a provisional
proof-generation method and does not import the Riemann declarations
into later proof tasks.
