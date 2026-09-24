# Exact checked grid-scan execution

This completed source case proves the exact maximum-speed
scan from [EulerGridStep](../../../../../LeanExe/Examples/EulerGridStep.lean).
The [model bound](../EulerGridStep/Scan.lean) proves accepted state checks,
positive finite selected speed and decoded-real comparison with every
computed cell speed.  [Generated program](Program.lean) is the generated Talos
module.  [Helper correspondence](Helpers.lean) proves by definitional equality that
functions 0–5 match the already proved conservative kernel and identifies
the named scan iteration at function 8 and exported scan at function 11.
The shared runtime functions at 12–15 are pinned by the runtime checks.

The current generated scan binary has 3,012 bytes and SHA-256
`2e5425802b6d1ae06283751c99f5737093016facfdd90a6eb56dbc6ef9a33373`.
The compiler computes both returned projections in one traversal.
[Index bounds](Indexing.lean) proves read bounds and
checked offset arithmetic.  [Scan iteration](Iteration.lean) proves exact
execution of the named scan body for every valid grid index, arbitrary seed
speed and array-capacity word, with three exact input loads, the checked-side
call, both status/max branches, and complete store preservation.  It composes
with any module satisfying the shared layout and uses only standard logical
axioms.  [Scan model](LoopModel.lean) relates each iteration to the
remaining scan.  [Loop shape](LoopShape.lean) identifies the generated
loop instructions.  [Loop frame](LoopFrame.lean) records
the scratch slots and preserved caller local.  [Loop proof](Loop.lean)
proves termination, exact result correspondence and store preservation for
the loop under an arbitrary following continuation.  Its measure counts
remaining cells and decreases on every continuing iteration.
[Entry execution](Execution.lean) composes the loop with the exact header
guards and output projections.  [Public specification](Spec.lean) proves total exact
execution for every logical input array fitting memory and attaches the
accepted speed certificate to those returned words.  Empty arrays and arrays
whose lengths are not multiples of three return status one and zero speed.
Both public theorems use only propext, Classical.choice and Quot.sound.
The bound concerns checked computed speeds; it is not an exact-real Euler
wave-speed bound.

The [frozen package](../../../../artifacts/euler_grid_scan/279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9/manifest.json)
contains the historical 3,292-byte binary.  [Artifact translation](ArtifactTranslation.lean)
connects its decoded and validated module to the preserved frozen execution
model.  Its `FrozenProgram` and `FrozenSpec` dependency closure retain the
historical two-traversal algorithm.
The focused package gate checks embedded-byte equality, decoding, validation,
translation and both behavioral declarations with axiom audits.  The existing
exact-byte native decision policy is unchanged; execution and safety use only
the three standard logical axioms.  The [grid-step proof](../EulerGridStep/README.md) covers the separate update entry.
