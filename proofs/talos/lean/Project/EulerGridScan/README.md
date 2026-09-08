# Exact checked grid-scan execution

This completed source case proves the exact maximum-speed
scan from [EulerGridStep](../../../../../LeanExe/Examples/EulerGridStep.lean).
The [model bound](../EulerGridStep/Scan.lean) proves accepted state checks,
positive finite selected speed and decoded-real comparison with every
computed cell speed. [Program.lean](Program.lean) is the generated Talos
module. [Helpers.lean](Helpers.lean) proves by definitional equality that
functions 0–5 match the already proved conservative kernel and identifies
the named scan iteration at function 8 and exported scan at function 11.
The shared runtime functions at 12–15 are pinned by the runtime checks.

The prepared scan binary has 3,292 bytes and SHA-256
`279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9`.
The same 31 focused grid/scan tests pass. The named iteration reduces code
duplication; the compiler emits two compact loops for the two returned
projections. This scan factoring left the then-current 11,222-byte grid-step
binary unchanged; its later writer factoring is recorded in the
[grid-step checkpoint](../EulerGridStep/README.md). [Indexing.lean](Indexing.lean) proves read bounds and
checked offset arithmetic. [Iteration.lean](Iteration.lean) proves exact
execution of the named scan body for every valid grid index, arbitrary seed
speed and array-capacity word, with three exact input loads, the checked-side
call, both status/max branches, and complete store preservation. It composes
with any module satisfying the shared layout and uses only standard logical
axioms. [LoopModel.lean](LoopModel.lean) relates each iteration to the
remaining scan. [LoopShape.lean](LoopShape.lean) proves that both generated
loops have identical instructions. [LoopFrame.lean](LoopFrame.lean) records
the scratch slots and preserved first-result slot. [Loop.lean](Loop.lean)
proves termination, exact result correspondence and store preservation for
either loop under an arbitrary following continuation. Its measure counts
remaining cells and decreases on every continuing iteration.
[Execution.lean](Execution.lean) composes both loops with the exact header
guards and output projections. [Spec.lean](Spec.lean) proves total exact
execution for every logical input array fitting memory and attaches the
accepted speed certificate to those returned words. Empty arrays and arrays
whose lengths are not multiples of three return status one and zero speed.
Both public theorems use only propext, Classical.choice and Quot.sound.
The bound concerns checked computed speeds; it is not an exact-real Euler
wave-speed bound.

The [frozen package](../../../../artifacts/euler_grid_scan/279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9/manifest.json)
contains those exact 3,292 bytes. [ArtifactTranslation.lean](ArtifactTranslation.lean)
connects their decoded and validated module to this exact execution model.
The focused package gate checks embedded-byte equality, decoding, validation,
translation and both behavioral declarations with axiom audits. The existing
exact-byte native decision policy is unchanged; execution and safety use only
the three standard logical axioms. The separate full grid-step proof remains open.
