# Exact checked grid-scan execution work

This explicitly incomplete source case prepares the exact maximum-speed
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
projections. This source factoring leaves the separate 11,222-byte grid-step
binary unchanged. [Indexing.lean](Indexing.lean) proves read bounds and
checked offset arithmetic. [Iteration.lean](Iteration.lean) proves exact
execution of the named scan body for every valid grid index, arbitrary seed
speed and array-capacity word, with three exact input loads, the checked-side
call, both status/max branches, and complete store preservation. It composes
with any module satisfying the shared layout and uses only standard logical
axioms. Whole-scan loop termination and result correspondence, execution
safety and frozen-byte verification remain open.
There is no completed behavioral specification or frozen package yet.
