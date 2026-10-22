# Integer ceiling square root

[The native function](Program.lean), `ceilSqrt`, performs 17 bracket halvings using `UInt64`.
[The mathematical proof](Proof.lean), `Sqrt.ceilSqrt_correct`, proves the least integer whose square
is at least the input, for inputs at most `2^32`.  [The compiled module](Compiled.lean) proves
execution of the definition under the verified compiler's premises.

The [drone planner](../../../../Demos/Drone/README.md) uses this bounded operation for its distance
calculation.  Inputs beyond the theorem's domain retain the function's defined word behavior.
