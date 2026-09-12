# Fuel and completion loop guard

`FuelGuard.program_spec` executes the seven-instruction prefix that tests
`fuel != 0 && done == 0` and exits the enclosing block when the test fails.
It accepts arbitrary combined-local indices, a module, a store, a frame,
and a continuation.  Fuel zero or a nonzero completion word produces
`Break 1`.  A positive fuel word and a zero completion word preserve the
store and frame before executing the remaining body.

`FuelGuard.zeroFuel_spec` needs only the fuel getter.  Zero fuel makes
the short-circuit guard skip the completion local, so the theorem also
covers frames without a valid completion local.

The while annotation matcher checks every guard instruction, both
short-circuit branches, the result type, and the branch depth.  It
generates `<region>_guard_eq` and `<region>_guard_tail_eq` against the
decoded program.  The recipe names these equalities and the shared
semantic theorem.  This support applies when the loop body includes
calls or memory operations and its scalar descriptor is absent.

Supply the fuel and completion getters from the application invariant.
The body theorem still establishes state preservation and measure
decrease.  The enclosing loop theorem handles termination and the
completed-state continuation.  `counter-transition` supplies the
nonzero UInt64 decrement fact when the body consumes one unit of fuel.

The Riemann retry and time-advance proofs use this guard at different
local layouts.  Generated equality also matches its initializer loop.
The complete Riemann artifact proof remains open.  This entry records
component reuse and has provisional status.

The retained order-book matcher uses the shared theorem for running,
completed, and zero-fuel guards.  Its current compiler output differs
from its retained artifact, so its new annotations failed matching.
This transfer uses the existing guard definition and proof model.
