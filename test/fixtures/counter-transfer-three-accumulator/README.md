# Three-accumulator counter transfer

This fixture comes from compiling a scalar identity helper with remaining, result, and independent audit accumulators.  Its scalar post-test loop has 23 locals, returns accumulator slot two, and increments the audit accumulator by two on every nonzero iteration.  The annotation consumer must discover the remaining-and-result pair from checked transition semantics rather than assume a two-accumulator layout.
