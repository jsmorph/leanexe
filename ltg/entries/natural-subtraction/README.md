# Saturating natural subtraction

`NatSub.program_spec` covers `emitNatSub` after operand staging.  The
unsigned comparison selects zero when the right operand exceeds the
left.  Otherwise, the unsigned subtraction equals the encoded natural
difference.  No product bound or nonzero premise is required.

The first local read changes the operand stack.  Use
`Frame.withValues_get` to rewrite the next read through the original
frame's getter.  The first proof draft supplied an unfolded getter at
this boundary and failed.  A focused trace identified the changed
frame, and the existing frame theorem closed the proof in two seconds.

Riemann's common initial-difference theorem composes multiplication,
division or remainder, and subtraction for both coordinates.  Its exact
region checks and execution theorem pass with standard axioms.  The
entry remains provisional.  A separate-artifact consumer and complete
Riemann artifact verification remain open.
