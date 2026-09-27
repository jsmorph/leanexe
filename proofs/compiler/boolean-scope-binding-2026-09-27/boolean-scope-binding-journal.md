# Scalar bindings around general Boolean scopes

Six new fixed probes reject, as does the unchanged word-let capture probe from
the retained Id helper-input increment. The corresponding bare-input capture
also rejects. The source grammar records exact ordinary-let syntax and a native
scalar domain certificate; it excludes the existing BooleanLocal grammar.

The first parser soundness proof split an unreduced Boolean input-kind choice.
Splitting that flag first fixes dependent elimination. Recognition and source
totality then pass 104 targets. The first extractor equations attempted simp over
proof-dependent matches; explicit match splits establish the equations instead.
The core extractor passes 139 targets. Existing dispatch paths are preserved;
the new binding cases are attempted only after those paths fail.

A diagnostic fun_induction True example exceeded its default heartbeat budget.
The existing generated induction theorem is available directly, so the diagnostic
was reduced to printing its type. Two unsupported pretty-printer options were
removed. The checked type has 103 cases: word binding at 63, final rejection at
64, and Boolean binding at 65. The source reconstruction proof follows that exact
case order, alongside evaluation, acceptance and generic IR invariant proofs.

The extraction reconstruction, acceptance, evaluation and generic IR invariant
proofs pass 140 targets on the first attempt after updating the checked induction
cases. Function integration and actual source probes are next.

Function integration passes 207 targets. All six fixed probes compile, and all
ten Id-input probes now compile, including the previously deferred capture.
Ten native fixtures pass 180 comparisons. The syntax matrix passes 16128
comparisons, 17280 invalid-input checks and 384 admission controls first try.
