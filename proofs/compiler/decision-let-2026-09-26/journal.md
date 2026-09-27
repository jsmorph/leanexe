# Let reduction in junction decision arguments

The prior proposition-let checks found a native condition whose conjunction
instance used True and False where the condition retained unused lets. This
increment leaves the runtime guard unchanged and introduces GuardCondition,
an independent source relation for retaining a proposition or reducing a prefix
of its leading lets. Its finite condition list and both directions of membership
are proved. Recursion follows the parsed guard; substituted expressions do not
need a new termination argument.

Junction decisions record each admitted condition argument and recursively
checked child evidence. Saved Boolean leaves retain exact conditions; the
opposite proposition may reduce its leading lets. The recognizer reconstructs
the entire standard connective and all outer negation wrappers after reading
four arguments. A first draft tried a global DecidableEq Expr membership instance;
the existing checked ExprEquality.same is used explicitly instead. The soundness
proof then needed the concrete accepted Boolean hypothesis before simplification.
Source membership, decision acceptance/soundness and guard parser proofs pass.
Scalar and loop proof integration and native tests are in progress.

Scalar extraction, whole-function correctness, loop-step and loop-exit invariant
checks pass. All ten new native examples pass 180 comparisons, including the
previously rejected unused-let conjunction. The raw matrix passes 96,768
comparisons, 50,720 rejections and 2,336 controls across canonical, partially
reduced and fully reduced argument pairs, saved-Boolean junction sides,
negation, Id annotations, ordinary/dependent choices and decide. Explicit tests
first accept reduced decision evidence and then reject unsupported unused bound
values. The 21 prior test files pass 103,336 comparisons, 63,969 rejections and
2,368 controls. Full theorem, axiom and native/V8 checks follow the candidate.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1026 declarations.
