# Inclusion proofs for interval programs

This entry applies to a dialect program that computes with `Library.Numerics.Interval` and to a
theorem that its accepted result contains a real quantity, stated with
`Library.Numerics.Interval.Contains`.  It also applies to a real bound on a library function's
result from an accuracy theorem of the form `LeanExe.ProofKit.F64SignedRounding.WithinSteps`, and
to a sum over panels that encloses an integral.

Work backward from the acceptance of the final result and then forward with the inclusions.  Each
theorem of the layer, such as `Library.Numerics.Interval.add_sound`,
`Library.Numerics.Interval.mul_sound`, `Library.Numerics.Interval.div_sound`,
`Library.Numerics.Interval.sqrt_sound`, and `Library.Numerics.Interval.clamp_sound`, takes the
hypothesis that its result has status zero and gives the acceptance of the operands with the
inclusion for every real point of them, so one `obtain` for each operation of the program, from
the outermost inward, yields every status, and the inclusions then compose in the order of
evaluation.  `Library.Numerics.Interval.div_sound` also gives that the divisor's point is not
zero, and `Library.Numerics.Interval.sqrt_sound` that the operand's point is not negative, which
supply facts such as a positive variance.  For a monotone library function, apply
`Library.Numerics.Interval.increasing_sound` or `Library.Numerics.Interval.decreasing_sound` with
the function's accuracy theorem at the two endpoints.  `Library.Numerics.Interval.Steps.two_up`
and `Library.Numerics.Interval.Steps.two_down` give the real bounds, from
`Library.Numerics.Interval.Steps.upper_of_position` and
`Library.Numerics.Interval.Steps.position_nextUp`, and
`LeanExe.ProofKit.F64SignedRounding.within_of_nonneg` converts the statement of `exp`, which uses
the nonnegative reference.  For a loop that adds panels, apply `LeanExe.Dialect.loop_induction`
with the invariant that an accepted sum of the first `k` panels contains the integral from the
first partition point to point `k`, and bound each panel with
`Demos.Conjunction.Model.integral_eq_width_mul`.

Three approaches fail.  An accuracy hypothesis stated for every endpoint cannot be discharged,
since the finiteness of an interval's endpoints follows only from a contained point, so
`Library.Numerics.Interval.increasing_sound` takes the accuracy under the hypothesis that the
endpoint is finite.  In a rejected branch, `simp only` with a hypothesis `¬ c = true` on a Boolean
condition leaves `if false = true`, and the branch closes only with `Bool.false_eq_true` in the
simp set, as `Library.Numerics.Interval.join_accepted` shows.  A product of two intervals whose
lower endpoints are zero has a lower endpoint one step below zero after outward rounding, so a
result that must not be negative needs `Library.Numerics.Interval.clamp_sound` with a proof that
the real quantity is not negative, such as `Demos.Conjunction.Model.pc_nonneg`.

`Demos.Conjunction.expI_sound` applies the monotone enclosure to `exp`,
`Demos.Conjunction.erfSumI_sound` chains the operations of the sum and derives a positive conditional
variance from an accepted division, `Demos.Conjunction.panel_sound` bounds one panel,
`Demos.Conjunction.panels_sound` is the loop induction, and `Demos.Conjunction.pc_enclosure`
combines them.
