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

An accuracy hypothesis stated for every endpoint cannot be discharged, since the finiteness of an
interval's endpoints follows only from a contained point, so
`Library.Numerics.Interval.increasing_sound` takes the accuracy under the hypothesis that the
endpoint is finite.  In a rejected branch, `simp only` with a hypothesis `¬ c = true` on a Boolean
condition leaves `if false = true`, and the branch closes only with `Bool.false_eq_true` in the
simp set, as `Library.Numerics.Interval.join_accepted` shows.
Outward rounding moves every rounded endpoint one step outward, an exact 0 included.
`Library.Numerics.Bounds.endpoint` takes the next word below a lower end, so
`mul (point 0) (point 0.5)`, `div (point 0) (point 3)`, and `sq (point 0)` have the lower end
`-5e-324`, and `Library.Numerics.Interval.sq` of an interval that holds 0 has the same lower end,
where `mul` of the interval with itself has the negative product of its endpoints.
`Library.Numerics.Bounds.outSqrt` accepts a lower end only when it is not negative or is `-0`, so
`sqrt` rejects each of these intervals and their sums, such as `sqrt (add (sq a) (sq b))` with
both operands the point 0.  A search that accepts a panel when the lower end of a squared
distance reaches the upper bound of a squared threshold rejects every zero distance, even for a
zero threshold, since the upper end of `sq (point 0)` is `5e-324`.  The
program therefore clamps a quantity that cannot be negative at 0 before a square root or a
comparison, with its own upper end, `clamp v 0 v.hi`, as `Demos.PassiveSafety.nonneg` and
`Demos.Attitude.QMethod.certify` do, or with a real upper bound, as `Demos.Gate.tailCore` clamps
`x/2` and its quotient by `π` to `[0, x]`.  `Library.Numerics.Interval.clamp_sound` with a proof
that the real quantity is not negative, such as `Demos.Conjunction.Model.pc_nonneg`, encloses the
clamped value, and `Demos.Attitude.QMethod.encloses_clamp0` needs only `0 ≤ x` and the
interval's upper end.  Other forms avoid the square root of such an interval.  A body of
`enclosure_def` takes `√(max u 0)`, whose `imax` has a lower end that is not negative, and
`Demos.Orbit.sqrt_max_zero` shows that the real value stays `√u`.  `Demos.Screening.keplerI` uses
`1 - |e|` in place of the `1 - √(e² + 0²)` of `Demos.Sgp4.Kepler.rootI`, which rejects every
circular orbit, and `Demos.Screening.kepler.encloses` relates the two with
`Real.sqrt_sq_eq_abs`.  `Demos.PassiveSafety.square` gives the point 0 for a zero threshold.  The
reviews of the passive-safety and gating requirements found these defects with their own models
of the interval library before the modules ran (finding 3 of `Demos/PassiveSafety/review.md` and
finding 1 of `Demos/Gate/review.md`).

Where the evaluation of a formula fails or is too wide, another form of the same real function
can take its place.  `Demos.Gate.tailWith` evaluates the chi-square tail's closed form, whose
factor `exp(-x/2)` leaves the normal range near `x = 1450`, only up to that point, and beyond it
returns the interval from 0 to the upper end at 1450, which contains the tail because
`Demos.Gate.tail_antitone` states that the tail decreases.  The natural interval form of
`x̂ᵀ C x̂` multiplies a large variance of `C` by the width of the interval of `x̂`, and
`Demos.Avoidance.project` evaluates instead the form centered at a point `g` near `x̂`,
`gᵀ C g + 2 (x̂ - g)ᵀ C g + (x̂ - g)ᵀ C (x̂ - g)`, which `Demos.Avoidance.project_eq` equates with
the plain form over the reals (finding 6 of `Demos/Avoidance/review.md`, which compares the two on
the oracle's inputs).  [The entry on searches over interval enclosures](../interval-searches/README.md)
covers the loops that bisect, march, or subdivide with these enclosures.

`Demos.Conjunction.expI_sound` applies the monotone enclosure to `exp`,
`Demos.Conjunction.erfSumI_sound` chains the operations of the sum and derives a positive conditional
variance from an accepted division, `Demos.Conjunction.panel_sound` bounds one panel,
`Demos.Conjunction.panels_sound` is the loop induction, and `Demos.Conjunction.pc_enclosure`
combines them.
