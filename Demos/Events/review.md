# Event windows requirements: decisions and review

[The requirements](requirements.md) specify the first iteration of candidate 5.1 of the space-operations plan, from brief 5.1 of the candidates' briefs.  This record gives each decision with its reason, the findings of the independent review, and the response to each.

## Decisions

| Question | Choice | Reason |
|---|---|---|
| Form of the theorem | The runs cover every time of the condition (E1), and the condition holds throughout a run labeled 1 (E2) | The brief's two sentences conflict, as the plan's correction states.  The cover form gives the first sentence.  The label gives the inside of each window, and with E1 it places every crossing in a run and at an end of every run labeled 1 that holds it (E5). |
| Sun's position | The USNO's approximate solar coordinates, with the decimal constants as real numbers | The program needs no table in its interface, the USNO states the accuracy, and the rate bound follows from `\|sin x − sin y\| ≤ \|x − y\|`.  A box of Sun directions per interval of time would move the model and its accuracy into an unverified converter. |
| Frame | The mean equator and equinox of date, as a premise | The formula's frame.  TEME lies within about 10″ of it, and J2000 elements need the caller's precession. |
| Shadow model | Conical, with a half-angle that the caller gives: positive for the penumbra, negative for the umbra, 0 for the cylinder | One condition covers the three models, and the penumbra is the conservative cone for the cover.  A fixed angle keeps the rate bound simple, and the angle's variation over the year is a premise. |
| Trajectory | Two-body motion through the screening demo's Kepler pieces | M3 of the screening demo bounds the speed by algebra, and the position's enclosure exists.  SGP4's velocity output is not the derivative of its position. |
| Body-fixed vectors | Fixed in the orbit's radial, along-track, and cross-track frame | A nadir-pointing spacecraft holds such an attitude, and an inertial attitude reduces to an inertial vector. |
| Perturbations | A padding `P` for the shadow, as margins of both functions | E4 covers every trajectory within the padding, for the cover and for the runs labeled 1.  A bound on the position bounds no error of the orbit's frame, so the exclusion events have no padding. |
| Parallax | The geocentric direction for the exclusion events, with the bound as a premise | Keeps the Sun's distance out of the model. |
| Reuse | By import from the screening demo | The orbit, the positions, their enclosures, the cells, the runs, the search's state, `triples`, and the loop lemmas need no change.  The join and its proof are new, since the screening merge ignores labels and its invariant names the screening condition. |
| Isolation | Bisection level by level, exclusion and the whole mark from the computed middle with the rate bounds and the margins, and the cells of the previous level kept at the cap | The proof of `Isolation.lean` holds for any functions within the margins of the model's, so the model's theorems and those of the padding share it. |

## Review

A fresh agent reviewed the requirements against brief 5.1 and the plan's sections "Starting point" and "What every design states" and its correction for 5.1, with [the method of independent review](../../VKB/entries/independent-review/README.md).  It received none of the author's reasoning.  It built its own model of the interface with outward-rounded intervals and 35 wrong programs, and an oracle of the request in mpmath with a different formulation of each event: the cone by its apex and angle, the orbit's frame from the velocity, and the Sun from its right ascension and declination.  The model agreed with the oracle on 22 constructed cases and 500 random valid inputs with 361 refined crossings.

The reviewer confirmed the citations of the tree, the transcription of the USNO formula constant for constant, and the cone's geometry, which agrees with the overlap of the Earth's and the Sun's disks at 397,599 random points outside the sphere.  It found the half-angles 0.26890° and 0.26401° at 1 AU, a parallax of 0.01643° at 42,164 km, and `ω_d = 0.017789750` radians per day, with the largest observed rate of `ŝ` at 0.999999 of it.  Every rate bound held for low, geostationary, transfer, and Molniya orbits and one with `e = 0.9`, at half-angles from −60° to 80°, with the largest observed ratio of rate to bound 0.9947.

| Finding | Severity | Response |
|---|---|---|
| 1. An output with one run over the window labeled 0, at status 0 or 1, meets E1 to E5. | Gap | Adopted in part.  E6, `events_progress`, states that outputs 0 and 3 are the search's status and levels, that status 0 comes with all `N` levels, and that status 1 comes with fewer levels and a next level of more than `C` cells.  The program is the definition of the method, and C1 ties the module to its text, so no second reference definition applies.  The trivial output still meets the theorems, and the requirements say so.  The tests' status and method checks reject it. |
| 2. The tests never check the status of a valid input. | Gap | Adopted.  Each case states its status, and the oracle checks the levels completed against `N`, the cell tests against `(N + 1) C`, and the length `4 + 3K`. |
| 3. The method check fails a correct program at `N ≥ 40`, where the cell width falls below the band of about `3 · 10⁻¹¹` minutes in which the enclosures' width keeps a cell undecided. | Defect | Adopted.  The check uses `Δ = max((t₁ − t₀) / 2^N, 10⁻⁹)` minutes. |
| 4. E2 is tested only at samples, and runs labeled 0 at crossings are narrower than the step.  The mutation that moves an end inward often leaves a correct output. | Gap | Adopted.  The requirements state the check at the failing time of every refined crossing, which the oracle carried, and each mutation is now wrong by construction: the start moves past a refined time of the condition, and the label 1 goes to a run that holds a refined time at which the condition fails. |
| 5. The cases miss several wrong programs: the radius `a (1 + e)` in the frame's rate, the whole mark from `g₂` alone, the rate of the frame without the Sun's term, and the shadow's rate without the Sun's term. | Gap | Adopted.  The oracle runs the reviewer's eccentric frame cases with crossings near perigee, an Earth radius of 7,000 km above a perigee of 6,871 km, a cross-track vector over two days, and a circular retrograde orbit at 200,000 km with three windows of two minutes at `N = 6` that the reviewer's model found to reject the shadow's rate without the Sun's term.  The case `C = 64` runs at `N = 20`. |
| 6. The factor `\|cos α\| + \|sin α\|` holds but is not needed. | Wording | Adopted as wording.  The requirements state that the factor is loose by up to `√2` and that `L₁` and `P` also serve `g₂`.  The program keeps the factor, whose proof is the triangle inequality, and the variants with `L₂ = L₁` and `W₂ = P` are sound, so no case can reject them. |
| 7. The rule for the umbral angle over the year is missing, and the angle varies by 3.4 percent from aphelion to perihelion. | Gap | Adopted, with the ranges and the rule for both cones. |
| 8. The cone conditions differ from the shading of the spheres within about 70 m of the surface. | Wording | Adopted. |
| 9. The frame is closest to the mean equator and equinox of date, TEME lies within about 10″ of it, the precession from J2000 runs from 0.363° to 0.377° over 2026, and the formula gives the apparent direction. | Wording | Adopted. |
| 10. The premises have no route into the theorems: the parallax bound assumed a radius, the margin for the exclusion events serves only the cover, the formula's accuracy holds for two centuries, and nothing carries the formula's error into the shadow. | Gap | Adopted.  The requirements state the parallax bound `arcsin(a (1 + e) / d)`, the rule of adding the angles to `β` for the cover and subtracting them for the runs labeled 1, the range `\|D\| ≤ 73,050` of the stated accuracy, and the padding `P ≥ δ + a (1 + e) θ` that carries an error `θ` of the Sun's direction into E4. |
| 11. Whether the orbit's requirements hold for the inertial event is undecided, and the frame event has no padding. | Gap | Adopted.  The orbit's requirements hold for every event, and the requirements state that the exclusion events have no padding. |
| 12. Whether the formula's constants are decimal reals or their binary64 roundings is unstated. | Wording | Adopted.  The constants are the decimal numbers, which the program encloses by exact ratios. |
| 13. `ρ`, `L`, `w`, `α′`, and `β′` each name two things. | Wording | Adopted.  The levels are `N`, a cell is `[c₀, c₁]` with radius `η`, the method check's width is `Δ`, and the margins are `Wₖ`. |
| 14. The library's `sqrt` rejects a negative lower end, not a zero one. | Wording | Adopted. |
| 15. The order of the runs, the separation of runs with equal labels, the memory, and the dialect are unstated, and a program without the join or with reversed children passes every check. | Gap | Adopted.  The requirements state the properties and the stored cells, and the oracle checks the order and the separation.  No theorem states them. |
| 16. E4 could state E5 for the displaced trajectory, the oracle cannot run mpmath at every sample, and the brief's question about the slew planner is unanswered. | Wording | Adopted in part.  The requirements describe the binary64 sampling with mpmath near zero and state that this iteration leaves the slew planner out.  E5 stays with the Kepler trajectory, since a trajectory within the padding need not be continuous. |

## Wrong programs

The reviewer's model computes the output of the interface and carries each wrong program as a variant.  Each variant ran through the checks of the requirements on the cases they list and on the reviewer's added cases, which the oracle now runs.  The table gives the cases that rejected each variant in the reviewer's runs.

| Wrong program | Cases that reject it |
|---|---|
| Sign of `α` reversed, or a cylinder in place of the cone | The eclipses, the umbra, the padding, the geostationary equinox, the transfer orbit, the grazing passes, the cap 64, the windows that begin or end in the shadow, the orbit at 200,000 km |
| No margin with `P > 0` | The padding |
| `ω = 0` in every bound, or `ω` per second | The inertial week, the cross-track vector over two days |
| `ω` omitted from the shadow's `L₁` only | The orbit at 200,000 km, in 23 of 200 windows of two minutes |
| `ω` omitted from the frame's bound only | The cross-track vector over two days |
| `ω` in degrees, sound but coarse | The inertial week and the cross-track vector, by the method check |
| `a n / 1 − e` in place of `a n / (1 − e)` | The transfer orbit, the eccentric frame cases |
| `a (1 + e)` in place of `a (1 − e)` in the frame's bound | The eccentric frame cases |
| `Ŝ = R̂ × Ŵ` | The frame every orbit, the eccentric frame cases |
| A merge across labels | Most cases, and the check at the failing time of each crossing |
| Status 0 at the cap | The caps 1 and 64, by the status and the method check |
| The window shrunk at its ends | The windows that begin or end in the shadow, the inertial week, the cross-track vector, the eccentric frame cases |
| Label 1 when the middle holds | Every case with crossings |
| The sign of `x` reversed, `g₁` omitted, or exclusion by `g₂` alone | Most shadow cases, the last by the method check |
| The whole mark from `g₂` alone | The Earth radius above the perigee |
| Errors in the Sun's formula: the obliquity's sign, `g` in radians, the mean longitude alone, `D` in seconds | Every case with crossings |
| No final pass | The eclipse, the padding, the geostationary equinox, the inertial week, by the method check |
| The window as one run labeled 0 at status 0 | Every case at status 0 with `N = 20` and a time without the condition |
| The window as one run labeled 0 at status 1, or status 1 always | The status of every case |

| Wrong program that no case rejects | Reason |
|---|---|
| `L₂ = L₁` or `W₂ = P` | Both are sound bounds, tighter than the requirements' (finding 6). |
| The radius `η` rounded down | The decisions change only within rounding of a threshold, which neither the step nor the refinement resolves.  The proof excludes it. |
| The cap test `≥ C` in place of `> C` | The output differs only when a level leaves exactly `C` cells, and then only in its status. |
| Cells marked whole split again | The runs are the same, and the cell tests and the level at which the cap stops differ only in cases that place a level's count at the cap. |

The program without the join and the program with reversed children, which the review found to pass every stated check, fail the oracle's checks of order and separation.
