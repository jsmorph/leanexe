# Conjunction screening requirements: decisions and review

[The requirements](requirements.md) specify the first iteration of candidate 5 of the space-operations plan, from brief 3.1 of the candidates' briefs.  This record gives each decision with its reason, the findings of the independent review, and the response to each.

## Decisions

| Question | Choice | Reason |
|---|---|---|
| Prerequisite: SGP4 boxes over an interval of time | No extension | `Demos.Sgp4.sgp4Box_sound` already holds for every real time in its interval argument, and the measurement in the requirements gives the widths. |
| Trajectory model | Two-body motion first, SGP4 in a later iteration | The classical filters reason about Kepler orbits, Kepler's equation gives a bound on the speed by algebra, and an SGP4 trajectory has no fixed path for the orbit-path filter.  SGP4's velocity output is not the derivative of its position, so its isolation would rest on boxes over cells of time instead of a speed bound. |
| Perturbations in the filters | A padding input `P`, added to the threshold | S1 covers every pair of trajectories within `δ₁` and `δ₂` of the Kepler trajectories with `δ₁ + δ₂ ≤ P`.  SGP4's own bounds on the radius belong to the SGP4 iteration. |
| Window ends | A closed window, and a one-sided minimum at an end counts | The theorem covers every time with a separation at most `D + P`, which includes each end below it, so consecutive windows miss no approach at their boundary. |
| Scope | The pairwise program | The catalog version waits on the measured cost of a pair. |
| Elements | `a` in km, `μ` as an input, angles in degrees, time in minutes, an epoch per object | Kepler elements suit two-body motion, and `n = 60 √(μ/a³)` needs no power function, so the module carries no power tables. |
| Root of Kepler's equation | A new enclosure with the least slope `1 − \|e\|` | `Demos.Sgp4.Kepler.rootI` computes `1 − √(e² + 0²)`, and the outward-rounded square of the point 0 has a lower end below zero, which `sqrt` rejects, so every circular orbit would be rejected.  Changing `rootI` would change the bytes of the SGP4 module. |
| Isolation | Bisection level by level, with exclusion by the speed bound at the computed middle, and the cells of the previous level kept at the cap | Every status other than 4 then carries I1, and the number of tests is at most `(L + 1) C`. |
| Orbit-path filter | Branch-and-bound over two eccentric anomalies from `[0, 6.5]²`, with a test of each cell's center for verdict 2 | 6.5 is exact in binary64 and exceeds `2π`, and the center test ends the search early for paths that cross. |
| Merge | The hull of consecutive kept cells that touch or overlap | Any hull of kept cells preserves the covering, and the cells' ends are finite by an invariant of the search. |

## Review

A fresh agent reviewed the requirements against brief 3.1 and the plan's sections "Starting point", "What every design states", and "5. Screening", with [the method of independent review](../../VKB/entries/independent-review/README.md).  It received none of the author's reasoning, built its own model of the requirements and an oracle of the request in Python, with a solver of Kepler's equation by bisection on the true anomaly and 40-digit refinement, ran 18 constructed and 30 random pairs, and wrote 24 wrong programs as variants of its model.  It confirmed the citations of the tree, M1 on 10,000 points, M3 with the maximum speed over `a n / (1 − e)` equal to `√(1 − e²)`, and the stated bounds on the counts.

| Finding | Severity | Response |
|---|---|---|
| 1. The inputs `t₀ = −10³⁰⁸` and `t₁ = 10³⁰⁸` are valid, `β − α` overflows, and the middle is infinite. | Defect | Adopted.  The window's ends must lie within `10⁹` minutes, so every computed width is finite.  The program already kept a cell with a middle that is not finite unsplit, so the cells with NaN ends of the reviewer's model did not arise in it, and the overflowing window gave one interval over the whole window.  The oracle's case "window beyond 1e9 minutes" expects status 4. |
| 2. A program that never excludes, never marks a cell certain, or reports status 0 at the cap satisfies every theorem and passes the described tests. | Gap | Adopted in part.  The oracle checks expected outcomes where the margins exceed rounding by far: status 1 for a radial gap above `D + P + 1` km, status 2 and verdict 2 for paths farther than `D + P + 1` km and nearer than `D + P − 1` km, a certain interval for every minimum below `D + P − 1` km, and the bound `D + P + (V₁ + V₂) w` on every returned time.  A mutation that returns the whole window must fail.  The theorem I3, `screen_within`, states that every returned interval lies in the window.  The module test ties the WebAssembly module to the Lean program bit for bit.  The interval ends are not compared with a second model, since rounding decides the cells near the thresholds. |
| 3. Exclusions were checked only over the window, and the path oracle had no criterion. | Gap | Adopted: for status 1 and 2 the least distance between the paths must exceed `D + P`, and for verdict 2 it must be at most `D + P`. |
| 4. The samples need not include the window's ends. | Gap | Adopted.  The oracle's samples include both ends, and it checks each end below `D + P` as a minimum.  The requirements state the step. |
| 5. The cases omit inputs that several wrong programs need. | Gap | Adopted: `P > 0` with misses between `D` and `D + P`, the apogee–perigee flag 0, `Lp = 0`, path verdicts 3 and 4, `L = 0`, `L = 40`, `C = 1` and `C = 64`, enclosures that reject, a head-on approach at the perigee of an orbit with `e = 0.3`, and the reviewer's coplanar circles 2 km apart and paths 3 km apart with `D = 1` and `P = 3`. |
| 6. The behavior of a test whose intervals reject is not stated. | Gap | Adopted.  The requirements state that such a test excludes nothing and marks nothing, and the case "rejected enclosures" runs two identical objects at `a = 10¹⁰³`. |
| 7. Cells inside the set where `s ≤ D + P` keep splitting, so a deep approach drives the count to the cap. | Gap | Adopted.  The test marks a cell whole when every time of it lies within `D + P` by the speed bound, and such a cell stops splitting.  The proof needed no new lemma, since an unsplit cell keeps the covering. |
| 8. A cell one binary64 step wide splits into a copy of itself. | Gap | Adopted: a cell splits only when its computed middle lies strictly inside it. |
| 9. The allocation bound and the target are not stated. | Gap | Adopted in part.  The requirements name the target, a WebAssembly ground program, and state that each level's new cells are stored before the test against the cap.  C1 states the generated bound `compiled.screen.bound`, and a closed form of it remains open. |
| 10. "Answers the reports of missed conjunctions on their own terms" claims more than the theorems. | Wording | Adopted.  The cited misses come from perturbations, and the requirements now say that the theorems cover the filters' geometric reasoning for Kepler orbits and cover perturbations only through the padding. |
| 11. "Certain to hold a close approach" overstates I2 for `P > 0`. | Wording | Adopted: the output row states a time within `D + P`. |
| 12. The time filter is not named. | Wording | Adopted: the isolation takes the place of the time filter. |
| 13. The request asks for enclosures of the times of local minima. | Gap (minor) | Adopted as a statement of the requirements: the intervals enclose every close approach and so every such minimum.  A theorem that a certain interval holds a local minimum, from the continuity of the trajectories, remains open. |
| 14. The units of `i`, `Ω`, and `ω` are unclear, and `P` names both the padding and a unit vector. | Wording | Adopted: the unit vectors are `p̂` and `q̂`, and every angle is in degrees. |
| 15. The counting of center tests, the verdict at the cap at level `Lp`, and the output of status 4 are not stated. | Wording | Adopted. |
| 16. The prerequisite's script lies in a gitignored directory, and its output is not recorded. | Wording | Adopted: the script is [`tests/screening/BoxWidth.lean`](../../tests/screening/BoxWidth.lean), and the requirements hold its results. |

## Wrong programs

The reviewer's model computes the output of the interface and carries each of its 24 wrong programs as a variant.  Each variant ran through the checks of `tests/screening/oracle.py` on eight general cases (an approach at half the threshold, two approaches cut off at an end of the window, two random pairs, an eccentric approach, the crossing paths 70 km apart, and the padding case) and on the cases aimed at that variant.  The model without a variant passed the eight general cases.  The table gives the cases that reject each variant.

| Wrong program | Cases that reject it |
|---|---|
| Apogee–perigee filter without `e` | "approach 0.5 D" (a close approach in a pair it excluded), "random LEO 0" (an exclusion without a radial gap) |
| Apogee–perigee filter with `D` in place of `D + P` | "circles 2 km apart, D 1, P 3" |
| Apogee–perigee filter with the signs swapped | 7 of the 8 general cases |
| Isolation that tests only `s(m)` | 5 of the 8 general cases |
| Speed bound `a n` | "eccentric approach", "head-on at perigee" |
| Speed bound `a n (1 + e)` | "head-on at perigee" |
| `max(V₁, V₂)` in place of `V₁ + V₂`, or `ρ = (β − α)/4` | "ends before the minimum", "padding 4 km, miss 7 km", "head-on at perigee" |
| Isolation with `D` in place of `D + P` | "padding 4 km, miss 7 km", "miss 3 km, D 1, P 3" |
| End cell dropped when the separation is monotone on it | The four cases cut off at an end |
| Window shrunk by one step at each end | The four cases cut off at an end |
| Intervals without an interior minimum dropped | Three of the four cases cut off at an end |
| Merge that keeps the first interval's end | 5 of the 8 general cases |
| Truncation of the cells at the cap | "cap 64", "cap 1" |
| Status 0 at the cap | "cap 64", "cap 1" (a deep minimum in no certain interval) |
| Every kept cell marked certain | "miss 1.5 km, D 1, 8 levels" |
| No cell marked certain | 5 of the 8 general cases |
| Nothing ever excluded | "approach 0.5 D", "eccentric approach", "random LEO 3", "LEO and GEO" |
| A rejection counted as an exclusion | "rejected enclosures" |
| Path filter that tests only centers | 5 of the 8 general cases |
| Path search over half of `E₁` | "approach 0.5 D" |
| Path filter with `D` in place of `D + P` | "paths 3 km apart, D 1, P 3" |
| An undecided path search reported as verdict 2 | "path verdict 3" |
| Path search from `[0, fl(2π)]²` | None |

The path search from `[0, fl(2π)]²` leaves uncovered anomalies whose points lie within about `10⁻¹²` km of `x(0)`, below the rounding of the coordinates, as the reviewer found, so only the proof of F2, which starts from `[0, 6.5]²`, excludes it.  The reviewer expected the status 0 at the cap to pass every check; the check of certain intervals at deep minima rejects it in both cases at the cap.
