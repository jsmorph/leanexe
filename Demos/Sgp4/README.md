# SGP4

SGP4 computes the position and the velocity of an Earth satellite from an element set of the public catalog.  [The binary64 program](Program.lean) implements its near-Earth part, for orbits with a period below 225 minutes, after the code of Vallado, Crawford, Hujsak, and Kelso (AIAA 2006-6753) with the WGS-72 constants.  [The requirements](requirements.md) define every quantity, and [the review](review.md) records each difference from that code.

## Functions

| Function | Result |
|---|---|
| `init n e incl node argp m bstar` | The constants of an element set: the mean motion in revolutions per day, the eccentricity, four angles in degrees, and the drag term |
| `propagate c t` | The state at `t` minutes from the epoch: a status, the position in km, and the velocity in km/s, in the TEME frame of that code |
| `sgp4 n e incl node argp m bstar t` | `propagate (init …) t` |

Status 0 marks a state of the model.  Statuses 1, 2, 4, and 6 are the errors of those numbers in the reference code, status 8 marks an element set of the deep-space path, and status 9 an element set with a value that is not finite or outside `0 < n` and `0 ≤ e < 1`.

## Theorems

[The compilation](Verified.lean) gives `compiled.init.implements`, `compiled.propagate.implements`, and `compiled.sgp4.implements`: the WebAssembly module returns the values of the Lean functions, which call the library's `sin`, `cos`, `pow`, and `atan2`.  [The file theorems](File.lean) identify `build/verified/sgp4.wasm`, a module of 27,852 bytes.

[Kepler's equation](Kepler.lean) in the form of SGP4 is `E + b cos E − a sin E = u`.  `exists_unique_root` states that it has exactly one root when `a² + b² < 1`, and `root_bound` states that every `E` lies within `|E + b cos E − a sin E − u| / (1 − √(a² + b²))` of that root.

## Tests

`tests/sgp4/run.sh` compares the program in native Lean with the states that the reference code printed for the near-Earth element sets of its verification file.  The 221 states agree within `5.0·10⁻⁹` km and `5.0·10⁻¹⁰` km/s, half a unit of the last printed digit.  `tests/verified/run.sh --cases sgp4` compares the module with native Lean on 195 calls and checks the axioms and the file theorems.

## Limits

The theorems relate the module to the Lean program.  The agreement of the program with the reference code rests on the test and on the review.  The program has no deep-space path, and it states nothing about the true orbit: the model's own error is of the order of kilometers and grows with the time from the epoch.

## References

- Vallado, Crawford, Hujsak, and Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753.
- Rhodes, [python-sgp4](https://github.com/brandon-rhodes/python-sgp4), the source of the code read and of the files `tests/sgp4/near-earth.tle` and `tests/sgp4/near-earth.out`, under the license in `tests/sgp4/LICENSE.python-sgp4`.
