# SGP4

SGP4 computes the position and the velocity of an Earth satellite from an element set of the public catalog.  This demo implements its near-Earth part, for orbits with a period below 225 minutes, after the code of Vallado, Crawford, Hujsak, and Kelso (AIAA 2006-6753) with the WGS-72 constants.  It holds a model over the real numbers, a binary64 program, and an enclosing program that returns an interval for each coordinate with a proof that the interval contains the model's value.  [The requirements](requirements.md) define every quantity, and [the review](review.md) records the decisions and each difference from that code.

## Example

The element set below is the first of the verification file of the Vallado code.  At 360 minutes from its epoch, `Tle.propagate` returns status 0 and the intervals of the table, with the endpoints rounded outward to 12 decimals, and the reference code printed the values of the last column.  Each printed value lies within half a unit of its last digit of its interval.

```
1 00005U 58002B   00179.78495062  .00000023  00000-0  28098-4 0  4753
2 00005  34.2682 348.7242 1859667 331.7664  19.3264 10.82419157413667
```

| Coordinate | Lower endpoint | Upper endpoint | Reference code |
|---|---|---|---|
| `x` (km) | −7154.031202016514 | −7154.031202013945 | −7154.03120202 |
| `y` (km) | −3783.176825038079 | −3783.176825035897 | −3783.17682504 |
| `z` (km) | −3536.194122943021 | −3536.194122941825 | −3536.19412294 |
| `vx` (km/s) | 4.741887408995 | 4.741887408998 | 4.741887409 |
| `vy` (km/s) | −4.151817765375 | −4.151817765372 | −4.151817765 |
| `vz` (km/s) | −2.093935424908 | −2.093935424906 | −2.093935425 |

## Parts

| Part | File | Content |
|---|---|---|
| Model | [`Spec.lean`](Spec.lean), [`Model.lean`](Model.lean) | Each quantity of the requirements as a real function, and the status, the position, and the velocity of an element set at a time |
| Binary64 program | [`Program.lean`](Program.lean) | `init`, `propagate`, and `sgp4` in binary64, in the order of the reference code |
| Enclosing program | [`Box.lean`](Box.lean) | `initBox`, `propagateBox`, `sgp4Box`, and `sgp4BoxAround`, which return a status and six intervals |
| Readers | [`Tle.lean`](Tle.lean), [`Omm.lean`](Omm.lean) | The fields of a two-line element set and the decimal values of an Orbit Mean-Elements Message, as intervals |

An element set holds the mean motion in revolutions per day, the eccentricity, four angles in degrees, and the drag term, and a time is in minutes from the epoch.  A position is in km and a velocity in km/s, in the TEME frame of the reference code.

| Status | Meaning |
|---|---|
| 0 | The result holds the model's position and velocity. |
| 1, 2, 4 | The error of that number in the reference code: a mean eccentricity outside `[−0.001, 1)`, a mean motion that is not positive, or a negative semilatus rectum. |
| 6 | The radius is below one Earth radius.  The result still holds the model's position and velocity. |
| 7 | Enclosing program only: the intervals do not decide a test of the model, or an operation was rejected. |
| 8 | The element set takes the deep-space path, which this demo does not compute. |
| 9 | The element set is outside `0 < n` and `0 ≤ e < 1`, a value is not finite, or the lines of a two-line element set do not have the layout. |

## One source for the model and the enclosing program

[The model](Spec.lean) states each part of the computation once, with [the command `enclosure_def`](../../Library/Numerics/Interval/README.md#one-source-for-a-real-function-and-its-interval-program).  The command declares the real function, the interval function that the enclosing program runs, and the theorem that the interval function's result encloses the real function's value when its arguments enclose the real arguments.

```lean
/-- `axnl`, `aynl`, and `u`. -/
enclosure_def longPeriod (am em argpm mm aycof xlcof) :=
  let axnl := em * cos argpm
  let temp := 1 / (am * (1 - em * em))
  (axnl, em * sin argpm + temp * aycof, mm + argpm + temp * xlcof * axnl)
```

The real function `longPeriod` is this text.  The interval function `longPeriodI` replaces each operation with [the interval operation](../../Library/Numerics/Interval/README.md), and `longPeriod.encloses` relates the two.  A test of the model, such as `ecco > 1.0e-4`, becomes a selection that rejects an interval with points on both sides of the threshold.

## Theorems

| Theorem | File | Statement |
|---|---|---|
| `exists_unique_root` | [`Kepler.lean`](Kepler.lean) | Kepler's equation in the form of SGP4, `E + b cos E − a sin E = u`, has exactly one root when `a² + b² < 1`. |
| `root_bound` | [`Kepler.lean`](Kepler.lean) | Every `E` lies within `\|E + b cos E − a sin E − u\| / (1 − √(a² + b²))` of that root. |
| `root.encloses` | [`KeplerBox.lean`](KeplerBox.lean) | The interval of `Kepler.rootI`, an approximate root widened by the enclosure of that bound, contains the root. |
| `two_body` | [`TwoBody.lean`](TwoBody.lean) | With `J2`, `J3/J2`, `J4`, and the drag term set to zero and an eccentricity of at least `10⁻⁶`, the model's position and velocity are those of the Kepler orbit with the semimajor axis `(xke / n)^(2/3)` and the eccentric anomaly `E` with `E − e sin E = M + n t`. |
| `anomaly_unit`, `sin_latitude`, `cos_latitude` | [`Latitude.lean`](Latitude.lean) | `(cosu, sinu)` is a unit vector, so the model's sine and cosine of the argument of latitude equal those of the reference code's angle. |
| `sgp4Box_sound` | [`BoxSound.lean`](BoxSound.lean) | For intervals that contain an element set and a time, the six intervals of a result with status 0 or 6 contain the model's position and velocity. |
| `status_sound` | [`BoxSound.lean`](BoxSound.lean) | For such intervals, a status of 0, 1, 2, 4, 6, or 8 is the model's status. |
| `read_status` | [`TleSound.lean`](TleSound.lean) | `Tle.read` returns status 0 exactly for two lines of the layout `WellFormed`: 69 bytes each, the line numbers, the checksums, the separators and the digits of the fields it reads, and equal catalog fields. |
| `read_encloses`, `propagate_sound`, `propagate_status` | [`TleSound.lean`](TleSound.lean) | The intervals of accepted lines contain the decimal values of their fields, and the results of `sgp4Box_sound` and `status_sound` hold for `Tle.propagate` with the element set that the digits denote. |
| `field_encloses`, `field_rejects` | [`OmmSound.lean`](OmmSound.lean) | The interval of `Omm.field` for a text that denotes `(−1)^neg · d · 10^e` in the grammar of the library's `parse64` contains that number, and a text outside the grammar has a rejected interval. |
| `compiled.sgp4.implements` and its siblings | [`Verified.lean`](Verified.lean), [`BoxVerified.lean`](BoxVerified.lean) | The WebAssembly modules return the values of the Lean functions. |

The proofs of the enclosing program use no accuracy theorem of `pow` and no enclosure of `atan2`.  The power `x^(2/3)` is accepted by a test of cubes against squares, and the argument of latitude enters only through its sine and cosine.  The sine and the cosine use the one-step accuracy theorems of the library's functions.

## Tests

`tests/sgp4/run.sh` runs both programs in native Lean on the near-Earth element sets of the verification file of the Vallado code and compares them with the 221 states that the reference code printed.

| Measure | Result |
|---|---|
| Binary64 program against the reference | At most `5.0·10⁻⁹` km and `5.0·10⁻¹⁰` km/s, half a unit of the last printed digit |
| Width of an interval | At most `4.2·10⁻⁸` km and `5.2·10⁻¹¹` km/s |
| Reference value outside its interval | At most `6.8·10⁻⁹` km and `5.0·10⁻¹⁰` km/s |
| Binary64 program outside its interval | At most `6.1·10⁻⁹` km and `6.9·10⁻¹²` km/s |

The reference code and the binary64 program stop their iteration for Kepler's equation at a correction below `10⁻¹²`, which moves the position by up to that times the semimajor axis, and the intervals contain the model's value with the exact root.  The test requires the status of the enclosing program to equal that of the binary64 program at every time, including the times after the decay of three objects.  It reads the same element sets through `Tle.propagate`, changes a digit of each line and expects status 9, and writes the catalog fields in the Alpha-5 form and expects the unchanged status.  It expects status 7 for an eccentricity of `10⁻⁴`, whose interval has points on both sides of a threshold of the model.

`tests/verified/run.sh --cases sgp4` and `--cases sgp4box` compare the modules with native Lean and check the axioms and the file theorems.

## Limits

The theorems relate the programs to the model of [`Spec.lean`](Spec.lean).  The agreement of the model with the reference code and with the operational code rests on the test and on the review.  The model's own error is of the order of kilometers and grows with the time from the epoch, so the intervals state nothing about the true orbit.

The demo has no deep-space path.  The reader of an Orbit Mean-Elements Message reads one decimal value: the search for a key in a message and the test of `MEAN_ELEMENT_THEORY` are left to the host.  The two-line reader gives the catalog number, the epoch, and the fields outside the propagation no value.  No test covers the full catalog, the C translation, or the AArch64 image.

## References

- Vallado, Crawford, Hujsak, and Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753.
- Rhodes, [python-sgp4](https://github.com/brandon-rhodes/python-sgp4), the source of the code read and of the files `tests/sgp4/near-earth.tle` and `tests/sgp4/near-earth.out`, under the license in `tests/sgp4/LICENSE.python-sgp4`.
