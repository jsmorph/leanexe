# SGP4 review

This review records the decisions behind [the requirements](requirements.md) and the differences from the reference code, the code of Vallado, Crawford, Hujsak, and Kelso (AIAA 2006-6753) as [python-sgp4](https://github.com/brandon-rhodes/python-sgp4) distributes it.

## Decisions

| Question | Decision | Reason |
|---|---|---|
| Scope | Near-Earth element sets, with status 8 for the deep-space path | The deep-space path adds the lunar and solar terms and the resonance integration, a later phase. |
| Constants | WGS-72 only | The verification file's states use them.  The other sets of `getgravconst` change four numbers and can become parameters later. |
| Units of the inputs | Revolutions per day and degrees, as an element set states them | The element set's fields are then the decimal numbers of the message, and the conversion belongs to the definition. |
| Programs | A binary64 program separate from the enclosing program | The binary64 program follows the reference code operation by operation and is the fast path.  The enclosing program evaluates the model's definitions on intervals. |
| Structure of the enclosing program | One source for each part of the model, from which `enclosure_def` declares the real function, the interval function in the compiler's dialect, and the theorem that relates them | The design proposed an interpreter of straight-line programs with one generic theorem.  An interpreter needs a second proof that its program computes the model.  With one source, the model is the text that the interval code evaluates, the proof of each part is one tactic call, and the code runs without interpretation.  The compiler's time grows faster than the size of a function, so the model is in parts of at most about 40 operations. |
| Fractional powers | `x^(2/3)` from `pow` at the endpoints, moved four steps outward and accepted only when the cubes bracket the squares of the endpoints.  `x^(3/2)` and `x^(7/2)` as products with a square root | The test of the cubes makes the enclosure independent of the accuracy of `pow` and of the rounding of the exponent `2/3`. |
| Sine and cosine | The library's value at the midpoint, two steps outward, widened by the distance to the endpoints | Both functions have the Lipschitz constant 1.  The intervals of the angles are narrow, so the bound loses little. |
| Kepler's equation | An approximate root in binary64, widened by the enclosure of its residual over `1 − √(axnl² + aynl²)` | `Kepler.root_bound`.  The result does not depend on the number of iterations. |
| Argument of latitude | The sine and the cosine of `su` from `sinu`, `cosu`, and the correction, without `atan2` | `(cosu, sinu)` is a unit vector (`anomaly_unit`), so the angle-difference formulas give the same values (`sin_latitude`, `cos_latitude`), and the program needs no enclosure of `atan2`. |
| Constants | Each decimal constant as the quotient of two integers in interval arithmetic | Each integer is exact in binary64, so the quotient's interval contains the decimal value. |
| Status 7 | One status for an undecided test and for a rejected operation | Both mean that the program has no enclosure to return. |
| Two-line reader | Each field as an integer of its digits over a power of ten, the catalog fields compared byte by byte, and no value for the epoch | The quotient of two exact integers contains the decimal value without a rounding argument.  The Alpha-5 form passes, since the reader gives the catalog field no value.  The near-Earth model does not read the epoch. |
| Reader of decimal values | The library's `parse64`, widened by one step on each side | `parse64` returns the nearest-even rounding of the decimal number, with a proof, so the widened interval contains the number. |
| Tolerance of the intervals | `2·10⁻⁸` km and `10⁻⁹` km/s between a reference value and its interval | The reference code stops its iteration for Kepler's equation at a correction below `10⁻¹²`, which moves the position by up to that times the semimajor axis, about `7·10⁻⁹` km, and it prints to `10⁻⁸` km.  The largest distances measured are `6.7·10⁻⁹` km and `4.9·10⁻¹⁰` km/s. |
| Integer and half-integer powers | `pow`, as the reference code calls it | The binary64 program then differs from the reference code only in its elementary functions and in the points listed below. |
| Test tolerance | `10⁻⁸` km and `10⁻⁹` km/s | The verification file prints positions to `10⁻⁸` km and velocities to `10⁻⁹` km/s.  The largest differences measured are `5.0·10⁻⁹` km and `5.0·10⁻¹⁰` km/s, half a unit of the last printed digit. |
| Validity | Status 9 for a value that is not finite, `n ≤ 0`, `e < 0`, or `1 ≤ e` | The reference code has no such test, and outside these ranges it takes powers and square roots of negative numbers. |

## Differences from the reference code

| Reference code | This program | Effect |
|---|---|---|
| Reduces `nodem`, `argpm`, `xlm`, and `u` modulo `2π` | No reduction | Every later use of these angles is a sine, a cosine, or Kepler's equation, whose solution shifts by the same multiple of `2π`.  The results differ by rounding. |
| `mm = (xlm − argpm − nodem) mod 2π` with `xlm = mm + argpm + nodem` | `mm` unchanged, and `u = mm + argpm + temp xlcof axnl` | The same real number.  The results differ by rounding. |
| Computes every constant, then tests for the deep-space path | Tests for the deep-space path after `no` | No effect on a near-Earth element set. |
| Omits the terms with `omgcof`, `xmcof`, `cc5`, `d2`, `d3`, `d4`, `t3cof`, `t4cof`, and `t5cof` when `isimp` holds | The binary64 program does the same.  The model and the enclosing program set these nine constants to 0 for such an element set and keep the terms | The same real numbers. |
| Computes `a`, `alta`, `altp`, `ainv`, and `gsto` | Omitted | The near-Earth propagation reads none of them. |
| Runs `sgp4` at time 0 at the end of `sgp4init` | Omitted | The call changes no constant on the near-Earth path. |
| Returns no state for the errors 1, 2, and 4 | Returns zeros with the status | None. |
| The platform's `sin`, `cos`, `pow`, and `atan2` | The library's functions, each within one or two steps of the correctly rounded value | The results are the same bits on every back end and differ from the reference code's by rounding. |

## Open

The deep-space path is not written, and the reader of an Orbit Mean-Elements Message reads one decimal value and leaves the search for a key to the host.  The enclosing program takes intervals for the element set, and `sgp4BoxAround` takes binary64 values and widens each by one step on each side, which contains the decimal number that a correctly rounding parser read.
