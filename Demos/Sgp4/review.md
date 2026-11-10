# SGP4 review

This review records the decisions behind [the requirements](requirements.md) and the differences from the reference code, the code of Vallado, Crawford, Hujsak, and Kelso (AIAA 2006-6753) as [python-sgp4](https://github.com/brandon-rhodes/python-sgp4) distributes it.

## Decisions

| Question | Decision | Reason |
|---|---|---|
| Scope | Near-Earth element sets, with status 8 for the deep-space path | The deep-space path adds the lunar and solar terms and the resonance integration, a later phase. |
| Constants | WGS-72 only | The verification file's states use them.  The other sets of `getgravconst` change four numbers and can become parameters later. |
| Units of the inputs | Revolutions per day and degrees, as an element set states them | The element set's fields are then the decimal numbers of the message, and the conversion belongs to the definition. |
| Programs | A binary64 program separate from the enclosing program | The binary64 program follows the reference code operation by operation and is the fast path.  The enclosing program evaluates the same definitions on intervals. |
| Integer and half-integer powers | `pow`, as the reference code calls it | The binary64 program then differs from the reference code only in its elementary functions and in the points listed below. |
| Test tolerance | `10⁻⁸` km and `10⁻⁹` km/s | The verification file prints positions to `10⁻⁸` km and velocities to `10⁻⁹` km/s.  The largest differences measured are `5.0·10⁻⁹` km and `5.0·10⁻¹⁰` km/s, half a unit of the last printed digit. |
| Validity | Status 9 for a value that is not finite, `n ≤ 0`, `e < 0`, or `1 ≤ e` | The reference code has no such test, and outside these ranges it takes powers and square roots of negative numbers. |

## Differences from the reference code

| Reference code | This program | Effect |
|---|---|---|
| Reduces `nodem`, `argpm`, `xlm`, and `u` modulo `2π` | No reduction | Every later use of these angles is a sine, a cosine, or Kepler's equation, whose solution shifts by the same multiple of `2π`.  The results differ by rounding. |
| `mm = (xlm − argpm − nodem) mod 2π` with `xlm = mm + argpm + nodem` | `mm` unchanged, and `u = mm + argpm + temp xlcof axnl` | The same real number.  The results differ by rounding. |
| Computes every constant, then tests for the deep-space path | Tests for the deep-space path after `no` | No effect on a near-Earth element set. |
| Leaves `d2`, `d3`, `d4`, `t3cof`, `t4cof`, and `t5cof` at 0 when `isimp` holds | The same | None. |
| Computes `a`, `alta`, `altp`, `ainv`, and `gsto` | Omitted | The near-Earth propagation reads none of them. |
| Runs `sgp4` at time 0 at the end of `sgp4init` | Omitted | The call changes no constant on the near-Earth path. |
| Returns no state for the errors 1, 2, and 4 | Returns zeros with the status | None. |
| The platform's `sin`, `cos`, `pow`, and `atan2` | The library's functions, each within one or two steps of the correctly rounded value | The results are the same bits on every back end and differ from the reference code's by rounding. |

## Open

The enclosing program, the real specification with its theorems, and the readers of OMM and TLE data are not written.  The deep-space mode, the proved reader's forms, and the handling of the epoch remain to decide with those parts.
