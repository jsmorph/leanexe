# Binary to decimal conversion: `print64` and `print32`

The module `PrintFloat` exports `print64`, `print64Ecma`, `print32`, and `print32Ecma`, which write a binary64 word, or the binary32 pattern in the low 32 bits of a word, as a decimal string.  The digits are those of the shortest decimal that rounds back to the word, the one nearest to the word's value among the shortest, with an even last digit at a tie [1, 2, 3], written in a scientific layout (`1.5e3`) or in the layout of ECMA-262's Number::toString (`1500`) [3].  The method finds the largest decimal exponent `J` at which a multiple of `10 ^ J` lies in the word's rounding interval and takes the multiple nearest to the value, with exact integers of any size from [the limb module](Uscale.md).  On branch `w/strconv` the implementation compiles with the verified compiler and agrees with an independent search on 889 words; the theorems of the specification below are open, and the track `strconv` is proving them (stage 4).

## Specification

A finite nonzero word `w` with sign `neg`, significand `Q`, and binade `E` rounds back from exactly the reals of its rounding interval (`StrconvInterval.interval_iff`), and `StrconvRound.Shortest64 w neg d e` states that `(-1)^neg · d · 10^e` lies in it, has the fewest significant digits among the decimals that do, the least distance from the value of `w` among those with as many digits, and an even last digit at an equal distance from a different decimal with as many digits.  This is ECMA-262's rule for Number::toString with the choice its Note 2 recommends, and the rule of Python's `repr` [3, 4]; Java's `Double.toString` differs, since it allows a two-digit decimal where the shortest has one digit [5].

| Word | `print64`, `print32` | `print64Ecma`, `print32Ecma` |
|---|---|---|
| finite nonzero, shortest `t · 10^k` with `t` not divisible by 10 | `sciLayout neg t k`: the digits of `t` with a point after the first when there are several, `e`, and the exponent of the first digit, with `-` when negative: `1.5e3`, `5e-324`, `-1.25e-1` | `ecmaLayout neg t k`: plain notation when the point position `n = k + digits` lies from -5 to 21, otherwise an exponent with `+` or `-`: `1500`, `0.000001`, `1e-7`, `1.5e+21` |
| `+0`, `-0` | `0e0`, `-0e0` | `0`, `-0` |
| infinities | `Infinity`, `-Infinity` | the same |
| NaNs | `NaN` | the same |

ECMA-262 prints negative zero as `0`; the printers print `-0`, so that the round trip through the parsers recovers every word (decision 7 of the research report).  The strings of finite words are numbers of RFC 8259's grammar, and every string is a number of the general grammar of [the parser document](ParseFloat.md).  The planned theorems, for every word `w`:

```lean
theorem print64_derives (w : UInt64) :
    ∃ s n, print64 w = words s ∧ Derives true s n ∧ round64 n = canon64 w
theorem print64_roundtrip (w : UInt64) : parse64 true (print64 w) = (true, canon64 w)
theorem print64_shortest (w : UInt64) (hf : Wasm.IEEE64.isFinite w)
    (hz : Wasm.IEEE64.scaledMagnitude w ≠ 0) :
    ∃ s neg d e, print64 w = words s ∧ Derives false s (.dec neg d e) ∧ Shortest64 w neg d e
theorem print64_layout (w : UInt64) (hf : Wasm.IEEE64.isFinite w)
    (hz : Wasm.IEEE64.scaledMagnitude w ≠ 0) :
    ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧
      print64 w = words (sciLayout neg t k) ∧ print64Ecma w = words (ecmaLayout neg t k)
-- the same for print64Ecma; print32_* on x : UInt32 with the input x.toUInt64, round32,
-- Shortest32, canon32; print32_low: print32 w = print32 (w.toUInt32.toUInt64)
```

## Algorithm

In quarter units of the least subnormal `2 ^ -ν` (`ν` = 1074 or 149), the value of a word with significand `Q` in binade `E` is `4 Q · 2 ^ (E - 1)`, and its rounding interval runs from `(4 Q - 2) · 2 ^ (E - 1)` to `(4 Q + 2) · 2 ^ (E - 1)`, with the lower end `(4 Q - 1) · 2 ^ (E - 1)` at the start of a normal binade (`E ≥ 2`, `Q = 2 ^ (p - 1)`), where the previous value lies at half the spacing; the ends belong to the interval when `Q` is even, since a tie rounds to the even significand.  Let `J` be the largest exponent for which some multiple of `10 ^ J` lies in the interval.  The multiples of `10 ^ J` in the interval form a run of consecutive integers `m` that contains no multiple of 10, so they all have the same number `D` of digits, and every other decimal in the interval has more digits, except a one-digit multiple of `10 ^ (J - 1)` when `D = 1`.  The printers therefore take the multiple of `10 ^ J` nearest to the value, the even one at a tie, and when it has one digit compare it with the nearest one-digit multiple of `10 ^ (J - 1)` in the interval.  The second case arises only for subnormal words with a significand below 10, as `9e-46` and `1e-45` both lie in the interval of the least binary32 subnormal, and there the multiple of `10 ^ J` is nearer; the printers make the comparison in every case rather than rely on such a count.

`shortest` searches for `J` from an exponent above the interval: the upper end is below `2 ^ B` with `B` the bit length of `4 Q + 2` plus `E - 1 - ν - 2`, and `10 ^ (j - 1) ≥ 2 ^ B` for `j = ⌈31 B / 100⌉` when `B ≥ 0` and `j = -⌊3 |B| / 10⌋` otherwise, since `2 ^ 100 < 10 ^ 31` and `10 ^ 3 < 2 ^ 10`.  At each exponent `j` the least and greatest multipliers in the interval are the quotients of the ends by `10 ^ j`, rounded up and down with the remainder flags of `Uscale.scaledQuot`, and the nearest multiplier to the value comes from `⌊2 v / 10 ^ j⌋` and its remainder flag; the clamp of that nearest integer into the run of multipliers is the nearest multiplier in the interval.  Signed exponents are words with the bias `2 ^ 62`, as in the parsers.

## Implementation

[`PrintFloat.lean`](PrintFloat.lean) holds the printers in the verified dialect, written for this project from the definitions above; no third-party code is ported.  The module compiles with `verified_compile` (`build/transcendentals/strconv-print-2.log` on the build host) together with the routines of `Uscale.lean` it calls.

| Function | Role |
|---|---|
| `limbsOf`, `quotAt` | A word as limbs, and the quotient of `N · 2 ^ sn` by `2 ^ sd · 10 ^ j` with its remainder flag, for a decimal exponent `j` of either sign |
| `range`, `found` | The least multiplier and the greatest plus one at exponent `j`, and whether there is one |
| `nearest`, `clamp` | The integer nearest to `v` from `⌊2 v⌋` and its remainder flag, and its clamp into a run |
| `startExp`, `shortest` | The start of the search, the search for `J`, and the choice of the decimal |
| `numDigits`, `digitAt` | The number of digits of a word and its digit `i` as an ASCII byte |
| `sciAt`, `sciLayoutW`, `ecmaAt`, `ecmaLayoutW` | Byte `i` of each layout and the array built from it |
| `fixed`, `special` | The strings of the non-finite words and the zeros |
| `print64With`, `print32With` | The fields of the word and the dispatch |

## Theorems

No printing theorem is proved yet.  The proof is planned in three parts: the choice of the decimal against `Shortest64` and `Shortest32`, in terms of the interval of `StrconvInterval`, with the analysis of significant digits above; the search and the quotients against that choice, with `Uscale.scaledQuot_spec`; and the layouts against `sciLayout` and `ecmaLayout`, element by element.  `print64_derives` and `print64_roundtrip` then follow from the layouts and the parsers' theorems.

## Tests

[`PrintFloatAccuracy.lean`](PrintFloatAccuracy.lean) runs the compiled native code of the four printers on the 889 words of [`data/strconv/print-cases.txt`](../../data/strconv/print-cases.txt), 563 binary64 and 326 binary32, and requires each string to equal the expected one, both strings of each word to read back through `ParseFloat.parse64` or `parse32` in the general grammar as the word (every NaN as the canonical NaN), and the strings of finite words to be numbers of RFC 8259's grammar.  [`tools/strconv/print_cases.py`](../../tools/strconv/print_cases.py) computes the expected strings by a search over the number of significant digits with exact rationals: for each count from 1 upward it collects every decimal of that many digits in the rounding interval at every exponent the interval reaches, and the first count with a candidate gives the nearest, with an even last digit at a tie.  This search does not use the largest exponent `J`, and for binary64 the program also checks the digits and exponent against Python's `repr`.  The words are the zeros, infinities, and NaNs, the twelve smallest subnormals, the largest subnormal, the smallest normal, starts and ends of binades across the exponent range, the largest finite word, the neighbors of powers of ten, values at the limits of the ECMAScript layout, and 180 words from a fixed seed.  All 889 cases agree, in 372 seconds through `lake env lean --run` (`build/transcendentals/strconv-praccuracy-2.log`).

## Limits

The theorems will trust Talos's semantics of WebAssembly and its decoder, as every theorem of the verified compiler does.  The printers write one byte per word, which costs eight bytes of memory per character.  Every NaN prints as `NaN`, since the grammar carries no payload, and the round trip recovers the canonical NaN.  The search costs about twenty exact quotients of integers of up to 18 limbs per word; the native check of 889 words, four strings and four parses each, takes 372 seconds under `lean --run`, and no faster method, such as Cox's or Schubfach's tables, is used.

## References

1. R. Cox, "Floating-Point Printing and Parsing Can Be Simple And Fast (Floating Point Formatting, Part 3)", 19 January 2026, [research.swtch.com/fp](https://research.swtch.com/fp).  Not peer reviewed.
2. R. Giulietti, "The Schubfach way to render doubles", revision of 20 March 2022, self-published, [PDF on Google Drive](https://drive.google.com/file/d/1gp5xv4CAa78SVgCeWfGqqI4FfYYYuNFb), CC BY-SA 4.0.  Not peer reviewed.
3. Ecma International, ECMA-262, *ECMAScript 2027 Language Specification*, draft of 9 October 2026, [tc39.es/ecma262](https://tc39.es/ecma262/): 6.1.6.1.20 (Number::toString) with Notes 1 to 3.
4. Python Software Foundation, Python documentation, [`sys.float_repr_style`](https://docs.python.org/3/library/sys.html#sys.float_repr_style) and [What's New in Python 3.1](https://docs.python.org/3/whatsnew/3.1.html).
5. Oracle, Java SE 21 API, [`Double.toString(double)`](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Double.html#toString(double)).
