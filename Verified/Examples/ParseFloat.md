# Decimal to binary conversion: `parse64` and `parse32`

The module `ParseFloat` will export `parse64` and `parse32`, which read a number string and return the binary64 or binary32 word of roundTiesToEven applied to the number the string denotes, for strings of any length, or a rejection when the string is not a number of the chosen grammar.  The method is Clinger's fast path for short inputs [1, 7] and otherwise one exact rounding of the decimal value, computed as Cox's unrounded scaling [2] with integers of any size, after the significant digits are cut to 768 (binary64) or 113 (binary32) with a half unit standing for any nonzero remainder.  The decided bound is correct rounding: the result equals the reference word `round64 n` or `round32 n` of the number `n` the string denotes, with no tolerance.  On branch `w/strconv` the specification of this document is proved (stage 1, merged into `transcendentals` at `cf227e3f`), the integer library `Uscale.lean` compiles with the verified compiler without its theorems, and the parsers and their theorems are not yet written; the track `strconv` does that work.

## Specification

### Grammar

A string is a list of bytes, and the compiled function receives it as an `Array UInt64` with one byte per word (`StrconvGrammar.words`).  The grammar is the inductive relation `Derives general s n` of [the grammar module](StrconvGrammar.lean), with one constructor per production, so that it can be compared with RFC 8259 [3].  With `general` false it is exactly RFC 8259's `number`; with `general` true it is a superset in the manner of C's `strtod` [5], without white space, NaN payloads, or the longest-prefix rule, so the whole input must match.

| Production | Grammar | Bytes | Number denoted |
|---|---|---|---|
| `Derives.json` | RFC 8259 | `[ "-" ] int [ frac ] [ exp ]` with `int = "0" / digit1-9 *DIGIT`, `frac = "." 1*DIGIT`, `exp = ("e" / "E") [ "+" / "-" ] 1*DIGIT` | `.dec neg (decValue (i ++ f)) (e - f.length)` |
| `Derives.decimal` | general | `[ "+" / "-" ] ( 1*DIGIT [ "." *DIGIT ] / "." 1*DIGIT ) [ exp ]` | the same |
| `Derives.hex` | general | `[ "+" / "-" ] ("0x" / "0X") ( 1*HEXDIG [ "." *HEXDIG ] / "." 1*HEXDIG ) ("p" / "P") [ "+" / "-" ] 1*DIGIT` | `.hex neg (hexValue (i ++ f)) (e - 4 · f.length)` |
| `Derives.inf` | general | `[ "+" / "-" ]` then `inf` or `infinity` in any case | `.inf neg` |
| `Derives.nan` | general | `[ "+" / "-" ]` then `nan` in any case | `.nan` |

`Num` has four forms: `.dec neg d e` for `(-1)^neg · d · 10^e`, `.hex neg d e` for `(-1)^neg · d · 2^e`, `.inf neg`, and `.nan`.  A decimal's integer and fraction digits form one integer `d`, and the exponent is reduced by the number of fraction digits, so `1.0` denotes `.dec false 10 (-1)` and `-0` denotes `.dec true 0 0`.  The general grammar accepts a sign before `inf`, `infinity`, and `nan`; since `Num.nan` has no sign, a signed NaN denotes the same number as an unsigned one.  The hexadecimal significand requires its binary exponent, as C's `%a` output always has one, so `0x10` is no number of the grammar.  The exponent may have any number of digits, and its value is an unbounded integer.

[The decoder module](StrconvDecode.lean) gives the grammar a second form: `decode general s` reads the sign, tests for the special words and the prefix `0x`, and splits the significand and the exponent at the first byte outside each class with `takeWhile` and `dropWhile`.  `derives_iff_decode` proves that `Derives general s n` holds exactly when `decode general s = some n`, so a string denotes at most one number (`derives_unique`), and `derives_general` shows that every RFC 8259 number is a number of the general grammar with the same value.  The parser's scanner computes the same splits with positions in the array, and its proof compares it with `decode`.

### Results

[The rounding module](StrconvRound.lean) defines the reference words.  `round64 (.dec neg d e)` is `F64PositiveRounding.roundNearestEven (d · 10^e)` with the sign applied by `Wasm.IEEE64.negate`, and `.hex` is the same with `2^e`; ProofKit's reference [F64PositiveRounding](../../LeanExe/ProofKit/F64PositiveRounding.lean) is the nearest finite nonnegative word, the even one at a tie, and positive infinity from `2^1024 - 2^970` on.  `round32` uses the binary32 reference of [the binary32 module](StrconvBinary32.lean), defined the same way over `UInt32` words with `CodeLib.IEEE32.value` and positive infinity from `2^128 - 2^103` on.  Applying the sign after rounding the magnitude is roundTiesToEven, since that rounding is symmetric, and it fixes the sign of zero as IEEE 754 clause 5.12.2 requires [4].

| Input | Number | `parse64` | `parse32` |
|---|---|---|---|
| `-0`, `-0.0e5` | `.dec true 0 _` | `(true, 0x8000000000000000)` | `(true, 0x80000000)` |
| `-1e-400` | below half the least subnormal | `(true, 0x8000000000000000)` | `(true, 0x80000000)` |
| `1e400`, `1e99999999999999999999` | beyond the overflow threshold | `(true, 0x7FF0000000000000)` | `(true, 0x7F800000)` |
| `-inf`, `-Infinity` (general) | `.inf true` | `(true, 0xFFF0000000000000)` | `(true, 0xFF800000)` |
| `nan`, `-NaN` (general) | `.nan` | `(true, 0x7FF8000000000000)` | `(true, 0x7FC00000)` |
| `+1`, `01`, `.5`, `inf` (RFC 8259) or `1e`, `0x10`, ` 1` (either) | none | `(false, 0)` | `(false, 0)` |

The planned theorems state the parsers' results for every string of fewer than `2 ^ 32` bytes:

```lean
theorem parse64_accept (general : Bool) (s : List UInt8) (n : Num) (hs : s.length < 2 ^ 32)
    (h : Derives general s n) : parse64 general (words s) = (true, round64 n)
theorem parse64_reject (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬ Derives general s n) : parse64 general (words s) = (false, 0)
-- parse32_accept and parse32_reject: the same with (round32 n).toUInt64
```

The length hypothesis keeps the dialect's 64-bit positions and counts exact.  It excludes no input of the compiled module: the module's memory holds at most 4 GiB, so an array of one-byte words passed to it has fewer than `2 ^ 29` elements, and every string it can receive satisfies the hypothesis.  Inputs of any length below that bound are rounded correctly, which meets IEEE 754's requirement of correct rounding for at least `p10 + 3` significant digits [4, 9] and is the behavior that C23 announces by defining `CR_DECIMAL_DIG` as `UINTMAX_MAX` [10].

### Decisions

The user decided the grammar's two modes, unlimited length, one byte per word, binary32 results as words holding the 32-bit pattern, the pair of a flag and a word as the result, and the exact first stage with Clinger's fast path, from the fourteen recommendations of the research report of 2026-10-12.  The journal section "Decimal strings and binary floating point, plan and statements (track `strconv`)" in [the development journal](../../devnotes.md) records the decisions, the statements, and their later adjustments, among them the signed NaN and the length hypothesis.

## Algorithm

The scanner reads the sign, the special words, and the hexadecimal prefix, then the integer digits, the point, the fraction digits, and the exponent, as `decode` does.  Leading zeros are skipped, the next 768 digits (113 for binary32) form an integer `D` with exponent `q`, and any nonzero digit after them is replaced by half a unit, `(2 D + 1) · 10^q / 2`.  This keeps the rounding because every decision point of binary64 rounding, a value of the grid or a midpoint between neighbors, has at most 768 significant digits, so none lies strictly between `D · 10^q` and `(D + 1) · 10^q` when `D ≥ 10^767` (`StrconvTruncate.truncate64`); the counts 768 and 113 come from `(2 ^ 54 + 1) · 5 ^ 1075 < 10 ^ 768` and `(2 ^ 25 + 1) · 5 ^ 150 < 10 ^ 113`.  A decimal exponent beyond a fixed bound saturates, since the value is then beyond the overflow threshold or below half the least subnormal whatever the digits.

When `D < 2 ^ 53` and `|q| ≤ 22`, both `D` and `10^|q|` are exact doubles, and one multiplication or division rounds once to the result [1, 7]; this is the fast path.  Otherwise the value `N / M` in units of the least subnormal, with `N` and `M` products of `D`, powers of ten, and powers of two, is rounded exactly.  The parser chooses a shift `s` from the bit lengths of `N` and `M` so that the quotient `u = ⌊N · 2^s / M⌋` has `p + 2` or `p + 3` bits and records whether the division leaves a remainder; this pair is Cox's unrounded form of `N · 2^s / M` [2], computed by `Uscale.scaledQuot` with exact integers.  The bit length of `u` gives the binade, the binade gives the number of bits to drop, and the dropped bits with the remainder flag give the nearest-even significand.  A hexadecimal significand needs no division: its bits and the binary exponent give the binade directly.

## Implementation

`Uscale.lean` holds the integer routines on arrays of 32-bit limbs in words, least significant first: `mulSmall` (multiply by a word below `2^32` and add one), `shl` (multiply by a power of two), `le`, `sub`, `bitLen`, `divBits` (restoring division with a quotient below `2^bits`), `scaledQuot`, and `pow10`.  A 32-bit limb keeps every product of a limb by a word below `2^32`, plus two such words, inside one 64-bit word, so no routine needs a 128-bit product.  The verified compiler accepts the module (`build/transcendentals/strconv-uscale-3.log` on the build host), which shows that each routine is within the dialect; their theorems are not yet written.  `ParseFloat.lean` does not exist yet.  No third-party code is ported: the algorithms follow the papers [1, 2], so no license notice applies beyond the citations.

## Theorems

Every theorem in the table is proved on branch `w/strconv` and reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  The parser theorems of the specification are open.

| Theorem | Module | Statement |
|---|---|---|
| `derives_iff_decode` | `StrconvDecode` | `Derives general s n ↔ decode general s = some n` |
| `derives_unique` | `StrconvDecode` | A string denotes at most one number. |
| `derives_general` | `StrconvDecode` | Every RFC 8259 number derives the same number in the general grammar. |
| `ref64`, `ref32` | `StrconvWords` | The references are the words of the grid's reference `refPos` at the value in units of `2^-1074` or `2^-149`. |
| `positive_reference` | `StrconvGrid` | When `RoundsTo f y E Q` (binade `E`, nearest-even significand `Q`), `refPos f y` is the encoding of `Q` in binade `E`, or infinity. |
| `rational64`, `rational32` | `StrconvRational` | Talos's `roundRationalMagnitude false N D` is the reference word of `N / D` for `N, D > 0`. |
| `dyadic64`, `dyadic32` | `StrconvRational` | Talos's `roundDyadicMagnitude false n k` is the reference word of `n / 2^k` for `n > 0`. |
| `ofScientific_spec` | `StrconvOfScientific` | `(Float.ofScientific m s e).toBits = round64 (.dec false m (if s then -e else e))` |
| `ofScientific32_spec` | `StrconvOfScientific32` | `(Float32.ofScientific m s e).toBits = round32 (.dec false m (if s then -e else e))` |
| `truncate64`, `truncate32` | `StrconvTruncate` | For `D ≥ 10^767` (`10^112`) and `0 < θ < 1`, `(D + θ) · 10^j` and `(D + 1/2) · 10^j` have the same reference. |

`ofScientific_spec` concerns Lean's own `Float.ofScientific` at `v4.34.0-rc2` [8], which both compilers use for the decimal literals of a program, so every decimal literal of type `Float` or `Float32` in a verified program means the correctly rounded value.

## Proof

[The grid module](StrconvGrid.lean) proves the rounding of a real number in units once for a format given by its precision and the exponent field of its infinities, from the ideas of `FmaGrid` and `FmaNearestEven`: `mag_succ`, `mag_dvd`, and `mag_below` describe the magnitudes of encodings, `nearest_even_pack` shows that a significand rounded in its binade gives the nearest-even encoding, and `nearest_even_unique` shows that two nearest encodings differ by at most one.  [The word module](StrconvWords.lean) connects the grid to ProofKit's binary64 reference and to the binary32 reference, and [the rational module](StrconvRational.lean) proves Talos's rational and dyadic roundings equal to them through `roundsTo_quotient`.  The two `ofScientific` modules follow Lean's definition: the fast path through `F64Bits` and `F32Bits` and the table of powers of ten checked entry by entry, and the model's path through ProofKit's `F64DivCore.pack_div_finite` and `F64RoundDyadic.pack_round_above_dyadic` and their binary32 counterparts.  [The truncation module](StrconvTruncate.lean) proves that two reals in an open interval free of half-grid points have the same reference (`refPos_transfer`) and bounds the significant digits of those points.  The journal sections of track `strconv` record the failed runs and their causes.

The parser's proof is planned in three parts: the limb routines' values as natural numbers (`UscaleTheorem`), the scanner against `decode` with the truncation and saturation lemmas, and the rounding of the unrounded quotient against `RoundsTo`, followed by the byte and file theorems in the form of `ExpTheorem.exp_bytes_accuracy`.

## Tests

No test of the parsers exists yet.  The planned native check `ParseFloatAccuracy.lean` compares `parse64` and `parse32` with Talos's `roundRationalMagnitude`, which `rational64` and `rational32` prove equal to the references, on a few hundred lines selected from Nigel Tao's parse-number-fxx-test-data to cover each of its source files, constructed inputs next to midpoints with up to 1,700 digits, Paxson's tables of hard cases as reproduced in Go's `testfp.txt`, and grammar cases for every production and rejection.  The selection and the Apache-2.0 notice of the included data will be recorded with the check.

## Limits

The theorems trust Talos's semantics of WebAssembly and its decoder, as every theorem of the verified compiler does, and the file theorem will trust `binary_file%` to read the bytes that the test script writes.  The grammar has no white space, no NaN payloads, no digit separators, and no longest-prefix rule, so a caller must trim the input; a rejected string gives `(false, 0)`, which no accepted string gives.  Every NaN result is the canonical NaN of its format, since the grammar carries no payload.  The binary32 parser returns the pattern in the low 32 bits of a word, since the verified dialect has no `Float32` type.

## References

1. W. D. Clinger, "How to Read Floating Point Numbers Accurately", *Proceedings of the ACM SIGPLAN 1990 Conference on Programming Language Design and Implementation (PLDI '90)*, pp. 92–101, 1990, [doi:10.1145/93542.93557](https://doi.org/10.1145/93542.93557).  Crossref record checked; the text layer of the author's copy could not be read, and the fast path's conditions are taken from [7].
2. R. Cox, "Floating-Point Printing and Parsing Can Be Simple And Fast (Floating Point Formatting, Part 3)", 19 January 2026, [research.swtch.com/fp](https://research.swtch.com/fp), section "Unrounded Numbers": the unrounded form `⟨x⟩` is the integer part of `x` followed by the half bit and a bit for any remainder.  Not peer reviewed.
3. T. Bray (Ed.), *The JavaScript Object Notation (JSON) Data Interchange Format*, RFC 8259, December 2017, [doi:10.17487/RFC8259](https://doi.org/10.17487/RFC8259), section 6, "Numbers".
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229), clause 5.12.  The standard is paywalled; clause 5.12 was read in the 2008 text that R. B. Kearfott quoted to the P1788 list on 4 July 2013, [msg06624](https://grouper.ieee.org/groups/1788/email/msg06624.html).
5. ISO/IEC JTC1/SC22/WG14, N1570, committee draft of ISO/IEC 9899:2011, 12 April 2011, [n1570.pdf](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), 7.22.1.3, "The strtod, strtof, and strtold functions".
6. Ecma International, ECMA-262, *ECMAScript 2027 Language Specification*, draft of 9 October 2026, [tc39.es/ecma262](https://tc39.es/ecma262/): 7.1.4.1.1 StringToNumber and 7.1.4.1.3 RoundMVResult, which rounds correctly up to 20 significant digits and leaves the rounding of longer inputs to the implementation.
7. D. Lemire, "Number Parsing at a Gigabyte per Second", *Software: Practice and Experience* 51(8):1700–1727, 2021, [doi:10.1002/spe.2984](https://doi.org/10.1002/spe.2984); read as [arXiv:2101.11408v9](https://arxiv.org/abs/2101.11408), section 3: Clinger's fast path for `w × 10^q` with `w ≤ 2^53` and `-22 ≤ q ≤ 22`, and `w ≤ 2^24` and `-10 ≤ q ≤ 10` for binary32.
8. Lean FRO, Lean 4 at tag `v4.34.0-rc2`, `src/Init/Data/OfScientific.lean` (`Float.ofScientific`, `Float32.ofScientific`) and `src/Init/Data/Float/Model/Unpacked/Operations/OfScientific.lean`, read in the toolchain of the repository's `lean-toolchain`.
9. S. Boldo, C.-P. Jeannerod, G. Melquiond, and J.-M. Muller, "Floating-point arithmetic", *Acta Numerica* 32:203–290, 2023, [doi:10.1017/S0962492922000101](https://doi.org/10.1017/S0962492922000101), section 2.11.2: the 2019 standard's requirement of correct rounding for at least `p10 + 3` digits.
10. ISO/IEC JTC1/SC22/WG14, N3220, working draft of ISO/IEC 9899:2024, 22 February 2024, [n3220.pdf](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3220.pdf), F.5: `CR_DECIMAL_DIG` is at least `M + 3`, and `UINTMAX_MAX` when every number of digits is correctly rounded.
