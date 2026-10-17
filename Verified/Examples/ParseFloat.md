# Decimal to binary conversion: `parse64` and `parse32`

The module `ParseFloat` exports `parse64` and `parse32`, which read a number string and return the binary64 or binary32 word of roundTiesToEven applied to the number the string denotes, for strings of fewer than `2^32` bytes, or a rejection when the string is not a number of the chosen grammar.  The method is Clinger's fast path for short inputs [1, 7] and otherwise one exact rounding of the decimal value, computed as Cox's unrounded scaling [2] with integers of any size, after the significant digits are cut to 768 (binary64) or 113 (binary32) with a half unit standing for any nonzero remainder.  The decided bound is correct rounding: the result equals the reference word `round64 n` or `round32 n` of the number `n` the string denotes, with no tolerance.  On branch `w/strconv` the specification of this document is proved (stage 1, merged into `transcendentals` at `cf227e3f`), the integer routines of [the limb module](Uscale.md) are proved (stage 2), `ParseFloat.lean` compiles with the verified compiler and agrees with exact references on 1,030 test strings, and [the theorem module](ParseFloatTheorem.lean) proves `parse64_accept`, `parse64_reject`, `parse32_accept`, and `parse32_reject`, with byte and file theorems for the compiled module (stage 3).

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

The theorems of `ParseFloatTheorem` state the parsers' results for every string of fewer than `2 ^ 32` bytes:

```lean
theorem parse64_accept (general : Bool) (s : List UInt8) (n : Num) (hs : s.length < 2 ^ 32)
    (h : Derives general s n) : parse64 general (words s) = (true, round64 n)
theorem parse64_reject (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬ Derives general s n) : parse64 general (words s) = (false, 0)
theorem parse32_accept (general : Bool) (s : List UInt8) (n : Num) (hs : s.length < 2 ^ 32)
    (h : Derives general s n) : parse32 general (words s) = (true, (round32 n).toUInt64)
theorem parse32_reject (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬ Derives general s n) : parse32 general (words s) = (false, 0)
```

They follow from `parse64_spec` and `parse32_spec`, which state `parse64 general (words s) = res64 (decode general s)` with `res64 (some n) = (true, round64 n)` and `res64 none = (false, 0)`, and `derives_iff_decode`.

The length hypothesis keeps the dialect's 64-bit positions and counts exact.  It excludes no input of the compiled module: the module's memory holds at most 4 GiB, so an array of one-byte words passed to it has fewer than `2 ^ 29` elements, and every string it can receive satisfies the hypothesis.  Inputs of any length below that bound are rounded correctly, which meets IEEE 754's requirement of correct rounding for at least `p10 + 3` significant digits [4, 9] and is the behavior that C23 announces by defining `CR_DECIMAL_DIG` as `UINTMAX_MAX` [10].

### Decisions

The user decided the grammar's two modes, unlimited length, one byte per word, binary32 results as words holding the 32-bit pattern, the pair of a flag and a word as the result, and the exact first stage with Clinger's fast path, from the fourteen recommendations of the research report of 2026-10-12.  The journal section "Decimal strings and binary floating point, plan and statements (track `strconv`, minideb2)" in [the development journal](../../devnotes.md) records the decisions, the statements, and their later adjustments, among them the signed NaN and the length hypothesis.

## Algorithm

The scanner reads the sign, the special words, and the hexadecimal prefix, then the integer digits, the point, the fraction digits, and the exponent, as `decode` does.  Leading zeros are skipped, the next 768 digits (113 for binary32) form an integer `D` with exponent `q`, and any nonzero digit after them is replaced by half a unit, `(2 D + 1) · 10^q / 2`.  This keeps the rounding because every decision point of binary64 rounding, a value of the grid or a midpoint between neighbors, has at most 768 significant digits, so none lies strictly between `D · 10^q` and `(D + 1) · 10^q` when `D ≥ 10^767` (`StrconvTruncate.truncate64`); the counts 768 and 113 come from `(2 ^ 54 + 1) · 5 ^ 1075 < 10 ^ 768` and `(2 ^ 25 + 1) · 5 ^ 150 < 10 ^ 113`.  A value of at least `10^309` lies beyond binary64's overflow threshold and one below `10^-325` below half its least subnormal, whatever the digits, so a decimal exponent outside that range needs no arithmetic; for binary32 the bounds are `10^39` and `10^-46`.

When no digit was dropped, `D < 2 ^ 53`, and `|q| ≤ 22`, both `D` and `10^|q|` are exact doubles, and one multiplication or division rounds once to the result [1, 7]; this is the fast path, used for binary64 only.  Otherwise the value is `N / M` units of the least subnormal, with `N` and `M` products of `D` (or `2 D + 1`), powers of ten, and powers of two.  The parser shifts `N` or `M` left so that the quotient `u = ⌊N · 2^s / M⌋` has `p + 2` or `p + 3` bits and records whether the division leaves a remainder; this pair is Cox's unrounded form of `N · 2^s / M` [2], computed by `Uscale.scaledQuot` with exact integers.  The bit length of `u` and the binary exponent give the binade `E`, the binade gives the number `r` of bits to drop, at least two, and the dropped bits with the remainder flag give the nearest-even significand `Q`: up when the dropped bits exceed half of `2 ^ r`, down when they fall short of it, and at exactly half up when the remainder is nonzero or `u >> r` is odd.  The word is `(E - 1) · 2 ^ (p - 1) + Q`, or infinity from the exponent field `F` on.

A hexadecimal significand needs no division.  Its first 15 significant hexadecimal digits, 60 bits, form a word `u`, any nonzero digit after them sets the remainder flag, and the binary exponent of the last kept digit places `u`, so the same rounding step gives the word.  When a digit is dropped, `u` has at least 57 bits, so at least two bits are dropped in every binade and the flag decides every tie.

## Implementation

[`ParseFloat.lean`](ParseFloat.lean) holds the parsers in the verified dialect, written for this project from the papers [1, 2]; no third-party code is ported, so no license notice applies beyond the citations.  The module compiles with `verified_compile` in 37 seconds (`build/transcendentals/strconv-parse-1.log` on minideb2) together with the routines of `Uscale.lean` it calls.  Every byte is read through `Uscale.limb`, which gives 0 past the end without reading past it, since native Lean prints a panic message for each read past the end and the test script counts such messages.

| Function | Role |
|---|---|
| `span s hex i` | The first position from `i` whose byte is no digit of the class, as `takeWhile` splits a list |
| `matchLower s i len w` | Whether the bytes from `i` to the end are, in lower case, the `len` bytes packed in `w` (`inf`, `infinity`, `nan`) |
| `expPart s i` | An exponent's sign and digits from `i` to the end: well formed, negative, and the value saturated at `10 ^ 11` |
| `digitPos`, `leadingZeros` | The position of significand digit `k` past the point, and the number of leading zeros |
| `digitsVal`, `chunkVal` | The value of the kept digits as limbs, nine digits at a time through `Uscale.mulSmall` |
| `anyNonzero` | Whether a dropped digit is nonzero, the sticky flag |
| `decParse`, `hexParse` | The significand and exponent of a decimal or hexadecimal string, with the flag of the grammar's checks |
| `decRound` | The saturations, the products by powers of ten, the shifts, and `Uscale.scaledQuot` |
| `roundUnits` | The binade and the nearest-even significand from the unrounded quotient, and the encoding |
| `pow10Float`, `fastPath` | Clinger's fast path with `10 ^ k` built by `k` exact multiplications by 10 |
| `parse64`, `parse32` | The sign, the special words, the hexadecimal prefix, and the dispatch |

Signed exponents are words with the bias `2 ^ 62`, which keeps every sum of exponents, digit counts, and shifts inside 64 bits, and an exponent's digits saturate at `10 ^ 11`.  The digits of a string of fewer than `2 ^ 32` bytes move the value by fewer than `2 ^ 32 + 1` decimal places or `2 ^ 34 + 4` binary places, so an exponent beyond `10 ^ 11` in magnitude puts the value beyond the overflow threshold or below half the least subnormal both before and after saturation.  The first version saturated at `10 ^ 10`, which a hexadecimal fraction of more than `2.5 · 10 ^ 9` digits can defeat; the compiled module never receives such a string, but the theorems' length hypothesis allows it.  `parse32` returns the binary32 pattern in the low 32 bits of a word and has no fast path, since the dialect has binary64 floats only.

## Theorems

Every theorem in the table reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

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
| `scaledQuot_spec`, `mulPow10_spec`, `bitLen_spec` | `UscaleDiv`, `UscaleArith` | The limb routines that the parsers call compute the quotient and remainder flag of `n · 2 ^ sn / (d · 2 ^ sd)`, products by powers of ten, and bit lengths; [the limb document](Uscale.md) lists every routine's theorem. |
| `roundUnits_spec` | `ParseFloatRound` | `roundUnits p F u sticky T` is `refPos f ((u + φ) · 2 ^ (T - 2 ^ 62))` for `φ` in `[0, 1)`, positive exactly when `sticky`, if `sticky` implies that `u` has at least `p + 2` bits. |
| `decRound_spec` | `ParseFloatDec` | `decRound` is `refPos f (D' · 10 ^ (qb - 2 ^ 62) · 2 ^ ν)` with `D' = D`, or `D + 1/2` when `sticky`, for `D` of `kept` digits and the format's saturation bounds. |
| `span_spec`, `matchLower_spec`, `expPart_spec` | `ParseFloatScan` | `span` stops where `takeWhile` of the class stops, `matchLower` tests the lower-case bytes, and `expPart` is `decodeExpDigits` with the value saturated at `10 ^ 11`. |
| `leadingZeros_spec`, `anyNonzero_spec`, `digitsVal_spec`, `hexVal_spec` | `ParseFloatDigits` | The number of leading zeros, whether a digit in a range is nonzero, and the value of a run of digits as limbs or as a word. |
| `decParse_spec`, `hexParse_spec` | `ParseFloatDecParse`, `ParseFloatHexParse` | The flag is the success of the decoder's decimal or hexadecimal branch, and the limbs or word, the count, the biased exponent, and the sticky flag are those of the significand's digits. |
| `pow10_exact`, `fastPath_spec` | `ParseFloatFast` | `pow10Float k` is the exact double `10 ^ k` for `k ≤ 22`, and `fastPath D qb` is the reference word of `D · 10 ^ q` for `D < 2 ^ 53` and `\|q\| ≤ 22`. |
| `dec_value`, `hex_value` | `ParseFloatValue` | `decRound` and `roundUnits` on the scanners' outputs are the references of `decValue L · 10 ^ (e - nf)` and `hexValue L · 2 ^ (e - 4 nf)` for the significand's digits `L`. |
| `parse64_spec`, `parse32_spec` | `ParseFloatTheorem` | `parse64 general (words s) = res64 (decode general s)` and the binary32 counterpart, for `s.length < 2 ^ 32`. |
| `parse64_accept`, `parse64_reject`, `parse32_accept`, `parse32_reject` | `ParseFloatTheorem` | The statements of the specification above. |
| `parse64_bytes_accuracy`, `parse32_bytes_accuracy` | `ParseFloatBytes` | The compiled entries 35 and 36 return the words of the parsers' results, or trap when memory runs out, and keep the caller's heap. |
| `parse_file`, `parse_file_decode` | `ParseFloatFile` | `build/verified/parsefloat.wasm` holds the encoding of the module and decodes to it. |

`ofScientific_spec` concerns Lean's own `Float.ofScientific` at `v4.34.0-rc2` [8], which both compilers use for the decimal literals of a program, so every decimal literal of type `Float` or `Float32` in a verified program means the correctly rounded value.

## Proof

[The grid module](StrconvGrid.lean) proves the rounding of a real number in units once for a format given by its precision and the exponent field of its infinities, from the ideas of `FmaGrid` and `FmaNearestEven`: `mag_succ`, `mag_dvd`, and `mag_below` describe the magnitudes of encodings, `nearest_even_pack` shows that a significand rounded in its binade gives the nearest-even encoding, and `nearest_even_unique` shows that two nearest encodings differ by at most one.  [The word module](StrconvWords.lean) connects the grid to ProofKit's binary64 reference and to the binary32 reference, and [the rational module](StrconvRational.lean) proves Talos's rational and dyadic roundings equal to them through `roundsTo_quotient`.  The two `ofScientific` modules follow Lean's definition: the fast path through `F64Bits` and `F32Bits` and the table of powers of ten checked entry by entry, and the model's path through ProofKit's `F64DivCore.pack_div_finite` and `F64RoundDyadic.pack_round_above_dyadic` and their binary32 counterparts.  [The truncation module](StrconvTruncate.lean) proves that two reals in an open interval free of half-grid points have the same reference (`refPos_transfer`) and bounds the significant digits of those points.  The journal sections of track `strconv` record the failed runs and their causes.

The parsers' proof has five parts.  `ParseFloatRound.roundUnits_spec` proves the rounding step: for `φ` in `[0, 1)` that is positive exactly when the flag is set, `roundUnits` gives `refPos f ((u + φ) · 2 ^ (T - 2 ^ 62))`.  `ParseFloatDec.decRound_spec` proves the exact decimal path with `Uscale.scaledQuot_spec`: `decRound` gives `refPos f (D' · 10 ^ q · 2 ^ ν)`, where `D'` is `D`, or `D + 1/2` when a dropped digit is nonzero, and it covers both saturations.  The scanner modules prove that `decParse` and `hexParse` compute the decoder's branches: `ParseFloatScan` reads spans, the special words, and exponents, `ParseFloatDigits` reads leading zeros, the sticky flag, and the values of the kept digits, and `ParseFloatDecParse.decParse_spec` and `ParseFloatHexParse.hexParse_spec` give the flag, the kept digits, their count, the biased exponent of the last kept digit, and the sticky flag in terms of the significand's digits `i ++ f`.  `ParseFloatFast` proves the fast path: `tenWord t`, the word that ProofKit's `F64GridExact.signed_grid_packing_exact` gives for `5 ^ t` on the grid of `2 ^ (1074 + t)`, is the reference word of `10 ^ t`, so each multiplication by `10.0` in `pow10Float` is exact up to `10 ^ 22`, and Talos's `mul` and `div` of two exact words are the reference words of the product and the quotient.  `ParseFloatValue` splits the significand's digits into the kept digits and the dropped digits: with no nonzero dropped digit the scanner's value is exact, and otherwise the truncation theorem applies, while an exponent beyond `10 ^ 11` in magnitude puts both the value and the scanner's value beyond the overflow threshold or below half the least subnormal.  `ParseFloatTheorem` writes `decode` as one chain of conditions (`decode_eq`), shows that the scanner computes each condition, and sets the sign by OR, which is Talos's `negate` on a nonnegative word.

[The byte module](ParseFloatBytes.lean) carries the theorems to the compiled module in the form of `ExpTheorem.exp_bytes_accuracy`.  The entries `parse64` (function 35) and `parse32` (function 36) take the flag of the general grammar as the word 1 or 0 and the string as a borrowed array of one-byte words.  `parse64_bytes_accuracy` states that the module's bytes decode to the module, that the store in which it starts is ready, and that a call from a ready store with a string `s` of fewer than `2 ^ 32` bytes either traps at `unreachable`, which happens only when an allocation finds no memory, or returns the word `w` and the flag `b` with `b = 1` and `w = round64 n` when `s` derives `n` and `b = 0` and `w = 0` when it derives no number.  The call leaves a ready store in which the string is still borrowed and every region of the heap before the call keeps its bytes, so the theorem covers every sequence of calls.  `parse32_bytes_accuracy` states the same with `(round32 n).toUInt64`.  [The file module](ParseFloatFile.lean) proves that `build/verified/parsefloat.wasm`, written by `tools/Emit.lean`, holds the encoding of the module and decodes to it (`strconv-pfile-3.log`).

## Tests

[`ParseFloatAccuracy.lean`](ParseFloatAccuracy.lean) runs the compiled native code of `parse64` and `parse32` on the 1,030 lines of [`data/strconv/parse-cases.txt`](../../data/strconv/parse-cases.txt) and requires each result to equal two references.  The first is the pair of words in the file, which [`tools/strconv/parse_cases.py`](../../tools/strconv/parse_cases.py) computes with Python's exact rationals, independent of the Lean code.  The second is computed in Lean: `StrconvDecode.decode` gives the number, and Talos's `roundRationalMagnitude`, which `StrconvRational.rational64` and `rational32` prove equal to the references, rounds it.  The lines are 330 lines of Nigel Tao's parse-number-fxx-test-data at `55d79b18` covering each of its 14 files [11], whose f32 and f64 fields the generator checks against its own words, the decimal inputs of Paxson's tables of hard cases [12] as Go's `testfp.txt` reproduces them, 300 strings next to the midpoints between neighboring values with up to 1,100 digits, and 182 grammar cases in both modes.  All 1,030 cases agree, in 12 seconds (`build/transcendentals/strconv-paccuracy-1.log`), and again after the exponent bound was raised to `10 ^ 11` (`strconv-paccuracy-2.log`).  [`data/strconv/NOTICE`](../../data/strconv/NOTICE) and the license file beside it carry the Apache-2.0 notice of Tao's lines and describe the changes.

[The test driver](../../tests/verified/run.sh) emits `parsefloat.wasm`, validates it with `wasm-tools`, builds `ParseFloatBytes`, checks `ParseFloatFile` against the emitted file, and runs `ParseFloatAccuracy.lean`.  The [integration record](../../devnotes.md#2026-10-16-integrating-the-two-compilers) records the accepted run with all parser cases and both file theorems.

## Limits

The theorems trust Talos's semantics of WebAssembly and its decoder, as every theorem of the verified compiler does, and the file theorem trusts `binary_file%` to read the bytes that `tools/Emit.lean` writes.  The grammar has no white space, no NaN payloads, no digit separators, and no longest-prefix rule, so a caller must trim the input; a rejected string gives `(false, 0)`, which no accepted string gives.  Every NaN result is the canonical NaN of its format, since the grammar carries no payload.  The binary32 parser returns the pattern in the low 32 bits of a word, since the verified dialect has no `Float32` type.

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
11. N. Tao, [parse-number-fxx-test-data](https://github.com/nigeltao/parse-number-fxx-test-data/tree/55d79b184b7d8fac2e143e89dc19b766ec4e54b8) at `55d79b18`, Apache-2.0.
12. V. Paxson, "A Program for Testing IEEE Decimal–Binary Conversion", CS 279 class project (Prof. W. Kahan), 22 May 1991, [testbase-report.pdf](https://www.icir.org/vern/papers/testbase-report.pdf); the tables as reproduced in Go's `src/internal/strconv/testdata/testfp.txt` at `2c3c1caa`, BSD-3-Clause.
