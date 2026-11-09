# Decimal text of `Int64`: `printInt64` and `readInt64`

## Request, specification, review, and program

[The request](request.txt) asks for a printer from `Int64` to its canonical decimal text and a reader that accepts exactly a documented grammar, rejects every other input, and inverts the printer.  A text is an array of words that hold one byte each, the representation that [the decimal parsers and printers](../ParseFloat/README.md) use.  [The specification](Spec.lean) states the printer as `expectedPrint x = words (ascii (toString x))`, the bytes of Lean's own `toString` [2], which writes `-` before the digits of a negative value, no leading zero, and `0` for zero.  It states the reader as `expectedRead`, which accepts the texts of the grammar

```
integer = "0" / [ "-" ] nonzero *digit
nonzero = "1" / "2" / "3" / "4" / "5" / "6" / "7" / "8" / "9"
digit   = "0" / nonzero
```

whose integer lies in [-2^63, 2^63 - 1], and returns `(true, x)` for the `Int64` of that integer and `(false, 0)` for every other array of words.  The grammar is RFC 8259's `[ minus ] int` without `-0` [1].  It rejects a leading `+`, a leading zero other than the text `0`, and `-0`, so that each value has one text, the printer's.  RFC 8259 admits `-0` and the library's binary64 parser reads it as negative zero, a value that `Int64` lacks.  The reader takes the whole array, as the library's parsers do, so white space, a stray byte, and a word above 255 make it reject.  The pair of a `Bool` and an `Int64` reports rejection, since the dialect has no `Option`, and its `(false, 0)` follows the library's parsers.  [The review](review.md) records three independent reviews of the specification and the case inputs, the corrections that they led to, and the classes of input that the cases leave out.

[The program](Program.lean) prints the magnitude `m`, the word `0 - x.toUInt64` for a negative `x`, which holds `2^63` for `minValue`.  `digitCount` counts the `L` digits by at most 19 divisions by 10, and `LeanExe.build` writes `-` and then the digits from the most significant, digit `j` as `digitByte m (L - 1 - j)`, where `digitByte m k` divides by 10 `k` times.  The reader takes an optional `-`, rejects an empty magnitude or one of more than 19 bytes, scans the digits with `scanDigits`, which accumulates their value in a word, and compares the value with `2^63 - 1`, or with `2^63` after `-`.  A numeral of at most 19 digits is below `10^19 < 2^64`, so the accumulation needs no test of overflow.  A magnitude of more than 19 bytes is outside the grammar or, without a leading zero, at least `10^19`, outside the range, so the reader rejects it without reading it.  The reader reads at most 20 words and allocates nothing, and the printer allocates one block of at most 20 words.

## The module reads and prints `Int64` as the specification states

`verified_compile compiled := [digitCount, digitByte, printInt64, isDigitW, scanDigits, readInt64]` in [the verified compilation](Compiled.lean) compiles the program into a module of 2,658 bytes whose exports `printInt64` and `readInt64` are functions 4 and 7.  Every iteration of the program is a `LeanExe.loop`, which compiles to a WebAssembly loop, so no theorem of the module has a call-depth premise.

| Theorem | File | Statement |
|---|---|---|
| `print_toList` | `Inverse.lean` | The text of `x` is `-` when `x.toInt < 0`, then the words of `Nat.toDigits 10` of the magnitude. |
| `expectedRead_print`, `expectedPrint_of_read`, `expectedRead_eq_true_iff`, `expectedRead_reject` | `Inverse.lean` | The specification's reader returns `(true, x)` on the text of `x`, accepts only the printer's texts, each with the value printed, and returns `(false, 0)` on every other array. |
| `digitWords_getElem?`, `digitCount_toNat`, `digitByte_eq` | `Proof.lean` | Digit `j` of `m` from the most significant is `m / 10 ^ (L - 1 - j) % 10`, `digitCount m` is the number `L` of digits, and `digitByte m k` is the byte of `m / 10 ^ k % 10`. |
| `printInt64_eq` | `Proof.lean` | `printInt64 x = expectedPrint x` for every `x`. |
| `scanDigits_spec`, `magnitude_cons` | `Proof.lean` | The scan of at most 19 words tests them for digits and, when they are, gives `digitsValue` of them, and `magnitude` accepts digits whose first is not 0. |
| `readInt64_eq` | `Proof.lean` | `readInt64 s = expectedRead s` for every array of fewer than `2^64` words, which every array in memory is. |
| `readInt64_printInt64`, `printInt64_of_read`, `readInt64_reject` | `Proof.lean` | The program's reader returns `(true, x)` on `printInt64 x`, every array on which it returns `(true, x)` is `printInt64 x`, and it returns `(false, 0)` on every other array. |
| `printInt64_export`, `readInt64_export` | `Compiled.lean` | Exports `printInt64` and `readInt64` of `compiled.module` are functions 4 and 7. |
| `printInt64_bound`, `printInt64_bound_le`, `readInt64_bound` | `Compiled.lean` | The generated bound of `printInt64` is one block of the text's words, at most 216 bytes, and that of `readInt64` is 0. |
| `printInt64_callSpec` | `Compiled.lean` | From a ready store with room for `compiled.printInt64.bound x` bytes, function 4, called with the word of `x`, returns without a trap an owned array that holds `expectedPrint x` and leaves a ready store, as `Verified.CallSpec` states. |
| `readInt64_callSpec` | `Compiled.lean` | From a ready store, function 7, called with a borrowed array `s`, returns without a trap the flag and the word of `expectedRead s` and leaves a ready store. |
| `int64Text_file`, `int64Text_file_decode` | `File.lean` | `build/verified/int64Text.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |
| `printInt64_runs` | `tests/TestSupport/A64/Int64Text.lean` | The AArch64 program that calls function 4 on the word of `x` writes the encoding of `printInt64 x` to the UART and returns 0, for every room and cap. |
| `int64min_image`, `int64min_image_spec` | `tests/TestSupport/A64/ImageFilesInt64Text.lean` | The arm64 Image `int64min.img` runs from boot to PSCI's `SYSTEM_OFF` after writing the encoding of `expectedPrint Int64.minValue`, the words of `-9223372036854775808`, and the status 0. |

`print_toList` reads `toString` through Lean's `Int.repr_eq_ite` and `Nat.toList_repr`, and the proofs split off the last digit with `Nat.toDigits_append_toDigits` and count the digits with `Nat.length_toDigits_le_iff`.  `expectedPrint_of_read` shows that a text of `nonzero *digit` is `Nat.toDigits 10` of its value, by induction from the right.  `readInt64_eq` follows the program's tests: the text after the sign is the list that `scanDigits` reads, and the test that the first digit is not 0 together with the scan's test for digits is `magnitude`'s test.  The axiom reports of the theorems in the table name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Decimal.Int64Text.Compiled
tests/verified/run.sh --cases int64Text
tests/native/verified.sh --module int64Text
tests/baremetal/a64-images.sh
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `printInputs` and `readInputs` in [the case inputs](../../../../tests/TestSupport/Modules/Int64Text.lean), and [the verified library cases](../../../../tests/TestSupport/LibraryCases.lean) print each with `expectedPrint` or `expectedRead`.  The 253 printed values include 0, ±1, the largest and smallest values and their neighbors, each power of ten up to `10^18` with its neighbor toward zero and both negated, and each power of two up to `2^62` with its negation.  The 370 read inputs include the empty array, `0`, `-0`, a lone sign, signs out of place, leading zeros, white space and other bytes before, inside, and after the digits, the values next to both ends of the range, 20-digit values whose accumulation in 64 bits wraps into the range, bytes from 128 to 255 whose low 7 bits are a digit or `-`, words above 255, and the text of every printed value.  [The verified driver](../../../../tests/verified/run.sh) runs the 623 cases in Wasmtime, checks that a call leaves one block, the host's array or the printed text, and, without `--cases`, checks the file theorems, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.  [The AArch64 driver](../../../../tests/baremetal/a64-images.sh) writes `int64min.img`, checks its theorems in the kernel, and runs it under QEMU, where the UART shows the 168 bytes of the text's encoding and the status 0.

## Related examples

[`ParseFloat`](../ParseFloat/README.md) and [`PrintFloat`](../PrintFloat/README.md) read and print binary64 and binary32 values in the same representation of text.  [`Floor`](../../../../Examples/Floor/README.md) proves `Int64` programs against `Int.fdiv` and the floor of the mean, and [the running sum](../../../../Demos/RunningSum/README.md) reads and prints integers of any length on arrays of digits.

## References

1. T. Bray (Ed.), *The JavaScript Object Notation (JSON) Data Interchange Format*, RFC 8259, December 2017, [doi:10.17487/RFC8259](https://doi.org/10.17487/RFC8259), section 6.
2. Lean FRO, Lean 4 at tag `v4.34.0-rc2`, `src/Init/Data/Int/Repr.lean` (`Int.repr`), `src/Init/Data/Repr.lean` (`Nat.toDigits`), and `src/Init/Data/Nat/ToString.lean`.
