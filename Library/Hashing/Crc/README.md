# CRC-32 and CRC-32C

The module `crc` computes CRC-32, the 32-bit frame check sequence of ITU-T V.42 [1] that gzip [3] and PNG use and that zlib's `crc32` computes, and CRC-32C, the CRC of RFC 3720 [2] for iSCSI.  Each export takes a message of `n` bytes packed eight to a word as [the hashing guide](../README.md) describes and returns without a trap one word whose value is the CRC that [the transcription](Spec.lean) gives for the message's bytes.  The update exports also take the CRC of earlier bytes and return the CRC of those bytes followed by the message, as zlib's `crc32(crc, buf, len)` does.  The message stays borrowed, and every region of the caller's heap keeps its bytes.  The file theorems of [`File.lean`](File.lean) state that `build/verified/crc.wasm` holds the module.  The module `crcBitwise`, which [its section](#bitwise-crc-32) describes, computes CRC-32 one bit at a time, with no table, for programs of the Cortex-M7 back end that have no area.

## Specification

[`Spec.lean`](Spec.lean) transcribes V.42 §8.1.1.6.2 and §8.1.2 and RFC 3720 §2.3.3 and §12.1 with Mathlib's polynomials over `ZMod 2` and its remainder `%ₘ`.  A message is a string of bits, the least significant bit of each byte first, and the first bit is the highest coefficient.  `fcs` is V.42's sequence, the ones complement of the sum of the remainders of `x^k L` and `x^32 M` by the generator, where `L = x^31 + … + 1` and `k` counts the bits of `M`.  `crc32` uses V.42's generator, and `crc32c` uses `0x11edc6f41` of RFC 3720, read as the RFC reads `0x3b` in its example.  `rfcProcess` transcribes the process of RFC 3720 §12.1, which complements the first 32 bits of the message, and `rfcProcess_eq` proves that it gives V.42's sequence for every message of at least 32 bits.  The RFC's process has no meaning for shorter messages, and V.42's form gives 0 for the empty message, as zlib and the Linux kernel do.

Neither document defines an integer for the sequence.  `value` gives the integer that zlib and other CRC code report, whose bit `i` is the coefficient of `x^(31 - i)`, so that the four octets of the sequence, each read with its least significant bit as `2^0`, are the bytes of the integer from the least significant.  RFC 1952 §2.1 stores the CRC of gzip in this order, and RFC 3720 Appendix B.4 lists its examples in it.  An independent review compared the transcription with V.42 and RFC 3720 and found no discrepancy in its definitions.

[`Division.lean`](Division.lean) gives a computable form of the transcription.  `lfsr` divides by a generator one bit at a time on strings of 32 bits, and `lfsr_spec` proves that from the remainder `S` and the bits `M` it gives the remainder of `x^k S + x^32 M`.  From 32 ones it gives the sum of V.42's two remainders, so `crc32Eval` and `crc32cEval` compute `crc32` and `crc32c`, as `crc32_eq` and `crc32c_eq` state.  `g32c_explicit` writes out the exponents of CRC-32C's generator.  A count beyond an array's bytes is accepted, and the missing bytes read as zero in both the program and the theorems.  An update reads only the low 32 bits of its CRC argument.

| Export | Function | Arguments | Result | Call theorem |
|---|---|---|---|---|
| `crc32` | 4 | Message array and `n`. | CRC-32 of the `n` bytes. | `crc32_call` |
| `crc32c` | 5 | Message array and `n`. | CRC-32C of the `n` bytes. | `crc32c_call` |
| `crc32Update` | 6 | CRC-32 of bytes `A`, the message array, and `n`. | CRC-32 of `A` and the `n` bytes. | `crc32Update_call` |
| `crc32cUpdate` | 7 | CRC-32C of bytes `A`, the message array, and `n`. | CRC-32C of `A` and the `n` bytes. | `crc32cUpdate_call` |

## Implementation

[The program](Program.lean) holds the remainder in the low 32 bits of a word, the coefficient of `x^31` in the least significant bit, which makes a step of the division a shift to the right by one and an XOR with the generator's low coefficients in the same order, `0xEDB88320` for CRC-32 and `0x82F63B78` for CRC-32C.  Entry `k` of a table of 256 words is the remainder after eight steps from the register `k`, so that `byteStep` performs the eight steps of a byte with one shift, one XOR, and one table read.  `updateWith` starts from the complement of the low 32 bits of the CRC argument, which is 32 ones for the CRC of no bytes, runs `byteStep` over the message's bytes, and complements the result.  The module writes the two tables in a data segment, at addresses 4096 and 6152, and each export passes its table to `updateWith` or `crcWith`.  No function allocates, as `compiled.updateWith.bound_eq` and `compiled.crcWith.bound_eq` state.

## Bitwise CRC-32

The module `crcBitwise` computes CRC-32 with no table, linear memory, global, or floating point, so a program of the Cortex-M7 back end that calls its functions has no area.  [Its program](Bitwise/Program.lean) holds the remainder in a register as `byteStep` does.  `crc32Reg` XORs a byte into the register's low eight bits and takes eight steps of the division, each a shift to the right by one and an XOR with `0xEDB88320`, which the product of the bit shifted out and the generator selects without a branch.  `crc32Byte` and `crc32Word` take and return a CRC as zlib's `crc32` does, so the CRC argument can be 0, zlib's initial value, or any other value, such as a constant of a link.  `crc32Word` continues the CRC with the first `n` bytes of a word, at most eight, from the most significant, the order in which `LeanExe.Requests.decode` packs the bytes of a record into words, and it calls `crc32Reg` once for each of those bytes.

| Export | Function | Arguments | Result | Call theorem |
|---|---|---|---|---|
| `crc32Reg` | 2 | Register `r` and word `b`. | `byteStep crc32Table r b`, the register after the low byte of `b`. | `crc32Reg_call` |
| `crc32Byte` | 3 | CRC-32 `crc` and word `b`. | `crc32Update crc #[b] 1`, the CRC continued with the low byte of `b`. | `crc32Byte_call` |
| `crc32Word` | 4 | CRC-32 `crc`, word `w`, and count `n`. | `crc32Update crc #[bswap w] (min n 8)`, the CRC continued with the first `min n 8` bytes of `w` from the most significant. | `crc32Word_call` |

[The proof](Bitwise/Proof.lean) equates each function with the table program for every argument.  A step is linear over GF(2), `bitStep_xor`, so eight steps of a register are eight steps of its bits above the low byte XORed with eight steps of its low byte.  Eight steps shift a register whose low byte is zero right by eight bits, `iterate_high`, and the kernel checks in `iterate_table` that eight steps from each of the 256 bytes give the byte's entry of `crc32Table`.  `crc32Reg_eq` follows, and from it `crc32Byte_eq` and `crc32Word_eq`, the equalities of the table's Result column.  For a CRC argument that is the CRC of some bytes `A`, `crc32Byte_spec` and `crc32Word_spec` give through `crc32Update_spec` the CRC of the transcription: of `A` followed by the low byte of `b`, and of `A` followed by the bytes of `w` that `LeanExe.Requests.wordBytes w (min n 8)` lists.  The verified compiler generates `compiled.f.pure` for each function, which states that the call returns the function's value from every store without a trap and keeps the store, so no call allocates.  The call theorems of [the compilation](Bitwise/Compiled.lean) compose it with the equalities.

[The Cortex-M7 check](../../../tests/TestSupport/M7/CrcBitwise.lean) states by the kernel's evaluation that no function that calls reach from an export loads, stores, or accesses a global, that the simulation covers their forms, and that the generator emits their code, which `functionsOf` lays out as `genProgram` lays out the functions of a step after `main`.  It gives the bounds of `staticCost` and `stackBound`, and `crcBitwise_cost` turns the first into bounds on the model's steps in every run of a call of `crc32Byte` or `crc32Word`, through `costRun_le_staticCost`.  The module has no image of its own, since the theorems of an image describe a program with requests, which the program that calls these functions supplies.

| Export | Code of the functions that calls reach, in bytes | `staticCost`, in steps of the model | Stack, in bytes |
|---|---|---|---|
| `crc32Reg` | 2,316 | 579 | 96 |
| `crc32Byte` | 2,612 | 653 | 136 |
| `crc32Word` | 5,528 | 5,363 | 224 |

## Proof

| Module | Content |
|---|---|
| [`Division.lean`](Division.lean) | `lfsr_spec`, `crc32_eq`, and `crc32c_eq` for the computable division; `rfcProcess_eq`; `g32_eq`, `g32c_eq`, and `g32c_explicit` for the generators. |
| [`Proof.lean`](Proof.lean) | `Holds`, which reads a register as 32 bits; `TableOf`, which `decide` checks for both tables against the division; `byteStep_holds`, the eight steps of a byte; `loop_holds`; and `crc32_spec`, `crc32c_spec`, `crc32Update_spec`, and `crc32cUpdate_spec`. |
| [`Compiled.lean`](Compiled.lean) | Verified compilation of `updateWith`, `crcWith`, and the export wrappers. |
| [`Bytes.lean`](Bytes.lean) | `crc32c_table`, the export facts, and the call theorems, from the generated `implements` theorems through `Verified.ImplementsTables.call` and the theorems above. |
| [`File.lean`](File.lean) | File theorems: the emitted file holds the module's encoding and decodes to the module. |
| [`Bitwise/Proof.lean`](Bitwise/Proof.lean) | `bitStep_xor`, `iterate_high`, `iterate_table`, `crc32Reg_eq`, `crc32Byte_eq`, `crc32Word_eq`, `crc32Byte_spec`, and `crc32Word_spec` for the module `crcBitwise`. |
| [`Bitwise/Compiled.lean`](Bitwise/Compiled.lean) | Verified compilation of `crc32Reg`, `crc32Byte`, and `crc32Word`, the export facts, and the call theorems. |
| [`Bitwise/File.lean`](Bitwise/File.lean) | File theorems of `build/verified/crcBitwise.wasm`. |

`byteStep_holds` compares polynomials: the register shifted by eight bits has degree below 32 and is its own remainder, and the table entry of the low byte XORed with the message byte is the remainder of that byte times `x^32`.  `poly_inj`, which states that strings of one length with one polynomial are equal, converts that equality of polynomials into the equality of bit strings that the loop's invariant uses.  The update theorems assume that the argument's value is the CRC of some bytes `A`, and `lfsr_append` gives the CRC of `A` followed by the message.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

The executable `crc-vectors`, built from [the vector check](../../../tests/TestSupport/Hashing/CrcVectors.lean), checks the computable transcription and the programs on [the vectors](../../../data/hashing/crc/NOTICE) of `data/hashing/crc`, which `generate.py` writes from zlib's CRC-32 and the Linux kernel's CRC-32C.  The vectors are the check string `123456789` of the CRC catalogue [4], the five examples of RFC 3720 Appendix B.4, and pseudorandom messages of every length to 256 bytes and of ten lengths to 4,097 bytes, and the script stops if zlib or the kernel disagrees with the published values.  The transcription and the programs agree on all 273 messages, and the update functions agree from six splits of each message, with and without nonzero high bits in the CRC argument.

[The module cases](../../../tests/TestSupport/Hashing/CrcCases.lean) compare 270 calls in Wasmtime with native Lean: messages of 0 to 17 bytes and of lengths around multiples of eight and of 4,096, the check string, counts beyond the array, and updates from several CRC arguments.  Each case requires that the call keep the host's message and allocate nothing of its own.

The vector check also runs the bitwise functions on every message from the CRC of no bytes: `crc32Byte` over the message's bytes, and `crc32Word` over its words of eight bytes from the most significant, the last word filled with bytes after the message and passed with the count of the message's bytes in it.  A second run passes nonzero high bits in each CRC and byte argument and the count 2^64 - 1 for each full word.  Both runs agree with zlib on all 273 messages.  [The cases of `crcBitwise`](../../../tests/TestSupport/Hashing/CrcBitwiseCases.lean) compare 417 calls in Wasmtime and in the module's translation to C with the CRC-32 that `zlib.crc32` gives, which [the generator](../../../data/hashing/crc/bitwise.py) writes to `data/hashing/crc/bitwise.txt`, and 16 calls of `crc32Reg` from registers with high bits with the table program's step.  The calls include CRC arguments and bytes with high bits set, counts from 0 to beyond 8, and the two words of the check string, `0x3132333435363738` with the count 8 and `0x3900000000000000` with the count 1, whose result is `0xCBF43926`.  Each case requires that the call allocate nothing.

```sh
tools/leanrun --timeout 1h lake build Library.Hashing.Crc.Bytes Library.Hashing.Crc.Bitwise.Compiled \
  TestSupport.M7.CrcBitwise crc-vectors
tools/leanrun --timeout 10m .lake/build/bin/crc-vectors
tests/verified/run.sh --cases crc
tests/verified/run.sh --cases crcBitwise
tests/native/verified.sh --module crcBitwise
tools/leanrun --timeout 10m lake env lean Library/Hashing/Crc/File.lean
tools/leanrun --timeout 10m lake env lean Library/Hashing/Crc/Bitwise/File.lean
```

## References

1. International Telecommunication Union, [*Error-correcting procedures for DCEs using asynchronous-to-synchronous conversion*](https://www.itu.int/rec/T-REC-V.42-200203-I/en), ITU-T Recommendation V.42 (03/2002).
2. J. Satran et al., [*Internet Small Computer Systems Interface (iSCSI)*](https://www.rfc-editor.org/rfc/rfc3720), RFC 3720, 2004.
3. P. Deutsch, [*GZIP file format specification version 4.3*](https://www.rfc-editor.org/rfc/rfc1952), RFC 1952, 1996.
4. G. Cook, [*Catalogue of parametrised CRC algorithms*](https://reveng.sourceforge.io/crc-catalogue/17plus.htm), CRC-32/ISO-HDLC and CRC-32/ISCSI.
