# Test inputs

## Hash vectors

| Corpus | Source and interpretation | Consumer |
|---|---|---|
| [SHA-2](hashing/sha2/NOTICE) | NIST byte-oriented short-message, long-message, and Monte Carlo vectors.  The [original explanation](hashing/sha2/Readme.txt) describes the response files.  The notice identifies the downloaded archive and its digest. | [SHA-2 vector test](../tests/TestSupport/Hashing/Sha2Vectors.lean) |
| [SHA-3 and SHAKE](hashing/sha3/NOTICE) | NIST byte-oriented vectors and short bit-oriented messages.  The bit length and the FIPS 202 byte convention determine the message, including its final partial byte. | [SHA-3 vector test](../tests/TestSupport/Hashing/Sha3Vectors.lean) |
| [CRC](hashing/crc/NOTICE) | Published check values and generated messages compared with Python's CRC-32 and the Linux crypto API's CRC-32C. | [CRC vector test](../tests/TestSupport/Hashing/CrcVectors.lean) |
| [SipHash](hashing/siphash/NOTICE) | Reference SipHash-2-4 vectors and generated SipHash-2-4 and SipHash-1-3 results from OpenSSL.  The notice fixes key, message, and result byte order. | [SipHash vector test](../tests/TestSupport/Hashing/SipHashVectors.lean) |
| [XXH64](hashing/xxhash64/NOTICE) | Reference lengths, seeds, and digests.  The notice specifies the generator that reconstructs each message. | [XXH64 vector test](../tests/TestSupport/Hashing/XxHash64Vectors.lean) |

The notices record the sources, file transformations, and licenses.  Downloaded NIST files
retain their original CRLF line endings.

## Decimal conversion

[Parser cases](strconv/parse-cases.txt) include imported hard cases, numbers near rounding
midpoints, and accepted and rejected strings for RFC 8259's `number` grammar and
[the parser's general grammar](../Library/Numerics/Decimal/ParseFloat/README.md#grammar),
which accepts decimal, hexadecimal, infinity, and NaN forms.
[The parser generator](../tools/strconv/parse_cases.py) computes expected binary32 and binary64
words with exact rational arithmetic.  [Printer cases](strconv/print-cases.txt) specify strings
for fixed floating-point words.  [The printer generator](../tools/strconv/print_cases.py)
searches rounding intervals for a shortest decimal, chooses the candidate nearest to the word's
value, and prefers an even last digit at a tie.

The [parser guide](../Library/Numerics/Decimal/ParseFloat/README.md#tests) and
[printer guide](../Library/Numerics/Decimal/PrintFloat/README.md#tests) explain the comparisons.
The [provenance notice](strconv/NOTICE) and [license](strconv/LICENSE-parse-number-fxx-test-data)
cover imported parser material.
