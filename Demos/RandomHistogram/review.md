# Review of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the samples](Samples.lean) against
[the request](request.txt), as step 5 of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md) describes.  Each received only the paths of
the request, the specification, the samples, and the samples' outputs, wrote its own model of the
request in Python, compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no disagreement.  Its model agreed with the 64 outputs of the first sample
set, and with a transcription of the specification on 200,000 argument buffers, 200,000 count
arrays, and 10,000 word arrays.  It found three comments to correct.  The comment on the width of a
count gave memory as the reason that counts never wrap, where the reason for a run of the command
is that N is below `2^64`.  The comments recorded two choices only by implication: that the range
test applies to the numeral's value, whatever its number of digits, and that the program name's
bytes are ignored.  The specification's comment now states all three.

The review named input classes that no sample covered, and the samples now cover each: an argument
with a trailing newline or a tab, the bytes 127 and 255, the digit five in fullwidth form and in
Arabic-Indic form, `2^64` after a leading zero, a 20-digit value below `2^64`, a terminated first
argument followed by a last argument without its zero byte, and counts of 7, 8, and 11 to 18
digits.

## Second review

The second review, of the revised specification and its 74 samples, found no disagreement and found
every open case recorded.  Its model agreed with all 74 outputs and with a transcription of the
specification on 40,000 random inputs for each function.  It named these classes that no sample
covers, which step 7 of the skill records without new samples:

| Function | Class |
|---|---|
| `parseN` | Values between `10^6` and `10^19`, such as `2^32 - 1`, `2^32`, and `2^63` |
| `parseN` | 20-digit numerals at or above `2^64` whose value modulo `2^64` is not below their first 19 digits' value, such as `30000000000000000000`; a program that detects overflow by a decrease of the accumulated word passes every sample and accepts this class |
| `histogram` | Counts above `2^32` |
| `render` | The boundaries `10^k - 1` and `10^k` for `k` = 4, 6, 7, 8, and 10 to 17, and `10^18 - 1` |

The program tests each digit against the bound before it adds the digit, and `parseN_eq` proves the
program equal to the specification on every buffer, so an error of the program in the second class
would contradict that theorem.  The review noted that the request's choices outside the three functions, the reading of the bytes as
little-endian words, the loop of at most 512 words, the statuses, and the output's stream, belong to
the command's theorem, which [the command's specification](CommandSpec.lean) states.
