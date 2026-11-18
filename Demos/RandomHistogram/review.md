# Reviews of the specification and of the executable's theorems

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

## Review of the executable's theorems

A fresh agent reviewed `histogram_elf_counts`, `linux_exec_counts`, the budget of `main`, and the
footprints against the request, by the method of the knowledge base's entry on independent review.
It received the request and the paths of the theorems, the specifications, the shim's model, and
the guide, wrote a model in Python of the specification, the shim's images, `Full`, `Counts`,
`Meets`, and the driver's checks, and ran no Lean code.  Its model agreed with `Counts` on 89
argument lists within the premises, and it replayed in the model runs for N of 1, 513, and 1,000
under replies that meet `Full`, so the premises and `Full` can hold together.  It recomputed
`budget`, 268,427,864 bytes, the slack of 3,496 bytes below 4,096 pages, and `drawLimit`, and it
checked the kernel's bound on the arguments in v4.13 and v6.12.

| Finding | Response |
|---|---|
| `Counts` stated no shape of the layer events, so extra calls, one call for all words, or `GRND_NONBLOCK` met it | Adopted: `Counts` states calls of `getrandom`, each of at most 4,096 bytes with flags 0 (`Drawing`), followed by one `write` of descriptor 1 |
| Comments called `Counts` what the request asks of a run, called `drawLimit` the largest N for the model's charge, and wrote "no call" for a refusal | Adopted: `Counts` states the run whose calls succeed, `drawLimit` is the largest N for `budget`, and a refusal has no layer event before `exit_group` |
| `Full` requires full `getrandom` counts, where the shim completes a short count | Kept: the request states the condition, and Linux 6.12 returns every byte of a read of at most a page unless the copy faults.  A statement for short counts remains open |
| A short write ends with status 0 and part of the output, which `Meets` admits | Recorded in the guide.  Whether to write with a loop, as readAll does, or to give a short write a nonzero status is the user's decision |
| The guide claimed constant memory without a theorem or a run | Adopted: the guide states that no theorem or run shows it.  A run with N of 50,000,000 is declined, since the runs keep N at most 1,000,000 |
| The guide's conditions for `Full` omitted full disks, `RLIMIT_FSIZE`, and signals, and its reason for short `getrandom` reads did not hold for Linux 6.12 | Adopted, with the kernel's code and the manual pages cited |
| The theorems read `histogram.elf` while the driver runs `command.elf` | Adopted in the comments and the guide, which state that both scripts write the file from the same module with the same commands |
| Rows of the guide's table omitted premises, and comments cited `loop_kept`, `random_full`, `linux_strings_any`, and the kernel's bound loosely | Adopted |
| No Lean theorem shows that the premises and `Full` hold together | Open: a witness needs a run of `main` under the shim's host with explicit replies |
| The driver did not check stderr, leading zeros, a plus sign, extra arguments, or the calls of a refused run | Adopted: the driver requires empty stderr, runs `007`, `+5`, and `5 extra`, and traces a refused run |

Classes that no check or theorem excludes: a program that leaks each pass's buffer, which fails
only above the runs' N; a guest trap above `drawLimit`, which `histogram_elf` admits with X0 at 2;
and a short write that ends with status 0.  `Meets`, through `histogram_elf` and `exec_main`,
excludes a program that ignores an errno, writes to stderr, or reads standard input, and the
corollary excludes wrong residues, wrong word orders, and wrong parsing of an N within `drawLimit`.
