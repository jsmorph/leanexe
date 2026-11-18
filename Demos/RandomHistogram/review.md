# Reviews of the specification, of the executable's theorems, and of the write loop

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
| A short write ends with status 0 and part of the output, which `Meets` admits | Adopted after the user's decision: `main` writes with `writeAll`, which follows a short write with a write of the rest, and `Written` states that status 0 holds exactly when the writes took the whole output |
| The guide claimed constant memory without a theorem or a run | Adopted: the guide states that no theorem or run shows it.  A run with N of 50,000,000 is declined, since the runs keep N at most 1,000,000 |
| The guide's conditions for `Full` omitted full disks, `RLIMIT_FSIZE`, and signals, and its reason for short `getrandom` reads did not hold for Linux 6.12 | Adopted, with the kernel's code and the manual pages cited |
| The theorems read `histogram.elf` while the driver runs `command.elf` | Adopted in the comments and the guide, which state that both scripts write the file from the same module with the same commands |
| Rows of the guide's table omitted premises, and comments cited `loop_kept`, `random_full`, `linux_strings_any`, and the kernel's bound loosely | Adopted |
| No Lean theorem shows that the premises and `Full` hold together | Adopted: `histogram_elf_witness` |
| The driver did not check stderr, leading zeros, a plus sign, extra arguments, or the calls of a refused run | Adopted: the driver requires empty stderr, runs `007`, `+5`, and `5 extra`, and traces a refused run |

Classes that no check or theorem excludes: a program that leaks each pass's buffer, which fails
only above the runs' N, and a guest trap above `drawLimit`, which `histogram_elf` admits with X0
at 2.  `Meets`, through `histogram_elf` and `exec_main`,
excludes a program that ignores an errno, writes to stderr, or reads standard input, and the
corollary excludes wrong residues, wrong word orders, and wrong parsing of an N within `drawLimit`.

## Review of the write loop and the witness

A fresh agent reviewed the theorems of the write loop, `Written`, `Meets`, the budget, `Full`,
`Counts`, and `histogram_elf_witness` against the request and the user's decisions on writes, by
the method of the knowledge base's entry on independent review, and ran no Lean code.  Its model
in Python ran `writeAll` and 20 wrong write loops under every host of at most five writes for
outputs of 1 to 4 bytes and under random hosts on 200 rendered outputs, ported the shim's
`writeReply`, `writeData`, `Full`, and `Counts`, checked the bytes of `witnessStack` against
`InitialStack` and `witnessMem` against `ElfLoaded`, and recomputed `writeCharge`, `budget`, and
`drawLimit`.  It confirmed that status 0 holds exactly when the writes took the whole output in
order, that 77 is no errno, the witness, and the budget's numbers.

| Finding | Response |
|---|---|
| `Written` admitted status 77 after fewer writes than passes, no write among them | Adopted: `Written` states `B + 1` writes for 77, which `WriteAllRun.taken` gives for a run that returns fewer bytes than the output holds |
| `Counts` admitted 77 after a failed write and writes after a failed write | Adopted: `Counts` states `Written`'s cases over the layer events, every `write` but a failing last one returning at most its count (`Took`) |
| Neither statement fixed the bytes that a write offers, so writes of one byte or of aligned chunks met both | Adopted: `Offered` and `OfferedLayer` state that each write offers the bytes that the writes before it did not take |
| No theorem stated that a short return took every pass | Adopted: `WriteAllRun.taken` states it |
| Docstrings called 77 the status of passes used up, which the statements did not state | Adopted with the statements above |
| `write_tail`'s docstring claimed statuses that its statement did not give, and `main_runs`'s claimed that `main` exits from `writeAll` | Adopted: the statement gives 0 or 77 and an exit status other than 0, and the docstring drops the claim |
| `Written` did not bound a failing write's errno | Adopted: it states at most 76 |
| The driver's strace run accepted any number of writes | Adopted: it requires one write of the output's size that takes all of it |
| No theorem shows that the premises of `total_meets` hold together | Recorded in the guide |
| The guide's sentence on a failed second write held only while the disk stays full or the limit holds, and `suffix`'s docstring omitted its precondition | Adopted |

The same agent then ran its model on the revised statements: the right program met `Written` and
`Counts` on 566 runs under every host for outputs of 1 to 4 bytes, on 132 runs under the shim that
meet `Full`, and on 5,000 random runs for N of 1,000, and in each run that ended with 77 some write
took no byte.  The revised statements exclude all 20 wrong write loops, among them a single write
with 77 when short, no write with 77, writes of one byte, of 16-byte windows, and of aligned
chunks, retries after a failed write, and 77 after a failed write.  No run on Linux detects three
of them, status 0 when the passes run out, 77 after two passes, and 77 at the first write of no
byte, since Linux gives no reply that tells them apart from the right program, and the statements
exclude all three.  Its three wording findings, on the docstrings of `write_image` and
`histogram_elf_counts` and on the description of the limited strace run, were adopted.

Classes that no check or theorem excludes remain those of the earlier review, a program that leaks
each pass's buffer and a guest trap above `drawLimit`, and one that the review named: status 2 is
also the WASI errno `acces`, which a write that fails with `EACCES` returns, so status 2 alone does
not tell a refused argument from that failure.  The events of `Meets` tell them apart.
