# Reviews of the specification, of the executable's theorems, of the write loop, of the premise on short reads, and of the writes of no byte

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

## Review of the premise on short reads

A fresh agent reviewed `InRange`, `Sized`, `RandomGroup`, `Counts`, the theorems that state them,
the random choice's `Mirrors` and `Choices`, the file theorems, and the witnesses against the
requests, the shim's `random_get` (`RandomCalls`, `randomLast`, `randomLoop`, and `randomStub`),
getrandom(2), write(2), and Linux v7.0's `drivers/char/random.c`, by the method of the knowledge
base's entry on independent review, and ran no Lean code.  Its model in Python ran the 32
instructions of `randomStub` against `randomInvoke` on 66,644 cases without a difference, compared
`RandomGroup` with the groups of `RandomCalls` on 12,489,044 sequences of events and errnos without
a difference, and ran both commands, 10 variants of the premise, and wrong programs and shims on
24,574 cases.  `InRange` admitted 6,174 runs of the histogram and 7,401 of the random choice, each
of which exits and meets its statement, and the other 5,002 and 5,997 runs trap.  The earlier
`Full` excluded 5,586 and 6,690 runs whose replies getrandom(2) allows.  A premise without
"positive for a positive length", or one that reads −4096 as an error number, admitted 1,582 and
1,887 runs that trap, and one that bounds a count by 4,096 bytes in place of the call's length
admitted 882 and 480.

| Finding | Response |
|---|---|
| `Counts` stated each draw as a group of 1 to 4,096 bytes, so programs that draw one word a call, two calls of 4 bytes a word, or the remainder's words first met it on all 4,786, 5,982, and 2,394 runs on which they differ from the right program, programs with an extra draw of 4 bytes or with draws of 4,096 bytes met it on 874 of 1,240 and 1,926 of 2,950, and a stub with an extra call of 1 byte after each draw on 857 of 1,432 | Adopted: `Counts` states groups that mirror, one for one, the calls of `Draws` (`RandomMirrors`), each for `8 · min r 512` bytes, and the model with those lengths rejected every differing run of every variant |
| The claim that `InRange` excludes exactly the results at which the shim traps had a theorem in one direction only | Adopted: `random_inRange` and `write_inRange` state that the image of a call that returned meets `InRange` |
| The write clause of that claim omitted "and no error number" | Adopted |
| `short_run` and `histogram_elf_witness` did not state the short read that their comments described, so full replies met them | Adopted: both conclude `ShortRead`, a `getrandom` that returned a count of at least 1 and below its length |
| `draws_groups`, `Mirrors`, `InRange`, and `randomData` had docstrings that stated more than the definitions, and `randomData` took the whole output of a call that returned an error number | Adopted: `draws_mirrors` replaces `draws_groups`, `Mirrors` describes the shim's events without a condition on the run, `InRange` names `getrandom` and `write`, and `randomData` takes the bytes of a `getrandom` only when its result is at most its length, as `LeanExe.Linux.Event.readBytes` does |
| `Sized` is needed: replies that move 2 bytes from the first output of a short read to the second leave the WASI reply unchanged and meet `InRange`, and the bytes of `randomData` then differ from the call's | Kept: `carried_sized` gives `Sized` for every run |
| No signal can shorten the commands' reads, of at most 4,096 bytes | Recorded: a raw `getrandom` with a signal sent in a loop on Linux 6.12 with pages of 4 KiB returned in full on 600,000 calls of 256, 4,095, and 4,096 bytes, and returned short on 199,293 of 200,000 calls of 4,097 bytes.  glibc 2.41's `getrandom()` uses the vDSO and was never short |

The review found that the random choice's `Choices` and `Mirrors` rejected every differing run of 10
wrong programs and 12 wrong shims, among them a short count taken as the whole buffer, a retry at
the buffer's start or for its whole length, an address advanced twice, flags 1, a failed draw's
bytes kept, an error taken as success, and a retry after `EINTR`.  Classes that no statement
excludes: wrong stubs of `random_get` that differ only at results outside `InRange`, which take a
count of 0 as the end, loop on 0, take a count above the length as the end, or read −4096 as an
error number, and which differed on none of the in-range cases, so that only
`Verified.ShimA64.randomStub_run` excludes them; an errno table that the shim and the statements
share; and the addresses and the `inputs` and `prior` of a `getrandom` event, of which the requests
ask nothing.

A second fresh agent reviewed the revised statements by the same method, updated the first model,
and ran it on 38,460 cases, 14,696 of the histogram and 23,764 of the random choice, among them
2,802 and 4,366 runs with a short read, 5,554 and 9,409 with a failed read, and 1,332 and 2,310
with a short read followed by a failed read in one group.  Every run that meets `InRange` exits and
meets its statement, and every other run traps.  Of the model's 42 wrong histogram programs and
shims and 39 of the random choice, `Counts` and `Choices` rejected every run that meets `InRange`
and differs from the right program's, among them one word a call, the remainder's words first, an
extra draw, a failed draw's bytes kept, the raw errno, a retry after `EINTR`, and writes of
descriptor 2, except for the classes below.

| Finding | Response |
|---|---|
| `Counts` admits a write of no byte after the output is whole, which offers `out.drop out.length` and returns 0, and the WASI specification's `Written` admits it too, while the random choice's `Writes` requires bytes to remain.  A program that adds such a write met `Counts` on 2,002 of the 2,179 runs on which it differs | Adopted: `Written` and `Counts` state that each write offered at least one byte, as the section "Review of the writes of no byte" describes |
| The comments of `random_short`, of the module, and of the file theorems described the calls of the witness's run, which the statements do not state | Adopted: the comments state `ShortRead` and the replies |
| `RandomGroup` let an error number below the bytes that remain end a group, where the shim continues, for lengths above `2^64 − 4,096`, and `ShortRead` counted such a result as a short read | Adopted: the last call of a failed group returned an error number above the bytes that remain, as the shim requires, and `ShortRead` requires a result that is no error number |
| Comments omitted `Sized` from the bytes of `randomData`, the fit of the arguments from `image_untrapped`, and the earlier writes' counts from the last alternative, and called `loop_trapped`'s event a `random_get` | Adopted |
| The random choice has no witness with a short read | Recorded: the histogram's witness has one, and both corollaries take the group from `random_group` |

Classes that no statement excludes, besides those of the first review: calls that make no layer
event, such as a `random_get` of 0 bytes or an extra `args_get`, whose
layer events equal the right program's, so that only `Meets` excludes them.

## Review of the writes of no byte

After the second review of the premise on short reads, `Written` states that each write offered at
least one byte (`LeanExe.Wasi.WroteSome`), and `Counts` that the input of each `write` holds at
least one byte.  A fresh agent reviewed `Written`, `Meets`, `Counts`, the write loop's statements,
and their comments against the request and the user's decisions on writes, by the method of the
knowledge base's entry on independent review, and ran no Lean code.  Its model in Python,
transcribed from the Lean text, ran `writeAll` and 29 wrong write loops under every host of at most
five writes for eight outputs of 1 to 4 bytes, through the WASI events and through the shim's
write image, and under 5,000 random hosts at each level on the command with N up to 1,024.  The
right program met `Written` and `Counts` on each of the 999 small runs that exit, among them 207
that end with 77 and 528 with a failed write, and on all 5,000 runs of the command at the WASI
level and the 4,920 at the layer that meet `InRange` and `Sized`.  Every run outside `InRange` or
`Sized` trapped.  The new conjuncts excluded the extra write of no byte after the whole output and a
loop whose test is `written ≤ length`, which the earlier statements admitted on 264 and 132 small
runs, and no run of the right program.  `Offered` and `OfferedLayer` already excluded a write of no
byte before the output is whole, since each write offers the bytes that the writes before it did
not take.

| Finding | Response |
|---|---|
| `Written` and `Counts` bounded the number of writes only for status 77, so a loop of B + 2 passes met them on 285 of the 338 small runs on which it differs from the right program, and a loop without a cap on all 376, each ending with status 0 or an errno after more than B + 1 writes.  The shim gives such runs when two writes of a positive count return 0, and the manifest checker's `LineWrites` and the random choice's `Writes` exclude them | Adopted: `Written` states `writes.length ≤ out.length + 1` and `Counts` the same bound over the `write` calls, from `WriteAllRun.shape` |
| `Counts` admitted layer sequences that no run gives: a `write` with a count argument of 0 over a nonempty input, one with a count argument of `2^64 − 1` that returned an error number, which `LeanExe.Linux.Event.writeBytes` counts as taking the whole input, and one that returned more than its input holds and at most its count argument | Adopted: `Counts` states that the count argument of each `write` is the length of its input, as the random choice's `Mirrors` does.  The statement admitted sequences that no run gives, and the change costs nothing at run time.  The shim's image gives the equation, since its arguments are the descriptor, the address, and the size and its input is the bytes offered |
| `Took`'s docstring said "at most the count of bytes that it offered" where the definition compares the result with the count argument, and `InRange`'s docstring and the module comment used the same phrase | Adopted: they state the count, the call's third argument |
| The write loop's module comment said that a write of the rest follows a short write, which fails when the passes run out | Adopted: the comment states it while passes remain |
| The guide said that exhausted passes take a write that took no byte, where B + 1 writes that took fewer than B bytes take at least two | Adopted |
| `writes_images`'s docstring omitted its premise `Offered` and its conclusion `OfferedLayer` | Adopted |
| `WriteAllRun.shape`'s docstring spoke of every run, where the theorem states runs that return or exit.  The docstrings of `writeAll_run`, `writeAll_run_whole`, and `WriteAllRun.taken` and the guide's row omitted their bounds on the number of bytes.  The module comment's description of `Offered` omitted its first `taken` bytes, and the guide's row named `WriteAllRun.trapped_write` without stating it | Adopted |

The same agent then transcribed the revised `Written`, `Meets`, and `Counts` again and ran its model
on them.  The right program met them on every run of its sets, and they admitted no run of any of
the 29 wrong loops, among them the loop of B + 2 passes and the loop without a cap.  It found that
the guide's row of the write loop gave every theorem the bound on bytes of `writeAll_run_whole`,
which was corrected.

Classes that no statement excludes, besides those of the earlier reviews: programs whose events
equal the right program's, such as one in which `writeAll` exits with 77 where `main` returns it,
which no statement over events tells apart, and a `write` with a second input region, which
`Counts` ignores and no event of `LeanExe.Linux.step` has.
