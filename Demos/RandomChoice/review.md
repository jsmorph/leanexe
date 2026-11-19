# Reviews of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the samples](Samples.lean) against
[the request](request.txt), as step 5 of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md) describes.  Each received only the paths of
the request, the specification, the samples, and the samples' outputs, wrote its own model of the
request in Python, compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no disagreement.  Its model agreed with the 119 outputs of the first sample
set and with a transcription of the specification on 200,000 random inputs for each function,
weighted toward zero bytes, the bytes beside the digits, numerals near `2^64`, and words near
`2^64 mod N`.  It confirmed by arithmetic for 20,011 values of N, and by an exhaustive count with
10-bit words, that every value in [1, N] has `⌊2^64 / N⌋` accepted words.  It found three comments
imprecise: the comment of `argument` did not say that zero bytes are counted from 1, the module
comment did not say that a missing argument is refused, and it stated the command's reading of N
and K without saying that the command's specification carries that choice.  The specification's
comments now state all three.

The review named input classes that no sample covered, and the samples now cover each: argument 0
with an empty program name and of the empty buffer, an overflowing numeral followed by a letter,
`N = 2^63 - 1` and `N = 3 · 2^62`, whose remainders 2 and `2^62` no other sample has, and the
powers of two 4 and `2^32`.

## Second review

The second review, of the revised specification and its 132 samples, found no disagreement.  Its
model, built from the request alone, and a transcription of the specification agreed with every
output and with each other on 200,000 random inputs weighted toward zero bytes, values near
`2^64`, powers of two, and words at `2^64 mod N`.  A check over 1,008 values of N confirmed that
each value in [1, N] has `⌊2^64 / N⌋` accepted words.  It found every open case recorded and
named three notes on the comments, which this review records without changing the frozen files.

| Note | Response |
|---|---|
| The comment names the command's specification as the place where N is argument 1, K argument 2, and the later arguments are ignored, which no file of the specification defines | [The command's specification](CommandSpec.lean) reads N and K as arguments 1 and 2 with `parseSpec`, and no event of a run depends on the other arguments |
| WASI's documentation of `args_get` does not state the layout of the buffer | `LeanExe.Wasi.args` passes the bytes of `args_get` to the program, and Wasmtime writes each argument followed by a zero byte, as the histogram's runs and the command's runs show |
| The request's formula `(0 - N) % N` accepts every word for N = 0, while `pickSpec` accepts none | `pick` tests `n != 0`, and `pick_eq` proves it equal to `pickSpec` for every N, 0 included |

It named these classes that no sample covers, which step 7 of the skill records without new
samples:

| Function | Class |
|---|---|
| `parseArg` | Numerals of more than 21 significant digits, which an accumulator wider than 64 bits would read differently |
| `pick` | An N with `2^64 mod N = N - 1`, the largest threshold, such as 274,177, a divisor of `2^64 + 1` |
| `render` | The boundaries 9,999 and 10,000, 999,999 and 1,000,000, and `10^k - 1` and `10^k` for k from 7 to 18 |

`parseArg_eq` and `pick_eq` prove the programs equal to the specifications on every input, and
`render_eq` on every array of fewer than `2^59` values, so an error of a program in these classes
would contradict those theorems.

# Reviews of the specification of `putPicks`

Two fresh agents reviewed [the specification of `putPicks`](PicksSpec.lean) and [its
samples](PicksSamples.lean) against [the request](request.txt) and [the request that `putPicks`
serves](picks-request.txt), with the specifications of [the pure core](Spec.lean) that it uses.  Each
received only the paths of those files and of the samples' outputs, wrote its own model in Python,
compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no input on which the specification contradicts the requests.  Its model,
built from the requests, and a transcription of the specification agreed with the 19 outputs of
the first sample set and with each other on 20,000 random inputs, among them 6,708 whose lines are
longer than the output buffer, 6,724 whose limit cuts the values, 593 with N = 0, 9,984 with bytes
after the last whole word, and 1,942 with more than 512 words.  It named notes on the comment and
input classes that no sample covered, with these responses.

| Note | Response |
|---|---|
| The comment does not record N = 0, which accepts no word | The comment states it and names `accepts` |
| The specification reads every whole word of the draw, which is right only when the command fills the whole draw buffer at each call | The comment states that the command fills the whole buffer of 4,096 bytes at each call of `random_get` |
| When the lines are longer than the buffer, the length and the count include lines that were dropped, which a caller that writes the length would get wrong | The comment states it, and that the command's buffer of 10,752 bytes holds the lines of 512 values of at most 20 digits, so the lines of a draw always fit |
| The heading of the decisions lists points that the request fixes | The comment separates what the request fixes from the choices that it leaves open |

The samples now cover each class that the review named: a buffer of varied bytes, lines longer
than a buffer that ends after a newline, lines that the limit cuts and that are longer than the
buffer, N of 2, `2^32`, and `2^63`, whose threshold is 0, 512 values of 20 digits, whose lines fill
10,752 bytes, and a draw of 600 words.

## Second review

The second review, of the revised specification and its 27 samples, found no disagreement.  Its
model, built from the requests and the comment's prose, rebuilt the 27 inputs from the samples'
file, agreed with every output, and agreed with a transcription of the specification on 200,000
random inputs weighted toward N at powers of two and their neighbors, words at the threshold and at
multiples of N, draws with trailing bytes, limits at the count of accepted words, and buffers at
the length of the lines.  It found every open case recorded and named two notes on the comment and
a remark on the design, which this review records without changing the frozen files.

| Note | Response |
|---|---|
| "every word of `draw` comes from the draw" means that no word of an earlier call is read again | The command fills the whole draw buffer at each call, which `Rounds` states of every pass with the event `random_get` of 4,096 bytes and its reply |
| The first decision lists the little-endian reading, which the request fixes; the open parts are the positions of the words and the bytes after the last whole word | The decision records both parts, and the request's reading agrees with it |
| When the lines are longer than `out`, the second component exceeds the filled window, which the command could not write | The command's buffer of 10,752 bytes holds the lines of every draw, and `pass_put` proves that the lines fit, so the command writes exactly the lines |

It named these classes that no sample covers, which step 7 of the skill records without new
samples: N ≥ 1 with a draw whose words are all rejected, a buffer that ends inside a line of two or
more digits, and counts of `2^64` or more, which need a draw of more than `2^67` bytes.
`putPicks_eq` proves the program equal to the specification on every draw of fewer than `2^32`
bytes, so an error of the program in the first two classes would contradict it.

# Review of the executable's theorems

A fresh agent reviewed `Mirrors`, `Choices`, `linux_exec_choices`, `witness_run`, the footprints,
`choice_elf`, `choice_elf_choices`, `choice_elf_witness`, the trapped case of `draw_loop`, and the
driver's native and strace checks against [the request](request.txt), by the method of the
knowledge base's entry on independent review.  It received the paths of the request, the theorems,
the specifications, the shim's model, the driver, and a draft of the guide's section, wrote a model
in Python of the shim's images under `Full`, of `Mirrors`, `Choices`, `Rounds`, and `Writes`, and of
the command, and ran no Lean code.  On 2,000 random runs that meet `Full`, which reached status 0,
refusals, the cap, stalls, and failed writes with ten error numbers, the right program met
`Choices` in every run, and each of 38 wrong programs failed `Choices` in exactly the runs where its
events or status differ from the right program's.  It found no defect of a statement: under `Full`,
`Choices` fixes every observable property of a run but the addresses passed to `getrandom` and
`write`, of which the request asks nothing.  It checked the witness's stack bytes against
`InitialStack` and replayed the witness's run.

| Finding | Response |
|---|---|
| The driver's comment claimed that every write offers the bytes of the pass that remain, which its check did not test, so writes of at most 1,024 bytes passed | Adopted: each later write of a pass must offer the bytes that the pass's earlier writes did not take, and with full returns a pass makes one write |
| strace prints a zero argument as `0`, which the parser did not read, so a write of no byte, or a write of another descriptor, passed | Adopted: the parser reads `0`, records the descriptor, and fails when a `getrandom` or `write` line does not parse, and every write must be of descriptor 1 and offer at least one byte |
| The summary of the first strace run checked the counts but not their order, so a program that draws every pass before writing passed | Adopted: the summary lists the calls in order, `g 1024 g 976` |
| No driver run reaches the cap or a stall | Adopted: a run with strace's injection of a `getrandom` result of 4,096, which leaves the draw buffer at zero bytes, must reach the cap with status 77 after ten calls and no write, and a run with injected `write` results of 0 must stall with status 78 after three writes |
| Decoding the bytes of each `getrandom` and recomputing the output would check the word order, the byte order, and the pick | Declined: `choice_elf_choices` states them, and the file theorem states that the driver's executable holds the bytes that `genWasiElf` gives |
| `witness_run`'s docstring and the module comment stated events that the theorem does not conclude | Adopted: the docstring states the status and `Full`, and the comment names the events as the proof's |
| The guide's heading claimed uniform values, which no theorem states | Adopted: the headings of the command's and the executable's sections name the picks of the first K accepted words |
| The draft guide dropped getrandom(2)'s condition that the urandom source is initialized | Adopted |
| "When N or K is 0" stood for a refusal of `parseSpec`, and `argN`'s docstring did not say that 0 marks one | Adopted |
| `Mirrors`'s docstring used "count" for the length argument and the reply's count, and did not say that no other event mirrors anything | Adopted |
| "A host that accepts every exit status below 126" stated more than the premise, that a rejected exit has a status of 126 or more | Adopted: "a host that rejects no exit status below 126" |
| The draft guide credited `witness_text` with a fact of `putPicks` | Adopted: it cites `pass_put` and `witness_text` |
| Lines of the driver and of the Lean files ran past 100 columns | Adopted for the new lines |

The model also ran the driver's checks on the wrong programs.  Every runner detects K ± 1 lines,
picks from 0, refusals with status 1, ignored or misreported failed writes, and writes to stderr.
The native and QEMU runs under the file size limit detect a stall at a short write.  The strace runs
detect draws of 2,048 bytes, other flags, other calls, rewrites after a short write, retries, one
write per line, and draws before parsing.  With the adopted checks they also detect writes of at
most 1,024 bytes, writes of no byte, draws of every pass before writing, picks of rejected words, a
status 0 at the cap, other caps, and stalls after fewer passes of `writeAll`.  Words read last to
first or big-endian and a threshold off by one change values only within [1, N], which no run
checks beyond their range, and `choice_elf_choices` excludes them.

Two classes of programs pass every statement and check.  Programs that differ only in the addresses
that they pass, each constant within a run, meet `Choices`, which leaves the addresses free.
For programs that differ only at replies outside `Full`, such as a short or failed `getrandom`,
`choice_elf` fixes the calls of the shim, but no theorem states the output.  A write that fails with
`EACCES` gives errno 2, `acces`, the status of a refused argument, so the status alone does not tell
the two apart.  The events of `Choices` do, since a refusal has none.
