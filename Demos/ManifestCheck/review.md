# Reviews of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the samples](Samples.lean) against
[the request](request.txt), as step 5 of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md) describes.  Each received only the paths of
the request, the specification, the samples, and the samples' outputs, wrote its own model of the
three functions in Python, compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no disagreement.  Its model reproduced the 83 lines of output of the first
sample set and agreed with a second, separately written model on 200,000 random manifests and hex
windows.  It compared the choices of the comment with GNU `sha256sum` 9.7, which skips a line that
is not in the format with a warning and status 0, refuses a manifest with no line with status 1,
removes a trailing carriage return, accepts a single space or a tab before the name, accepts
leading blanks and the tagged form, skips comments, cuts a name at a zero byte, and escapes names
that hold a backslash, a carriage return, or a newline.  The specification differs from it in
each of these, and the comment records each choice.

The review asked for three changes of the comment, which the specification now makes.  The comment
stated the refusal of a single space or a tab only through the definition of the format, and it
now states it.  It stated only through "the name keeps every byte" that absolute names and names
with `..` components are in the format, and it now states that the format admits them and that the
host's resolution confines each open to the preopened directory.  It named the names for which
`sha256sum` writes the escaped form, and the review found a third, so the comment now says "some
names".  The review noted that the status of a refused manifest, and the wording of the verdict for
a manifest with no line, belong to the command's specification.

The review named input classes that no sample covered, and the samples now cover each: the bytes
`/`, `:`, `@`, `` ` ``, and `G` in the digits of a line and of a hex window, a backslash inside a
name, binary mode with a name that starts with `*` or a space, a malformed line between two lines
in the format, empty lines after the last line, a leading tab, a digest that differs only in its
second or third word or in a high half after byte 0, and a name with a backslash in an output line.

## Second review

The second review, of the revised specification and its 99 samples, found no disagreement and
found every open case recorded.  Its model agreed with all 99 outputs and with a transcription of
the specification on 200,000 random inputs, 13,786 of them accepted manifests and 38,415 matching
digests.  It compared the choices with GNU's `split_3`, `digest_check`, and `problematic_chars` in
coreutils `src/cksum.c`.  The specification departs from `sha256sum -c` in the trailing carriage
return, leading blanks, `#` lines, a tab or a single space before the name, escaped and tagged
lines, the refusal of a whole manifest for one line that is not in the format, and the escaping of
output names.  Each choice agrees with the request's literal `HEX  NAME` and `NAME: OK`.  The
review noted that whether "like `sha256sum -c`" asks for any of GNU's behaviors is the user's
decision.

It named these classes that no sample covers, which step 7 of the skill records without new
samples:

| Function | Class |
|---|---|
| `parseSpec`, `hexMatchesSpec` | A zero byte or a byte of 128 or more among the 64 digits |
| `parseSpec` | A carriage return inside a line, as in a manifest whose lines end in carriage returns alone |
| `parseSpec` | A name of one byte that is a space or `*` |
| `parseSpec` | A last line without a newline that is not in the format, after lines in the format |
| `hexMatchesSpec` | Text in upper or mixed case that does not match |

`parse_eq` and `hexMatches_eq` prove the program equal to the specification on every manifest of
the sizes that a store holds, so an error of the program in these classes would contradict those
theorems.  `tools/verified-request-check --freeze` supports only `Examples/<Name>/`, so
`spec.sha256` holds the output of `sha256sum` on `Spec.lean` and `Samples.lean`, and the demo's
driver checks it with `sha256sum -c`.

## Review of the command's specification

A fresh agent reviewed `Meets` of [the command's specification](CommandSpec.lean) and the
statements of `exec_main`, `start_ends`, and `total_meets` against the request, by the method of
the knowledge base's entry on independent review.  It read neither the program nor its proof and
ran no Lean code.  It transcribed `Meets` into a Python predicate over event traces, wrote its own
model of the command from the request, and ran both on 1,581 traces of scripted hosts: matching,
changed, missing, empty, and large files, names with `..`, absolute names, links out of the
directory, short reads and writes, and an errno of each call.  The predicate accepted every trace
of the model.  It checked the rights bits, the layout of `filestat`, the flag `symlink_follow`, and
the errnos against the pinned witx, and GNU's handling of a failed close in coreutils
`src/cksum.c`.

| Finding | Response |
|---|---|
| Before the case `tooLarge`, no trace met `ManifestBody` for a reported size of `2^32` or more, since `Call.reject` refuses such a read without an event | Adopted while the review ran: `readManifest` answers such a size with status 61 (`overflow`) and no read, as `args` answers sizes that reach `2^32` |
| `LineWrites` bounded the number of writes only for `stalled`, so a program with more write passes met `Meets` with another status on the same host | Adopted: `LineWrites` states at most one write more than the line's bytes in every case |
| `LineWrites.all` admitted writes that offer no byte after the whole line | Adopted: each write offers at least one byte (`WroteSome`) |
| A read error after the last byte, a failed close, and a failed open give FAILED, where the request's verdict sentence read literally gives OK for bytes whose digest matches | Kept and recorded: the request asks the command to read each file to its end and close it, and GNU reports a failed close as "FAILED open or read" |
| A manifest without a line gives status 1, where "0 exactly when every line says OK" holds vacuously | Kept: the pure core refuses such a manifest, and GNU fails when it finds no line in the format |
| A line outside the format gives status 1 and no check | Kept: the pure core refuses the whole manifest, as `sha256sum -c --strict` fails |
| An argument buffer without exactly one argument gives status 1, which is also the status of a FAILED line and errno 1 (`2big`) | Kept: the request fixes 0, 1, and the errnos, and the events tell the cases apart |
| The manifest is read through `fd_filestat_get` and a buffer of the reported size, with a last read that tests for more bytes, so a manifest whose bytes number fewer or more than its size gives status 1 | Kept: the buffer of the reported size copies no byte of the manifest, and the request does not fix how the manifest is read |
| The module docstring stated the status without the condition of an accepted manifest, said "one verdict", and did not state the writes that give 77; `Handled`, `ManifestBody`, and `ManifestReads` had imprecise phrases | Adopted |

The review found no wrong arithmetic: 2,097,154 is `2 + 2^21`, the size lies at byte 32 of
`filestat`, `2^45 - 1` reads of at most 65,536 bytes stay below `2^61` bytes, and the windows hold
from 1 to 65,536 bytes.  Of the review's 42 wrong programs, `Meets` rejected every trace that
differs from the command's for all but three.  It rejected, among others, a missing file passed
with the digest of no bytes, an ignored read error or close errno, status 0 after a FAILED line, a
file left open after a read error, a write to descriptor 2, an open of a name that the manifest
does not list, with write rights, or relative to another descriptor, a skipped malformed line,
bytes after the reported size ignored, a file read twice or hashed only in its first chunk, and
checks continued after a stalled write.  It accepted a program with more write passes on 29 of
its traces and a program that writes an empty window after each line, which the revised
`LineWrites` excludes, and a read attempted at a size of `2^32` or more, whose events equal the
command's.

Classes that no statement over events excludes, at the time of this review: a program that
buffers each whole file and hashes it at the end, whose events equal those of the streaming
program, and which the later budget excludes; a guest trap at `unreachable` outside the budget
premise of `total_meets`; the host's resolution of names, which confines them to the preopened
directory outside the theorems; and the relation between the bytes that the host returns and the
files on disk.

## Review of the final statements

A second fresh agent reviewed `Meets`, `exec_main`, `Ends`, `start_ends`, `total_meets`, and the
statements of [the budget](Budget.lean), `budget`, `budget_le`, `body_bounded`, `prefix_bound`, and
`total_meets_budget`, by the same method and without the program, its proofs, or the guide.  It
updated the first reviewer's transcription to the revised `LineWrites`, ran it on 1,589 traces of
its model, none rejected, and on 81,039 traces of 51 wrong programs.  `Meets` rejected 49 of them
on every trace that differs from the command's, among them nine new programs with more or fewer
write passes, empty windows before or after a line, and a write errno taken as 1.  The other two
make the command's events: a read attempted at a size of `2^32` or more, which `Call.reject`
refuses without an event, and a program that buffers each whole file, which `body_bounded`
excludes.  It found every response marked "Adopted" above in the Lean text, recomputed `budget`
and `budget_le`, and found no defect of the statements as Lean text.

| Finding | Response |
|---|---|
| `Confined` and `Handled` hold only of runs that end with the accepted exit: `Ends` gives a run that traps only `Exec` or `Prefix` of `main`, so a program that opens an unlisted name and then exhausts the memory meets every statement for hosts outside the premises of `total_meets_budget` | Adopted: `SoFar` states the three properties of the events of every run that stops, and `Ends` gives it in its trap cases, as the next review records |
| The premise on `fd_filestat_get` covers every reply, while the command asks it only of the manifest, so a host whose checked files report large sizes is excluded | Recorded in the docstrings of `body_bounded` and `total_meets_budget` |
| No theorem showed that the premises of `total_meets_budget` hold together | Adopted: `initial_within` gives the bound on the heap for every `M` of at most 23,000,000 |
| The docstrings of `checkBudget`, `budget`, `body_bounded`, `total_meets`, `total_meets_budget`, and `ManifestBody` claimed more or less than their Lean text | Adopted |
| A manifest whose reported size differs from its bytes, such as a FIFO, a file of `/proc` that reports size 0, or a file being appended to, gives status 1 | Recorded: the command reads a manifest of the size that the host reports, and the guide states it |

Classes that no statement excluded at the time of this review: the opens and writes of a run that
traps, for the first finding's reason; an engine that refuses `memory.grow` below the cap, since
the exclusion of the guest trap holds under Talos's semantics of memory growth; a read attempted at
a size of `2^32` or more, whose events equal the command's; and, as before, the host's resolution
of names and the relation between the bytes that it returns and the files on disk.

## Review of the statements for runs that stop

A third fresh agent reviewed `SoFar`, `ConfinedSoFar`, `HandledSoFar`, `Unfinished`, the trap cases
of `Ends`, and the statements of [the runs that stop](CommandPrefix.lean), by the same method and
without the proofs.  It transcribed `SoFar` into Python predicates over event lists, with a second
transcription that tries every split that the existentials allow, and wrote an oracle of the
request's confinement and handles apart from the Lean text.  It ran them on the event lists of runs
that stop: every prefix of a run, a trap of the host at each event, and a rejected exit after the
last.  Of its model's 1,593 runs and 65,122 such lists, neither `SoFar` nor the oracle rejected
any, and the two transcriptions agreed on 11,144.  It ran 32 wrong programs on 393 scenarios,
542,074 lists.

| Finding | Response |
|---|---|
| `Confined` accepted the bytes after the first 66 of every line of the manifest, in the format or not, so a run that stops could open the tail of a malformed line, the empty name among them | Adopted: the file case of `Confined` requires `WellFormed l.2`, which `Run` gives in `Meets` |
| `SoFar` accepted the names of the lines in the format of a manifest that the pure core refuses for another line, which the command refuses before it opens a file | Adopted: the file case of `ConfinedSoFar` requires the condition under which `Run` checks the lines, `lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2` |
| `SoFar` constrained no output line written before a stop, while the request states the verdict property of every run: a program that writes `b.bin: OK` for a changed file and then stops met it | Adopted: `VerdictsSoFar` is the third part of `SoFar` |
| The module docstring said that `ConfinedSoFar` takes the bytes that the reads of the manifest returned, where it takes those of a `ManifestRun` with status 0 after `args`, or none | Adopted |
| The docstrings of `SoFar` and the module called `SoFar` what the request asks, while it stated two properties, and "before its exit" described runs that end with a rejected exit | Adopted: "without an accepted exit" |
| The docstrings of `writes_soFar`, `withOpen_stops`, `stalled_stops`, `step_stops`, `checks_stops`, and `checkLines_stops` claimed more than their Lean text, and those of `LinesSoFar`, `readManifest_every`, and `hashFile_every` less; a line of `Handled`'s docstring passed the line width | Adopted.  `LinesSoFar` and `writeAll_stops` replace `writes_soFar` |

`VerdictsSoFar` states that no event writes to standard output, or that the events are those of
`args`, of a `ManifestRun` with status 0 of a manifest that the pure core accepts, and of
`ChecksSoFar` for its lines, followed by events that write nothing to standard output.
`ChecksSoFar` states the checks of the first lines as `Checks` states them, followed by none or by
the `FileCheck` of the next line and writes that offer the bytes of its output line, with that
line's verdict, after those that the writes before them took.  A check that stops before its writes
writes nothing, so the statement needs no prefix form of the reads of a file or of the manifest.
`writeAll_stops` of [the stopped-run lemmas](../../Verified/Wasi/Stops.lean) gives the bytes that
each write of a run of `writeAll` that stops offers.

The reviewer's transcription with the three changes, and an oracle of the verdict property
written apart from the Lean text, accepted all 65,122 lists of the model, and the two
transcriptions agreed on the same 11,144 lists.  The transcription rejected every list of the
reviewer's wrong programs on which its oracle finds a violation, among them the opens of the bytes
of a malformed line and of the names of a refused manifest.  On 52 programs of the three reviews,
867,468 lists, it rejected the reviewer's program that writes OK for a changed file, and every list
on which a written line holds a wrong verdict or wrong bytes: a missing file passed with the
digest of no bytes, an ignored read error or close errno, a file hashed only in its first chunk,
digits compared in one case, a write of no byte, and a line written in two fixed pieces whatever
the first write took.  Like `Meets`, it also rejects lists that the request allows, once a write
follows: a file read twice or the manifest reopened, and reads into windows other than the
specification's.

Classes that no statement excludes, after this review: in a run that stops, checks after the last
write that write nothing, such as a file checked twice, output lines held back to the end, or
checks continued after a stalled line, of which the oracle flags 7,330 lists, none with a wrong
line written; reopening the manifest or reading a file twice before any write; the host's
resolution of names; the relation between the bytes that the host returns and the files on disk; a
read attempted at a size of `2^32` or more; and an engine that refuses `memory.grow` below the cap.

## Review of the executable's theorems

A fourth fresh agent reviewed the native statements against [the request](request.txt), by the
method of the knowledge base's entry on independent review: `InRange`, `Opening`, and `NMeets` of
[the specification over Linux events](NativeSpec.lean), the statements of [the corollary under the
shim](NativeMeets.lean), `StatBounded` and `budget_fits` of [the footprints](Native.lean), the
executable's theorems with their witness, the driver's native, QEMU, and strace checks, and a draft
of the guide's section.  It received the paths of these files, the shim's model, and the request,
wrote a model in Python of `InRange`, of `NMeets` with a search over every alternative of every
constructor, of the shim's images, of a kernel with injected faults, and of the command, and ran
no Lean code.  The right program met `NMeets` in all 33 of its scenarios, and `NMeets` detected 32
of its 39 wrong programs.

| Finding | Response |
|---|---|
| `Opening` accepted any errno other than 0 for an open that made no call, so a program that exits with status 1 without a call met `NMeets` for every argument list, and so did a program that writes FAILED for every line without opening a file | Adopted: `Opening held name` gives an open without a call the errno of the shim's checks, `nameCheck held name`, and an open with calls requires that the checks pass.  `NMeets` takes `held`, whether the shim holds descriptor 3, which `manifest_elf_meets` gives as the startup check's grant.  `InRange` requires an `openat2` descriptor of 4 or more, so the shim holds descriptor 3 throughout the run exactly when the check granted it (`spares3_three`) |
| The `more` constructors of `NManifestReads` and `NFileReads` accepted a read that returned an error number, whose `toNat` is positive, so a program that retries after `EIO` and reports OK met `NMeets` | Adopted: each requires `Linux.isError e.ret = false` |
| `StatBounded manifestLimit R` fails on correct runs: a `read` that returns 0 leaves its window's old bytes, which `Carried` records as the reply's bytes, and a file whose last 65,536 bytes hold a size above 1 MiB where a `statx` record holds `stx_size` gives such a reply | Adopted in the guide, which states the case.  A premise on the run's `statx` events alone needs a budget that follows the run's worlds, a change of `body_bounded`'s premise that this review leaves open |
| The guide's row of `manifest_elf_meets` and the file's docstrings said "when the check grants descriptor 3", while the theorem's case also covers a check that grants nothing | Adopted: "when the check does not end the run", and `NMeets` names the grant |
| `InRange`'s docstring called the bound of 1,024 Linux's, which is the shim's limit, and the guide cited statx(2) for nanoseconds below `10^9`, which the page does not state | Adopted: the docstring and the guide name the shim's limit, and the guide gives the bound on nanoseconds as `InRange`'s premise, under which the shim does not trap |
| The docstrings of `linux_exec_meets`, `image_untrapped`, and `read_native` omitted premises | Adopted |
| No driver run caused a read error, a failed `close`, `EAGAIN`, or a short write, so the driver passed 22 of the 39 wrong programs | Adopted in part: five runs under strace's injection make the first read of a file fail with `EIO`, the first three and the first four `openat2` calls return `EAGAIN`, the manifest's `close` fail with `EIO`, and every `write` return 0.  Declined: a checker of `NMeets` over the strace log, since `manifest_elf_meets` states those properties of the bytes that `manifest_elf_file` checks, and the driver's traces test the kernel's agreement with the call layer |
| A program that gives up after fewer than four `openat2` calls that return `EAGAIN` met `Opening` | Adopted: an `EAGAIN` ends an opening only as its fourth call, as `OpenCalls` states |
| The guide's counts were those of `RUNNERS=wasm`, and the file of 5 MiB and 17 bytes takes 82 reads, the last of which returns 0 | Adopted |

The reviewer found that the other premises of `manifest_elf_meets` hold on Linux: the strings and
pointers of `argv` and `envp` take at most 6 MiB (`bprm_stack_limits`), `read` and `write` return
at most their counts, `close` and `statx` return 0 or a negated error number, and `Sized` follows
from `Carried`.  It checked the witness's stack against `InitialStack` field by field and the
witness's replies against `preopenRun`.  `NMeets` also fixes the method that the request leaves
open: each read's count, the probe of 65,536 bytes after the manifest, and the flags and mask of
`statx`, so a program that meets the request with other reads fails it.

Classes that no statement excludes, after this review: programs that differ only in registers or
memory that no statement constrains; runs whose replies fail `StatBounded`, of which the corollary
states nothing; and the kernel's resolution of names, which the traces show for the names of the
driver.

## Second review of the executable's theorems

A fifth fresh agent reviewed the revised statements, the responses above, the guide's sections, and
the driver by the same method.  Its model of `InRange`, `nameCheck`, and `NMeets`, of the shim,
and of the command ran 52 wrong programs on 904 scenarios: 15 manifests, among them line names
that the shim's checks refuse, about 60 fault cases each, with one, three, and four `EAGAIN`
results, failed and short reads, failed closes, short and failed writes, times before 1970,
descriptors up to 1,023, and descriptor 3 not granted, and ten argument lists with and without
descriptor 3.  The right program met `InRange` and `NMeets` in all 904 scenarios, and `NMeets`
rejected 50 of the 52 wrong programs.  It found the responses above held in the Lean text, and no
defect of a statement.

| Finding | Response |
|---|---|
| The guide's example of a reply that fails `StatBounded` needs seconds that keep each time below `2^64` nanoseconds, since a larger time gives errno 61 | Adopted |
| The section on confinement credited the retries after `EAGAIN` to `run_openHow`, which states the record | Adopted: it cites `run_openLoop` and `openStub_sim` and says that the stub calls `openat2` again after each `EAGAIN` of the first three |
| The section on confinement said that the driver shows Wasmtime refusing each name that leaves the directory with errno 63, which it checks only for the manifest named with `..`; the lines give FAILED | Adopted |
| The docstrings of `run_native` and `handled_native` and the module docstring of the corollary omitted premises, and the module docstring called each WASI event's image unique | Adopted |
| `NFileReads`'s docstring described each read as one of `window done` bytes, where each read takes the window after the bytes of the reads before it | Adopted |
| `NManifestBody`'s docstring and the guide said that any time of `2^64` nanoseconds or more gives status 61, where `Overflows` reads the access, modification, and reported birth times | Adopted |
| The guide did not say that the corollary covers manifests of at most 1 MiB | Adopted |

Two wrong programs met every statement and check.  A program that tests a line's name for a zero
byte and for its length in another order makes no call and writes FAILED either way, since a
refused line discards its errno.  A program that opens the checked files with the rights
`manifestRights` makes the same Linux events, since the open flags depend only on `fd_write`, and
`Confined` at WASI excludes it.  A program that reads a file in full before hashing it, with the
same reads, meets `NMeets`, and `manifest_elf_meets` excludes it only through the guest trap of a
file that outgrows the executable's 4,096 pages.
