# Manifest checker

## Request, specification, review, and program

[The request](request.txt) asks for a SHA-256 manifest checker like `sha256sum -c`.  The approved
plan fixes its behavior: `check MANIFEST` opens and reads MANIFEST under the preopened directory,
and for each line in `sha256sum`'s format, `HEX  NAME`, it opens NAME read-only under the same
directory, reads it to its end through a streaming SHA-256, closes it, and writes `NAME: OK` or
`NAME: FAILED`.  The status is 0 when every file matches, 1 when one fails, and the errno when a
call on the manifest fails.  This directory holds the pure core of the checker, the functions that
parse the manifest, compare a line's digits with a digest, and render an output line, with their
reviewed specifications and call theorems, the WASI command around them, with theorems about its
verdicts, the files that it opens, and its descriptors, and the command's AArch64 Linux executable,
with the same theorems over Linux's system calls.

The pure core has three functions, whose specifications [the specification](Spec.lean) states,
written and reviewed by the method of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md).  `parseSpec` gives the lines of a manifest
in `sha256sum`'s format, two positions to a line, or the empty array for a manifest that it
refuses.  `hexMatchesSpec` states whether the 64 bytes of a manifest from a position are the hex
digits of a digest, and `renderSpec` gives the output line of a name and a verdict.  The
specification's comment records each choice that the request leaves open.  A line is a run of
bytes between newlines, so a final newline is optional and empty lines are skipped, and a carriage
return is a byte of its line.  A line in the format has 64 hex digits of either case, a space, a
space or `*`, and a name of at least one byte, which keeps every byte and has no escapes.  A
manifest without a line or with a line outside the format is refused as a whole, so a command that
uses `parse` checks every line or none.  The format admits absolute names and names with `..`,
which the host's resolution confines to the preopened directory, as the section on confinement
states.

Two fresh agents reviewed the specification against the request, as [the review](review.md)
records.  Neither found a disagreement.  The first asked for three corrections of the comment and
named inputs that no sample covered, and [the samples](Samples.lean) now cover them, 99 in all.  The
second listed the choices that depart from GNU `sha256sum -c`, among them the refusal of a whole
manifest for one malformed line, the kept carriage return, and the unescaped output names, and
named five classes that no sample covers, which the review lists.

[The program](Program.lean) holds the three functions in the verified compiler's dialect.  `parse`
reads the manifest once with one array as its state, which the loop moves from pass to pass and
updates in place: the start of the current line, whether every line so far is in the format, and
the positions found so far.  A newline, or the end after the last byte, closes a line, and
`lineOk` tests its format.  `hexMatches` tests first that the 64 bytes lie within the manifest, so
that no position wraps, and then compares each pair of digits with a byte of the digest.  `render`
builds the output line from the name's bytes and the bytes of `: OK` or `: FAILED` and a newline,
which `suffixByte` computes from their positions.  [The verified compilation](Compiled.lean) writes
a module that exports `parse`, `hexMatches`, and `render` as functions 6, 8, and 10.

[The streaming SHA-256](../../Library/Hashing/Sha256/README.md#implementation) of the library
hashes a message that arrives in pieces: `update` compresses the whole blocks of a byte string into
the hash value, and `finish` pads the bytes after the last whole block with the length of the whole
message.

## The pure core computes its specification

| Theorem | Statement |
|---|---|
| `parse_eq`, `hexMatches_eq`, `render_eq` | Each program equals its specification, for a manifest of fewer than `2^62` bytes, a manifest of fewer than `2^64` bytes, and a name of fewer than `2^64 - 9` bytes ([the proof](Proof.lean)). |
| `parse_callSpec`, `hexMatches_callSpec`, `render_callSpec` | `Verified.CallSpec compiled.module compiled.tables K spec compiled.f.bound` for `K` = 6, 8, and 10: called with borrowed arguments from a ready store with room for the bound, the function returns the specification's value without a trap and leaves a ready store ([the compilation](Compiled.lean)). |
| `parse_bound`, `hexMatches_bound`, `render_bound` | The generated bounds are at most `176 n + 464` bytes for a manifest of `n` bytes, 0, and at most `n + 64` bytes for a name of `n` bytes, for `n` below `2^32`. |
| `update_toVec32`, `finish_spec`, `stream_spec` | The streaming SHA-256 computes the digest of the transcription of FIPS 180-4 for the whole message ([the library's proof](../../Library/Hashing/Sha256/StreamProof.lean)). |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.  `parse_eq`
follows the lines: the step of `parse` keeps its state at a byte other than a newline, and at the
byte that closes a line it adds the line's positions and its test, so `parse_from` proves by strong
induction on the positions that remain that the loop adds the positions of the lines that
`linesFrom` gives for the pieces of the rest.  `parseStep_enc` relates the array of the program's
state to a state of three parts, on which the induction runs.

## The command

[The command](Command.lean) is `main : Action UInt64`.  It reads its one argument with `args` and
`argScan`, builds a read buffer of 65,536 bytes, and opens the manifest of that name under the
preopened directory with `withOpen`, with the rights `fd_read` and `fd_filestat_get`.
`readManifest` asks the manifest's size with `fdFilestatGet` and answers a size of `2^32` bytes or
more, for which a read's length does not fit its 32 bits, with status 61 (`overflow`).  `readBytes`
builds a buffer of the reported size and reads the manifest into it with `fdRead`, each read into
the window after the bytes already read, until the buffer is full, a read returns no bytes, or a
read returns an errno.  A last read into the read buffer tests that the manifest has no byte after
them, so a manifest whose bytes number fewer or more than its size gives status 1, as do a FIFO, a
file of `/proc` that reports size 0, and a file being appended to.  The bracket closes the
manifest, and `parse` gives the positions of its lines, or none for a manifest that the pure core
refuses, which gives status 1.

`checkLines` checks the lines in order, with the read buffer in its loop's state.  For each line it
copies the name from the manifest with `slice`, opens it under the preopened directory with the
right `fd_read` alone, hashes the file with `hashFile`, closes it, compares the digest with the
line's digits with `hexMatches`, and writes `render` of the name and the verdict with
`writeAll line 0 line.size` of [the shared write loop](../../LeanExe/Wasi/WriteAll.lean), which
writes the window of the line that remains after a short write.  Every open names descriptor 3, the
flag `symlink_follow`, no open flags, no inherited rights, and no descriptor flags.  `hashFile`
reads the file into the window of the read buffer after the bytes that it holds, and when a read
fills the buffer it compresses the buffer's 1,024 blocks into the hash value with `update` and
starts again at the buffer's first byte.  When a read returns no bytes, it compresses the whole
blocks that the buffer holds and passes the bytes after them to `finish` with the file's length.
Its loop makes at most `2^45 - 1` reads of at most 65,536 bytes each, so the bytes that it hashes
number fewer than `2^61`, the limit of SHA-256's length field.  The read buffer moves from pass to
pass and into each bracket and out of it, and the windows of the reads are its bytes, so no pass of
a read loop builds a buffer.

A line's verdict is OK when the open of its name returned errno 0, a read returned no bytes before
any read returned an errno, the close returned errno 0, and the line's digits give the digest of the
bytes that the reads returned.  A file that fails to open, a read that returns an errno before the
file's end, a failed close, and reads that stop after `2^45 - 1` reads give FAILED, and the checks
continue.  The status is the errno of `args`, 1 for an argument buffer without exactly one argument
after the program name, the errno of the manifest's open, of `fdFilestatGet`, of one of its reads,
or of its close, 61 for a reported size of `2^32` bytes or more, and 1 for a manifest whose bytes
disagree with its size or that the pure core refuses.  After a manifest that the core accepts, the
status is 0 when every line says OK and 1 when one says FAILED, 77 when the writes of an output line
stop with bytes left, which ends the checks, and the errno of a write that fails, with which
`writeAll` exits.  Every errno lies from 0 to 76, so 77 differs from every errno.
`verified_compile_wasi` writes a module of 17,882 bytes that imports `fd_read` twice, as the stream
read of the ABI and as the flat call, `fd_write`, `proc_exit`, `fd_filestat_get`, `path_open`,
`fd_close`, `args_sizes_get`, and `args_get`.

## The command meets the request

| Theorem | Statement |
|---|---|
| `exec_main` | Under every host, every run of `main` followed by its exit that ends with the status `code` has the events `events ++ [.exit code]`, where `events` meet `Meets`, and `code` is at most 77 ([the command's proof](CommandProof.lean)). |
| `start_ends` | For every host, every host environment that satisfies `hostSpecWith host command.sysCalls`, and every world, every run of `_start` from the command's initial store with enough fuel ends as `Ends` states: the accepted exit after events that meet `Meets`, a trap of the host or a rejected exit after a run of `main` whose events meet `SoFar`, or a guest trap at `unreachable` after a prefix of `main` whose events meet `SoFar` ([the compiled command](CommandStart.lean)). |
| `stops_soFar`, `trapped_soFar`, `prefix_soFar` | Under every host, the events of every run of `main` followed by its exit that stops without an accepted exit, a run that traps or a prefix of a run, meet `SoFar`: confinement, the use of descriptors, and the verdicts of the output lines written before the stop ([the runs that stop](CommandPrefix.lean)). |
| `total_meets` | Under the premises of the generated `command.total` as well, a budget that fits the initial store's free memory and bounds the heap of every prefix of `main`, and a host that traps nowhere along `main` and its exit, every such run ends with the accepted exit after events that meet `Meets`. |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.  `Meets` of
[the command's specification](CommandSpec.lean) holds three properties of a run's events, which
record each call and the host's reply.  `Run` states the verdicts and the status: the events of
`args`, then `ManifestRun`, the open of the manifest, the call of `fd_filestat_get`, the reads of
`ManifestReads` and the last read, and the close, and then `Checks`, which states for each line of
the manifest in order `FileCheck`, the open of its name, the reads of `FileReads`, and the close,
with the verdict above, followed by `LineWrites`, the writes of its output line,
`renderSpec (name, ok)`.  Each write offers at least one byte, the bytes of the line that the writes
before it did not take, and the writes of a line number at most one more than its bytes.  The
verdict is OK exactly when `DigestOf` holds: the line's 64 hex digits give the digest of the
transcription of FIPS 180-4 for the bytes that the reads returned.  `Confined` states that every
`path_open` names descriptor 3, the read-only rights `manifestRights` or `fileRights`, and the
argument or the name of a line of the manifest in the format.  `Handled` states that the events
are calls of `args_sizes_get` and `args_get`, opens that fail, brackets of an open, calls on its
descriptor, and its close, and writes to standard output, so each descriptor is closed before the
next open and before the exit.  [The review](review.md) records the decisions of the cases that the
request leaves open.

`SoFar` states the three properties of the events of a run that stops without an accepted exit:
at a trap of the host, at an exit that the host rejects, or at a trap of the guest.
`ConfinedSoFar` states `Confined` of the events for the buffer that `args` returned and the bytes
of a `ManifestRun` with status 0 after the events of `args` whose manifest the pure core accepts,
or for no bytes when the events hold no such run.  An open of a line's name therefore follows the
whole reading of a manifest that the command checks.  `HandledSoFar` states that the events are
those of `Handled` followed by those of `Unfinished`: none, an open that returned errno 0 followed
by calls on its descriptor and no close, an open that trapped, or an exit that the host rejected.
`VerdictsSoFar` states that no event writes to standard output, or that the events are those of
`args`, of such a `ManifestRun`, and of `ChecksSoFar` for the manifest's lines, followed by events
that write nothing to standard output.  `ChecksSoFar` states the checks of the first lines as
`Checks` states them, followed by none or by the `FileCheck` of the next line and writes that
offer the bytes of its output line, with that line's verdict, after those that the writes before
them took.  Every output line written before a stop, whole or in part, therefore holds the verdict
of its `FileCheck`, from the digest of the bytes that the host returned for its file.

The proof follows `main`.  `argument_cases` relates the program's test of the argument buffer to
`OneArgument`.  `manifest_loop` follows the reads of the manifest: a read places the window's
output at the window's start (`splice_take`), so the buffer's first bytes are those that the reads
returned, and a buffer that the reads fill holds the manifest.  `readBytes_run` and
`readManifest_run` add the last read and the call of `fd_filestat_get`.  `Hashed` relates the state
of `hashFile`'s loop to the bytes that its reads returned: the hash value after their whole buffers
of 65,536 bytes, and the bytes after those, which the read buffer holds from its start.
`Hashed.part` and `Hashed.full` keep it across a read, through `update_toVec32` and
`blocksFold_append`, `hashed_finish` gives the digest bytes of `SHS.SHA256.Impl.sha256` through
`finish_bytes`, and `hash_loop` follows the loop by induction on its passes.  `withOpen_run` gives
the events of a bracket, `entry_check` those of `FileCheck` for a line with the program's verdict,
which `hexMatchesSpec_iff` and `digestOf_iff` relate to `DigestOf`, and `line_writes` those of
`LineWrites` from `WriteAllRun.taken`.  `checks_loop` follows the loop of `checkLines` by induction
on the lines, from the positions that `parse` gives (`parse_accepted`, `entry_get`), and
`meets_of` assembles `Run`, `Confined`, and `Handled` from the parts.  `main` takes the table of
SHA-256's round constants, which the module holds in its static data, as its argument, and
`table_rep` and `table_low` give the generated theorems the table's representation.

`stops_soFar` follows `main` again, with the lemmas of [the runs that
stop](../../Verified/Wasi/Stops.lean): a run of `Action.bind first next` that stops is a run of
`first` that stops, or a run of `first` that returns followed by a run of `next` that stops
(`Stops.bind`).  The parts that return have the events that the lemmas above give, and a part that
stops has only the events that `Every` allows of it: the calls of `args` and the calls on the
descriptor of a bracket's body (`readManifest_every`, `hashFile_every`).  `writeAll_stops` gives
the writes of a run of `writeAll` that stops, each of which offers the bytes of the output line
that the writes before it did not take, with at most one rejected exit at their end.
`withOpen_stops` gives the events of a bracket that stops, which write nothing to standard output.
`LinesSoFar` states the opens, the use of descriptors, and `ChecksSoFar` after each pass of the
loop of `checkLines` (`step_stops`, `checks_stops`), and `confined_of` and `soFar_of` assemble
`ConfinedSoFar` and `VerdictsSoFar` from the run of `args`, the `ManifestRun`, and the checks of
the lines that follow it.  A run that stops after `main` returned has the events of `Meets`, whose
`Checks` give `ChecksSoFar` (`Checks.soFar`, `verdicts_of_meets`).

## Memory

| Theorem | Statement |
|---|---|
| `body_bounded`, `prefix_bound`, `total_meets_budget`, `initial_within` | Every run and every prefix of `main`'s body charges at most `budget M` under a host whose replies give an argument block of at most `argsLimit` bytes and sizes of at most `M` bytes from `fd_filestat_get`, `total_meets` holds with these two premises in place of the bound on the heap, and the budget fits the module's cap for every `M` of at most 23,000,000 ([the budget](Budget.lean)). |

The command holds the block of `args`, the read buffer of 65,536 bytes, the manifest's buffer of
the size that `fd_filestat_get` reports, the positions that `parse` gives, and for each line the
name's copy, the output line of `render`, and the eight words that `finish` packs.  The reads of a
file and of the manifest fill windows of the buffers that their loops keep in their states and move, so no read
copies a byte beyond what the host writes into the window, and the memory does not depend on the
sizes of the files checked.  The resource model credits no release, so its charge sums the blocks
of every line.

[The budget](Budget.lean) states that charge as a function of the manifest's size.  `body_bounded`
bounds every run and every prefix of `main`'s body by `budget M` under every host whose successful
`args_sizes_get` replies report at most `argsLimit` bytes, 6 MiB, the most that Linux lets the
strings and pointers of `argv` and `envp` take, and whose successful `fd_filestat_get` replies
report a size of at most `M` bytes.  `budget M` sums the block of `args` and the copy of the
manifest's name, at most `argsLimit` bytes each, the read buffer of 65,536 bytes, the manifest's
buffer of at most `M` bytes, the charge of `parse`, at most `176 M + 464` bytes, and the charge of
`checkLines`, at most `4 (M + 1)` bytes.  The call of `fd_filestat_get` charges nothing, since a
record call places its record in the call area of low memory.  The charge of `checkLines` follows
the lines: a pass charges at most four bytes for each byte of its line and the newline after it
(`loop_bounded_sum`), and the lines with their newlines hold at most one byte more than the
manifest (`lines_total`).  A pass of the reads of a file, of the reads of the manifest, and of
`writeAll` charges nothing.  `budget_le` states `budget M ≤ 181 M + 12,649,115`, and
`initial_within` states that the budget fits the 65,535 pages of the module's cap for every `M` of
at most 23,000,000.

## Confinement

The specification admits every name, absolute names and names with `..` among them, because both
hosts resolve each open of a name under the preopened directory beneath that directory.  [The Linux
shim's specification](../../Verified/Shim/Replies.lean) makes every `path_open` an `openat2` call
whose `open_how` record, `openHowBytes`, holds the resolution flags `RESOLVE_BENEATH` and
`RESOLVE_NO_MAGICLINKS` (10), and the AArch64 stub of `path_open` in
[`LeanExe/A64/WasiFiles.lean`](../../LeanExe/A64/WasiFiles.lean) writes that record (`openHow`) and
calls `openat2` up to four times, again after each `EAGAIN` of the first three (`openCalls`), which
`run_openHow` of [the record's proof](../../Verified/ShimA64/OpenHow.lean) and `run_openLoop` and
`openStub_sim` of [the stub's proof](../../Verified/ShimA64/Open.lean) prove.  The shim never falls
back to `openat`: `ENOSYS` gives errno 29 (`io`), and `errnoOf` gives `EXDEV`, Linux's refusal of a
resolution that leaves the directory, as 63 (`perm`).  With `RESOLVE_BENEATH`, openat2(2) refuses an
absolute name, a `..` that leaves the directory, and a symbolic link, absolute or relative, whose
target lies outside it, and `RESOLVE_NO_MAGICLINKS` refuses the links of `/proc`.  The repository's
Wasmtime host preopens the directory with `wasi_config_preopen_dir` of
[`tools/wasmtime-host.c`](../../tools/wasmtime-host.c), and Wasmtime resolves names with cap-std,
which confines them as well.  `Confined` therefore states the names that the command asks the host
to open, relative to descriptor 3, and relies on the host's resolution for the rest, which no
theorem of the repository states for Linux's kernel.  In the driver's runs a manifest named with a
`..` that leaves the directory gives status 63 (`perm`), and a line that names a file through such a
`..`, by an absolute name, or through a link out of the directory gives FAILED, where `sha256sum -c`
reads the file.  The driver's traces of the native executable show Linux refusing the `openat2` of
each of these names with `EXDEV`.

## The native executable checks the manifest

`genWasiElf` writes the command's AArch64 Linux executable of 74,248 bytes from the module, with
the shim's stubs for the stream functions, `args_sizes_get`, `args_get`, `path_open`, `fd_close`,
`fd_read` on a handle, and `fd_filestat_get`, and a linear memory of 4,096 pages.  The module
imports `path_open`, so the executable first checks descriptor 3 with `openat` of `.` and closes
the result, and a directory there becomes the preopened directory.  `tests/linux/a64-wasi.sh`
writes the executable as `manifest.elf` and elaborates the theorems of the file beside it, and the
demo's driver writes it from the same module with the same commands as
`build/manifest-check/command.elf` and runs it.  The theorems of the next table lie in [the
executable's theorems](../../tests/TestSupport/A64/ImageFilesManifestCheck.lean), [the
footprints](Native.lean), and [the corollary under the shim](NativeMeets.lean), and [the
specification over Linux events](NativeSpec.lean) states `InRange` and `NMeets`.

| Theorem | Statement |
|---|---|
| `manifest_elf_file`, `manifest_elf_segments`, `manifest_elf_layout`, `manifest_elf_entry`, `manifest_elf_room` | The file's bytes are those that `genWasiElf` gives for the command's module, its program headers are those of the generator's layout, its entry is the shim's prefix, and the stack's room holds the module's stack bound. |
| `manifest_elf` | For every reply sequence, a process that Linux's loader started from the file reaches `exit_group`.  When the check of descriptor 3 ends the run, X0 is 67.  Otherwise the trace holds the check's events and then the layer events of a run of `main` and its exit under the shim's host with the process's arguments, which name only standard streams and the descriptors that the shim holds open: an accepted exit, whose status X0 holds, a rejected exit, a trap of the shim, or a guest trap after a prefix. |
| `linux_footprint_bounded`, `budget_fits` | Under the shim's host, with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes and replies that meet `StatBounded M`, at a cap of at most 65,535 pages that holds `budget M` above the static heap's top, every run of `_start` with enough fuel ends without a guest trap.  The budget for a manifest of `manifestLimit` bytes, 1 MiB, fits the executable's 4,096 pages. |
| `linux_exec_meets` | Under the shim's host, from a world without layer events, with arguments without a zero byte whose strings and eight-byte pointers take at most `argsLimit` bytes, a run of `main` and its exit whose layer events meet `InRange` and `Sized` ends at the accepted exit, and its status and layer events meet `NMeets` for the launch's grant of descriptor 3. |
| `manifest_elf_meets` | For every reply sequence that meets `StatBounded manifestLimit`, a process started from the file with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes reaches `exit_group` with layer events that hold the replies, and when the check of descriptor 3 does not end the run and the layer events meet `InRange`, X0 and the events meet `NMeets` for the check's grant. |
| `manifest_elf_witness` | The premises of `manifest_elf_meets` and `InRange` hold together: for the replies `witnessReplies`, the arguments `h` and `1`, and a process that holds the file and the initial stack, the check grants descriptor 3, and the process reaches `exit_group` after layer events that meet `InRange` and, with X0, `NMeets`. |

`NMeets held args ls code` restates `Meets` over the layer events `ls`, which record each Linux
call's arguments, the bytes of its input regions, the bytes of its output region, and its result,
for a shim that holds descriptor 3 exactly when `held`.  `NRun` states the verdicts and the status
as `Run` does: the opening of the manifest, its `statx`, its reads, and its `close`
(`NManifestRun`), and for each line of an accepted manifest the opening of its name, the reads of
the file, its `close`, and the writes of its output line to descriptor 1 (`NChecks`).  An opening
(`Opening`) makes no call when the shim's checks refuse the name and gives their errno
(`nameCheck`): 25 for a name that is not UTF-8, 8 when the shim does not hold descriptor 3, 28 for a
name with a zero byte, and 37 for a name of 4,096 bytes or more.  Otherwise it makes at most four
`openat2` calls, each but the last of which returned `EAGAIN`, and the last returned `EAGAIN` only
as the fourth.  A read before the last of a file or of the manifest returned a count of one byte or
more.  A line's verdict is OK exactly when its opening returned a descriptor, a `read` returned 0
before any `read` returned an error number, the `close` returned 0, and the line's digits give the
digest of the bytes that the reads returned.  Each other errno is the shim's `errnoOf` of a negated
error number, and a `statx` that reports an access, modification, or birth time of `2^64`
nanoseconds or more, as each such time before 1970 does, or a size of `2^32` bytes or more gives
status 61.  `NConfined` states that every `openat2` is relative to descriptor 3 with the flags
`O_RDONLY | O_CLOEXEC` and the resolution `RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS`, and names the
argument or the name of a line of an accepted manifest.  `NHandled` states that the events are
`openat2` calls that returned an error number, brackets of an `openat2` that returned a descriptor,
`read` and `statx` calls of that descriptor, and its `close`, and writes to descriptor 1.

`InRange ls` states the results that Linux gives for the command's calls and that the shim
accepts.  A `read` or a `write` returns an error number or at most its count (read(2), write(2)), a
`close` 0 or an error number, and a `statx` an error number or 0 (statx(2)).  `InRange` also
requires nanoseconds below `10^9` in each time that a `statx` reports, for which the shim traps
otherwise.  An `openat2` returns an error number or the lowest descriptor that the process does not
hold (open(2)).  The startup check received a descriptor of 4 or more, so the process held 0 to 3,
and the command closes only descriptors that its `openat2` calls returned, so each such descriptor
is 4 or more.  It lies below 1,024, the shim's limit, while the process holds fewer than 1,024
descriptors, as the usual soft limit of `RLIMIT_NOFILE` ensures, and the shim traps for a
descriptor of 1,024 or more.  Since no `openat2` returns 3 and no `close` names it, the shim holds
descriptor 3 throughout the run exactly when the check granted it.  `Sized`, that each `read`'s
output holds as many bytes as the `read` asked for, follows from `Carried`.

`StatBounded M R` states the premise of `body_bounded` on `fd_filestat_get` over the replies: every
reply of `R` that the shim's `filestatReply` reads as a `statx` record with errno 0 reports a size
of at most `M` bytes.  `linuxHost` answers a `fd_filestat_get` at any world from the reply whose
index is the number of the world's layer events, and `body_bounded` covers every world, so the
premise covers every reply of `R`, those to the command's other calls among them.  The corollary
therefore covers manifests of at most 1 MiB, `manifestLimit`, and holds for reply sequences whose
every reply meets the bound, a stronger premise than a bound on the size that the manifest's `statx`
reports, and real runs can fail it.  A `read` that returns 0 leaves its window's bytes in place, and
the reply that `Carried` records for it holds those bytes.  A file whose last 65,536 bytes hold a
size above 1 MiB where a `statx` record holds `stx_size`, and, where it holds the times, seconds
that keep each time that the shim reads below `2^64` nanoseconds and nanoseconds below `10^9`, gives
such a reply at its last `read`, and the corollary states nothing of that run, whose verdict is
correct.  A premise on the `statx` events of the run alone needs a budget that follows the run's
worlds.

The proof composes the footprint with the command's theorems.  `linux_footprint_bounded` gives the
budget premise of the generated `command.start` from `body_bounded` through `call_prefix_bound`,
since the shim answers `args_sizes_get` with the count and size of the launch's arguments
(`linux_sizes`, `reportedSize_le`) and `fd_filestat_get` with the size of a reply that meets
`StatBounded M` (`linux_stat_bound`).  `linux_exec_meets` excludes the trapped runs.  Under a host
that rejects only exit statuses of 126 or more, as the shim does, a trapped run of `main` and its
exit has a trapped call among its events (`exec_trapped_call`, from `TrapsInCall` of each part of
`main`), and no call of the command whose image meets `InRange` traps (`image_untrapped`).  For
the accepted exit, `exec_main` gives `Meets`, and `run_native` and `handled_native` translate `Run`
and `Handled` through the image of each WASI event: `path_open` gives the `openat2` calls of
`Opening` (`open_native`), `fd_filestat_get` one `statx` (`stat_native`), `fd_read` on a handle one
`read` (`read_native`), `fd_close` one `close` (`close_native`), and a write to standard output one
`write` of descriptor 1 (`write_native`).  A descriptor that an `openat2` returned stays among the
numbers that the shim holds until its `close` (`Opening.held`, `held_quiet`), so the calls on it
reach Linux, and `confined_accepted` gives the names of `NConfined` from `Confined`.

`manifest_elf_witness` gives the premises: a memory that holds the file's two segments below
`2^32` and the initial stack of `h` and `1` at `2^32` (`loadedMem` of [the shared
witness](../../tests/TestSupport/A64/ElfWitness.lean)), and the replies `witnessReplies`, which
answer the check's `openat` with descriptor 4, its `close` with 0, and every later call with
`-ENOENT`.  Every layer event after the check returns an error number, so `InRange` holds, and of
the replies that the shim reads as `statx` records, only the `close`'s gives errno 0, and its zero
bytes report a size of 0, so `StatBounded manifestLimit` holds.  The kernel evaluates no run of
the executable: the footprint theorem gives the process's run, and the proof reasons over its
events.

## Building, running, and testing

```sh
tests/manifest-check/run.sh
build/tools/leanexe-wasmtime-host --dir build/manifest-check/dir --arg check --arg good.sha256 \
  run build/manifest-check/command.wasm
build/manifest-check/command.elf good.sha256 3< build/manifest-check/dir
qemu-aarch64 build/manifest-check/command.elf good.sha256 3< build/manifest-check/dir
tests/linux/a64-wasi.sh
tests/verified/run.sh --cases manifestCheck
tests/native/verified.sh --module manifestCheck
tests/baremetal/verified.sh --module manifestCheck
```

[The demo's driver](../../tests/manifest-check/run.sh) checks the hashes of the reviewed
specification and samples, builds the demo's modules, elaborates [the theorem
statements](../../tests/manifest-check/Axioms.lean), which requires that each theorem use only the
three axioms, emits and validates the command's module, and writes its executable with `a64-wasi
wasm`, which fails when `genWasiElf` rejects the module.  It then runs the command in the Wasmtime
host over a preopened test directory, on the host's processor, which must be AArch64 Linux, with the
directory open as descriptor 3, and under `qemu-aarch64`, QEMU's user-mode emulator, or `QEMU_USER`
when set, which must be QEMU 9.2 or later, the first release that implements `openat2`.  `RUNNERS`
selects among the three.  Each run's output lines must be the verdicts of GNU `sha256sum -c` on the
same manifest, which reads every name that the manifest lists, with FAILED for each name that leaves
the directory.  In each runner the runs cover matching files, a changed file, a missing file, an
empty file, a file of 5 MiB and 17 bytes that takes 82 reads, a name with spaces, a binary-mode
line, links inside and outside the directory, names with `..` inside and outside it, an absolute
name, a malformed and an empty manifest, no argument and two arguments, a missing manifest and one
outside the directory, and a standard output on `/dev/full`.  No run writes to stderr.

Natively, the driver runs the manifests of matching files and of mixed verdicts under strace.  The
traces hold only `openat`, `openat2`, `read`, `statx`, `close`, `write`, and `exit_group`.  The one
`openat` opens `.` beneath descriptor 3 with `O_DIRECTORY`, the startup's check, and every
`openat2` opens a name beneath descriptor 3 with `O_RDONLY | O_CLOEXEC` and the resolution
`RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS`.  Every `statx` passes the empty path with
`AT_EMPTY_PATH` and the mask `STATX_ALL`, every `write` names descriptor 1, and every `read`,
`statx`, and `close` names the descriptor that the last open returned, which a `close` ends before
the next open and before the exit.  The `openat2` of `../outside/secret.txt`, of the absolute name,
and of the link out of the directory fails in the kernel with `EXDEV`.

Five more native runs on the manifest of matching files replace results with strace's injection.
When the first read of `a.txt` fails with `EIO`, `a.txt` gives FAILED, the other lines OK, and the
status is 1.  When the first three `openat2` calls return `EAGAIN`, the fourth opens the manifest
and the run writes the verdicts of a run without injection.  When the first four return `EAGAIN`,
the run stops after them with status 29 (`io`), the shim's errno for `EAGAIN`.  When the manifest's
`close` fails with `EIO`, the run writes nothing and exits with status 29.  When every `write`
returns 0, the run makes 11 writes of the 10 bytes of `a.txt`'s line and exits with status 77.  With
`QEMU_USER=~/qemu-9.2/bin/qemu-aarch64`, QEMU 9.2.4 built from source, the driver prints
`manifest check axiom check passed for 23 theorems`, the module's size, 17,882 bytes, the
executable's size, 74,248 bytes, and its SHA-256,
204e28743ab1d9e40136218d1da96786b265fffd8c76bdb22315c10fe02d5c12, and
`manifest check: 34 runs passed, 39 verdicts agree with sha256sum -c`.

The second command runs the module on the manifest `good.sha256` of the driver's test directory,
after the driver has written both, and the third and fourth run the executable on it natively and
under QEMU, with the directory open as descriptor 3.  Each writes `a.txt: OK`, `empty: OK`, `name
with spaces: OK`, `big.bin: OK`, `sub/../a.txt: OK`, and `inside-link: OK`, one to a line, and exits
with status 0.  The manifest's last line has no final newline, and its `big.bin` line is in binary
mode.  `tests/linux/a64-wasi.sh` writes the executable from the module that `tools/Emit.lean` emits
and elaborates [the executable's theorems](../../tests/TestSupport/A64/ImageFilesManifestCheck.lean)
beside it, which requires the three axioms of each.

[The verified driver](../../tests/verified/run.sh) runs the 99 samples of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime against the specifications, and each case
requires the blocks that stay allocated after the call: the manifest's and the result's for
`parse`, the manifest's for `hexMatches`, and the name's and the result's for `render`.  It checks
[the file theorems](File.lean), which state that `build/verified/manifestCheck.wasm`, which it
writes, holds the module.  The native driver runs the same cases on the module's translation to C,
compiled with CompCert, and the bare-metal driver on that translation under QEMU without an
operating system.

## Related examples

[The random-residue histogram](../RandomHistogram/README.md) is a run of the same method on a
parser of the command line, and [the unbiased random choice](../RandomChoice/README.md) keeps its
buffers in its loop's state in the same way.  [The SHA-256
guide](../../Library/Hashing/Sha256/README.md) states the library's theorems, and [the files
command](../../Verified/Examples/WasiFiles.lean) opens, reads, and writes files under the
preopened directory with `withOpen`.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [WASI Preview 1 declarations](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx)
- [openat2(2)](https://man7.org/linux/man-pages/man2/openat2.2.html)
- [sha256sum, GNU coreutils](https://www.gnu.org/software/coreutils/manual/html_node/sha2-utilities.html)
- [FIPS 180-4](https://csrc.nist.gov/pubs/fips/180-4/final)
