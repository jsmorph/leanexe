# Manifest checker

## Request, specification, review, and program

[The request](request.txt) asks for a SHA-256 manifest checker like `sha256sum -c`.  The approved
plan fixes its behavior: `check MANIFEST` opens and reads MANIFEST under the preopened directory,
and for each line in `sha256sum`'s format, `HEX  NAME`, it opens NAME read-only under the same
directory, reads it to its end through a streaming SHA-256, closes it, and writes `NAME: OK` or
`NAME: FAILED`.  The status is 0 when every file matches, 1 when one fails, and the errno when a
call on the manifest fails.  This directory holds the pure core of the checker, the functions that
parse the manifest, compare a line's digits with a digest, and render an output line, with their
reviewed specifications and call theorems, and the WASI command around them, with theorems about
its verdicts, the files that it opens, and its descriptors.

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

## The core computes its specification

| Theorem | Statement |
|---|---|
| `parse_eq`, `hexMatches_eq`, `render_eq` | Each program equals its specification, for a manifest of fewer than `2^62` bytes, a manifest of fewer than `2^64` bytes, and a name of fewer than `2^64 - 9` bytes ([the proof](Proof.lean)). |
| `parse_callSpec`, `hexMatches_callSpec`, `render_callSpec` | `Verified.CallSpec compiled.module compiled.tables K spec compiled.f.bound` for `K` = 6, 8, and 10: called with borrowed arguments from a ready store with room for the bound, the function returns the specification's value without a trap and leaves a ready store ([the compilation](Compiled.lean)). |
| `parse_bound`, `hexMatches_bound`, `render_bound` | The generated bounds are at most `176 n + 464` bytes for a manifest of `n` bytes, 0, and at most `n + 64` bytes for a name of `n` bytes. |
| `update_toVec32`, `finish_spec`, `stream_spec` | The streaming SHA-256 computes the digest of the transcription of FIPS 180-4 for the whole message ([the library's proof](../../Library/Hashing/Sha256/StreamProof.lean)). |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.  `parse_eq`
follows the lines: the step of `parse` keeps its state at a byte other than a newline, and at the
byte that closes a line it adds the line's positions and its test, so `parse_from` proves by strong
induction on the positions that remain that the loop adds the positions of the lines that
`linesFrom` gives for the pieces of the rest.  `parseStep_enc` relates the array of the program's
state to a state of three parts, on which the induction runs.

## The command checks every line

[The command](Command.lean) is `main : Action UInt64`.  It reads its one argument with `args` and
`argScan`, builds a read buffer of 65,536 bytes, and opens the manifest of that name under the
preopened directory with `withOpen`, with the rights `fd_read` and `fd_filestat_get`.
`readManifest` asks the manifest's size with `fdFilestatGet` and answers a size of `2^32` bytes or
more, for which a read's length does not fit its 32 bits, with status 61 (`overflow`).  `readBytes`
builds a buffer of the reported size and reads the manifest into it with `fdRead`, each read into
the window after the bytes already read, until the buffer is full, a read returns no bytes, or a
read returns an errno.  A last read into the read buffer tests that the manifest has no byte after
them, so a manifest whose bytes number fewer or more than its size gives status 1, as do a FIFO,
a file of `/proc` that reports size 0, and a file being appended to.  The bracket
closes the manifest, and `parse` gives the positions of its lines, or none for a manifest that the
pure core refuses, which gives status 1.

`checkLines` checks the lines in order, with the read buffer in its loop's state.  For each line it
copies the name from the manifest with `slice`, opens it under the preopened directory with the
right `fd_read` alone, hashes the file with `hashFile`, closes it, compares the digest with the
line's digits with `hexMatches`, and writes `render` of the name and the verdict with
`writeAll line 0 line.size` of [the shared write loop](../../LeanExe/Wasi/WriteAll.lean), which
writes the window of the line that remains after a short write.  Every open names descriptor 3, the flag
`symlink_follow`, no open flags, no inherited rights, and no descriptor flags.  `hashFile` reads
the file into the window of the read buffer after the bytes that it holds, and when a read fills
the buffer it compresses the buffer's 1,024 blocks into the hash value with `update` and starts
again at the buffer's first byte.  When a read returns no bytes, it compresses the whole blocks
that the buffer holds and passes the bytes after them to `finish` with the file's length.  Its loop
makes at most `2^45 - 1` reads of at most 65,536 bytes each, so the bytes that it hashes number
fewer than `2^61`, the limit of SHA-256's length field.  The read buffer moves from pass to pass
and into each bracket and out of it, and the windows of the reads are its bytes, so no pass of a
read loop builds a buffer.

A line's verdict is OK when the open of its name returned errno 0, a read returned no bytes before
any read returned an errno, the close returned errno 0, and the line's digits give the digest of
the bytes that the reads returned.  A file that fails to open, a read that returns an errno before
the file's end, a failed close, and reads that stop after `2^45 - 1` reads give FAILED, and the
checks continue.  The status is the errno of `args`, 1 for an argument buffer without exactly one
argument after the program name, the errno of the manifest's open, of `fdFilestatGet`, of one of
its reads, or of its close, 61 for a reported size of `2^32` bytes or more, and 1 for a manifest
whose bytes disagree with its size or that the pure core refuses.  After a manifest that the core
accepts, the status is 0 when every line says OK and 1 when one says FAILED, 77 when the writes of
an output line stop with bytes left, which ends the checks, and the errno of a write that fails,
with which `writeAll` exits.  Every errno lies from 0 to 76, so 77 differs from every errno.
`verified_compile_wasi` writes a module of 17,962 bytes that imports `fd_read` twice, as the stream
read of the ABI and as the flat call, `fd_write`, `proc_exit`, `fd_filestat_get`, `path_open`,
`fd_close`, `args_sizes_get`, and `args_get`.

## The command meets the request

| Theorem | Statement |
|---|---|
| `exec_main` | Under every host, every run of `main` followed by its exit that ends with the status `code` has the events `events ++ [.exit code]`, where `events` meet `Meets`, and `code` is at most 77 ([the command's proof](CommandProof.lean)). |
| `start_ends` | For every host, every host environment that satisfies `hostSpecWith host command.sysCalls`, and every world, every run of `_start` from the command's initial store with enough fuel ends as `Ends` states: the accepted exit after events that meet `Meets`, a trap of the host or a rejected exit after a run of `main` whose events meet `SoFar`, or a guest trap at `unreachable` after a prefix of `main` whose events meet `SoFar` ([the compiled command](CommandStart.lean)). |
| `stops_soFar`, `trapped_soFar`, `prefix_soFar` | Under every host, the events of every run of `main` followed by its exit that stops before the exit, a run that traps or a prefix of a run, meet `SoFar` ([the runs that stop](CommandPrefix.lean)). |
| `total_meets` | Under the premises of the generated `command.total` as well, a budget that fits the initial store's free memory and bounds the heap of every prefix of `main`, and a host that traps nowhere along `main` and its exit, every such run ends with the accepted exit after events that meet `Meets`. |
| `body_bounded`, `prefix_bound`, `total_meets_budget`, `initial_within` | Every run and every prefix of `main`'s body charges at most `budget M` under a host whose replies give an argument block of at most `argsLimit` bytes and sizes of at most `M` bytes from `fd_filestat_get`, `total_meets` holds with these two premises in place of the bound on the heap, and the budget fits the module's cap for every `M` of at most 23,000,000 ([the budget](Budget.lean)).  The theorems state `Meets` of the runs that end with the accepted exit and `SoFar` of the runs that trap. |

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
argument or the name of a line of the manifest.  `Handled` states that the events are calls of
`args_sizes_get` and `args_get`, opens that fail, brackets of an open, calls on its descriptor, and
its close, and writes to standard output, so each descriptor is closed before the next open and
before the exit.  [The review](review.md) records the decisions of the cases that the request
leaves open.

`SoFar` states confinement and the use of descriptors of the events of a run that stops before its
exit: at a trap of the host, at an exit that the host rejects, or at a trap of the guest.
`ConfinedSoFar` states `Confined` of the events for the buffer that `args` returned and the bytes
that the reads of the manifest returned, the bytes of a `ManifestRun` with status 0 after the
events of `args`, or no bytes when the events hold no such run.  An open of a line's name therefore
follows the whole reading of the manifest.  `HandledSoFar` states that the events are those of
`Handled` followed by those of `Unfinished`: none, an open that returned errno 0 followed by calls
on its descriptor and no close, an open that trapped, or an exit that the host rejected.

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
`table_rep` and `table_scratch` give the generated theorems the table's representation.

`stops_soFar` follows `main` again, with the lemmas of [the runs that
stop](../../Verified/Wasi/Stops.lean): a run of `Action.bind first next` that stops is a run of
`first` that stops, or a run of `first` that returns followed by a run of `next` that stops
(`Stops.bind`).  The parts that return have the events that the lemmas above give, and a part that
stops has only the events that `Every` allows of it: the calls of `args`, the calls on the
descriptor of a bracket's body (`readManifest_every`, `hashFile_every`), and the writes of
`writeAll` with at most one rejected exit at their end (`writeAll_stops`).  `withOpen_stops` gives
the events of a bracket that stops, `checks_stops` those of the loop of `checkLines`, and
`confined_of` assembles `ConfinedSoFar` from the run of `args`, the `ManifestRun`, and the opens
of the lines that follow it.

## Memory

The command holds the block of `args`, the read buffer of 65,536 bytes, the manifest's buffer of
the size that `fd_filestat_get` reports, the positions that `parse` gives, and for each line the
name's copy, the output line of `render`, and the eight words that `finish` packs.  The reads of a
file and of the manifest fill windows of the buffers that their loops carry by moves, so no read
copies a byte beyond what the host writes into the window, and the memory does not depend on the
sizes of the files checked.  The resource model credits no release, so its charge sums the blocks
of every line.

[The budget](Budget.lean) states that charge as a function of the manifest's size.  `body_bounded`
bounds every run and every prefix of `main`'s body by `budget M` under every host whose successful
`args_sizes_get` replies report at most `argsLimit` bytes, 6 MiB, the most that Linux lets the
strings and pointers of `argv` and `envp` take, and whose successful `fd_filestat_get` replies
report a size of at most `M` bytes.  `budget M` sums the block of `args` and the copy of the
manifest's name, at most `argsLimit` bytes each, the read buffer of 65,536 bytes, the record block
of `fd_filestat_get`, the manifest's buffer of at most `M` bytes, the charge of `parse`, at most
`176 M + 464` bytes, and the charge of `checkLines`, at most `4 (M + 1)` bytes.  The charge of
`checkLines` follows the lines: a pass charges at most four bytes for each byte of its line and the
newline after it (`loop_bounded_sum`), and the lines with their newlines hold at most one byte more
than the manifest (`lines_total`).  A pass of the reads of a file, of the reads of the manifest,
and of `writeAll` charges nothing, and `budget_le` states `budget M ≤ 181 M + 12,649,235`, and `initial_within` states
that the budget fits the 65,535 pages of the module's cap for every `M` of at most 23,000,000.

## Confinement

The specification admits every name, absolute names and names with `..` among them, because both
hosts resolve each open of a name under the preopened directory beneath that directory.  [The Linux
shim's specification](../../Verified/Shim/Replies.lean) makes every `path_open` an `openat2` call
whose `open_how` record, `openHowBytes`, holds the resolution flags `RESOLVE_BENEATH` and
`RESOLVE_NO_MAGICLINKS` (10), and the AArch64 stub of `path_open` in
[`LeanExe/A64/WasiFiles.lean`](../../LeanExe/A64/WasiFiles.lean) writes that record (`openHow`) and
calls `openat2` up to four times after `EAGAIN` (`openCalls`), which `run_openHow` of [the stub's
proof](../../Verified/ShimA64/OpenHow.lean) proves.  The shim never falls back to `openat`: `ENOSYS`
gives errno 29 (`io`), and `errnoOf` gives `EXDEV`, Linux's refusal of a resolution that leaves the
directory, as 63 (`perm`).  With `RESOLVE_BENEATH`, openat2(2) refuses an absolute name, a `..` that
leaves the directory, and a symbolic link, absolute or relative, whose target lies outside it, and
`RESOLVE_NO_MAGICLINKS` refuses the links of `/proc`.  The repository's Wasmtime host preopens the
directory with `wasi_config_preopen_dir` of [`tools/wasmtime-host.c`](../../tools/wasmtime-host.c),
and Wasmtime resolves names with cap-std, which confines them as well.  `Confined` therefore
states the names that the command asks the host to open, relative to descriptor 3, and relies on the
host's resolution for the rest, which no theorem of the repository states for Linux's kernel.  The
driver's runs show Wasmtime 44 refusing a name with `..` that leaves the directory, an absolute
name, and a link out of the directory with errno 63 (`perm`), which `sha256sum -c` reads.

## Building and testing

```sh
sha256sum -c Demos/ManifestCheck/spec.sha256
tools/leanrun --timeout 60m lake build Demos.ManifestCheck.Compiled
tests/verified/run.sh --cases manifestCheck
tools/leanrun --timeout 10m lake env lean Demos/ManifestCheck/File.lean
tests/native/verified.sh --module manifestCheck
tests/baremetal/verified.sh --module manifestCheck
tools/leanrun --timeout 60m lake build Demos.ManifestCheck.CommandStart
tests/manifest-check/run.sh
```

The first command checks that the specification and the samples are the reviewed ones.
[The verified driver](../../tests/verified/run.sh) runs the 99 samples of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime against the specifications, and each case
requires the blocks that stay allocated after the call: the manifest's and the result's for
`parse`, the manifest's for `hexMatches`, and the name's and the result's for `render`.  [The file
theorems](File.lean) state that `build/verified/manifestCheck.wasm`, which the driver writes, holds
the module.  The native driver runs the same cases on the module's translation to C, compiled with
CompCert, and the bare-metal driver on that translation under QEMU without an operating system.

[The command's driver](../../tests/manifest-check/run.sh) elaborates [the theorem
statements](../../tests/manifest-check/Axioms.lean) and checks their axioms, emits and validates
the module, and runs it in the Wasmtime host over a preopened test directory.  It compares each
output line with the verdict of GNU `sha256sum -c` on the same manifest, which reads every name
that the manifest lists, and requires FAILED for each name that leaves the directory.  The runs
cover matching files, a changed file, a missing file, an empty file, a file of 5 MiB and 17 bytes
read in 81 chunks, a name with spaces, a binary-mode line, links inside and outside the directory,
names with `..` inside and outside it, an absolute name, a malformed and an empty manifest, no
argument and two arguments, a missing manifest and one outside the directory, and a standard
output on `/dev/full`.

## Related examples

[The random-residue histogram](../RandomHistogram/README.md) is a run of the same method on a
parser of the command line, and [the SHA-256 guide](../../Library/Hashing/Sha256/README.md) states
the library's theorems.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [WASI Preview 1 declarations](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx)
- [openat2(2)](https://man7.org/linux/man-pages/man2/openat2.2.html)
- [sha256sum, GNU coreutils](https://www.gnu.org/software/coreutils/manual/html_node/sha2-utilities.html)
- [FIPS 180-4](https://csrc.nist.gov/pubs/fips/180-4/final)
