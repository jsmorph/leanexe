# Manifest checker

## Request, specification, review, and program

[The request](request.txt) asks for a SHA-256 manifest checker like `sha256sum -c`.  The approved
plan fixes its behavior: `check MANIFEST` opens and reads MANIFEST under the preopened directory,
and for each line in `sha256sum`'s format, `HEX  NAME`, it opens NAME read-only under the same
directory, reads it to its end through a streaming SHA-256, closes it, and writes `NAME: OK` or
`NAME: FAILED`.  The status is 0 when every file matches, 1 when one fails, and the errno when a
call on the manifest fails.  This directory holds the pure core of the checker, the functions that
parse the manifest, compare a line's digits with a digest, and render an output line, with their
reviewed specifications and call theorems.  The WASI command around them is not part of it.

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

[The streaming SHA-256](../../Library/Hashing/Sha256/README.md#implementation) of the library hashes a
message that arrives in pieces: `update` compresses the whole blocks of a byte string into the hash
value, and `finish` pads the bytes after the last whole block with the length of the whole message.

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

## Confinement

The specification admits every name, absolute names and names with `..` among them, because both
hosts resolve each open of a name under the preopened directory beneath that directory.  [The Linux shim's
specification](../../Verified/Shim/Replies.lean) makes every `path_open` an `openat2` call whose
`open_how` record, `openHowBytes`, holds the resolution flags `RESOLVE_BENEATH` and
`RESOLVE_NO_MAGICLINKS` (10), and the AArch64 stub of `path_open` in
[`LeanExe/A64/WasiFiles.lean`](../../LeanExe/A64/WasiFiles.lean) writes that record (`openHow`) and
calls `openat2` up to four times after `EAGAIN` (`openCalls`), which `run_openHow` of
[the stub's proof](../../Verified/ShimA64/OpenHow.lean) proves.  The shim never falls back to
`openat`: `ENOSYS` gives errno 29 (`io`), and `errnoOf` gives `EXDEV`, Linux's refusal of a
resolution that leaves the directory, as 63 (`perm`).  With `RESOLVE_BENEATH`, openat2(2) refuses an
absolute name, a `..` that leaves the directory, and a symbolic link, absolute or relative, whose
target lies outside it, and `RESOLVE_NO_MAGICLINKS` refuses the links of `/proc`.  The repository's
Wasmtime host preopens the directory with `wasi_config_preopen_dir` of
[`tools/wasmtime-host.c`](../../tools/wasmtime-host.c), and Wasmtime resolves names with cap-std,
which confines them as well.  A confinement theorem of a command can therefore state the names
that the command asks the host to open, relative to descriptor 3, and rely on the host's resolution
for the rest, which no theorem of the repository states for Linux's kernel.

## Building and testing

```sh
sha256sum -c Demos/ManifestCheck/spec.sha256
tools/leanrun --timeout 60m lake build Demos.ManifestCheck.Compiled
tests/verified/run.sh --cases manifestCheck
tools/leanrun --timeout 10m lake env lean Demos/ManifestCheck/File.lean
tests/native/verified.sh --module manifestCheck
tests/baremetal/verified.sh --module manifestCheck
```

The first command checks that the specification and the samples are the reviewed ones.
[The verified driver](../../tests/verified/run.sh) runs the 99 samples of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime against the specifications, and each case
requires the blocks that stay allocated after the call: the manifest's and the result's for
`parse`, the manifest's for `hexMatches`, and the name's and the result's for `render`.  [The file
theorems](File.lean) state that `build/verified/manifestCheck.wasm`, which the driver writes, holds
the module.  The native driver runs the same cases on the module's translation to C, compiled with
CompCert, and the bare-metal driver on that translation under QEMU without an operating system.

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
