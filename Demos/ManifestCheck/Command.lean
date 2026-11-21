import Demos.ManifestCheck.Program
import Library.Hashing.Sha256.Stream
import Library.Hashing.Words.Encoding
import Verified.Wasi
import LeanExe.Wasi.WriteAll

/-! The WASI command of the manifest checker.  `main` reads its one argument with `args` and
`argScan`, builds the read buffer of 65,536 bytes, and opens the manifest of that name under the
preopened directory with `withOpen`.  `readManifest` asks the size of the open manifest with
`fdFilestatGet`, and `readBytes` builds a buffer of that size when it is below `2^32` bytes and
reads the manifest into it with `fdRead`, each read into the window after the bytes already read,
until the buffer is full, a read returns no bytes, or a read returns an errno.  A last read into
the read buffer tests that the manifest has no byte after them.  The bracket then closes the
manifest, and `main` parses it with `parse`.

`checkLines` checks the lines in order, with the read buffer in its loop's state.  For each line it
opens the line's name under the preopened directory, hashes the file with `hashFile`, closes it,
compares the digest with the line's digits with `hexMatches`, and writes `render` of the name and
the verdict with `writeAll` over the whole line, which writes the window that remains after a short
write and exits with the errno of a write that fails.  `hashFile` reads the file with `fdRead` into
the window of the read buffer after the bytes that it holds, and when a read fills the buffer it
compresses the buffer's 1,024 blocks into the hash value with `update` and starts again at its first
byte.  When a read returns no bytes, it compresses the whole blocks that the buffer holds and passes
the bytes after them to `finish` with the length of the file.  Its loop makes at most `fileReads`,
`2^45 - 1`, reads of at most 65,536 bytes, so the bytes that it hashes number fewer than `2^61`, the
limit of SHA-256's length field.  The read buffer moves from pass to pass, into each bracket and out
of it, and no pass of a read loop builds a buffer.

The manifest opens with the right `fd_read` and the right `fd_filestat_get`, and each file with
the right `fd_read` alone, each under descriptor 3 with the flag `symlink_follow`, no open flags,
no inherited rights, and no descriptor flags.  A line's verdict is OK when the open of its name
returned errno 0, a read returned no bytes before any read returned an errno, the close returned
errno 0, and the line's digits give the digest of the bytes read.

The status is the errno of `args`, 1 for an argument buffer without exactly one argument after the
program name, the errno of the manifest's open, of `fdFilestatGet`, of one of its reads, or of its
close, 61 (`overflow`) for a reported size of `2^32` bytes or more, for which a read's length does
not fit its 32 bits, 1 for a manifest whose bytes number fewer or more than its size, and 1 for a
manifest that `parse` refuses.  Otherwise it is 77 when the writes of an output line end with bytes
left, which ends the checks, and else 0 when every line says OK and 1 when one says FAILED. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Library.Hashing.Words Library.Hashing.Sha256

/-- The size of the read buffer, 1,024 blocks of SHA-256. -/
def chunk : UInt64 := 65536

/-- The most reads of one checked file, `2^45 - 1`, whose 65,536 bytes each make fewer than `2^61`
bytes. -/
def fileReads : UInt64 := 35184372088831

/-- The `len` bytes of `b` from position `start`. -/
def slice (b : Bytes) (start len : UInt64) : Bytes :=
  Bytes.build len fun i => b.get (start + i)

/-- The state of `argScan` after the byte `b`, from the state `st` before it: the zero bytes seen,
the position of the first, and the position of the byte `b`. -/
def argStep (st : UInt64 × UInt64 × UInt64) (b : UInt64) : UInt64 × UInt64 × UInt64 :=
  if b == 0 then (st.1 + 1, (if st.1 == 0 then st.2.2 else st.2.1), st.2.2 + 1)
  else (st.1, st.2.1, st.2.2 + 1)

/-- The number of zero bytes of the argument buffer `a`, the position of the first, and the size
of `a`. -/
def argScan (a : Bytes) : UInt64 × UInt64 × UInt64 :=
  LeanExe.loop a.size ((0 : UInt64), (0 : UInt64), (0 : UInt64)) fun i st => argStep st (a.get i)

/-- The status, the bytes, and the read buffer of the manifest `file` of `size` bytes, read into a
buffer of that size, with the read buffer `buffer` for the last read.  The status is the errno of a
read, 1 when a read returns no bytes before the buffer is full or the last read returns bytes, and
otherwise 0, with the bytes of the manifest. -/
def readBytes (file : Handle) (size : UInt64) (buffer : Bytes) :
    Action (UInt64 × Bytes × Bytes) := do
  let s ← Wasi.loop size (Bytes.build size fun _ => 0, (0 : UInt64), (0 : UInt64))
    (fun _ s => s.2.2 == 0 && s.2.1 < size) fun _ s => do
      let got ← fdRead file s.1 s.2.1 (size - s.2.1)
      if got.errno != 0 then
        pure (got.buffer, s.2.1, got.errno)
      else if got.count == 0 then
        pure (got.buffer, s.2.1, 1)
      else
        pure (got.buffer, s.2.1 + got.count, 0)
  if s.2.2 != 0 then
    pure (s.2.2, s.1, buffer)
  else
    let probe ← fdRead file buffer 0 chunk
    if probe.errno != 0 then
      pure (probe.errno, s.1, probe.buffer)
    else if probe.count != 0 then
      pure (1, s.1, probe.buffer)
    else
      pure (0, s.1, probe.buffer)

/-- The status, the bytes, and the read buffer of the manifest `file`, with the read buffer
`buffer`.  The status is the errno of `fdFilestatGet`, 61 (`overflow`) for a size of `2^32` bytes
or more, and otherwise that of `readBytes`. -/
def readManifest (file : Handle) (buffer : Bytes) : Action (UInt64 × Bytes × Bytes) := do
  let stat ← fdFilestatGet file
  if stat.errno != 0 then
    pure (stat.errno, Bytes.build 0 fun _ => 0, buffer)
  else if 4294967296 ≤ stat.size then
    pure (61, Bytes.build 0 fun _ => 0, buffer)
  else
    readBytes file stat.size buffer

/-- The SHA-256 digest of the bytes of the file `file` that its reads into `buffer` returned, how
the reads ended, 1 when a read returned no bytes, 2 when a read returned an errno, and 0 when the
reads used up `fileReads`, and the buffer. -/
def hashFile (file : Handle) (buffer : Bytes) : Action (Words4 × UInt64 × Bytes) := do
  let s ← Wasi.loop fileReads (iv256, buffer, (0 : UInt64), (0 : UInt64), (0 : UInt64))
    (fun _ s => s.2.2.2.2 == 0) fun _ s => do
      let got ← fdRead file s.2.1 s.2.2.1 (chunk - s.2.2.1)
      if got.errno != 0 then
        pure (s.1, got.buffer, s.2.2.1, s.2.2.2.1, 2)
      else if got.count == 0 then
        pure (s.1, got.buffer, s.2.2.1, s.2.2.2.1, 1)
      else if s.2.2.1 + got.count == chunk then
        pure (update s.1 got.buffer 1024, got.buffer, 0, s.2.2.2.1 + got.count, 0)
      else
        pure (s.1, got.buffer, s.2.2.1 + got.count, s.2.2.2.1 + got.count, 0)
  pure (finish (update s.1 s.2.1 (s.2.2.1 >>> 6)) s.2.1 ((s.2.2.1 >>> 6) <<< 6) (s.2.2.1 &&& 63)
      s.2.2.2.1, s.2.2.2.2, s.2.1)

/-- The checks of the lines of the manifest `m`, whose positions are `entries`, with the read
buffer `buffer`.  The status is 77 when the writes of an output line end with bytes left, which
ends the checks, and otherwise 0 when every line says OK and 1 when one says FAILED. -/
def checkLines (m : Bytes) (entries : Array UInt64) (buffer : Bytes) : Action UInt64 := do
  let s ← Wasi.loop (entries.size.toUInt64 >>> 1) (buffer, (0 : UInt64), (0 : UInt64))
      (fun _ s => s.2.2 == 0) fun j s => do
    let start := entries[(2 * j).toNat]!
    let stop := entries[(2 * j + 1).toNat]!
    let name := slice m (start + 66) (stop - start - 66)
    let checked ← withOpen .preopened 1 name 0 2 0 0
      (fun _ => pure ((⟨0, 0, 0, 0⟩ : Words4), (0 : UInt64), s.1)) fun file => hashFile file s.1
    let ok := checked.1.2.1 == 1 && checked.2 == 0 && hexMatches m start checked.1.1
    let line := render name ok
    let written ← writeAll line 0 line.size
    pure (checked.1.2.2, (if ok then s.2.1 else 1), (if written < line.size then 1 else 0))
  if s.2.2 != 0 then pure 77 else pure s.2.1

def main : Action UInt64 := do
  let arguments ← args
  if arguments.errno != 0 then
    pure arguments.errno
  else
    let scan := argScan arguments.bytes
    if scan.1 != 2 || arguments.bytes.get (arguments.bytes.size - 1) != 0 then
      pure 1
    else
      let name := slice arguments.bytes (scan.2.1 + 1) (arguments.bytes.size - scan.2.1 - 2)
      let buffer := Bytes.build chunk fun _ => 0
      let got ← withOpen .preopened 1 name 0 2097154 0 0
        (fun errno => pure (errno, Bytes.build 0 fun _ => 0, Bytes.build 0 fun _ => 0))
        fun file => readManifest file buffer
      if got.1.1 != 0 then
        pure got.1.1
      else if got.2 != 0 then
        pure got.2
      else
        let entries := parse got.1.2.1
        if entries.size.toUInt64 == 0 then
          pure 1
        else
          checkLines got.1.2.1 entries got.1.2.2

verified_compile_wasi command (main := main) :=
  [isHex, hexDigit, lineOk, parseStep, parse, digestByte, hexMatches, suffixByte, render, bswap,
    paddedWord, loadBlock, roundStep, advance, compress, hashFrom, byteWord, byteBlock, updateWith,
    packWord, pack, finishWith, update, finish, slice, argStep, argScan, readBytes, readManifest,
    hashFile, writeAll, checkLines, main]

end Demos.ManifestCheck
