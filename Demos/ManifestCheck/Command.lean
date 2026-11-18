import Demos.ManifestCheck.Program
import Library.Hashing.Sha256.Stream
import Verified.Wasi

/-! The WASI command of the manifest checker.  `main` reads its one argument with `args` and
`argScan`, opens the manifest of that name under the preopened directory with `withOpen`, reads it
to its end with `readManifest`, and closes it.  It then parses the manifest with `parse`, and for
each line opens the line's name under the preopened directory, hashes the file with `hashFile`,
closes it, compares the digest with the line's digits with `hexMatches`, and writes `render` of the
name and the verdict.

Every open names the directory 3, the flag `symlink_follow` (1), no open flags, and the right
`fd_read` (2) alone.  `readManifest` reads 65,536 bytes a call and appends them to the bytes held,
until a read returns an errno or no bytes, or the bytes held exceed 1,048,576.  `hashFile` reads
65,536 bytes a call into a streaming SHA-256: it puts the bytes after the last whole block of the
bytes before them, `update`s the state with the whole blocks of the joined bytes, and keeps the
rest, until a read returns an errno or no bytes, and then `finish`es the digest with the bytes
kept.  Its loop makes at most `fileReads`, `2^45 - 1`, reads, so the bytes that it hashes number
fewer than `2^61`, the limit of SHA-256's length field.

The status is the errno of `args`, 1 for an argument buffer without exactly one argument after the
program name, the errno of the manifest's open, of one of its reads, or of its close, 1 for a
manifest of more than 1,048,576 bytes or one that `parse` refuses, and otherwise 0 when every line
says OK and 1 when one says FAILED. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Library.Hashing.Words Library.Hashing.Sha256

/-- The capacity of each read. -/
def chunk : UInt64 := 65536

/-- The largest manifest that the command checks, in bytes. -/
def manifestLimit : UInt64 := 1048576

/-- The most reads of one checked file, `2^45 - 1`, whose 65,536 bytes each make fewer than `2^61`
bytes. -/
def fileReads : UInt64 := 35184372088831

/-- The `len` bytes of `b` from position `start`. -/
def slice (b : Bytes) (start len : UInt64) : Bytes :=
  Bytes.build len fun i => b.get (start + i)

/-- The bytes of `a` followed by those of `b`. -/
def join (a b : Bytes) : Bytes :=
  Bytes.build (a.size + b.size) fun i => if i < a.size then a.get i else b.get (i - a.size)

/-- The state of `argScan` after the byte `b`, from the state `st` before it: the zero bytes seen,
the position of the first, and the position of the byte `b`. -/
def argStep (st : UInt64 × UInt64 × UInt64) (b : UInt64) : UInt64 × UInt64 × UInt64 :=
  if b == 0 then (st.1 + 1, (if st.1 == 0 then st.2.2 else st.2.1), st.2.2 + 1)
  else (st.1, st.2.1, st.2.2 + 1)

/-- The number of zero bytes of the argument buffer `a`, the position of the first, and the size
of `a`. -/
def argScan (a : Bytes) : UInt64 × UInt64 × UInt64 :=
  LeanExe.loop a.size ((0 : UInt64), (0 : UInt64), (0 : UInt64)) fun i st => argStep st (a.get i)

/-- The bytes of the file `file` to their end, or until they exceed `manifestLimit`, and the errno
of a read that failed. -/
def readManifest (file : Handle) : Action (Bytes × UInt64) := do
  let s ← Wasi.loop (manifestLimit + 2) (Bytes.build 0 fun _ => 0, (0 : UInt64), false)
    (fun _ s => !s.2.2) fun _ s => do
      let got ← fdRead file chunk
      if got.errno != 0 then
        pure (s.1, got.errno, true)
      else if got.bytes.size == 0 then
        pure (s.1, (0 : UInt64), true)
      else
        let held := join s.1 got.bytes
        pure (held, (0 : UInt64), manifestLimit < held.size)
  pure (s.1, s.2.1)

/-- The SHA-256 digest of the bytes of the file `file` to their end, and whether the reads reached
the end: a read returned no bytes before any read returned an errno, within `fileReads` reads. -/
def hashFile (file : Handle) : Action (Words4 × Bool) := do
  let s ← Wasi.loop fileReads (iv256, Bytes.build 0 fun _ => 0, (0 : UInt64), false, false)
    (fun _ s => !s.2.2.2.2) fun _ s => do
      let got ← fdRead file chunk
      if got.errno != 0 then
        pure (s.1, s.2.1, s.2.2.1, false, true)
      else if got.bytes.size == 0 then
        pure (s.1, s.2.1, s.2.2.1, true, true)
      else
        let joined := join s.2.1 got.bytes
        let whole := (joined.size >>> 6) <<< 6
        pure (update s.1 joined, slice joined whole (joined.size - whole),
          s.2.2.1 + got.bytes.size, false, false)
  pure (finish s.1 s.2.1 s.2.2.1, s.2.2.2.1)

end Demos.ManifestCheck
