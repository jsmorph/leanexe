import Demos.ManifestCheck.Spec
import Library.Hashing.Sha2.Equiv.SHA256.Main
import LeanExe.Wasi.Bracket
import LeanExe.Wasi.Semantics
import LeanExe.Wasi.Sys

/-! The specification of the runs of the manifest checker's WASI command, in terms of the events of
a run, `LeanExe.Wasi.Event`, which record each call with the reply that the host gave.

`OneArgument buffer name` states that the argument buffer that `args_get` fills holds the program
name and exactly one argument, `name`, each followed by a zero byte.  Every open of a run is the
event of `openArgs`: `path_open` under descriptor 3 with the flag `symlink_follow`, no open flags,
the right `fd_read` alone, no inherited rights, and no descriptor flags.  `FileReads` and
`ManifestReads` state the reads of an open file, each of 65,536 bytes, and the bytes that they
returned: `FileReads` until a read returns no bytes or an errno, within a number of reads, and
`ManifestReads` until a read returns no bytes or an errno, or the bytes exceed 1,048,576.
`DigestOf hex bytes` states that the 64 hex digits `hex` give the digest of FIPS 180-4 of the bits
of `bytes`, and `FileCheck` the events of the check of one line of the manifest and its verdict. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding
  SHS.Equiv.SHA256.Pipeline

/-- The bytes `bs` as a byte string. -/
def bytesOf (bs : List UInt8) : Bytes := ⟨⟨bs.toArray⟩⟩

/-- The argument buffer `buffer` holds a program name and exactly one argument, `name`, each
followed by a zero byte. -/
def OneArgument (buffer name : List UInt8) : Prop :=
  ∃ program, buffer = program ++ 0 :: (name ++ [0]) ∧ (0 : UInt8) ∉ program ∧ (0 : UInt8) ∉ name

/-- The arguments of the open of `name`: the directory 3, the flag `symlink_follow` (1), no open
flags, the right `fd_read` (2), no inherited rights, and no descriptor flags. -/
def openArgs (name : List UInt8) : List Arg :=
  [.word 3, .word 1, .bytes (bytesOf name), .word 0, .word 2, .word 0, .word 0]

/-- The arguments of a read of 65,536 bytes of descriptor `fd`. -/
def readArgs (fd : UInt64) : List Arg := [.word fd, .space 65536]

/-- The bytes that a read returned with errno 0 and the outputs `outputs`: the bytes of the buffer
up to the count that the call returned. -/
def returned (outputs : List Bytes) : List UInt8 :=
  ((⟨0, outputs⟩ : Reply).prefixBytes 0 ((⟨0, outputs⟩ : Reply).word 1)).data.data.toList

/-- How the reads of a file ended: a read returned no bytes, a read returned an errno, or the reads
stopped before either. -/
inductive Ending where
  | eof
  | failed (errno : UInt64)
  | cut
  deriving DecidableEq

/-- `FileReads fd r events bytes ending`: `events` are reads of 65,536 bytes of descriptor `fd`, at
most `r` of them, each but the last returning errno 0 and some bytes, which `bytes` collects.  The
last read returned no bytes (`eof`) or an errno (`failed`), or `r` reads returned bytes (`cut`). -/
inductive FileReads (fd : UInt64) : Nat → List Event → List UInt8 → Ending → Prop
  | cut : FileReads fd 0 [] [] .cut
  | eof {r : Nat} {outputs : List Bytes} (empty : returned outputs = []) :
      FileReads fd (r + 1) [.sys .fdRead (readArgs fd) (.returned 0 outputs)] [] .eof
  | failed {r : Nat} {errno : UInt64} {outputs : List Bytes} (nonzero : errno ≠ 0) :
      FileReads fd (r + 1) [.sys .fdRead (readArgs fd) (.returned errno outputs)] []
        (.failed errno)
  | more {r : Nat} {outputs : List Bytes} {events : List Event} {bytes : List UInt8}
      {ending : Ending} (nonempty : returned outputs ≠ [])
      (rest : FileReads fd r events bytes ending) :
      FileReads fd (r + 1) (.sys .fdRead (readArgs fd) (.returned 0 outputs) :: events)
        (returned outputs ++ bytes) ending

/-- `ManifestReads fd held events bytes ending`: `events` are reads of 65,536 bytes of descriptor
`fd` after the bytes `held`, and `bytes` are `held` followed by the bytes that they returned.  The
last read returned no bytes (`eof`), an errno (`failed`), or bytes that bring the total above
1,048,576 (`cut`); each read before it returned errno 0 and some bytes, with a total of at most
1,048,576. -/
inductive ManifestReads (fd : UInt64) : List UInt8 → List Event → List UInt8 → Ending → Prop
  | eof {held : List UInt8} {outputs : List Bytes} (empty : returned outputs = []) :
      ManifestReads fd held [.sys .fdRead (readArgs fd) (.returned 0 outputs)] held .eof
  | failed {held : List UInt8} {errno : UInt64} {outputs : List Bytes} (nonzero : errno ≠ 0) :
      ManifestReads fd held [.sys .fdRead (readArgs fd) (.returned errno outputs)] held
        (.failed errno)
  | over {held : List UInt8} {outputs : List Bytes} (nonempty : returned outputs ≠ [])
      (large : 1048576 < (held ++ returned outputs).length) :
      ManifestReads fd held [.sys .fdRead (readArgs fd) (.returned 0 outputs)]
        (held ++ returned outputs) .cut
  | more {held : List UInt8} {outputs : List Bytes} {events : List Event} {bytes : List UInt8}
      {ending : Ending} (nonempty : returned outputs ≠ [])
      (small : (held ++ returned outputs).length ≤ 1048576)
      (rest : ManifestReads fd (held ++ returned outputs) events bytes ending) :
      ManifestReads fd held (.sys .fdRead (readArgs fd) (.returned 0 outputs) :: events) bytes
        ending

/-- The 64 hex digits of `hex` give the 32 bytes `d`, two digits to a byte, the high half first. -/
def HexDigits (hex : List UInt8) (d : Vector UInt8 32) : Prop :=
  ∀ k (hk : k < 32), hexValue (hex.getD (2 * k) 0) = some (d[k].toNat / 16) ∧
    hexValue (hex.getD (2 * k + 1) 0) = some (d[k].toNat % 16)

/-- The hex digits of `hex` give the SHA-256 digest of FIPS 180-4 of the bits of `bytes`, which
number fewer than `2^61` bytes. -/
def DigestOf (hex bytes : List UInt8) : Prop :=
  ∃ (d : Vector UInt8 32) (small : (bytesOf bytes).data.size < 2 ^ 61), HexDigits hex d ∧
    digestBitVec d = SHS.SHA256.sha256 (bytesToBitMessage (bytesOf bytes).data)
      (bitLen_lt_of_size_lt _ small)

/-- `FileCheck name hex events ok`: `events` are those of the check of the line whose name is
`name` and whose digits are `hex`, and `ok` is its verdict.  An open that returns an errno ends the
check with the verdict false.  Otherwise the reads of the file follow, `FileReads` within
`2^45 - 1` reads, and the close of its descriptor, and the verdict holds exactly when a read
returned no bytes before any read returned an errno, the close returned errno 0, and the digits
give the digest of the bytes that the reads returned. -/
inductive FileCheck (name hex : List UInt8) : List Event → Bool → Prop
  | refused {errno : UInt64} {outputs : List Bytes} (nonzero : errno ≠ 0) :
      FileCheck name hex [.sys .pathOpen (openArgs name) (.returned errno outputs)] false
  | opened {outputs : List Bytes} {events : List Event} {bytes : List UInt8} {ending : Ending}
      {closeErrno : UInt64} {committed : List Bytes} {ok : Bool}
      (reads : FileReads (openedDescriptor outputs) 35184372088831 events bytes ending)
      (verdict : ok = true ↔ ending = .eof ∧ closeErrno = 0 ∧ DigestOf hex bytes) :
      FileCheck name hex (.sys .pathOpen (openArgs name) (.returned 0 outputs) :: events ++
        [.sys .fdClose [.word (openedDescriptor outputs)] (.returned closeErrno committed)]) ok

end Demos.ManifestCheck
