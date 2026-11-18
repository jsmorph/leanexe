import LeanExe.Dialect.Bytes
import Library.Hashing.Words.Bytes

/-! The specifications of the pure core of the request in `Demos/ManifestCheck/request.txt`:
`parseSpec`, the lines of a manifest in `sha256sum`'s format, `hexMatchesSpec`, whether a line's hex
digits give a digest, and `renderSpec`, the output line of a file.

Decisions the request leaves to the specifications:

- A line is a run of bytes between newlines (10), without its newline.  An empty run is no line,
  so a newline after the last line is optional and empty lines are skipped.  A carriage return
  (13) is a byte of its line.
- A line in `sha256sum`'s format has at least 67 bytes: 64 hex digits, a space (32), a space for
  text mode or `*` (42) for binary mode, and a name of at least one byte, the rest of the line.
  The two modes mean the same.  A hex digit is `0` to `9` (48 to 57), `a` to `f` (97 to 102), or
  `A` to `F` (65 to 70).  A single space or a tab between the digits and the name is not in the
  format.  The name keeps every byte, spaces, carriage returns, and backslashes included, and has
  no escapes, so a line in the escaped form that `sha256sum` writes for some names, which starts
  with `\` (92), is not in the format.  Leading spaces, comments, and the tagged form
  `SHA256 (NAME) = HEX` are not in the format either.
- The format admits every name, absolute names and names with `..` components among them.  The
  command opens each name relative to the preopened directory, and the host's resolution of the
  name confines it to that directory.
- A manifest is refused when it has no line or when one of its lines is not in the format, so the
  command checks every line or none.  The command's specification gives the status of a refused
  manifest.  `parseSpec` returns the empty array for a refused manifest, and otherwise two words
  for each line, in order: the position of the line's first byte and the position after its last
  byte.  The line's digits start at the first position, and its name runs
  from 66 bytes after it to the second.
- `hexMatchesSpec` reads the 64 bytes of the manifest from a position as 32 pairs of hex digits, the
  first digit of a pair the high half of its byte, either case accepted, and compares them with
  the 32 bytes of a digest of four words, eight bytes to a word, least significant first, the
  packing of `Library.Hashing.Words`.  Bytes past the end of the manifest are not hex digits.
- `renderSpec` writes the name's bytes unchanged, followed by `: OK` or `: FAILED` and a newline.
-/

namespace Demos.ManifestCheck

open LeanExe Library.Hashing.Words

/-- The lines of the pieces `pieces`, the first of which starts at position `s`, each piece
followed by one separating byte: each nonempty piece with the position of its first byte. -/
def linesFrom : Nat → List (List UInt8) → List (Nat × List UInt8)
  | _, [] => []
  | s, p :: ps => (if p = [] then [] else [(s, p)]) ++ linesFrom (s + p.length + 1) ps

/-- The lines of `m`, each with the position of its first byte: the nonempty runs of bytes
between newlines (10). -/
def lines (m : List UInt8) : List (Nat × List UInt8) := linesFrom 0 (m.splitOn 10)

/-- The value of the hex digit `b`, `none` for a byte that is not one. -/
def hexValue (b : UInt8) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b ∧ b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b ∧ b ≤ 70 then some (b.toNat - 55)
  else none

/-- `line` is in `sha256sum`'s format: 64 hex digits, a space, a space or `*`, and a name of at
least one byte. -/
abbrev WellFormed (line : List UInt8) : Prop :=
  67 ≤ line.length ∧ (∀ i, i < 64 → (hexValue (line.getD i 0)).isSome) ∧
    line.getD 64 0 = 32 ∧ (line.getD 65 0 = 32 ∨ line.getD 65 0 = 42)

/-- The lines of the manifest `m` as positions: for each line, the position of its first byte and
the position after its last byte, or the empty array when `m` has no line or a line that is not in
`sha256sum`'s format. -/
def parseSpec (m : Bytes) : Array UInt64 :=
  let ls := lines m.data.data.toList
  if ls ≠ [] ∧ ∀ l ∈ ls, WellFormed l.2 then
    (ls.flatMap fun l => [UInt64.ofNat l.1, UInt64.ofNat (l.1 + l.2.length)]).toArray
  else #[]

/-- Whether the 64 bytes of `m` from position `start` are the hex digits of the 32 bytes of the
digest `d`, two digits to a byte, the high half first. -/
def hexMatchesSpec (x : Bytes × UInt64 × Words4) : Bool :=
  let (m, start, d) := x
  let text := m.data.data.toList
  (List.range 32).all fun k =>
    hexValue (text.getD (start.toNat + 2 * k) 0) == some ((d.bytes 32)[k]!.toNat / 16) &&
      hexValue (text.getD (start.toNat + 2 * k + 1) 0) == some ((d.bytes 32)[k]!.toNat % 16)

/-- The output line of the file `name`: its name followed by `: OK` when `ok` holds and by
`: FAILED` otherwise, and a newline. -/
def renderSpec (x : Bytes × Bool) : Bytes :=
  let (name, ok) := x
  ⟨⟨(name.data.data.toList ++ (if ok then ": OK" else ": FAILED").toUTF8.data.toList ++
    [10]).toArray⟩⟩

end Demos.ManifestCheck
