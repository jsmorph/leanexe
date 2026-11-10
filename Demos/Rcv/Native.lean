import Demos.Rcv.Spec
import Demos.Rcv.Program

/-!
Native runs of the specification on canonical ballot files and word arrays, for comparisons with
the requirements' reports, the Python reference, and the module.  The reader of the requirements is
not part of the first increment, so `load` reads a file with a parser of its own and accepts the
result only when `Demos.Rcv.Spec.write` prints it as the file's exact bytes and it meets
`Contest.WellFormed`.  A structure that meets the constraints and prints as the file is the file's
structure, so the parser's own defects can reject a file but cannot change a count.

Word arrays are packed as the reference packs them: little-endian 64-bit words, eight bytes each.
`rcv-spec report FILE` writes the specification's report of the file to standard output.
`rcv-spec contest-words FILE` writes the file's contest words, and `rcv-spec words FILE` the result
words of `countWords` on them.  `rcv-spec array FILE` reads a packed word array and writes the
result words of `countWords`, and `rcv-spec program FILE` writes those of `Demos.Rcv.Program.count`,
the program that the module compiles, run natively.  `rcv-spec district4 FILE` compares the round
lines of the report with the District 4 report of the requirements, prints each line that differs,
and exits with status 1 if any does.  A file that does not load gives status 1.
-/

namespace Demos.Rcv.Native

open Demos.Rcv Demos.Rcv.Spec

/-- The pieces of `bs` between the bytes `sep`. -/
def split (sep : UInt8) (bs : List UInt8) : List (List UInt8) :=
  let step := fun (acc : List (List UInt8) × List UInt8) (b : UInt8) =>
    if b == sep then (acc.2.reverse :: acc.1, []) else (acc.1, b :: acc.2)
  let r := bs.foldl step ([], [])
  (r.2.reverse :: r.1).reverse

def parseNat (bs : List UInt8) : Except String Nat :=
  if !bs.isEmpty && bs.all fun b : UInt8 => (0x30 : UInt8) ≤ b && b ≤ (0x39 : UInt8) then
    .ok (bs.foldl (fun (v : Nat) (b : UInt8) => 10 * v + (b.toNat - 0x30)) 0)
  else .error s!"not a number: {String.fromUTF8? ⟨bs.toArray⟩}"

/-- `bs` without the prefix `p`. -/
def after (p bs : List UInt8) : Except String (List UInt8) :=
  if bs.take p.length == p then .ok (bs.drop p.length)
  else .error s!"expected a line starting with {String.fromUTF8? ⟨p.toArray⟩}"

def parseKind (bs : List UInt8) : Except String Kind :=
  if bs == ascii "listed" then .ok .listed
  else if bs == ascii "named-writein" then .ok .namedWritein
  else if bs == ascii "aggregate-writein" then .ok .aggregateWritein
  else if bs == ascii "excluded" then .ok .excluded
  else .error "unknown kind"

def parseField (bs : List UInt8) : Except String UInt64 := do
  if bs.isEmpty then return 0
  if bs == ascii "*" then return unnamedOvervote
  let is ← (split (0x7C : UInt8) bs).mapM parseNat
  return (is.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum.toUInt64

def parseCandidate (line : List UInt8) : Except String Candidate := do
  let rest ← after (ascii "candidate ") line
  let rest := rest.dropWhile (· != (0x20 : UInt8))
  let rest := rest.drop 1
  let kindBytes := rest.takeWhile (· != (0x20 : UInt8))
  let name := (rest.dropWhile (· != (0x20 : UInt8))).drop 1
  return { kind := ← parseKind kindBytes, name }

def parseBallot (k : Nat) (line : List UInt8) : Except String Ballot := do
  let fields := split (0x2C : UInt8) line
  if fields.length == k + 1 then
    return { ident := fields.head?, positions := ← (fields.drop 1).mapM parseField }
  else return { ident := none, positions := ← fields.mapM parseField }

/-- The contest structure of a canonical file's bytes, by a parser that does not check the
grammar. -/
def parse (bs : List UInt8) : Except String Contest := do
  let lines := (split (0x0A : UInt8) bs).dropLast
  let contest ← after (ascii "contest ") (lines.getD 1 [])
  let k ← parseNat (← after (ascii "positions ") (lines.getD 2 []))
  let n ← parseNat (← after (ascii "candidates ") (lines.getD 3 []))
  let candidates ← ((lines.drop 4).take n).mapM parseCandidate
  let order ←
    (split (0x20 : UInt8) (← after (ascii "order ") (lines.getD (4 + n) []))).mapM parseNat
  let ballots ← (lines.drop (6 + n)).mapM (parseBallot k)
  return { contest, positions := k, candidates, order, ballots }

/-- The contest structure of the file at `path`, accepted when it prints as the file and meets the
constraints. -/
def load (path : String) : IO Contest := do
  let bs := (← IO.FS.readBinFile path).toList
  match parse bs with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok c =>
    if write c != bs then
      throw (IO.userError s!"{path}: the structure read does not print as the file")
    if !decide c.WellFormed then
      throw (IO.userError s!"{path}: the structure read breaks a constraint")
    return c

/-- The round lines of the 2022 District 4 report in the requirements. -/
def district4 : String :=
  "round 1
continuing 26432
votes 1 8227
votes 2 8190
votes 3 10015
inactive blank 4269
inactive uncounted 134
inactive overvote 148
inactive exhausted 0
eliminate lowest 2
round 2
continuing 24586
votes 1 12421
votes 3 12165
inactive blank 4269
inactive uncounted 134
inactive overvote 173
inactive exhausted 1821
winner 1
"

def writeBytes (bs : List UInt8) : IO Unit := do
  (← IO.getStdout).write ⟨bs.toArray⟩

def compareDistrict4 (c : Contest) : IO UInt32 := do
  let got := (reportLines c).drop (7 + c.candidates.length)
  let want := (split (0x0A : UInt8) (ascii district4)).dropLast
  let mut bad : Nat := 0
  for i in List.range (max got.length want.length) do
    let g := got.getD i []
    let w := want.getD i []
    if g != w then
      bad := bad + 1
      IO.println s!"line {i + 1} after the header: {String.fromUTF8? ⟨g.toArray⟩} \
        against {String.fromUTF8? ⟨w.toArray⟩}"
  IO.println s!"{c.ballots.length} ballots, {got.length} round lines, \
    {bad} differ from the requirements"
  return if bad == 0 then 0 else 1

/-- The little-endian 64-bit words of `bs`. -/
def unpack (path : String) (bs : ByteArray) : IO (Array UInt64) := do
  if bs.size % 8 != 0 then
    throw (IO.userError s!"{path}: {bs.size} bytes, not a multiple of 8")
  return (Array.range (bs.size / 8)).map fun i : Nat =>
    (List.range 8).foldl (fun (w : UInt64) (j : Nat) =>
      w ||| bs[8 * i + j]!.toUInt64 <<< (8 * j).toUInt64) 0

/-- The words `ws`, each as eight bytes, least significant first. -/
def pack (ws : Array UInt64) : ByteArray :=
  ws.foldl (fun (acc : ByteArray) (w : UInt64) =>
    (List.range 8).foldl (fun (acc : ByteArray) (j : Nat) =>
      acc.push (w >>> (8 * j).toUInt64).toUInt8) acc) ByteArray.empty

def writePacked (ws : Array UInt64) : IO Unit := do
  (← IO.getStdout).write (pack ws)

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["report", path] =>
      writeBytes (report (← load path))
      return 0
    | ["contest-words", path] =>
      writePacked (contestWords (← load path)).toArray
      return 0
    | ["words", path] =>
      writePacked (countWords (contestWords (← load path))).toArray
      return 0
    | ["array", path] =>
      writePacked (countArray (← unpack path (← IO.FS.readBinFile path)))
      return 0
    | ["program", path] =>
      writePacked (Demos.Rcv.Program.count (← unpack path (← IO.FS.readBinFile path)))
      return 0
    | ["district4", path] => compareDistrict4 (← load path)
    | _ =>
      IO.eprintln ("usage: rcv-spec report FILE | rcv-spec contest-words FILE | " ++
        "rcv-spec words FILE | rcv-spec array FILE | rcv-spec program FILE | " ++
        "rcv-spec district4 FILE")
      return 2
  catch e =>
    IO.eprintln s!"{e}"
    return 1

end Demos.Rcv.Native

def main (args : List String) : IO UInt32 := Demos.Rcv.Native.main args
