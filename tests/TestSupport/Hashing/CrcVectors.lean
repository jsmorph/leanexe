import Library.Hashing.Crc.Division
import Library.Hashing.Crc.Program
import TestSupport.Hashing.Packing

/-! A check of the CRC transcription and the programs of `Library.Hashing.Crc` on the vectors of
`data/hashing/crc/vectors.txt`: CRC-32 by zlib and CRC-32C by the Linux kernel, for the check
string of the CRC catalogue, the examples of RFC 3720 Appendix B.4, and pseudorandom messages of
up to 4,097 bytes.  The transcription's division, `crc32Eval` and `crc32cEval`, which
`Library.Hashing.Crc.Division` proves equal to `crc32` and `crc32c`, runs on each message.  The
programs run on the message packed eight to a word and followed by a word of nonzero bytes, which
the result must ignore.  The update functions run from the CRC of each split of the message into
a prefix and the rest, at six points, once with the prefix's CRC and once with nonzero high bits
added to it, which the result must ignore.  The check exits with an error at the first
difference.  Run the executable `crc-vectors`; `--no-spec` skips the transcription, and
`--no-program` skips the programs. -/

namespace TestSupport.Hashing.CrcVectors

open Library.Hashing.Crc TestSupport.Hashing.Packing

/-- A function of the vectors: the transcription's division, the program, and its update. -/
structure Function where
  name : String
  spec : List UInt8 → Nat
  program : Array UInt64 → UInt64 → UInt64
  update : UInt64 → Array UInt64 → UInt64 → UInt64

def functions : List Function := [
  { name := "crc32", spec := Division.crc32Eval, program := crc32, update := crc32Update },
  { name := "crc32c", spec := Division.crc32cEval, program := crc32c, update := crc32cUpdate }]

def hex8 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

/-- The value of a CRC written as eight lowercase hexadecimal digits. -/
def crcOfHex (s : String) : Option Nat :=
  if s.length == 8 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    some (s.foldl (fun acc c => 16 * acc + hexDigit c) 0)
  else none

/-- The points at which the update check splits a message of `n` bytes. -/
def splits (n : Nat) : List Nat := ([0, 1, n / 3, n / 2, n - 1, n].filter (· ≤ n)).eraseDups

/-- Checks one function on the message `m` with the expected CRC `want`. -/
def checkOne (fn : Function) (label : String) (m : List UInt8) (want : Nat) (spec program : Bool) :
    IO Unit := do
  let fail (what : String) (got : Nat) : IO Unit :=
    throw <| IO.userError
      s!"{fn.name}: {label} message of {m.length} bytes: {what} {hex8 got}, expected {hex8 want}"
  if spec then
    let got := fn.spec m
    unless got == want do fail "transcription" got
  if program then
    let n := m.length
    let got := (fn.program (pack m) n.toUInt64).toNat
    unless got == want do fail "program" got
    for k in splits n do
      let pre := fn.program (pack (m.take k)) k.toUInt64
      let rest := pack (m.drop k)
      for c in [pre, pre ||| 0x5A5A5A5A00000000] do
        let got := (fn.update c rest (n - k).toUInt64).toNat
        unless got == want do fail s!"update from byte {k}" got

def main (args : List String) : IO UInt32 := do
  let spec := !args.contains "--no-spec"
  let program := !args.contains "--no-program"
  let text ← IO.FS.readFile "data/hashing/crc/vectors.txt"
  let mut counts : List (String × Nat) := []
  let start ← IO.monoMsNow
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [label, a, c, hex] := line.splitOn " "
      | throw <| IO.userError s!"vectors.txt: malformed line {line}"
    let m := if hex == "-" then [] else bytesOfHex hex
    let some va := crcOfHex a | throw <| IO.userError s!"vectors.txt: bad CRC-32 {a}"
    let some vc := crcOfHex c | throw <| IO.userError s!"vectors.txt: bad CRC-32C {c}"
    for (fn, want) in functions.zip [va, vc] do
      checkOne fn label m want spec program
    counts := match counts.lookup label with
      | some k => counts.map fun (l, v) => if l == label then (l, k + 1) else (l, v)
      | none => counts ++ [(label, 1)]
  for (label, k) in counts do
    IO.println s!"{label}: CRC-32 and CRC-32C agree on {k} {if k == 1 then "message" else "messages"}"
  IO.println s!"crc: {counts.foldl (· + ·.2) 0} messages agree ({(← IO.monoMsNow) - start} ms)"
  return 0

end TestSupport.Hashing.CrcVectors

def main (args : List String) : IO UInt32 := TestSupport.Hashing.CrcVectors.main args
