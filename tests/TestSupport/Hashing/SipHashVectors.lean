import Library.Hashing.SipHash.Program
import TestSupport.Hashing.Packing

/-! A check of the SipHash transcription `Library.Hashing.SipHash.Spec` and the programs of
`Library.Hashing.SipHash`.  The transcription runs the example of Appendix A of the SipHash paper
and must reach each of its intermediate states.  The transcription and the programs run the 64
SipHash-2-4 vectors of the reference implementation in `data/hashing/siphash/vectors.h` and the
SipHash-2-4 and SipHash-1-3 tags of OpenSSL in `data/hashing/siphash/vectors.txt`.  A program
takes the key as its two packed words and the message packed eight to a word and followed by a
word of nonzero bytes, which the result must ignore.  The check exits with an error at the first
difference.  Run the executable `siphash-vectors`; `--no-spec` skips the transcription, and
`--no-program` skips the programs. -/

namespace TestSupport.Hashing.SipHashVectors

open Library.Hashing.SipHash TestSupport.Hashing.Packing

def hex16 (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The value of a tag written as sixteen lowercase hexadecimal digits. -/
def tagOfHex (s : String) : Option UInt64 :=
  if s.length == 16 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    some (s.foldl (fun acc c => 16 * acc + hexDigit c) 0).toUInt64
  else none

/-- Checks SipHash-c-d of `key` and `m` against `want` in the transcription and the program. -/
def checkOne (what : String) (c d : Nat) (program : UInt64 → UInt64 → Array UInt64 → UInt64 → UInt64)
    (key m : List UInt8) (want : UInt64) (spec run : Bool) : IO Unit := do
  let fail (who : String) (got : UInt64) : IO Unit :=
    throw <| IO.userError
      s!"{what}: SipHash-{c}-{d} of {m.length} bytes: {who} {hex16 got}, expected {hex16 want}"
  if spec then
    let got := Spec.sipHash c d key m
    unless got == want do fail "transcription" got
  if run then
    let k := pack key
    let got := program k[0]! k[1]! (pack m) m.length.toUInt64
    unless got == want do fail "program" got

def words (s : Spec.State) : List UInt64 := [s.v0, s.v1, s.v2, s.v3]

/-- The example of Appendix A: SipHash-2-4 of the 15 bytes `00` to `0e` with the key `00` to
`0f`, with the intermediate states that the appendix lists. -/
def appendixA : IO Unit := do
  let key := (List.range 16).map Nat.toUInt8
  let m := (List.range 15).map Nat.toUInt8
  let k0 := Spec.le64 (key.take 8)
  let k1 := Spec.le64 (key.drop 8)
  let [m0, m1] := Spec.messageWords m | throw <| IO.userError "Appendix A: not two words"
  let s0 := Spec.initial k0 k1
  let s1 := Spec.rounds 2 { s0 with v3 := s0.v3 ^^^ m0 }
  let s2 := Spec.compress 2 s0 m0
  let s3 := { Spec.compress 2 s2 m1 with v2 := (Spec.compress 2 s2 m1).v2 ^^^ 0xff }
  let s4 := Spec.rounds 4 s3
  let checks : List (String × List UInt64 × List UInt64) := [
    ("key words", [k0, k1], [0x0706050403020100, 0x0f0e0d0c0b0a0908]),
    ("message words", [m0, m1], [0x0706050403020100, 0x0f0e0d0c0b0a0908]),
    ("initial state", words s0,
      [0x7469686173716475, 0x6b617f6d656e6665, 0x6b7f62616d677361, 0x7b6b696e727e6c7b]),
    ("two SipRounds", words s1,
      [0x4d07749cdd0858e0, 0x0d52f6f62a4f59a4, 0x634cb3577b01fd3d, 0xa5224d6f55c7d9c8]),
    ("first block", words s2,
      [0x4a017198de0a59e0, 0x0d52f6f62a4f59a4, 0x634cb3577b01fd3d, 0xa5224d6f55c7d9c8]),
    ("last block and ff", words s3,
      [0x3c85b3ab6f55be51, 0x414fc3fb98efe374, 0xccf13ea527b9f442, 0x5293f5da84008f82]),
    ("four SipRounds", words s4,
      [0xf6bcd53893fecff1, 0x54b9964c7ea0d937, 0x1b38329c099bb55a, 0x1814bb89ad7be679]),
    ("tag", [Spec.sipHash 2 4 key m], [0xa129ca6149be45e5])]
  for (name, got, want) in checks do
    unless got == want do
      throw <| IO.userError s!"Appendix A: {name}: {got.map hex16}, expected {want.map hex16}"

/-- The 64 tags of `vectors_sip64` in the reference implementation's `vectors.h`. -/
def reference : IO (List UInt64) := do
  let text ← IO.FS.readFile "data/hashing/siphash/vectors.h"
  let some body := (text.splitOn "vectors_sip64")[1]?.bind fun t => (t.splitOn "vectors_sip128")[0]?
    | throw <| IO.userError "vectors.h: no vectors_sip64"
  let bytes := (body.splitOn "0x").drop 1 |>.map fun t => bytesOfHex (String.ofList (t.toList.take 2))
  let bytes := bytes.flatten
  unless bytes.length == 512 do
    throw <| IO.userError s!"vectors.h: {bytes.length} bytes in vectors_sip64"
  return (List.range 64).map fun i =>
    ((List.range 8).foldl (fun acc j => acc ||| (bytes[8 * i + j]!.toUInt64 <<< (8 * j).toUInt64)) 0)

def main (args : List String) : IO UInt32 := do
  let spec := !args.contains "--no-spec"
  let run := !args.contains "--no-program"
  let start ← IO.monoMsNow
  if spec then
    appendixA
    IO.println "Appendix A: the transcription reaches every intermediate state"
  let key := (List.range 16).map Nat.toUInt8
  let tags ← reference
  for (tag, i) in tags.zip (List.range 64) do
    checkOne "vectors.h" 2 4 siphash24 key ((List.range i).map Nat.toUInt8) tag spec run
  IO.println "vectors.h: SipHash-2-4 agrees on 64 messages"
  let text ← IO.FS.readFile "data/hashing/siphash/vectors.txt"
  let mut count := 0
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [k, a, b, hex] := line.splitOn " "
      | throw <| IO.userError s!"vectors.txt: malformed line {line}"
    let (some ta, some tb) := (tagOfHex a, tagOfHex b)
      | throw <| IO.userError s!"vectors.txt: bad tag on line {line}"
    let m := if hex == "-" then [] else bytesOfHex hex
    checkOne "vectors.txt" 2 4 siphash24 (bytesOfHex k) m ta spec run
    checkOne "vectors.txt" 1 3 siphash13 (bytesOfHex k) m tb spec run
    count := count + 1
  IO.println s!"vectors.txt: SipHash-2-4 and SipHash-1-3 agree on {count} messages"
  IO.println s!"siphash: {64 + count} messages agree ({(← IO.monoMsNow) - start} ms)"
  return 0

end TestSupport.Hashing.SipHashVectors

def main (args : List String) : IO UInt32 := TestSupport.Hashing.SipHashVectors.main args
