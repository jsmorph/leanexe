import Library.Hashing.XxHash64.Program
import TestSupport.Hashing.Packing

/-! A check of the XXH64 transcription `Library.Hashing.XxHash64.Spec` and the program of
`Library.Hashing.XxHash64` on the 8,322 vectors of `data/hashing/xxhash64/xxh64.txt`, taken from
the xxHash repository's sanity test.  Each vector hashes the first `len` bytes of the sanity
test's buffer of 4,161 bytes with a seed of 0 or `0x9E3779B1`.  The program takes the bytes packed
eight to a word and followed by a word of nonzero bytes, which the result must ignore.  The check
exits with an error at the first difference.  Run the executable `xxhash64-vectors`; `--no-spec`
skips the transcription, and `--no-program` skips the program. -/

namespace TestSupport.Hashing.XxHash64Vectors

open TestSupport.Hashing.Packing

/-- The buffer of `fillTestBuffer` in the xxHash repository's `tests/sanity_test.c`. -/
def buffer (n : Nat) : List UInt8 :=
  ((List.range n).foldl (fun (acc : List UInt8 × UInt64) _ =>
    ((acc.2 >>> 56).toUInt8 :: acc.1, acc.2 * 11400714785074694797)) ([], 2654435761)).1.reverse

def hex16 (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The value of sixteen lowercase hexadecimal digits. -/
def wordOfHex (s : String) : Option UInt64 :=
  if s.length == 16 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    some (s.foldl (fun acc c => 16 * acc + hexDigit c) 0).toUInt64
  else none

def main (args : List String) : IO UInt32 := do
  let spec := !args.contains "--no-spec"
  let run := !args.contains "--no-program"
  let buf := buffer 4161
  let text ← IO.FS.readFile "data/hashing/xxhash64/xxh64.txt"
  let start ← IO.monoMsNow
  let mut count := 0
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [l, s, r] := line.splitOn " " | throw <| IO.userError s!"xxh64.txt: malformed line {line}"
    let (some len, some seed, some want) := (l.toNat?, wordOfHex s, wordOfHex r)
      | throw <| IO.userError s!"xxh64.txt: malformed line {line}"
    let m := buf.take len
    if spec then
      let got := Library.Hashing.XxHash64.Spec.xxh64 m seed
      unless got == want do
        throw <| IO.userError s!"len {len} seed {hex16 seed}: transcription {hex16 got}"
    if run then
      let got := Library.Hashing.XxHash64.xxh64 (pack m) len.toUInt64 seed
      unless got == want do
        throw <| IO.userError s!"len {len} seed {hex16 seed}: program {hex16 got}"
    count := count + 1
  IO.println s!"xxhash64: {count} vectors agree ({(← IO.monoMsNow) - start} ms)"
  return 0

end TestSupport.Hashing.XxHash64Vectors

def main (args : List String) : IO UInt32 := TestSupport.Hashing.XxHash64Vectors.main args
