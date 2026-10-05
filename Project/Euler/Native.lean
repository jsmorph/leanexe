import LeanExe.Examples.Euler

/-! `euler-native N FILE` runs the first-order solver natively on the N × N grid and writes
the words of `solve N` to FILE, little-endian, eight bytes each. -/

open LeanExe.Examples.Euler

def wordBytes (w : UInt64) : ByteArray :=
  ⟨(List.range 8).toArray.map fun i => (w >>> (8 * i).toUInt64).toUInt8⟩

def main (args : List String) : IO UInt32 := do
  let [nText, path] := args
    | IO.eprintln "usage: euler-native N FILE"; return 2
  let some n := nText.toNat? | IO.eprintln s!"not a number: {nText}"; return 2
  let start ← IO.monoMsNow
  let words := solve n.toUInt64
  let mut bytes := ByteArray.empty
  for w in words do
    bytes := bytes ++ wordBytes w
  IO.FS.writeBinFile path bytes
  let stop ← IO.monoMsNow
  IO.println s!"status {words[0]!} time {words[1]!} words {words.size} seconds {(stop - start).toFloat / 1000}"
  return 0
