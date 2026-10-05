import LeanExe.Examples.EulerReconstructed

/-! `euler-native N FILE` runs the first-order solver natively on the N × N grid and writes
the words of `solve N` to FILE, little-endian, eight bytes each.  `euler-native N FILE TRIALS`
runs the reconstructed solver with at most TRIALS reconstruction tries. -/

open LeanExe.Examples.Euler

def wordBytes (w : UInt64) : ByteArray :=
  ⟨(List.range 8).toArray.map fun i => (w >>> (8 * i).toUInt64).toUInt8⟩

def main (args : List String) : IO UInt32 := do
  let (nText, path, trials?) ← match args with
    | [nText, path] => pure (nText, path, none)
    | [nText, path, trialsText] => pure (nText, path, some trialsText)
    | _ => IO.eprintln "usage: euler-native N FILE [TRIALS]"; return 2
  let some n := nText.toNat? | IO.eprintln s!"not a number: {nText}"; return 2
  let start ← IO.monoMsNow
  let words ← match trials? with
    | none => pure (solve n.toUInt64)
    | some trialsText =>
      match trialsText.toNat? with
      | some trials => pure (reconstructedSolve n.toUInt64 trials.toUInt64)
      | none => IO.eprintln s!"not a number: {trialsText}"; return 2
  let mut bytes := ByteArray.empty
  for w in words do
    bytes := bytes ++ wordBytes w
  IO.FS.writeBinFile path bytes
  let stop ← IO.monoMsNow
  IO.println s!"status {words[0]!} time {words[1]!} words {words.size} seconds {(stop - start).toFloat / 1000}"
  return 0
