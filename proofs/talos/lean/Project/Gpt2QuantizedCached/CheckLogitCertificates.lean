import Project.ProofKit.F32LogitCertificate
import LeanExe.Packed

open Project.ProofKit

private def readWords (bytes : ByteArray) (offset count : Nat) : Array UInt32 :=
  (List.range count).toArray.map fun i => LeanExe.Packed.getUInt32LE! bytes (offset + i * 4)

private def certify (reference quantized : Array UInt32) (shift : Int) (winner : Nat) :
    Option { index : Nat //
      GreedyMaximum.index (fun i => Wasm.IEEE32.scaledValue quantized[i]!) quantized.size = index } :=
  let errors := (List.range reference.size).toArray.map fun i =>
    (Wasm.IEEE32.scaledValue quantized[i]! - Wasm.IEEE32.scaledValue reference[i]! - shift).natAbs
  if h : F32LogitCertificate.check reference quantized errors shift winner = true then
    some ⟨winner, F32LogitCertificate.greedy reference quantized errors shift winner h⟩
  else none

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: CheckLogitCertificates <logit-pairs.bin>")
  let bytes ← IO.FS.readBinFile path
  if bytes.size < 16 || bytes.extract 0 8 != "LXQLG001".toUTF8 then
    throw (IO.userError "invalid logit-pair header")
  let count := (LeanExe.Packed.getUInt32LE! bytes 8).toNat
  let width := (LeanExe.Packed.getUInt32LE! bytes 12).toNat
  if count > 10000 || width != 50257 || bytes.size != 16 + count * (12 + width * 8) then
    throw (IO.userError "invalid logit-pair extent")
  let mut rawCount := 0
  let mut shiftedCount := 0
  for row in [:count] do
    let start := 16 + row * (12 + width * 8)
    let sequence := (LeanExe.Packed.getUInt32LE! bytes start).toNat
    let position := (LeanExe.Packed.getUInt32LE! bytes (start + 4)).toNat
    let winner := (LeanExe.Packed.getUInt32LE! bytes (start + 8)).toNat
    if winner ≥ width then throw (IO.userError "winner is outside the vocabulary")
    let reference := readWords bytes (start + 12) width
    let quantized := readWords bytes (start + 12 + width * 4) width
    let shift := Wasm.IEEE32.scaledValue quantized[winner]! - Wasm.IEEE32.scaledValue reference[winner]!
    let raw := (certify reference quantized 0 winner).isSome
    let shifted := (certify reference quantized shift winner).isSome
    if raw then rawCount := rawCount + 1
    if shifted then shiftedCount := shiftedCount + 1
    IO.println s!"row {row} sequence {sequence} position {position} raw {raw} shifted {shifted}"
  IO.println s!"checked {count} raw {rawCount} shifted {shiftedCount}"
  return 0
