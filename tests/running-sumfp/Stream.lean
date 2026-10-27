import Demos.RunningSumFp.Stream

open LeanExe LeanExe.Wasi

private def chunks (input : ByteArray) (width : Nat) : List Bytes := Id.run do
  let mut result := []
  let mut offset := 0
  while offset < input.size do
    result := ⟨input.extract offset (offset + width)⟩ :: result
    offset := offset + width
  return result.reverse

private def check (input expected : String) (status : UInt64 := 0) (chunkSize : Nat := 4096)
    (writeSize : Nat := 4096) (zeroWrites : Nat := 0)
    (readErrorAt writeErrorAt : Option Nat := none) : IO Unit := do
  let pending ← IO.mkRef (chunks input.toUTF8 chunkSize)
  let output ← IO.mkRef ByteArray.empty
  let reads ← IO.mkRef (0 : Nat)
  let writes ← IO.mkRef (0 : Nat)
  let host : NativeHost := {
    read := fun capacity => do
      let index ← reads.get
      reads.set (index + 1)
      if readErrorAt == some index then return .returned 29 Bytes.empty
      match ← pending.get with
      | [] => pure (.returned 0 Bytes.empty)
      | bytes :: rest =>
          if bytes.data.size > capacity.toNat then
            throw (IO.userError "Running sumfp requested a short scripted input")
          pending.set rest
          pure (.returned 0 bytes)
    write := fun stream bytes => do
      if stream != .stdout then throw (IO.userError "Running sumfp wrote to stderr")
      let index ← writes.get
      writes.set (index + 1)
      let count := if index < zeroWrites then 0 else min writeSize bytes.data.size
      output.modify (· ++ bytes.data.extract 0 count)
      pure (.returned (if writeErrorAt == some index then 29 else 0) count.toUInt64)
    exit := fun _ => pure (.ok ()) }
  let outcome ← Demos.RunningSumFp.process.runFrom host Demos.RunningSumFp.initial
  let .returned actualStatus := outcome
    | throw (IO.userError "Running sumfp produced a terminal host outcome")
  if actualStatus != status then
    throw (IO.userError s!"Running sumfp returned {actualStatus}, expected {status}")
  if (← output.get) != expected.toUTF8 then
    throw (IO.userError s!"Running sumfp output differs at chunk size {chunkSize}, write size {writeSize}")

def main : IO Unit := do
  check "" ""
  check "12\n-5\n20\n" "1.2e1\n7e0\n2.7e1\n"
  check "12\n-5\n20" "1.2e1\n7e0\n2.7e1\n"
  check "+00012\r\n-00012\r\n-0\n" "1.2e1\n0e0\n0e0\n" 0 1 1 3
  for width in [1, 2, 3, 7, 4096] do
    check "0.1\n0.2\n-0.3\r\n" "1e-1\n3.0000000000000004e-1\n5.551115123125783e-17\n"
      0 width 1 2
  check "Infinity\n-Infinity\n1" "Infinity\nNaN\nNaN\n" 0 3 2 1
  check "5e-324\n5e-324\n-1e-323" "5e-324\n1e-323\n0e0\n" 0 2 1
  check "\n" "" 28
  check "1\n2x\n3\n" "1e0\n" 28 1
  check "1\n2\n" "1e0\n" 29 2 4096 0 (some 1)
  check "12\n-5\n" "1." 29 4096 1 0 none (some 1)
  let zeros := String.ofList (List.replicate 5000 '0')
  check (zeros ++ "1.25\n-1.25") "1.25e0\n0e0\n" 0 113 2 3
  IO.println "Running sumfp stream: 16 cases passed"
