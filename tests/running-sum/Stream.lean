import Demos.RunningSum.Stream

open LeanExe LeanExe.Wasi

private def chunks (input : ByteArray) (width : Nat) : List Bytes := Id.run do
  let mut result := []
  let mut offset := 0
  while offset < input.size do
    result := ⟨input.extract offset (offset + width)⟩ :: result
    offset := offset + width
  return result.reverse

private def check (input expected : String) (status : UInt64 := 0) (chunkSize : Nat := 4096)
    (writeSize : Nat := 4096) (zeroFirstWrite : Bool := false)
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
            throw (IO.userError "Running sum requested a short scripted input")
          pending.set rest
          pure (.returned 0 bytes)
    write := fun stream bytes => do
      if stream != .stdout then throw (IO.userError "Running sum wrote to stderr")
      let index ← writes.get
      writes.set (index + 1)
      let count := if zeroFirstWrite && index == 0 then 0 else min writeSize bytes.data.size
      output.modify (· ++ bytes.data.extract 0 count)
      pure (.returned (if writeErrorAt == some index then 29 else 0) count.toUInt64)
    exit := fun _ => pure (.ok ()) }
  let outcome ← Demos.RunningSum.process.runFrom host Demos.RunningSum.initial
  let .returned actualStatus := outcome
    | throw (IO.userError "Running sum produced a terminal host outcome")
  if actualStatus != status then
    throw (IO.userError s!"Running sum returned {actualStatus}, expected {status}")
  if (← output.get) != expected.toUTF8 then
    throw (IO.userError s!"Running sum output differs at chunk size {chunkSize}, write size {writeSize}")

def main : IO Unit := do
  check "" ""
  check "12\n-5\n20\n" "12\n7\n27\n"
  check "12\n-5\n20" "12\n7\n27\n"
  check "+00012\r\n-00012\r\n-0\n" "12\n0\n0\n" 0 1 1 true
  for width in [1, 2, 3, 7, 4096] do
    check "1\n-2\n+003\n4\r\n-6" "1\n-1\n2\n6\n0\n" 0 width 1
  check "\n" "" 28
  check "+\n" "" 28
  check "1\n2x\n3\n" "1\n" 28 1
  check "1\n2\n" "1\n" 29 2 4096 false (some 1)
  check "1\n2\n" "1\n" 29 4096 1 false none (some 1)
  let nines := String.ofList (List.replicate 5000 '9')
  let power := "1" ++ String.ofList (List.replicate 5000 '0')
  check (nines ++ "\n1\n-" ++ power) (nines ++ "\n" ++ power ++ "\n0\n") 0 113 97 true
  let mut input := ""
  let mut expected := ""
  let mut total : Int := 0
  for i in [:1000] do
    let value : Int := if i % 3 == 0 then -(i : Int) else i
    total := total + value
    input := input ++ toString value ++ "\n"
    expected := expected ++ toString total ++ "\n"
  check input expected 0 113 3 true
  IO.println "Running sum stream: 16 cases passed"
