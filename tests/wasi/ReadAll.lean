import LeanExe.Wasi.Interpreter
import LeanExe.Wasi.ReadAll

/-! Native runs of `readAll` against scripted replies: the bytes returned, the errno, and the
reads made, at EOF, at a read error, at and above the limit, and for a limit with no room for its
buffer. -/

open LeanExe LeanExe.Wasi

namespace ReadAllTest

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- A host that answers reads from `replies` in order and records each capacity. -/
private def scripted (replies : IO.Ref (List (Transfer Bytes))) (calls : IO.Ref (Array UInt64)) :
    NativeHost where
  read capacity := do
    calls.modify (·.push capacity)
    match ← replies.get with
    | reply :: rest =>
      replies.set rest
      pure reply
    | [] => throw (IO.userError "readAll made a read after its last reply")
  write _ bytes := pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())

private def bytesOf (count : Nat) (start : Nat := 0) : Bytes :=
  ⟨⟨Array.ofFn (n := count) fun i => UInt8.ofNat (start + i)⟩⟩

/-- Runs `readAll limit` on `replies` and checks its result and its count of reads. -/
private def expect (name : String) (limit : UInt64) (replies : List (Transfer Bytes))
    (errno : UInt64) (bytes : Bytes) (reads : Nat) : IO Unit := do
  let queue ← IO.mkRef replies
  let calls ← IO.mkRef #[]
  match ← (readAll limit).run (scripted queue calls) with
  | .returned result =>
    check (result.errno == errno) s!"{name}: errno {result.errno}, expected {errno}"
    check (result.bytes.data.data == bytes.data.data) s!"{name}: wrong bytes"
  | _ => throw (IO.userError s!"{name}: expected a return")
  let made ← calls.get
  check (made.size == reads) s!"{name}: {made.size} reads, expected {reads}"
  check (made.all (· == 4096)) s!"{name}: a read of capacity other than 4096"

private def chunks (bytes : Bytes) (size : Nat) : List (Transfer Bytes) :=
  let rec go (offset : Nat) (fuel : Nat) : List (Transfer Bytes) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if offset ≥ bytes.data.size then []
      else
        let stop := min bytes.data.size (offset + size)
        .returned 0 ⟨bytes.data.extract offset stop⟩ :: go stop fuel
  go 0 (bytes.data.size + 1)

def main : IO Unit := do
  let eof : Transfer Bytes := .returned 0 Bytes.empty
  expect "empty input" 100 [eof] 0 Bytes.empty 1
  for size in [1, 4095, 4096, 4097, 10000] do
    let input := bytesOf size
    for chunk in [1, 1024, 4096] do
      let replies := chunks input chunk ++ [eof]
      expect s!"{size} bytes in reads of {chunk}" 10000 replies 0 input replies.length
  let input := bytesOf 10001
  expect "limit plus one in reads of 4096" 10000 (chunks input 4096) 0 input 3
  expect "limit plus one in reads of 1" 10000 (chunks input 1) 0 input 10001
  let over := bytesOf 12288
  expect "a read past the limit" 10000 (chunks over 4096) 0 over 3
  expect "a read error after bytes" 10000
    [.returned 0 (bytesOf 3), .returned 0 (bytesOf 2 3), .returned 29 Bytes.empty] 29
    (bytesOf 5) 3
  expect "a read error first" 10000 [.returned 31 Bytes.empty] 31 Bytes.empty 1
  expect "no room for the buffer" 4294963200 [] 61 Bytes.empty 0
  expect "the largest limit" 4294963199 [eof] 0 Bytes.empty 1
  let queue ← IO.mkRef [.returned 0 (bytesOf 7), .trapped "host trap" Bytes.empty]
  let calls ← IO.mkRef #[]
  match ← (readAll 100).run (scripted queue calls) with
  | .trapped message => check (message == "host trap") "trap message"
  | _ => throw (IO.userError "expected a trap")
  IO.println "readAll native cases passed"

end ReadAllTest

def main : IO Unit := ReadAllTest.main
