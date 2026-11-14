import LeanExe.Wasi.CallTable

/-! The expectations of the rejection sweep against `Call.reject`.  Each line that
`uv run tools/wasi-calls.py --reject-sweep DIR` prints is `MODULE trap|errno CALL ARG...`, with
`w:N` for a word, `b:HEX` for an input, and `s:N` for the capacity of an output, the arguments of
the module's call.  The program computes `Call.reject` of those arguments for the description named
`CALL` and requires it to be nonzero exactly on the lines marked `trap`.  It fails on a line that it
cannot read and on a call without a description in `calls`, so a description that the list lacks
fails the run when the sweep reaches it.
Usage: lake env lean --run tests/wasi/SysSweep.lean FILE -/

open LeanExe LeanExe.Wasi

namespace SysSweep

/-- The descriptions of `LeanExe/Wasi/CallTable.lean`. -/
def calls : List Call :=
  [.argsGet, .argsSizesGet, .environGet, .environSizesGet, .clockResGet, .clockTimeGet, .fdAdvise,
   .fdAllocate, .fdClose, .fdDatasync, .fdFdstatGet, .fdFdstatSetFlags, .fdFdstatSetRights,
   .fdFilestatGet, .fdFilestatSetSize, .fdFilestatSetTimes, .fdPrestatGet, .fdPrestatDirName,
   .fdReaddir, .fdRenumber, .fdSeek, .fdSync, .fdTell, .pathCreateDirectory, .pathFilestatGet,
   .pathFilestatSetTimes, .pathLink, .pathOpen, .pathReadlink, .pathRemoveDirectory, .pathRename,
   .pathSymlink, .pathUnlinkFile, .procRaise, .schedYield, .randomGet, .sockAccept, .sockShutdown]

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes? : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
    let high ← hexDigit? high
    let low ← hexDigit? low
    let rest ← hexBytes? rest
    pure ((16 * high + low).toUInt8 :: rest)
  | [_] => none

def word? (text : String) : Option UInt64 := do
  let value ← text.toNat?
  if value < 2 ^ 64 then some (UInt64.ofNat value) else none

def arg? (token : String) : Option Arg :=
  match token.splitOn ":" with
  | ["w", value] => (word? value).map .word
  | ["s", value] => (word? value).map .space
  | ["b", hex] => (hexBytes? hex.toList).map fun bytes => .bytes ⟨⟨bytes.toArray⟩⟩
  | _ => none

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lake env lean --run tests/wasi/SysSweep.lean FILE"
      return 2
  let mut checked := 0
  for line in (← IO.FS.lines path) do
    let name :: expected :: callName :: tokens := line.splitOn " "
      | IO.eprintln s!"unreadable line: {line}"
        return 1
    let some call := calls.find? (·.name == callName)
      | IO.eprintln s!"{name}: no description named {callName}"
        return 1
    let some arguments := tokens.mapM arg?
      | IO.eprintln s!"{name}: unreadable arguments"
        return 1
    let errno := call.reject arguments
    unless (expected == "trap" && errno != 0) || (expected == "errno" && errno == 0) do
      IO.eprintln s!"{name}: the sweep expects {expected}, and Call.reject gives {errno}"
      return 1
    checked := checked + 1
  if checked == 0 then
    IO.eprintln "the sweep list is empty"
    return 1
  IO.println s!"rejection sweep expectations agree with Call.reject: {checked}"
  return 0

end SysSweep

def main (args : List String) : IO UInt32 := SysSweep.main args
