import Demos.Bms.Stream

/-!
The native replay of the logs of `tests/baremetal/uart_bms.py` against the specification of
`Demos/Bms/Spec.lean`.  `bms-replay PREFIX` reads `PREFIX.in`, one line for each write of the
bridge in hexadecimal or the line `reset` at a board reset, and `PREFIX.out`, one line for each
answer that the board sent, its encoding and its `0x00` in hexadecimal, with `reset` at each board
reset.  For each part of `PREFIX.in` between `reset` lines it computes
`delimAnswers machine maxSegment init` of the part's bytes, the encoded answers of the
specification's machine to the part's non-empty segments, from the state after a board reset,
and it writes each answer and its `0x00` as one line, with `reset` between the parts.  The
result must equal `PREFIX.out` line for line.  The command prints the number of answers and exits
with status 0 when every line agrees, and it prints the first difference and exits with status 1
otherwise.  The bytes after the last `0x00` of a part form no segment and get no answer.
-/

namespace TestSupport.Bms.Replay

open LeanExe.Requests Demos.Bms.Spec

/-- The bytes as hexadecimal digits, two to a byte. -/
def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let d := Nat.toDigits 16 b.toNat
    String.ofList (if d.length < 2 then '0' :: d else d))

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes of a string of hexadecimal digits. -/
def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let x ← hexDigit a
      let y ← hexDigit b
      let r ← parseHex rest
      return UInt8.ofNat (16 * x + y) :: r
  | _ => none

/-- The lines of the answers to the bytes `bs` from a board reset: each encoded answer and its
`0x00`. -/
def answerLines (bs : List UInt8) : List String :=
  (segments (delimAnswers machine maxSegment init bs)).map fun s => hexOf (s ++ [0])

/-- The parts of the lines of `PREFIX.in` between `reset` lines, each as its bytes. -/
def parts (lines : List String) : Except String (List (List UInt8)) := do
  let mut done : Array (List UInt8) := #[]
  let mut cur : Array UInt8 := #[]
  for line in lines do
    if line = "reset" then
      done := done.push cur.toList
      cur := #[]
    else
      match parseHex line.toList with
      | some bs => cur := cur ++ bs.toArray
      | none => throw s!"not hexadecimal: {line}"
  return (done.push cur.toList).toList

/-- The lines that the replay gives for the parts `ps`. -/
def replayLines (ps : List (List UInt8)) : List String :=
  (ps.map answerLines).intersperse ["reset"] |>.flatten

/-- The lines of a file without blank lines. -/
def readLines (path : String) : IO (List String) := do
  let lines ← IO.FS.lines path
  return (lines.toList.map String.trimAscii |>.map (·.toString)).filter (· ≠ "")

def main (args : List String) : IO UInt32 := do
  match args with
  | [pre] =>
      let ins ← readLines (pre ++ ".in")
      let outs ← readLines (pre ++ ".out")
      match parts ins with
      | .error e =>
          IO.eprintln s!"bms-replay: {pre}.in: {e}"
          return 1
      | .ok ps =>
          let lean := replayLines ps
          let pairs := (lean.zip outs).zipIdx
          match pairs.find? (fun ((l, o), _) => l ≠ o) with
          | some ((l, o), i) =>
              IO.eprintln s!"bms-replay: line {i + 1} of {pre}.out is {o}, and Lean gives {l}"
              return 1
          | none =>
              if lean.length ≠ outs.length then
                IO.eprintln (s!"bms-replay: {pre}.out has {outs.length} lines, and Lean " ++
                  s!"gives {lean.length}")
                return 1
              let n := (outs.filter (· ≠ "reset")).length
              IO.println (s!"bms-replay: {n} answers in {ps.length} parts equal to Lean's " ++
                s!"replay of {pre}.in")
              return 0
  | _ =>
      IO.eprintln "usage: bms-replay PREFIX"
      return 2

end TestSupport.Bms.Replay

def main (args : List String) : IO UInt32 := TestSupport.Bms.Replay.main args
