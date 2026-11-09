import TestSupport.M7.Delim

/-!
The Lean side of `tests/baremetal/delim_frame.py check`: `lake env lean --run
tests/baremetal/DelimMirror.lean CASES OUT` reads the cases that `delim_frame.py gen` wrote, one a
line, and writes for each the answer of the Lean definitions: `ok HEX` or `none`.  A line
`enc HEX` asks for `cobsEncode` of the bytes, `dec HEX` for `cobsDecode`, and `ans HEX` for
`delimAnswers echoMach 36 0`.
-/

open LeanExe.Requests TestSupport.M7.Delim

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

/-- The answer of the Lean definitions to one case. -/
def answer (line : String) : Except String String := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  let (kind, hex) ← match ws with
    | [k] => pure (k, "")
    | [k, h] => pure (k, h)
    | _ => throw s!"not a case: {line}"
  let some bs := parseHex hex.toList | throw s!"not hexadecimal: {line}"
  match kind with
  | "enc" => return "ok " ++ hexOf (cobsEncode bs)
  | "dec" => return match cobsDecode bs with
      | some r => "ok " ++ hexOf r
      | none => "none"
  | "ans" => return "ok " ++ hexOf (delimAnswers echoMach 36 0 bs)
  | _ => throw s!"no case kind {kind}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [cases, out] =>
      let lines ← IO.FS.lines cases
      let mut res : Array String := #[]
      for line in lines do
        if line.all Char.isWhitespace then continue
        match answer line with
        | .ok a => res := res.push a
        | .error e =>
            IO.eprintln s!"DelimMirror: {e}"
            return 1
      IO.FS.writeFile out (String.join (res.toList.map (· ++ "\n")))
      return 0
  | _ =>
      IO.eprintln "usage: lake env lean --run tests/baremetal/DelimMirror.lean CASES OUT"
      return 2
