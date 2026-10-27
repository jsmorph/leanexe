import Demos.RunningSum.Program

open Demos.RunningSum

private def lineWords (text : String) : Array UInt64 :=
  text.toUTF8.data.map UInt8.toUInt64

private def requireParsed (text : String) : IO Decimal := do
  let parsed := parse (lineWords text)
  if !parsed.valid then
    throw (IO.userError s!"Running sum rejected {text}")
  return parsed.value

private def checkValue (text : String) (expected : Int) : IO Unit := do
  let value ← requireParsed text
  let actual := (render value).data
  let wanted := (toString expected ++ "\n").toUTF8
  if actual != wanted then
    throw (IO.userError s!"Running sum rendered {text} as {String.fromUTF8! actual}")

private def checkAdd (left right expected : String) : IO Unit := do
  let a ← requireParsed left
  let b ← requireParsed right
  let actual := (render (add a b)).data
  if actual != (expected ++ "\n").toUTF8 then
    throw (IO.userError s!"Running sum failed {left} + {right}")

def main : IO Unit := do
  for (text, value) in
      [("0", 0), ("-0", 0), ("+000", 0), ("00012", 12), ("-00012\r", -12),
        ("+12\r", 12), ("123456789012345678901234567890", 123456789012345678901234567890)] do
    checkValue text value
  for text in ["", "\r", "+", "-", "+\r", " 1", "1 ", "1\r\r", "1x", "1\n", "é"] do
    if (parse (lineWords text)).valid then
      throw (IO.userError s!"Running sum accepted invalid input {text}")
  let nines := String.ofList (List.replicate 5000 '9')
  let power := "1" ++ String.ofList (List.replicate 5000 '0')
  checkAdd nines "1" power
  checkAdd power "-1" nines
  checkAdd ("-" ++ nines) "-1" ("-" ++ power)
  checkAdd nines ("-" ++ nines) "0"
  let mut seed : UInt64 := 17
  for _ in [:4000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let a : Int := if seed >>> 63 == 0 then seed.toNat else -(seed.toNat : Int)
    seed := seed * 6364136223846793005 + 1442695040888963407
    let b : Int := if seed >>> 63 == 0 then seed.toNat else -(seed.toNat : Int)
    checkAdd (toString a) (toString b) (toString (a + b))
  IO.println "Running sum arithmetic: 4022 cases passed"
