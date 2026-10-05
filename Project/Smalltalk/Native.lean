import Lean.Data.Json
import LeanExe.Smalltalk.Runtime
open Lean LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

private def member (j : Json) (key : String) : IO Json := IO.ofExcept (j.getObjVal? key)
private def number (j : Json) : IO UInt64 := do
  let n ← match j with
    | .str text => match text.toNat? with
      | some n => pure n
      | none => throw <| IO.userError s!"invalid word {text}"
    | _ => IO.ofExcept j.getNat?
  if n ≥ 2^64 then throw <| IO.userError "word exceeds UInt64"
  return n.toUInt64
def main (args : List String) : IO Unit := do
  let input := args.headD "build/smalltalk/corpus.json"
  let output := args[1]?.getD "build/smalltalk/native.json"
  let corpus ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let cases ← IO.ofExcept corpus.getArr?
  let mut results : Array Json := #[]
  for test in cases do
    let name ← IO.ofExcept (← member test "name").getStr?
    let code ← (← IO.ofExcept (← member test "code").getArr?).mapM number
    let cap ← number (← member test "capacity")
    let fuel ← number (← member test "fuel")
    let expected ← number (← member test "expected")
    let error ← number (← member test "error")
    let expectedKind ← number (← member test "kind")
    for stress in [0, 1] do
      let s := run code (boot code (init cap stress)) fuel
      if read s 15 != error || (error == 0 && (read s 0 != 3 ||
          kind s (read s 7) != expectedKind || resultWord s != expected)) then
        throw <| IO.userError s!"{name}, stress={stress}: phase={read s 0}, error={read s 15}, result={resultWord s}"
      let s := collect s
      if read s 15 != error then throw <| IO.userError s!"{name}: collection changed error"
      results := results.push <| Json.mkObj [("name", toJson name), ("stress", toJson stress.toNat),
        ("state", .arr (s.map fun x => toJson (toString x)))]
      IO.println s!"native {name} stress={stress}: ok; GC={read s 11}, peak={read s 13}/{cap}"
  IO.FS.writeFile output (Json.pretty (.arr results))
  IO.println s!"native: {results.size} cases passed"
