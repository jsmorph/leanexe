import Lean.Data.Json
import LeanExe.Scheme.Runtime

open Lean LeanExe.Scheme.Arena LeanExe.Scheme.Runtime

private def member (j : Json) (key : String) : IO Json := IO.ofExcept (j.getObjVal? key)
private def number (j : Json) : IO UInt64 := do
  match j with
  | .str s =>
    match s.toNat? with
    | some n => pure n.toUInt64
    | none => throw <| IO.userError s!"invalid word {s}"
  | _ => return (← IO.ofExcept j.getNat?).toUInt64

def main (args : List String) : IO Unit := do
  let output := args.headD "build/scheme/native.json"
  let corpus ← IO.ofExcept <| Json.parse (← IO.FS.readFile "build/scheme/corpus.json")
  let cases ← IO.ofExcept corpus.getArr?
  let mut results : Array Json := #[]
  for case in cases do
    let name ← IO.ofExcept (← member case "name").getStr?
    let words ← IO.ofExcept (← member case "code").getArr?
    let code ← words.mapM number
    let cap ← number (← member case "capacity")
    let fuel ← number (← member case "fuel")
    let expected ← number (← member case "expected")
    let error ← number (← member case "error")
    let expectedKind ← number (← member case "kind")
    for stress in [0, 1] do
      let s := run code (init cap stress) fuel
      if read s 15 != error || (error == 0 && (read s 0 != 3 ||
          kind s (read s 7) != expectedKind || resultWord s != expected)) then
        throw <| IO.userError s!"{name}, stress={stress}: phase={read s 0}, error={read s 15}, result={resultWord s}"
      if let .ok counter := case.getObjVal? "counter" then
        let counter ← number counter
        let loc := lookup s (read s 16) 1
        if field s (field s loc 2) 2 != counter then
          throw <| IO.userError s!"{name}: mutation was lost"
      let s := collect s
      if read s 15 != error then throw <| IO.userError s!"{name}: collection changed error"
      results := results.push <| Json.mkObj [
        ("name", toJson name), ("stress", toJson stress.toNat),
        ("state", .arr (s.map fun x => toJson (toString x)))]
      IO.println s!"native {name}, stress={stress}: ok, collections={read s 11}, peak={read s 13}/{cap}"
  IO.FS.writeFile output (Json.pretty (.arr results))
  IO.println s!"native: {results.size} cases passed"
