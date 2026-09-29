import Lean.Data.Json
import Interpreter.Wasm.Decoder.Wat
import Project.Encoding
import Project.Encoding.Decode

/-!
Runs `Wasm.Encoding.decode` over the modules that `wasm-tools json-from-wast`
extracts from the official testsuite.

For each `module` command whose binary lies in the decoder's subset, the decoded
module must equal the module that Talos's WAT decoder reads from `wasm-tools print`
of the same file, and `decode (encode m)` must return `m` when `encode m` succeeds.
Every binary `assert_malformed` module must be rejected.

Usage: `lean --run DecodeTest.lean <wasm-tools> <json-directory>`
-/

open Lean

namespace Wasm.Encoding.DecodeTest

structure Tally where
  accepted : Nat := 0
  matched : Nat := 0
  roundTrips : Nat := 0
  outsideEncoder : Nat := 0
  unsupported : Nat := 0
  watUnavailable : Nat := 0
  malformedRejected : Nat := 0
  malformedUnsupported : Nat := 0
  failures : Array String := #[]

def Tally.fail (tally : Tally) (message : String) : Tally :=
  { tally with failures := tally.failures.push message }

/-- The fields of a module that the binary format determines. -/
def binaryView (m : Wasm.Module) : String :=
  toString <| repr
    (m.types,
     m.imports.map (fun i => (i.module, i.name, i.params, i.results)),
     m.funcs.map (fun f => (f.params, f.locals, f.body, f.results)),
     m.memory.map (fun d => (d.pagesMin, d.pagesMax)),
     m.globals.map (fun g => (g.init, g.isMut)),
     m.exports.map (fun e => (e.name, e.funcIdx)),
     m.globalExports, m.memoryExports)

def wasmTools (tool : String) (args : Array String) : IO (Except String String) := do
  let out ← IO.Process.output { cmd := tool, args }
  pure <| if out.exitCode = 0 then .ok out.stdout else .error out.stderr

/-- The module Talos's testsuite runner builds from a binary file. -/
def watModule (tool : String) (path : System.FilePath) : IO (Except String Wasm.Module) := do
  let stripped := path.toString ++ ".stripped"
  match ← wasmTools tool #["strip", "--all", path.toString, "-o", stripped] with
  | .error message => pure (.error message)
  | .ok _ =>
      match ← wasmTools tool #["print", stripped] with
      | .error message => pure (.error message)
      | .ok text => pure (Wasm.Decoder.Wat.decode text)

def checkValid (tool : String) (path : System.FilePath) (tally : Tally) : IO Tally := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error (.unsupported _) => pure { tally with unsupported := tally.unsupported + 1 }
  | .error error => pure (tally.fail s!"{path}: valid module rejected: {repr error}")
  | .ok m =>
      let mut tally := { tally with accepted := tally.accepted + 1 }
      match ← watModule tool path with
      | .ok w =>
          if binaryView w == binaryView m then
            tally := { tally with matched := tally.matched + 1 }
          else
            tally := tally.fail s!"{path}: decoded module differs from the WAT path"
      | .error _ => tally := { tally with watUnavailable := tally.watUnavailable + 1 }
      match encode m with
      | .error _ => pure { tally with outsideEncoder := tally.outsideEncoder + 1 }
      | .ok encoded =>
          match decode encoded with
          | .ok back =>
              if toString (repr back) == toString (repr m) then
                pure { tally with roundTrips := tally.roundTrips + 1 }
              else pure (tally.fail s!"{path}: decode (encode m) differs from m")
          | .error error => pure (tally.fail s!"{path}: encoded module rejected: {repr error}")

def checkMalformed (path : System.FilePath) (tally : Tally) : IO Tally := do
  match decode (← IO.FS.readBinFile path) with
  | .ok _ => pure (tally.fail s!"{path}: malformed module accepted")
  | .error (.unsupported _) =>
      pure { tally with malformedUnsupported := tally.malformedUnsupported + 1 }
  | .error _ => pure { tally with malformedRejected := tally.malformedRejected + 1 }

def checkScript (tool : String) (directory jsonPath : System.FilePath) (tally : Tally) :
    IO Tally := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile jsonPath)
  let commands ← IO.ofExcept <| json.getObjValAs? (Array Json) "commands"
  let mut tally := tally
  for command in commands do
    let kind := (command.getObjValAs? String "type").toOption.getD ""
    let file := (command.getObjValAs? String "filename").toOption.getD ""
    let moduleType := (command.getObjValAs? String "module_type").toOption.getD "binary"
    if file.endsWith ".wasm" then
      if kind == "module" then
        tally ← checkValid tool (directory / file) tally
      else if kind == "assert_malformed" && moduleType == "binary" then
        tally ← checkMalformed (directory / file) tally
  pure tally

def main : List String → IO UInt32
  | [tool, directoryText] => do
      let directory : System.FilePath := directoryText
      let scripts := (← directory.readDir).filter (·.path.extension == some "json")
      let mut tally : Tally := {}
      for entry in scripts.qsort (·.fileName < ·.fileName) do
        tally ← checkScript tool directory entry.path tally
      IO.println s!"valid modules decoded: {tally.accepted}"
      IO.println s!"  equal to the WAT path: {tally.matched}"
      IO.println s!"  WAT path unavailable: {tally.watUnavailable}"
      IO.println s!"  decode (encode m) = m: {tally.roundTrips}"
      IO.println s!"  outside the encoder's domain: {tally.outsideEncoder}"
      IO.println s!"valid modules outside the decoder's subset: {tally.unsupported}"
      IO.println s!"malformed modules rejected: {tally.malformedRejected}"
      IO.println s!"malformed modules outside the subset: {tally.malformedUnsupported}"
      IO.println s!"failures: {tally.failures.size}"
      for failure in tally.failures.toList.take 40 do
        IO.println s!"  {failure}"
      pure (if tally.failures.isEmpty then 0 else 1)
  | _ => do
      IO.eprintln "usage: DecodeTest.lean <wasm-tools> <json-directory>"
      pure 2

end Wasm.Encoding.DecodeTest

def main (args : List String) : IO UInt32 := Wasm.Encoding.DecodeTest.main args
