import LeanExe.Core
import LeanExe.Extract.Report
import LeanExe.Examples.AsciiDigits
import LeanExe.Examples.Collatz
import LeanExe.Wasm.Binary

namespace LeanExe.CLI

def usage : String :=
  String.intercalate "\n" [
    "lean-wasm commands:",
    "  lean-wasm emit --out <path>",
    "  lean-wasm wat --out <path>",
    "  lean-wasm report --out <path>",
    "  lean-wasm report --module <module> --entry <name>",
    "  lean-wasm report --module <module> --entry <name> --out <path>",
    "  lean-wasm eval --hex <hex-bytes>",
    "  lean-wasm collatz-emit --out <path>",
    "  lean-wasm collatz-wat --out <path>",
    "  lean-wasm collatz-eval --input <n>",
    "",
    "This prototype supports LeanExe.Examples.AsciiDigits.validate only."
  ]

def ensureParent (path : System.FilePath) : IO Unit := do
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()

def writeText (path : String) (content : String) : IO Unit := do
  let file := System.FilePath.mk path
  ensureParent file
  IO.FS.writeFile file content

def writeBytes (path : String) (content : ByteArray) : IO Unit := do
  let file := System.FilePath.mk path
  ensureParent file
  IO.FS.writeBinFile file content

def extractionReport : String :=
  String.intercalate "\n" [
    "LeanExe extraction report",
    "",
    "entry: LeanExe.Examples.AsciiDigits.validate",
    "shape: ByteArray -> Bool",
    "status: accepted",
    "",
    "accepted declarations:",
    "- LeanExe.Examples.AsciiDigits.isAsciiDigit",
    "- LeanExe.Examples.AsciiDigits.validate",
    "- LeanExe.Examples.AsciiDigits.WellFormed",
    "- LeanExe.Core.asciiDigits",
    "- LeanExe.Core.lower",
    "",
    "proofs present in Lean:",
    "- LeanExe.Examples.AsciiDigits.validate_sound",
    "- LeanExe.Examples.AsciiDigits.validate_complete",
    "- LeanExe.Examples.AsciiDigits.validate_spec",
    "- LeanExe.Core.asciiDigits_correct",
    "- LeanExe.Core.eraseProofs_eval",
    "- LeanExe.Core.lower_correct",
    "",
    "emitted Wasm exports:",
    "- memory",
    "- alloc(len: i32) -> i32",
    "- reset()",
    "- validate(ptr: i32, len: i32) -> i32",
    "",
    "unsupported in this prototype:",
    "- arbitrary Lean environment extraction",
    "- dependency graph traversal",
    "- polymorphism beyond this closed validator",
    "- typeclass specialization",
    "- higher-order values",
    "- IO, unsafe code, reflection, and FFI",
    ""
  ]

def hexVal? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 <= n ∧ n <= 57 then
    some (n - 48)
  else if 65 <= n ∧ n <= 70 then
    some (n - 55)
  else if 97 <= n ∧ n <= 102 then
    some (n - 87)
  else
    none

partial def parseHexLoop : List Char → Array UInt8 → Except String (Array UInt8)
  | [], acc => .ok acc
  | [_], _ => .error "hex input has odd length"
  | hi :: lo :: rest, acc =>
      match hexVal? hi, hexVal? lo with
      | some h, some l =>
          parseHexLoop rest (acc.push (UInt8.ofNat (h * 16 + l)))
      | none, _ => .error s!"invalid hex digit: {hi}"
      | _, none => .error s!"invalid hex digit: {lo}"

def parseHex (s : String) : Except String ByteArray :=
  match parseHexLoop s.toList #[] with
  | .ok bytes => .ok (ByteArray.mk bytes)
  | .error error => .error error

def boolCode (b : Bool) : String :=
  if b then "1" else "0"

def emitAll (out : String) : IO Unit := do
  writeBytes out LeanExe.Wasm.Binary.moduleBytes

def parseNatArg (text : String) : Except String Nat :=
  match text.toNat? with
  | some n => .ok n
  | none => .error s!"invalid natural number: {text}"

def main : List String → IO UInt32
  | ["emit", "--out", out] => do
      emitAll out
      return 0
  | ["wat", "--out", out] => do
      writeText out LeanExe.Wasm.Binary.wat
      return 0
  | ["report", "--out", out] => do
      writeText out extractionReport
      return 0
  | ["report", "--module", moduleName, "--entry", entryName] => do
      IO.println (← LeanExe.Extract.Report.makeReport moduleName entryName)
      return 0
  | ["report", "--module", moduleName, "--entry", entryName, "--out", out] => do
      writeText out (← LeanExe.Extract.Report.makeReport moduleName entryName)
      return 0
  | ["eval", "--hex", hex] => do
      match parseHex hex with
      | .ok input =>
          IO.println (boolCode (LeanExe.Examples.AsciiDigits.validate input))
          return 0
      | .error error =>
          IO.eprintln error
          return 2
  | ["collatz-emit", "--out", out] => do
      writeBytes out LeanExe.Wasm.Binary.collatzModuleBytes
      return 0
  | ["collatz-wat", "--out", out] => do
      writeText out LeanExe.Wasm.Binary.collatzWat
      return 0
  | ["collatz-eval", "--input", input] => do
      match parseNatArg input with
      | .ok n =>
          let steps := LeanExe.Examples.Collatz.steps (UInt64.ofNat n)
          IO.println s!"{steps.toNat}"
          return 0
      | .error error =>
          IO.eprintln error
          return 2
  | ["help"] => do
      IO.println usage
      return 0
  | ["--help"] => do
      IO.println usage
      return 0
  | _ => do
      IO.eprintln usage
      return 2

end LeanExe.CLI
