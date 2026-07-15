import LeanExe.Core
import LeanExe.Extract.Core
import LeanExe.Extract.Eval
import LeanExe.Extract.OwnershipReport
import LeanExe.Extract.Report
import LeanExe.Examples.AsciiDigits
import LeanExe.Examples.Collatz
import LeanExe.Wasm.Binary
import LeanExe.Wasm.Wat

namespace LeanExe.CLI

def usage : String :=
  String.intercalate "\n" [
    "lean-wasm commands:",
    "  lean-wasm emit --out <path>",
    "  lean-wasm wat --out <path>",
    "  lean-wasm report --out <path>",
    "  lean-wasm report --module <module> --entry <name>",
    "  lean-wasm report --module <module> --entry <name> --out <path>",
    "  lean-wasm dump-ir --module <module> --entry <name>",
    "  lean-wasm ownership-report --module <module> --entry <name>",
    "  lean-wasm ownership-report --module <module> --entry <name> --out <path>",
    "  lean-wasm eval --hex <hex-bytes>",
    "  lean-wasm eval-ir --module <module> --entry <name> [arg ...]",
    "  lean-wasm compile --module <module> --entry <name> --out <path>",
    "  lean-wasm compile-wat --module <module> --entry <name> --out <path>",
    "  lean-wasm compile-wasi --module <module> --entry <name> --out <path>",
    "  lean-wasm compile-wasi-stdin --max-input-bytes <n> --module <module> --entry <name> --out <path>",
    "  lean-wasm compile-wasi-stdin-except --max-input-bytes <n> --module <module> --entry <name> --out <path>",
    "  lean-wasm compile-wasi-argv-except --max-args <n> --max-argv-bytes <n> --module <module> --entry <name> --out <path>",
    "  lean-wasm compile-wasi-stdin-argv-except --max-input-bytes <n> --max-args <n> --max-argv-bytes <n> --module <module> --entry <name> --out <path>",
    "  lean-wasm collatz-eval --input <n>",
    "  lean-wasm collatz-bench --input <n> --iters <n>",
    "",
    "LeanExe compiles checked declarations in the subset documented in spec.md."
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

def parseNatArg (option text : String) : Except String Nat :=
  match text.toNat? with
  | some n => .ok n
  | none => .error s!"invalid value for {option}: expected a natural number, got {reprStr text}"

def parseU64Args : List String → Except String (List UInt64)
  | [] => .ok []
  | arg :: rest =>
      match arg.toNat?, parseU64Args rest with
      | some n, .ok values => .ok (UInt64.ofNat n :: values)
      | none, _ => .error s!"invalid eval-ir argument: expected an unsigned integer, got {reprStr arg}"
      | _, .error error => .error error

inductive ErrorKind where
  | usage
  | source
  | io
  | internal

def ErrorKind.label : ErrorKind → String
  | .usage => "usage"
  | .source => "source"
  | .io => "I/O"
  | .internal => "internal"

def ErrorKind.status : ErrorKind → UInt32
  | .usage => 2
  | .source => 3
  | .io => 4
  | .internal => 5

structure Error where
  kind : ErrorKind
  context : String
  detail : String

def Error.render (error : Error) : String :=
  s!"lean-wasm: {error.kind.label}: {error.context}: {error.detail}"

def commandContext (command : String) (fields : List (String × String) := []) : String :=
  String.intercalate ", " <|
    s!"command {reprStr command}" :: fields.map fun field =>
      s!"{field.fst} {reprStr field.snd}"

def commandName (args : List String) : String :=
  args.head?.getD "<none>"

def reportError (error : Error) : IO UInt32 := do
  IO.eprintln error.render
  return error.kind.status

def fail (kind : ErrorKind) (context detail : String) : IO UInt32 := do
  reportError { kind := kind, context := context, detail := detail }

def captureError (kind : ErrorKind) (context : String) (action : IO α) :
    IO (Except Error α) := do
  try
    return .ok (← action)
  catch error =>
    return .error { kind := kind, context := context, detail := toString error }

def writeTextResult (context path content : String) : IO UInt32 := do
  match ← captureError .io context (writeText path content) with
  | .ok _ => return 0
  | .error error => reportError error

def writeBytesResult (context path : String) (content : ByteArray) : IO UInt32 := do
  match ← captureError .io context (writeBytes path content) with
  | .ok _ => return 0
  | .error error => reportError error

def printTextResult (context content : String) : IO UInt32 := do
  match ← captureError .io context (IO.println content) with
  | .ok _ => return 0
  | .error error => reportError error

def compileBytesResult
    (context out : String)
    (compileAction : IO LeanExe.IR.Module)
    (encode : LeanExe.IR.Module → Except String ByteArray) : IO UInt32 := do
  match ← captureError .source context compileAction with
  | .error error => reportError error
  | .ok module_ =>
      match encode module_ with
      | .error detail => fail .internal context detail
      | .ok bytes => writeBytesResult context out bytes

def sourcePrintResult (context : String) (action : IO String) : IO UInt32 := do
  match ← captureError .source context action with
  | .error error => reportError error
  | .ok content => printTextResult context content

def sourceWriteTextResult (context out : String) (action : IO String) : IO UInt32 := do
  match ← captureError .source context action with
  | .error error => reportError error
  | .ok content => writeTextResult context out content

def validateMaxInput (maxInput : Nat) : Except String Unit :=
  if maxInput > LeanExe.Wasm.Binary.CoreWasm.wasiMaxInputBytes then
    .error s!"max input bytes exceeds WASM memory capacity: {maxInput}"
  else
    .ok ()

def validateArgvStorage (maxArgs maxArgBytes : Nat) : Except String Unit :=
  let reserved := LeanExe.Wasm.Binary.CoreWasm.wasiArgvReservedBytes maxArgs maxArgBytes
  if reserved > LeanExe.Wasm.Binary.CoreWasm.wasiMaxReservedBytes then
    .error s!"max argv storage exceeds WASM memory capacity: {reserved}"
  else
    .ok ()

def validateStdinArgvStorage (maxInput maxArgs maxArgBytes : Nat) : Except String Unit :=
  let reserved := LeanExe.Wasm.Binary.CoreWasm.wasiArgvReservedBytes maxArgs maxArgBytes
  if maxInput > LeanExe.Wasm.Binary.CoreWasm.wasiMaxInputBytes then
    .error s!"max input bytes exceeds WASM memory capacity: {maxInput}"
  else if maxInput + 8 + reserved > LeanExe.Wasm.Binary.CoreWasm.wasiMaxReservedBytes then
    .error s!"max stdin and argv storage exceeds WASM memory capacity: {maxInput + 8 + reserved}"
  else
    .ok ()

def dispatch : List String → IO UInt32
  | ["emit", "--out", out] =>
      writeBytesResult (commandContext "emit" [("output", out)]) out
        LeanExe.Wasm.Binary.moduleBytes
  | ["wat", "--out", out] =>
      writeTextResult (commandContext "wat" [("output", out)]) out LeanExe.Wasm.Binary.wat
  | ["report", "--out", out] =>
      writeTextResult (commandContext "report" [("output", out)]) out extractionReport
  | ["report", "--module", moduleName, "--entry", entryName] =>
      sourcePrintResult
        (commandContext "report" [("module", moduleName), ("entry", entryName)])
        (LeanExe.Extract.Report.makeReport moduleName entryName)
  | ["report", "--module", moduleName, "--entry", entryName, "--out", out] =>
      sourceWriteTextResult
        (commandContext "report"
          [("module", moduleName), ("entry", entryName), ("output", out)])
        out
        (LeanExe.Extract.Report.makeReport moduleName entryName)
  | ["dump-ir", "--module", moduleName, "--entry", entryName] =>
      sourcePrintResult
        (commandContext "dump-ir" [("module", moduleName), ("entry", entryName)])
        (LeanExe.Extract.OwnershipReport.makeIRDump moduleName entryName)
  | ["ownership-report", "--module", moduleName, "--entry", entryName] =>
      sourcePrintResult
        (commandContext "ownership-report" [("module", moduleName), ("entry", entryName)])
        (LeanExe.Extract.OwnershipReport.makeReport moduleName entryName)
  | ["ownership-report", "--module", moduleName, "--entry", entryName, "--out", out] =>
      sourceWriteTextResult
        (commandContext "ownership-report"
          [("module", moduleName), ("entry", entryName), ("output", out)])
        out
        (LeanExe.Extract.OwnershipReport.makeReport moduleName entryName)
  | ["eval", "--hex", hex] => do
      let context := commandContext "eval"
      match parseHex hex with
      | .ok input =>
          printTextResult context (boolCode (LeanExe.Examples.AsciiDigits.validate input))
      | .error detail => fail .usage context detail
  | "eval-ir" :: "--module" :: moduleName :: "--entry" :: entryName :: rest => do
      let context := commandContext "eval-ir" [("module", moduleName), ("entry", entryName)]
      match parseU64Args rest with
      | .error detail => fail .usage context detail
      | .ok args =>
          match ← captureError .source context
              (LeanExe.Extract.Eval.evalEntry moduleName entryName args) with
          | .error error => reportError error
          | .ok (.outsideFragment reason) => fail .source context reason
          | .ok (.results values) => do
              let printValues : IO Unit := do
                for value in values do
                  IO.println s!"{value.toNat}"
              match ← captureError .io context printValues with
              | .ok _ => return 0
              | .error error => reportError error
  | ["compile", "--module", moduleName, "--entry", entryName, "--out", out] =>
      compileBytesResult
        (commandContext "compile"
          [("module", moduleName), ("entry", entryName), ("output", out)])
        out
        (LeanExe.Extract.Core.compile moduleName entryName)
        (fun module_ => .ok (LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_))
  | ["compile-wat", "--module", moduleName, "--entry", entryName, "--out", out] =>
      sourceWriteTextResult
        (commandContext "compile-wat"
          [("module", moduleName), ("entry", entryName), ("output", out)])
        out
        (LeanExe.Wasm.Wat.moduleWat <$> LeanExe.Extract.Core.compile moduleName entryName)
  | ["compile-wasi", "--module", moduleName, "--entry", entryName, "--out", out] =>
      compileBytesResult
        (commandContext "compile-wasi"
          [("module", moduleName), ("entry", entryName), ("output", out)])
        out
        (LeanExe.Extract.Core.compileProgram moduleName entryName)
        LeanExe.Wasm.Binary.CoreWasm.wasiModuleBytes
  | ["compile-wasi-stdin", "--max-input-bytes", maxInput, "--module", moduleName,
      "--entry", entryName, "--out", out] => do
      let context := commandContext "compile-wasi-stdin"
        [("module", moduleName), ("entry", entryName), ("output", out)]
      match parseNatArg "--max-input-bytes" maxInput with
      | .error detail => fail .usage context detail
      | .ok maxBytes =>
          match validateMaxInput maxBytes with
          | .error detail => fail .usage context detail
          | .ok _ =>
              compileBytesResult context out
                (LeanExe.Extract.Core.compileStdinProgram moduleName entryName)
                (LeanExe.Wasm.Binary.CoreWasm.wasiStdinModuleBytes maxBytes)
  | ["compile-wasi-stdin-except", "--max-input-bytes", maxInput, "--module", moduleName,
      "--entry", entryName, "--out", out] => do
      let context := commandContext "compile-wasi-stdin-except"
        [("module", moduleName), ("entry", entryName), ("output", out)]
      match parseNatArg "--max-input-bytes" maxInput with
      | .error detail => fail .usage context detail
      | .ok maxBytes =>
          match validateMaxInput maxBytes with
          | .error detail => fail .usage context detail
          | .ok _ =>
              compileBytesResult context out
                (LeanExe.Extract.Core.compileStdinExceptProgram moduleName entryName)
                (LeanExe.Wasm.Binary.CoreWasm.wasiStdinExceptModuleBytes maxBytes)
  | ["compile-wasi-argv-except", "--max-args", maxArgs, "--max-argv-bytes", maxArgBytes,
      "--module", moduleName, "--entry", entryName, "--out", out] => do
      let context := commandContext "compile-wasi-argv-except"
        [("module", moduleName), ("entry", entryName), ("output", out)]
      match parseNatArg "--max-args" maxArgs, parseNatArg "--max-argv-bytes" maxArgBytes with
      | .error detail, _ => fail .usage context detail
      | _, .error detail => fail .usage context detail
      | .ok maxArgsValue, .ok maxArgBytesValue =>
          match validateArgvStorage maxArgsValue maxArgBytesValue with
          | .error detail => fail .usage context detail
          | .ok _ =>
              let entry := LeanExe.Extract.Env.parseName entryName
              compileBytesResult context out
                (LeanExe.Extract.Core.compileArgvExceptProgram moduleName entryName)
                (LeanExe.Wasm.Binary.CoreWasm.wasiArgvExceptModuleBytes
                  maxArgsValue maxArgBytesValue entry)
  | ["compile-wasi-stdin-argv-except", "--max-input-bytes", maxInput, "--max-args", maxArgs,
      "--max-argv-bytes", maxArgBytes, "--module", moduleName, "--entry", entryName,
      "--out", out] => do
      let context := commandContext "compile-wasi-stdin-argv-except"
        [("module", moduleName), ("entry", entryName), ("output", out)]
      match parseNatArg "--max-input-bytes" maxInput, parseNatArg "--max-args" maxArgs,
          parseNatArg "--max-argv-bytes" maxArgBytes with
      | .error detail, _, _ => fail .usage context detail
      | _, .error detail, _ => fail .usage context detail
      | _, _, .error detail => fail .usage context detail
      | .ok maxInputValue, .ok maxArgsValue, .ok maxArgBytesValue =>
          match validateStdinArgvStorage maxInputValue maxArgsValue maxArgBytesValue with
          | .error detail => fail .usage context detail
          | .ok _ =>
              let entry := LeanExe.Extract.Env.parseName entryName
              compileBytesResult context out
                (LeanExe.Extract.Core.compileStdinArgvExceptProgram moduleName entryName)
                (LeanExe.Wasm.Binary.CoreWasm.wasiStdinArgvExceptModuleBytes
                  maxInputValue maxArgsValue maxArgBytesValue entry)
  | ["collatz-eval", "--input", input] => do
      let context := commandContext "collatz-eval"
      match parseNatArg "--input" input with
      | .ok n =>
          let steps := LeanExe.Examples.Collatz.steps (UInt64.ofNat n)
          printTextResult context s!"{steps.toNat}"
      | .error detail => fail .usage context detail
  | ["collatz-bench", "--input", input, "--iters", iters] => do
      let context := commandContext "collatz-bench"
      match parseNatArg "--input" input, parseNatArg "--iters" iters with
      | .ok n, .ok count =>
          let result := LeanExe.Examples.Collatz.bench (UInt64.ofNat n) (UInt64.ofNat count)
          printTextResult context s!"{result.toNat}"
      | .error detail, _ => fail .usage context detail
      | _, .error detail => fail .usage context detail
  | ["help"] => printTextResult (commandContext "help") usage
  | ["--help"] => printTextResult (commandContext "--help") usage
  | args =>
      fail .usage (commandContext (commandName args)) ("invalid command or arguments\n" ++ usage)

def main (args : List String) : IO UInt32 := do
  try
    dispatch args
  catch error =>
    fail .internal (commandContext (commandName args)) (toString error)

end LeanExe.CLI
