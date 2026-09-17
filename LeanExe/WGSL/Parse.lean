import LeanExe.WGSL.Lexer
import LeanExe.WGSL.Generate

namespace LeanExe.WGSL

/-- V1's syntax tree has one supported body form. Its grammar is written below
independently of renderGemm: explicit edge guard, source-ordered dot product,
and one row-major store. Other WGSL bodies must be rejected, not abstracted away. -/
inductive GemmBody where
  | guardedRowMajor
  deriving BEq, Repr, DecidableEq

structure GemmSyntax where
  config : GemmConfig
  body : GemmBody
  deriving BEq, Repr

private abbrev Parser := StateT (List String) (Except String)

private def token (expected : String) : Parser Unit := do
  match ← get with
  | actual :: rest =>
      if actual == expected then set rest
      else throw s!"expected {expected}, found {actual}"
  | [] => throw s!"expected {expected}, found end of input"

private def tokens (expected : List String) : Parser Unit :=
  expected.forM token

private def natural (unsigned : Bool := false) : Parser Nat := do
  let actual ← match ← get with
    | t :: rest => set rest; pure t
    | [] => throw "expected decimal integer, found end of input"
  let digits := if unsigned then
      match actual.toList.reverse with
      | 'u' :: rest => String.ofList rest.reverse
      | _ => ""
    else actual
  match digits.toNat? with
  | none => throw s!"invalid decimal integer: {actual}"
  | some n =>
      if actual != toString n ++ (if unsigned then "u" else "") || n > 4294967295 then
        throw s!"noncanonical or out-of-range decimal integer: {actual}"
      return n

private def constant (name : String) : Parser Nat := do
  tokens ["const", name, ":", "u32", "="]
  let n ← natural true
  token ";"
  return n

private def buffer (name access : String) : Parser (Nat × Nat) := do
  tokens ["@", "group", "("]
  let group ← natural
  tokens [")", "@", "binding", "("]
  let binding ← natural
  tokens [")", "var", "<", "storage", ",", access, ">", name, ":",
    "array", "<", "f32", ">", ";"]
  return (group, binding)

/-- Fixed body grammar, independently reviewed against the captured WGSL.
The exact tokens preserve operation order, identifiers, bounds, indices,
zero initialization, loop control and the sole output store. -/
def gemmBodyTokens : List String := [
  "fn", "gemm_f32", "(", "@", "builtin", "(", "global_invocation_id", ")",
  "gid", ":", "vec3", "<", "u32", ">", ")", "{",
  "let", "col", ":", "u32", "=", "gid", ".", "x", ";",
  "let", "row", ":", "u32", "=", "gid", ".", "y", ";",
  "if", "(", "col", ">=", "N", "||", "row", ">=", "M", ")", "{", "return", ";", "}",
  "var", "acc", ":", "f32", "=", "0.0f", ";",
  "for", "(", "var", "k", ":", "u32", "=", "0u", ";", "k", "<", "K", ";",
  "k", "=", "k", "+", "1u", ")", "{",
  "let", "product", ":", "f32", "=", "a", "[", "row", "*", "K", "+", "k", "]",
  "*", "b", "[", "k", "*", "N", "+", "col", "]", ";",
  "acc", "=", "acc", "+", "product", ";", "}",
  "c", "[", "row", "*", "N", "+", "col", "]", "=", "acc", ";", "}"]

private def moduleParser : Parser GemmSyntax := do
  let rows ← constant "M"
  let cols ← constant "N"
  let inner ← constant "K"
  let a ← buffer "a" "read"
  let b ← buffer "b" "read"
  let c ← buffer "c" "read_write"
  if a.1 != b.1 || a.1 != c.1 then throw "GEMM buffers must share a bind group"
  tokens ["@", "compute", "@", "workgroup_size", "("]
  let x ← natural
  token ","
  let y ← natural
  tokens [",", "1", ")"]
  tokens gemmBodyTokens
  if !(← get).isEmpty then throw "trailing tokens after GEMM module"
  let config : GemmConfig := {
    rows := rows
    cols := cols
    inner := inner
    group := a.1
    bindingA := a.2
    bindingB := b.2
    bindingC := c.2
    workgroupX := x
    workgroupY := y
  }
  return ⟨config, .guardedRowMajor⟩

/-- Parses actual source text without consulting a manifest or the renderer.
Successful parsing consumes the complete token stream. -/
def parseGemm (source : String) : Except String GemmSyntax := do
  let ts ← tokenize source
  let (ast, _) ← moduleParser.run ts
  return ast

/-- Parsed syntax plus the explicitly checked resource/index envelope. -/
structure CheckedGemm where
  ast : GemmSyntax
  valid : ast.config.Valid

def checkGemm (source : String) : Except String CheckedGemm := do
  let ast ← parseGemm source
  if h : ast.config.Valid then return ⟨ast, h⟩
  else throw "parsed GEMM exceeds the supported resource/index envelope"

theorem CheckedGemm.config_valid (kernel : CheckedGemm) : kernel.ast.config.Valid :=
  kernel.valid

#print axioms CheckedGemm.config_valid

end LeanExe.WGSL
