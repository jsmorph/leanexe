import LeanExe.WGSL.Statement
import LeanExe.WGSL.Lexer

/-! Independent parser for the structured shader grammar. It reads actual
WGSL tokens; it does not call the emitter or accept an expected source body.
Bindings and loops are retained as statements, with local names resolved to
slots. The parser checks the initializer, test, increment, sole accumulator
assignment and scope of each loop. -/
namespace LeanExe.WGSL.Source
open Statement

private abbrev P := StateT (List String) (Except String)
private abbrev Words := List String
private abbrev Indices := List String

private def take : P String := do
  match ← get with
  | x :: xs => set xs; pure x
  | [] => throw "unexpected end of shader"

private def token (expected : String) : P Unit := do
  let actual ← take
  unless actual == expected do throw s!"expected {expected}, found {actual}"

private def tokens (expected : List String) : P Unit := expected.forM token

private def natural (unsigned : Bool := true) : P Nat := do
  let raw ← take
  let digits := if unsigned then
      match raw.toList.reverse with
      | 'u' :: rest => rest.reverse
      | _ => []
    else raw.toList
  unless !digits.isEmpty && digits.all (fun c => '0' ≤ c && c ≤ '9') do
    throw s!"invalid decimal literal {raw}"
  if digits.length > 1 && digits.head? == some '0' then throw "noncanonical leading zero"
  let n := digits.foldl (fun n c => n * 10 + (c.toNat - 48)) (0 : Nat)
  if n > 4294967295 then throw "literal exceeds u32"
  pure n

private def lookupWord (env : Words) (name : String) : P Nat :=
  match env.idxOf? name with
  | some slot => pure slot
  | none => throw s!"undefined word {name}"

private def identifier : P String := do
  let name ← take
  let digits := if name.startsWith "acc" then name.toList.drop 3
    else if name.startsWith "v" || name.startsWith "k" then name.toList.drop 1 else []
  unless !digits.isEmpty && digits.all (fun c => '0' ≤ c && c ≤ '9') do
    throw s!"unsupported local identifier {name}; expected v, k or acc followed by digits"
  pure name

private def fresh (words : Words) (indices : Indices) : P String := do
  let name ← identifier
  if words.contains name || indices.contains name then throw s!"duplicate local {name}"
  pure name

private def parseIndex : Nat → Indices → P Index
  | 0, _ => throw "index parser fuel exhausted"
  | fuel + 1, env => do
      match (← get).head? with
      | some "(" =>
          token "("
          let a ← parseIndex fuel env
          let op ← take
          let b ← parseIndex fuel env
          token ")"
          if op == "+" then return .add a b
          if op == "*" then return .mul a b
          throw s!"unsupported index operator {op}"
      | some "row" => token "row"; pure .row
      | some "col" => token "col"; pure .col
      | some name =>
          if let some i := env.idxOf? name then token name; pure (.local i)
          else pure (.lit (← natural))
      | none => throw "expected index expression"

private def rhs (words : Words) (indices : Indices) : P Prim := do
  let first ← take
  if first == "bitcast" then
    tokens ["<", "f32", ">", "("]
    let word ← natural
    token ")"
    return .literal (UInt32.ofNat word)
  if first == "a" || first == "b" then
    token "["
    let i ← parseIndex (← get).length indices
    token "]"
    return if first == "a" then .loadA i else .loadB i
  let a ← lookupWord words first
  match (← get).head? with
  | some "+" => token "+"; return .add a (← lookupWord words (← take))
  | some "*" => token "*"; return .mul a (← lookupWord words (← take))
  | _ => pure (.copy a)

private def statements : Nat → Words → Indices → Option String → P Code
  | 0, _, _, _ => throw "statement parser fuel exhausted"
  | fuel + 1, words, indices, finish => do
      let first ← take
      if first == "let" then
        let name ← fresh words indices
        tokens [":", "f32", "="]
        let value ← rhs words indices
        token ";"
        return .bind value (← statements fuel (name :: words) indices finish)
      if first == "var" then
        let acc ← fresh words indices
        tokens [":", "f32", "="]
        let initial ← lookupWord words (← take)
        tokens [";", "for", "(", "var"]
        let k ← fresh (acc :: words) indices
        tokens [":", "u32", "=", "0u", ";", k, "<"]
        let count ← natural
        tokens [";", k, "=", k, "+", "1u", ")", "{"]
        let innerWords := acc :: words
        let innerIndices := k :: indices
        let body ← statements fuel innerWords innerIndices (some acc)
        return .loop count initial body (← statements fuel (acc :: words) indices finish)
      else
        match finish with
        | some acc =>
            unless first == acc do throw s!"expected loop accumulator assignment to {acc}"
            token "="
            let value ← lookupWord words (← take)
            tokens [";", "}"]
            pure (.finish value)
        | none =>
            unless first == "c" do throw "expected the sole output store"
            tokens ["[", "row", "*", "N", "+", "col", "]", "="]
            let value ← lookupWord words (← take)
            tokens [";", "}"]
            pure (.finish value)

structure Parsed where
  rows : Nat
  cols : Nat
  code : Code
  deriving Repr, BEq, DecidableEq

def Parsed.body (parsed : Parsed) : Term := parsed.code.term

private def moduleP : P Parsed := do
  tokens ["const", "M", ":", "u32", "="]
  let rows ← natural
  tokens [";", "const", "N", ":", "u32", "="]
  let cols ← natural
  token ";"
  for (name, access, binding) in [("a", "read", "0"), ("b", "read", "1"), ("c", "read_write", "2")] do
    tokens ["@", "group", "(", "0", ")", "@", "binding", "(", binding, ")",
      "var", "<", "storage", ",", access, ">", name, ":", "array", "<", "f32", ">", ";"]
  tokens ["@", "compute", "@", "workgroup_size", "(", "8", ",", "8", ",", "1", ")",
    "fn", "lean_kernel", "(", "@", "builtin", "(", "global_invocation_id", ")",
    "gid", ":", "vec3", "<", "u32", ">", ")", "{",
    "let", "col", ":", "u32", "=", "gid", ".", "x", ";",
    "let", "row", ":", "u32", "=", "gid", ".", "y", ";",
    "if", "(", "col", ">=", "N", "||", "row", ">=", "M", ")", "{", "return", ";", "}"]
  let body ← statements (← get).length [] [] none
  unless (← get).isEmpty do throw "trailing tokens after kernel"
  pure ⟨rows, cols, body⟩

def parseTokens (ts : List String) : Except String Parsed := do
  let (parsed, _) ← moduleP.run ts
  pure parsed

def parse (shader : String) : Except String Parsed := do
  parseTokens (← tokenize shader)

theorem ok_of_toOption (result : Except String α) (value : α)
    (h : result.toOption = some value) : result = .ok value := by
  cases result with
  | error message => cases h
  | ok actual => cases h; rfl

/-- Keep character scanning and token interpretation as separately checked
reductions, so artifact proofs need not repeatedly reduce the whole pipeline. -/
theorem parse_of_tokens (shader : String) (ts : List String) (parsed : Parsed)
    (lexed : tokenize shader = .ok ts) (body : parseTokens ts = .ok parsed) :
    parse shader = .ok parsed := by
  unfold parse
  rw [lexed]
  exact body

end LeanExe.WGSL.Source
