import LeanExe.WGSL.UInt

/-! Independent parser for the emitted integer subset. It checks declarations,
bindings, dispatch guard, all expressions, unique SSA locals, output ownership,
and end-of-file. It does not invoke the shader emitter. -/
namespace LeanExe.WGSL.UInt

/-- Structural decimal parser, following the existing WGSL parser. Keeping
slice iterators out of proof reduction makes each token kernel-computable. -/
def decimal : List Char → Option Nat
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | chars =>
    if chars.all (fun c => '0' ≤ c && c ≤ '9') then
      some (chars.foldl (fun n c => n*10 + (c.toNat-48)) 0)
    else none

def word? (text : String) : Option Nat := do
  let 'u' :: reversed := text.toList.reverse | none
  let n ← decimal reversed.reverse
  if n < modulus then some n else none

/-- Canonical emitted local names also exclude WGSL keywords such as `var`. -/
def localName (name : String) : Bool :=
  match name.toList with
  | 'v' :: digits => (decimal digits).isSome
  | _ => false

abbrev Locals := List (String × Expr)

def lookup (locals : Locals) (name : String) : Option Expr :=
  (locals.find? (fun p => p.1 == name)).map Prod.snd

def rhs? (locals : Locals) : List String → Option Expr
  | [literal] => Expr.lit <$> word? literal
  | [buffer, "[", index, "]"] => do
    let n ← word? index
    if buffer == "scene" && n < 16 then some (.read .scene n)
    else if buffer == "params" && n < 4 then some (.read .params n) else none
  | ["directions", "[", "gid", ".", "x", "]"] => some .direction
  | [a, "+", b] => return .add (← lookup locals a) (← lookup locals b)
  | [a, "*", b] => return .mul (← lookup locals a) (← lookup locals b)
  | ["max", "(", a, ",", b, ")", "-", c] => do
    if b != c then none else return .sub (← lookup locals a) (← lookup locals b)
  | ["min", "(", a, ",", b, ")"] => return .min (← lookup locals a) (← lookup locals b)
  | ["select", "(", "0u", ",", "1u", ",", a, "<=", b, ")"] =>
    return .le (← lookup locals a) (← lookup locals b)
  | ["select", "(", "0u", ",", "1u", ",", a, "==", b, ")"] =>
    return .eq (← lookup locals a) (← lookup locals b)
  | ["select", "(", "0u", ",", "1u", ",", "(", a, "!=", "0u", ")", "&&",
      "(", b, "!=", "0u", ")", ")"] =>
    return .both (← lookup locals a) (← lookup locals b)
  | ["select", "(", no, ",", yes, ",", c, "!=", "0u", ")"] =>
    return .choose (← lookup locals c) (← lookup locals yes) (← lookup locals no)
  | _ => none

def body? : Nat → Locals → List String → Option Expr
  | 0, _, _ => none
  | fuel+1, locals, "let" :: name :: ":" :: "u32" :: "=" :: rest => do
    if (lookup locals name).isSome || !(localName name) then none else do
      let value ← rhs? locals (rest.takeWhile (· != ";"))
      let rest ← (rest.dropWhile (· != ";")).tail?
      body? fuel ((name,value)::locals) rest
  | _+1, locals, ["results", "[", "gid", ".", "x", "]", "=", name, ";", "}"] => lookup locals name
  | _, _, _ => none

def header : String :=
  "@group(0) @binding(0) var<storage, read> scene: array<u32>; " ++
  "@group(0) @binding(1) var<storage, read> directions: array<u32>; " ++
  "@group(0) @binding(2) var<storage, read> params: array<u32>; " ++
  "@group(0) @binding(3) var<storage, read_write> results: array<u32>; " ++
  "@compute @workgroup_size(4) " ++
  "fn lidar(@builtin(global_invocation_id) gid: vec3<u32>) { " ++
  "if (gid.x >= 4u) { return; }"

def parseTokens (tokens : List String) : Option Expr := do
  let headerTokens ← tokenize header |>.toOption
  if tokens.take headerTokens.length != headerTokens then none
  else body? tokens.length [] (tokens.drop headerTokens.length)

def parse (source : String) : Option Expr := do
  let tokens ← tokenize source |>.toOption
  parseTokens tokens

end LeanExe.WGSL.UInt
