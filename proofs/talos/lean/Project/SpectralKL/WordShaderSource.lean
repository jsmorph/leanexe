import Project.SpectralKL.WordShader

namespace Project.SpectralKL.WordShader

def tokenizeChars : List Char → List Char → List String
  | [],[] => []
  | [],token => [String.ofList token.reverse]
  | c::cs,token =>
    if c = ' ' ∨ c = '\n' then
      if token = [] then tokenizeChars cs []
      else String.ofList token.reverse::tokenizeChars cs []
    else tokenizeChars cs (c::token)

def tokenize (s : String) : List String := tokenizeChars s.toList []

def consume (expected input : List String) : Option (List String) :=
  if input.take expected.length = expected then some (input.drop expected.length) else none

def parseVar : String → Option Var
  | "row" => some .row | "entry" => some .entry | "params.width" => some .width
  | "lo" => some .lo | "hi" => some .hi | "old" => some .old | "term" => some .term
  | _ => none

def parseOp : String → Option Op
  | "+" => some .add | "-" => some .sub | "*" => some .mul
  | "/" => some .div | "%" => some .mod | _ => none

/-- Parser for the fully parenthesized u32 expression subset emitted by the kernel.
No expression text is skipped or treated as an uninterpreted annotation. -/
def parseExpr : Nat → List String → Option (Expr × List String)
  | 0,_ => none
  | fuel+1,tokens => do
    match tokens with
    | "("::rest =>
      let (a,rest) ← parseExpr fuel rest
      let op::rest := rest | none
      let op ← parseOp op
      let (b,rest) ← parseExpr fuel rest
      let rest ← consume [")"] rest
      return (.bin op a b,rest)
    | "samples"::"["::rest =>
      let (i,rest) ← parseExpr fuel rest
      let rest ← consume ["]"] rest
      return (.load i,rest)
    | "select"::rest =>
      let rest ← consume ["(","0u",",","1u",",","("] rest
      let (a,rest) ← parseExpr fuel rest
      let rest ← consume ["<"] rest
      let (b,rest) ← parseExpr fuel rest
      let rest ← consume [")",")"] rest
      return (.carry a b,rest)
    | token::rest =>
      if let some v := parseVar token then return (.var v,rest)
      else
        if !token.endsWith "u" then none else do
          let n ← token.dropEnd 1 |>.toString.toNat?
          if n ≥ 4294967296 then none else return (.lit (UInt32.ofNat n),rest)
    | [] => none

/-- The surrounding declarations, entry guard, increasing loop, bindings, and
output write must match the supported kernel form exactly. -/
def parseTokens (tokens : List String) : Option Program := do
  let rest ← consume preamble tokens
  let (meanTerm,rest) ← parseExpr 64 rest
  let rest ← consume middle1 rest
  let (productTerm,rest) ← parseExpr 64 rest
  let rest ← consume middle2 rest
  let (nextLo,rest) ← parseExpr 64 rest
  let rest ← consume middle3 rest
  let (nextHi,rest) ← parseExpr 64 rest
  let rest ← consume suffix rest
  if rest = [] then some ⟨meanTerm,productTerm,nextLo,nextHi⟩ else none

def parseProgram (source : String) : Option Program := parseTokens (tokenize source)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem tokens_parse : parseTokens kernel.tokens = some kernel := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem source_tokenizes : tokenize kernel.source = kernel.tokens := by
  simp only [tokenize,Program.source,String.toList_ofList]
  decide +kernel

theorem source_parses : parseProgram kernel.source = some kernel := by
  rw [parseProgram,source_tokenizes,tokens_parse]

/-- Execution semantics for the parsed kernel subset. The WebGPU compiler and
device are trusted to implement WGSL's integer and dispatch semantics. -/
def runSource (source : String) (input : Nat → UInt32) (width entry count entries : UInt32) :
    Option WordMoments.Sum64 := do
  let p ← parseProgram source
  if entry < entries then return run p input width entry count else none

theorem source_run (input : Nat → UInt32) (width entry count entries : UInt32) (ha : entry < entries) :
    runSource kernel.source input width entry count entries = some (run kernel input width entry count) := by
  simp [runSource,source_parses,ha]

theorem source_sum (input : Nat → UInt32) (width entry count entries : UInt32)
    (h : count.toNat ≤ 1048576) (ha : entry < entries) :
    (runSource kernel.source input width entry count entries).map WordMoments.Sum64.value =
      some (((List.range count.toNat).map fun r => (termAt kernel input width entry (UInt32.ofNat r)).toNat).sum) := by
  rw [source_run input width entry count entries ha]
  simp only [Option.map_some,run_value input width entry count h]

theorem source_inactive (input : Nat → UInt32) (width entry count entries : UInt32)
    (ha : ¬ entry < entries) : runSource kernel.source input width entry count entries = none := by
  simp [runSource,source_parses,ha]

#print axioms source_parses
#print axioms source_sum
end Project.SpectralKL.WordShader
