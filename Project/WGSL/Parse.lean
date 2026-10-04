import Project.WGSL.Print

/-!
The parser of the printed kernel format.  The lexer splits the text at spaces and newlines and
drops empty pieces.  A token is a literal (`0x`, eight hexadecimal digits, `u`), a variable (`v`
and eight digits), a buffer (`b` and eight digits), or a keyword or punctuation token.  The parser
reads exactly the printer's forms, with fuel that bounds the depth of recursion.
-/

namespace Project.WGSL

def isSeparator (c : Char) : Bool := c = ' ' || c = '\n'

def lex (text : String) : List String :=
  ((text.toList.splitOnP isSeparator).filter (· ≠ [])).map String.ofList

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else none

/-- The value of eight hexadecimal digits, most significant first. -/
def digitsValue : List Char → Option Nat
  | [d7, d6, d5, d4, d3, d2, d1, d0] => do
      let v7 ← hexValue d7
      let v6 ← hexValue d6
      let v5 ← hexValue d5
      let v4 ← hexValue d4
      let v3 ← hexValue d3
      let v2 ← hexValue d2
      let v1 ← hexValue d1
      let v0 ← hexValue d0
      pure (((((((v7 * 16 + v6) * 16 + v5) * 16 + v4) * 16 + v3) * 16 + v2) * 16 + v1) * 16 + v0)
  | _ => none

def parseLit (token : String) : Option UInt32 :=
  match token.toList with
  | '0' :: 'x' :: [d7, d6, d5, d4, d3, d2, d1, d0, 'u'] =>
      (digitsValue [d7, d6, d5, d4, d3, d2, d1, d0]).map UInt32.ofNat
  | _ => none

def parseName (letter : Char) (token : String) : Option Nat :=
  match token.toList with
  | c :: digits => if c = letter then digitsValue digits else none
  | [] => none

/-- What a token is. -/
inductive Head where
  | lit (value : UInt32)
  | var (index : Nat)
  | buf (index : Nat)
  | kw (token : String)

def classify (token : String) : Head :=
  match parseLit token with
  | some v => .lit v
  | none =>
    match parseName 'v' token with
    | some n => .var n
    | none =>
      match parseName 'b' token with
      | some n => .buf n
      | none => .kw token

def expect (token : String) : List String → Option (List String)
  | t :: rest => if t = token then some rest else none
  | [] => none

def parseOp (token : String) : Option BinOp :=
  match token with
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "/" => some .div
  | "<" => some .lt
  | "<=" => some .le
  | "==" => some .eq
  | "&&" => some .and
  | "||" => some .or
  | _ => none

def parseExpr : Nat → List String → Option (Expr × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
    match classify t with
    | .lit v => some (.lit v, rest)
    | .var n =>
        match rest with
        | "." :: "x" :: rest' => some (.fst n, rest')
        | "." :: "y" :: rest' => some (.snd n, rest')
        | _ => some (.var n, rest)
    | .buf n => do
        let rest ← expect "[" rest
        let (p, rest) ← parseExpr fuel rest
        let rest ← expect "]" rest
        pure (.index n p, rest)
    | .kw k =>
      match k, rest with
      | "(", rest => do
          let (a, rest) ← parseExpr fuel rest
          let op :: rest := rest | none
          let op ← parseOp op
          let (b, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.bin op a b, rest)
      | "!", rest => do
          let (a, rest) ← parseExpr fuel rest
          pure (.not a, rest)
      | "true", rest => some (.bool true, rest)
      | "false", rest => some (.bool false, rest)
      | "gid", "." :: "x" :: rest => some (.gidX, rest)
      | "vec2", "<" :: "u32" :: ">" :: "(" :: rest => do
          let (a, rest) ← parseExpr fuel rest
          let rest ← expect "," rest
          let (b, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.vec2 a b, rest)
      | "bitcast", "<" :: "f32" :: ">" :: "(" :: rest => do
          let (a, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.toF32 a, rest)
      | "bitcast", "<" :: "u32" :: ">" :: "(" :: rest => do
          let (a, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.toU32 a, rest)
      | "sqrt", "(" :: rest => do
          let (a, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.sqrt a, rest)
      | "abs", "(" :: rest => do
          let (a, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.abs a, rest)
      | "select", "(" :: rest => do
          let (f, rest) ← parseExpr fuel rest
          let rest ← expect "," rest
          let (t, rest) ← parseExpr fuel rest
          let rest ← expect "," rest
          let (c, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.select f t c, rest)
      | "min", "(" :: rest => do
          let (a, rest) ← parseExpr fuel rest
          let rest ← expect "," rest
          let (b, rest) ← parseExpr fuel rest
          let rest ← expect ")" rest
          pure (.min a b, rest)
      | "arrayLength", "(" :: "&" :: b :: ")" :: rest => do
          let .buf n := classify b | none
          pure (.length n, rest)
      | _, _ => none

def parseTy : List String → Option (Ty × List String)
  | "u32" :: rest => some (.u32, rest)
  | "f32" :: rest => some (.f32, rest)
  | "bool" :: rest => some (.bool, rest)
  | "vec2" :: "<" :: "u32" :: ">" :: rest => some (.vec2u, rest)
  | _ => none

mutual
  /-- One statement. -/
  def parseStmt : Nat → List String → Option (Stmt × List String)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, t :: rest =>
      match classify t with
      | .var n => do
          let rest ← expect "=" rest
          let (e, rest) ← parseExpr fuel rest
          let rest ← expect ";" rest
          pure (.assign n e, rest)
      | .buf n => do
          let rest ← expect "[" rest
          let (p, rest) ← parseExpr fuel rest
          let rest ← expect "]" rest
          let rest ← expect "=" rest
          let (e, rest) ← parseExpr fuel rest
          let rest ← expect ";" rest
          pure (.store n p e, rest)
      | .lit _ => none
      | .kw k =>
        match k, rest with
        | "let", v :: ":" :: rest => do
            let .var n := classify v | none
            let (ty, rest) ← parseTy rest
            let rest ← expect "=" rest
            let (e, rest) ← parseExpr fuel rest
            let rest ← expect ";" rest
            pure (.let_ n ty e, rest)
        | "var", v :: ":" :: rest => do
            let .var n := classify v | none
            let (ty, rest) ← parseTy rest
            let rest ← expect "=" rest
            let (e, rest) ← parseExpr fuel rest
            let rest ← expect ";" rest
            pure (.var n ty e, rest)
        | "if", rest => do
            let (c, rest) ← parseExpr fuel rest
            let rest ← expect "{" rest
            let (ts, rest) ← parseStmts fuel rest
            let rest ← expect "}" rest
            let rest ← expect "else" rest
            let rest ← expect "{" rest
            let (es, rest) ← parseStmts fuel rest
            let rest ← expect "}" rest
            pure (.ite c ts es, rest)
        | "return", ";" :: rest => some (.ret, rest)
        | _, _ => none

  /-- Statements up to a closing `}`, which stays in the remaining tokens. -/
  def parseStmts : Nat → List String → Option (List Stmt × List String)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, t :: rest =>
      if t = "}" then some ([], t :: rest)
      else do
        let (s, rest') ← parseStmt fuel (t :: rest)
        let (ss, rest'') ← parseStmts fuel rest'
        pure (s :: ss, rest'')
end

/-- The declarations of buffers `i` and later: read-only ones, then the read-write one, whose
binding gives the number of inputs. -/
def parseBuffers : Nat → Nat → List String → Option (Nat × List String)
  | 0, _, _ => none
  | fuel + 1, i, ts =>
    if (bufferTokens i false).isPrefixOf ts then
      parseBuffers fuel (i + 1) (ts.drop (bufferTokens i false).length)
    else if (bufferTokens i true).isPrefixOf ts then
      some (i, ts.drop (bufferTokens i true).length)
    else none

def parseModule (ts : List String) : Option Module := do
  let fuel := ts.length + 1
  let (inputs, rest) ← parseBuffers fuel 0 ts
  let "@" :: "compute" :: "@" :: "workgroup_size" :: "(" :: size :: ")" :: "fn" :: "main" :: "(" ::
    "@" :: "builtin" :: "(" :: "global_invocation_id" :: ")" :: "gid" :: ":" :: "vec3" :: "<" ::
    "u32" :: ">" :: ")" :: "{" :: rest := rest | none
  let .lit size := classify size | none
  let (body, rest) ← parseStmts fuel rest
  let ["}"] := rest | none
  pure { inputs, workgroupSize := size.toNat, body }

/-- The kernel a text holds. -/
def Module.parse (text : String) : Option Module := parseModule (lex text)

end Project.WGSL
