import Project.WGSL.Syntax

/-!
The printed form of a kernel: a list of tokens, rendered with one separator between consecutive
tokens, a newline after `;`, `{`, and `}` and a space elsewhere.  Every number is eight
hexadecimal digits: a literal is `0x` and the digits followed by `u`, a variable `v` and the
digits, and a buffer `b` and the digits.  Every binary expression is parenthesized, so the
printed text never depends on operator precedence.
-/

namespace Project.WGSL

def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The eight hexadecimal digits of `n % 2^32`, most significant first. -/
def digits8 (n : Nat) : List Char :=
  [7, 6, 5, 4, 3, 2, 1, 0].map fun k => hexDigit (n / 16 ^ k % 16)

def litToken (value : UInt32) : String := String.ofList ('0' :: 'x' :: digits8 value.toNat ++ ['u'])

def varToken (index : Nat) : String := String.ofList ('v' :: digits8 index)

def bufToken (index : Nat) : String := String.ofList ('b' :: digits8 index)

def BinOp.token : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .lt => "<"
  | .le => "<="
  | .eq => "=="
  | .and => "&&"
  | .or => "||"

def Ty.tokens : Ty → List String
  | .u32 => ["u32"]
  | .f32 => ["f32"]
  | .bool => ["bool"]
  | .vec2u => ["vec2", "<", "u32", ">"]

def Expr.tokens : Expr → List String
  | .lit value => [litToken value]
  | .bool true => ["true"]
  | .bool false => ["false"]
  | .var n => [varToken n]
  | .gidX => ["gid", ".", "x"]
  | .fst n => [varToken n, ".", "x"]
  | .snd n => [varToken n, ".", "y"]
  | .vec2 low high => ["vec2", "<", "u32", ">", "("] ++ low.tokens ++ [","] ++ high.tokens ++ [")"]
  | .bin op left right => ["("] ++ left.tokens ++ [op.token] ++ right.tokens ++ [")"]
  | .not operand => ["!"] ++ operand.tokens
  | .toF32 operand => ["bitcast", "<", "f32", ">", "("] ++ operand.tokens ++ [")"]
  | .toU32 operand => ["bitcast", "<", "u32", ">", "("] ++ operand.tokens ++ [")"]
  | .sqrt operand => ["sqrt", "("] ++ operand.tokens ++ [")"]
  | .round operand => ["round", "("] ++ operand.tokens ++ [")"]
  | .abs operand => ["abs", "("] ++ operand.tokens ++ [")"]
  | .select f t c => ["select", "("] ++ f.tokens ++ [","] ++ t.tokens ++ [","] ++ c.tokens ++ [")"]
  | .min left right => ["min", "("] ++ left.tokens ++ [","] ++ right.tokens ++ [")"]
  | .length buffer => ["arrayLength", "(", "&", bufToken buffer, ")"]
  | .index buffer position => [bufToken buffer, "["] ++ position.tokens ++ ["]"]

mutual
  def Stmt.tokens : Stmt → List String
    | .let_ n type value =>
        ["let", varToken n, ":"] ++ type.tokens ++ ["="] ++ value.tokens ++ [";"]
    | .var n type value =>
        ["var", varToken n, ":"] ++ type.tokens ++ ["="] ++ value.tokens ++ [";"]
    | .assign n value => [varToken n, "="] ++ value.tokens ++ [";"]
    | .store buffer position value =>
        [bufToken buffer, "["] ++ position.tokens ++ ["]", "="] ++ value.tokens ++ [";"]
    | .ite condition thenStmts elseStmts =>
        ["if"] ++ condition.tokens ++ ["{"] ++ Stmt.listTokens thenStmts ++ ["}", "else", "{"] ++
          Stmt.listTokens elseStmts ++ ["}"]
    | .while_ condition body =>
        ["while"] ++ condition.tokens ++ ["{"] ++ Stmt.listTokens body ++ ["}"]
    | .ret => ["return", ";"]

  def Stmt.listTokens : List Stmt → List String
    | [] => []
    | s :: rest => s.tokens ++ Stmt.listTokens rest
end

/-- The declaration of buffer `index`, read-only or read-write. -/
def bufferTokens (index : Nat) (writable : Bool) : List String :=
  ["@", "group", "(", litToken 0, ")", "@", "binding", "(", litToken (UInt32.ofNat index), ")",
    "var", "<", "storage", ",", if writable then "read_write" else "read", ">", bufToken index,
    ":", "array", "<", "u32", ">", ";"]

def inputTokens : Nat → List String
  | 0 => []
  | n + 1 => inputTokens n ++ bufferTokens n false

def Module.tokens (m : Module) : List String :=
  inputTokens m.inputs ++ bufferTokens m.inputs true ++
    ["@", "compute", "@", "workgroup_size", "(", litToken (UInt32.ofNat m.workgroupSize), ")",
      "fn", "main", "(", "@", "builtin", "(", "global_invocation_id", ")", "gid", ":", "vec3",
      "<", "u32", ">", ")", "{"] ++ Stmt.listTokens m.body ++ ["}"]

/-- The separator after a token: a newline after `;`, `{`, and `}`, and otherwise a space. -/
def separator (token : String) : Char :=
  if token = ";" ∨ token = "{" ∨ token = "}" then '\n' else ' '

def renderChars : List String → List Char
  | [] => []
  | [t] => t.toList ++ ['\n']
  | t :: rest => t.toList ++ separator t :: renderChars rest

/-- The text of a kernel. -/
def Module.print (m : Module) : String := String.ofList (renderChars m.tokens)

end Project.WGSL
