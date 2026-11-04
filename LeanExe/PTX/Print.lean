import LeanExe.PTX.Syntax

/-!
The printed form of a kernel: a list of tokens, rendered with one separator between consecutive
tokens, a newline after `;`, `{`, `}`, a label's `:`, and the values of the header directives,
and a space elsewhere.  Registers are `%w`, `%d`, and `%p` followed by eight hexadecimal digits,
parameters `b` and eight digits, and labels `$L` and eight digits.  A 32-bit immediate is `0x` and
eight digits, and a 64-bit immediate `0x` and sixteen.  A guard is one token, `@%p...` or
`@!%p...`.  The printer numbers labels with a counter in the order of the statements: a
conditional takes two labels, for its else part and its end, and so does a loop, for its head and
its end.
-/

namespace LeanExe.PTX

def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The `n` lowest hexadecimal digits of `v`, most significant first. -/
def hexDigits (n v : Nat) : List Char :=
  ((List.range n).reverse).map fun k => hexDigit (v / 16 ^ k % 16)

/-- A name: the characters `pre` and eight hexadecimal digits of `index`. -/
def nameToken (pre : List Char) (index : Nat) : String := String.ofList (pre ++ hexDigits 8 index)

def w32Token (i : Nat) : String := nameToken ['%', 'w'] i
def w64Token (i : Nat) : String := nameToken ['%', 'd'] i
def fToken (i : Nat) : String := nameToken ['%', 'f'] i
def predToken (i : Nat) : String := nameToken ['%', 'p'] i
def paramToken (i : Nat) : String := nameToken ['b'] i
def labelToken (i : Nat) : String := nameToken ['$', 'L'] i

def imm32Token (v : UInt32) : String := String.ofList ('0' :: 'x' :: hexDigits 8 v.toNat)
def imm64Token (v : UInt64) : String := String.ofList ('0' :: 'x' :: hexDigits 16 v.toNat)

def Src64.token : Src64 → String
  | .reg i => w64Token i
  | .imm v => imm64Token v

def Src32.token : Src32 → String
  | .reg i => w32Token i
  | .imm v => imm32Token v

def SrcF.token : SrcF → String
  | .reg i => fToken i
  | .imm v => imm32Token v

def Special.token : Special → String
  | .tidX => "%tid.x"
  | .ntidX => "%ntid.x"
  | .ctaidX => "%ctaid.x"

def Bin64.token : Bin64 → String
  | .add => "add.u64"
  | .sub => "sub.u64"
  | .mulLo => "mul.lo.u64"
  | .div => "div.u64"
  | .rem => "rem.u64"
  | .and => "and.b64"
  | .or => "or.b64"
  | .xor => "xor.b64"

def Shift.token : Shift → String
  | .shl => "shl.b64"
  | .shr => "shr.b64"

def BinF.token : BinF → String
  | .add => "add.rn.f32"
  | .sub => "sub.rn.f32"
  | .mul => "mul.rn.f32"
  | .div => "div.rn.f32"

def CmpF.token : CmpF → String
  | .eq => "setp.eq.f32"
  | .lt => "setp.lt.f32"
  | .le => "setp.le.f32"

def Cmp.token : Cmp → String
  | .eq => "setp.eq.u64"
  | .ne => "setp.ne.u64"
  | .lt => "setp.lt.u64"
  | .le => "setp.le.u64"

/-- The tokens of an address `[ a + imm ]`. -/
def addressTokens (a : Nat) (imm : UInt64) : List String :=
  ["[", w64Token a, "+", imm64Token imm, "]"]

def Instr.tokens : Instr → List String
  | .special d s => ["mov.u32", w32Token d, ",", s.token, ";"]
  | .mov32 d a => ["mov.b32", w32Token d, ",", a.token, ";"]
  | .mov64 d a => ["mov.b64", w64Token d, ",", a.token, ";"]
  | .bin64 op d a b => [op.token, w64Token d, ",", w64Token a, ",", b.token, ";"]
  | .shift op d a b => [op.token, w64Token d, ",", w64Token a, ",", b.token, ";"]
  | .setp c p a b => [c.token, predToken p, ",", w64Token a, ",", b.token, ";"]
  | .selp d t f p => ["selp.b64", w64Token d, ",", t.token, ",", f.token, ",", predToken p, ";"]
  | .notPred d a => ["not.pred", predToken d, ",", predToken a, ";"]
  | .widen d a => ["cvt.u64.u32", w64Token d, ",", w32Token a, ";"]
  | .narrow d a => ["cvt.u32.u64", w32Token d, ",", w64Token a, ";"]
  | .madWide d a b c =>
      ["mad.wide.u32", w64Token d, ",", w32Token a, ",", w32Token b, ",", w64Token c, ";"]
  | .ldParam d j => ["ld.param.u64", w64Token d, ",", "[", paramToken j, "]", ";"]
  | .cvtaGlobal d a => ["cvta.to.global.u64", w64Token d, ",", w64Token a, ";"]
  | .ld d a imm => ["ld.global.u64", w64Token d, ","] ++ addressTokens a imm ++ [";"]
  | .st a imm v => ["st.global.u64"] ++ addressTokens a imm ++ [",", w64Token v, ";"]
  | .binF op d a b => [op.token, fToken d, ",", fToken a, ",", fToken b, ";"]
  | .sqrtF d a => ["sqrt.rn.f32", fToken d, ",", fToken a, ";"]
  | .rniF d a => ["cvt.rni.f32.f32", fToken d, ",", fToken a, ";"]
  | .setpF c p a b => [c.token, predToken p, ",", fToken a, ",", fToken b, ";"]
  | .testNaN p a => ["testp.notanumber.f32", predToken p, ",", fToken a, ";"]
  | .selpF d t f p => ["selp.b32", fToken d, ",", t.token, ",", f.token, ",", predToken p, ";"]
  | .toF d a => ["mov.b32", fToken d, ",", w32Token a, ";"]
  | .ofF d a => ["mov.b32", w32Token d, ",", fToken a, ";"]

def Guard.token (g : Guard) : String :=
  nameToken (if g.negated then ['@', '!', '%', 'p'] else ['@', '%', 'p']) g.pred

/-- A branch to label `target` when predicate `p` does not hold. -/
def branchUnless (p target : Nat) : List String :=
  [Guard.token ⟨true, p⟩, "bra", labelToken target, ";"]

mutual
  /-- The tokens of a statement whose labels are numbered from `n`, and the next label number. -/
  def Stmt.tokens (n : Nat) : Stmt → List String × Nat
    | .instr none i => (i.tokens, n)
    | .instr (some g) i => (g.token :: i.tokens, n)
    | .ite p ts es =>
        let t := Stmt.listTokens (n + 2) ts
        let e := Stmt.listTokens t.2 es
        (branchUnless p n ++ t.1 ++ ["bra", labelToken (n + 1), ";", labelToken n, ":"] ++ e.1 ++
          [labelToken (n + 1), ":"], e.2)
    | .while_ cond p body =>
        let c := Stmt.listTokens (n + 2) cond
        let b := Stmt.listTokens c.2 body
        ([labelToken n, ":"] ++ c.1 ++ branchUnless p (n + 1) ++ b.1 ++
          ["bra", labelToken n, ";", labelToken (n + 1), ":"], b.2)
    | .ret => (["ret", ";"], n)

  def Stmt.listTokens (n : Nat) : List Stmt → List String × Nat
    | [] => ([], n)
    | s :: rest =>
        let t := Stmt.tokens n s
        let r := Stmt.listTokens t.2 rest
        (t.1 ++ r.1, r.2)
end

/-- The parameters `i` to `i + k`, separated by commas. -/
def paramTokens (i : Nat) : Nat → List String
  | 0 => [".param", ".u64", paramToken i]
  | k + 1 => [".param", ".u64", paramToken i, ","] ++ paramTokens (i + 1) k

/-- The declarations of `k` registers of a class, from register `i`. -/
def regDecls (cls : String) (name : Nat → String) (i : Nat) : Nat → List String
  | 0 => []
  | k + 1 => [".reg", cls, name i, ";"] ++ regDecls cls name (i + 1) k

def Module.tokens (m : Module) : List String :=
  [".version", "7.0", ".target", "sm_80", ".address_size", "64", ".visible", ".entry", "main",
    "("] ++ paramTokens 0 m.inputs ++ [")", "{"] ++ regDecls ".b32" w32Token 0 m.regs32 ++
    regDecls ".b64" w64Token 0 m.regs64 ++ regDecls ".f32" fToken 0 m.regsF ++
    regDecls ".pred" predToken 0 m.preds ++
    (Stmt.listTokens 0 m.body).1 ++ ["ret", ";", "}"]

/-- The separator after a token. -/
def separator (token : String) : Char :=
  if token = ";" ∨ token = "{" ∨ token = "}" ∨ token = ":" ∨ token = "7.0" ∨ token = "sm_80" ∨
      token = "64" then '\n'
  else ' '

def renderChars : List String → List Char
  | [] => []
  | [t] => t.toList ++ ['\n']
  | t :: rest => t.toList ++ separator t :: renderChars rest

/-- The text of a kernel. -/
def Module.print (m : Module) : String := String.ofList (renderChars m.tokens)

end LeanExe.PTX
