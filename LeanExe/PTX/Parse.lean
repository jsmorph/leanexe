import LeanExe.PTX.Print

/-!
The parser of the printed kernel format.  The lexer splits the text at spaces and newlines and
drops empty pieces.  The parser reads exactly the printer's forms.  A statement list ends at an
unguarded `bra`, at a guarded `bra` or a label whose number is not the next label number, or at
the final `ret ; }` of the kernel.  A conditional starts with a guarded `bra` to the next label
number, and a loop with the next label number and `:`.
-/

namespace LeanExe.PTX

def isSeparator (c : Char) : Bool := c = ' ' || c = '\n'

def lex (text : String) : List String :=
  ((text.toList.splitOnP isSeparator).filter (· ≠ [])).map String.ofList

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else none

/-- The value of hexadecimal digits, most significant first. -/
def hexNum : List Char → Option Nat
  | [] => some 0
  | c :: cs => do
      let d ← hexValue c
      let r ← hexNum cs
      pure (d * 16 ^ cs.length + r)

/-- The number in a token made of the characters `pre` and `n` hexadecimal digits. -/
def parseNum (pre : List Char) (n : Nat) (t : String) : Option Nat :=
  if pre.isPrefixOf t.toList ∧ t.toList.length = pre.length + n then
    hexNum (t.toList.drop pre.length)
  else none

def w32Idx (t : String) : Option Nat := parseNum ['%', 'w'] 8 t
def w64Idx (t : String) : Option Nat := parseNum ['%', 'd'] 8 t
def fIdx (t : String) : Option Nat := parseNum ['%', 'f'] 8 t
def predIdx (t : String) : Option Nat := parseNum ['%', 'p'] 8 t
def paramIdx (t : String) : Option Nat := parseNum ['b'] 8 t
def imm32 (t : String) : Option UInt32 := (parseNum ['0', 'x'] 8 t).map UInt32.ofNat
def imm64 (t : String) : Option UInt64 := (parseNum ['0', 'x'] 16 t).map UInt64.ofNat

def parseSrc64 (t : String) : Option Src64 :=
  match w64Idx t with
  | some i => some (.reg i)
  | none => (imm64 t).map .imm

def parseSrc32 (t : String) : Option Src32 :=
  match w32Idx t with
  | some i => some (.reg i)
  | none => (imm32 t).map .imm

def parseSrcF (t : String) : Option SrcF :=
  match fIdx t with
  | some i => some (.reg i)
  | none => (imm32 t).map .imm

def parseGuard (t : String) : Option Guard :=
  match parseNum ['@', '%', 'p'] 8 t with
  | some p => some ⟨false, p⟩
  | none => (parseNum ['@', '!', '%', 'p'] 8 t).map fun p => ⟨true, p⟩

def parseSpecial : String → Option Special
  | "%tid.x" => some .tidX
  | "%ntid.x" => some .ntidX
  | "%ctaid.x" => some .ctaidX
  | _ => none

def parseBin64 : String → Option Bin64
  | "add.u64" => some .add
  | "sub.u64" => some .sub
  | "mul.lo.u64" => some .mulLo
  | "div.u64" => some .div
  | "rem.u64" => some .rem
  | "and.b64" => some .and
  | "or.b64" => some .or
  | "xor.b64" => some .xor
  | _ => none

def parseShift : String → Option Shift
  | "shl.b64" => some .shl
  | "shr.b64" => some .shr
  | _ => none

def parseCmp : String → Option Cmp
  | "setp.eq.u64" => some .eq
  | "setp.ne.u64" => some .ne
  | "setp.lt.u64" => some .lt
  | "setp.le.u64" => some .le
  | _ => none

def parseBinF : String → Option BinF
  | "add.rn.f32" => some .add
  | "sub.rn.f32" => some .sub
  | "mul.rn.f32" => some .mul
  | "div.rn.f32" => some .div
  | _ => none

def parseCmpF : String → Option CmpF
  | "setp.eq.f32" => some .eq
  | "setp.lt.f32" => some .lt
  | "setp.le.f32" => some .le
  | _ => none

/-- The operands `d , a ;` and the tokens after them. -/
def ops2 : List String → Option (String × String × List String)
  | d :: "," :: a :: ";" :: rest => some (d, a, rest)
  | _ => none

/-- The operands `d , a , b ;` and the tokens after them. -/
def ops3 : List String → Option (String × String × String × List String)
  | d :: "," :: a :: "," :: b :: ";" :: rest => some (d, a, b, rest)
  | _ => none

/-- The operands `d , a , b , c ;` and the tokens after them. -/
def ops4 : List String → Option (String × String × String × String × List String)
  | d :: "," :: a :: "," :: b :: "," :: c :: ";" :: rest => some (d, a, b, c, rest)
  | _ => none

/-- `mov.b32` between `.b32` registers, from an immediate, or between a `.b32` and a `.f32`
register. -/
def parseMov32 (d a : String) : Option Instr :=
  match w32Idx d with
  | some dw => match parseSrc32 a with
    | some s => some (.mov32 dw s)
    | none => (fIdx a).map (.ofF dw)
  | none => do pure (.toF (← fIdx d) (← w32Idx a))

/-- An instruction with three operands whose opcode names its operation. -/
def parseOp3 (op d a b : String) : Option Instr :=
  match parseBin64 op, parseShift op, parseCmp op, parseBinF op, parseCmpF op with
  | some o, _, _, _, _ => do pure (.bin64 o (← w64Idx d) (← w64Idx a) (← parseSrc64 b))
  | none, some s, _, _, _ => do pure (.shift s (← w64Idx d) (← w64Idx a) (← parseSrc32 b))
  | none, none, some c, _, _ => do pure (.setp c (← predIdx d) (← w64Idx a) (← parseSrc64 b))
  | none, none, none, some o, _ => do pure (.binF o (← fIdx d) (← fIdx a) (← fIdx b))
  | none, none, none, none, some c => do pure (.setpF c (← predIdx d) (← fIdx a) (← fIdx b))
  | none, none, none, none, none => none

/-- An instruction with opcode `op` and the operand tokens that follow it. -/
def parseInstr (op : String) (ts : List String) : Option (Instr × List String) :=
  match op with
  | "mov.u32" => do
      let (d, s, rest) ← ops2 ts
      pure (.special (← w32Idx d) (← parseSpecial s), rest)
  | "mov.b32" => do
      let (d, a, rest) ← ops2 ts
      pure (← parseMov32 d a, rest)
  | "mov.b64" => do
      let (d, a, rest) ← ops2 ts
      pure (.mov64 (← w64Idx d) (← parseSrc64 a), rest)
  | "selp.b64" => do
      let (d, t, f, p, rest) ← ops4 ts
      pure (.selp (← w64Idx d) (← parseSrc64 t) (← parseSrc64 f) (← predIdx p), rest)
  | "selp.b32" => do
      let (d, t, f, p, rest) ← ops4 ts
      pure (.selpF (← fIdx d) (← parseSrcF t) (← parseSrcF f) (← predIdx p), rest)
  | "not.pred" => do
      let (d, a, rest) ← ops2 ts
      pure (.notPred (← predIdx d) (← predIdx a), rest)
  | "cvt.u64.u32" => do
      let (d, a, rest) ← ops2 ts
      pure (.widen (← w64Idx d) (← w32Idx a), rest)
  | "cvt.u32.u64" => do
      let (d, a, rest) ← ops2 ts
      pure (.narrow (← w32Idx d) (← w64Idx a), rest)
  | "mad.wide.u32" => do
      let (d, a, b, c, rest) ← ops4 ts
      pure (.madWide (← w64Idx d) (← w32Idx a) (← w32Idx b) (← w64Idx c), rest)
  | "ld.param.u64" => match ts with
      | d :: "," :: "[" :: j :: "]" :: ";" :: rest => do
          pure (.ldParam (← w64Idx d) (← paramIdx j), rest)
      | _ => none
  | "cvta.to.global.u64" => do
      let (d, a, rest) ← ops2 ts
      pure (.cvtaGlobal (← w64Idx d) (← w64Idx a), rest)
  | "ld.global.u64" => match ts with
      | d :: "," :: "[" :: a :: "+" :: imm :: "]" :: ";" :: rest => do
          pure (.ld (← w64Idx d) (← w64Idx a) (← imm64 imm), rest)
      | _ => none
  | "st.global.u64" => match ts with
      | "[" :: a :: "+" :: imm :: "]" :: "," :: v :: ";" :: rest => do
          pure (.st (← w64Idx a) (← imm64 imm) (← w64Idx v), rest)
      | _ => none
  | "sqrt.rn.f32" => do
      let (d, a, rest) ← ops2 ts
      pure (.sqrtF (← fIdx d) (← fIdx a), rest)
  | "cvt.rni.f32.f32" => do
      let (d, a, rest) ← ops2 ts
      pure (.rniF (← fIdx d) (← fIdx a), rest)
  | "testp.notanumber.f32" => do
      let (p, a, rest) ← ops2 ts
      pure (.testNaN (← predIdx p) (← fIdx a), rest)
  | _ => do
      let (d, a, b, rest) ← ops3 ts
      pure (← parseOp3 op d a b, rest)

/-- Whether a statement list ends before the tokens `ts`, when the next label number is `n`. -/
def stops (n : Nat) : List String → Bool
  | "bra" :: _ => true
  | ["ret", ";", "}"] => true
  | g :: "bra" :: lab :: _ => (parseGuard g).isSome && lab != labelToken n
  | lab :: ":" :: _ => lab != labelToken n
  | _ => false

/-- The tokens `want` at the start of `ts`, and the tokens after them. -/
def expectAll (want ts : List String) : Option (List String) :=
  if want.isPrefixOf ts then some (ts.drop want.length) else none

mutual
  /-- One statement whose labels are numbered from `n`, the tokens after it, and the next label
  number. -/
  def parseStmt : Nat → Nat → List String → Option (Stmt × List String × Nat)
    | 0, _, _ => none
    | fuel + 1, n, ts =>
      match ts with
      | "ret" :: ";" :: rest => some (.ret, rest, n)
      | g :: "bra" :: lab :: ";" :: rest =>
          match parseGuard g with
          | some ⟨true, p⟩ =>
              if lab = labelToken n then do
                let (tt, rest, n1) ← parseStmts fuel (n + 2) rest
                let rest ← expectAll ["bra", labelToken (n + 1), ";", labelToken n, ":"] rest
                let (et, rest, n2) ← parseStmts fuel n1 rest
                let rest ← expectAll [labelToken (n + 1), ":"] rest
                pure (.ite p tt et, rest, n2)
              else none
          | _ => none
      | lab :: ":" :: rest =>
          if lab = labelToken n then do
            let (ct, rest, n1) ← parseStmts fuel (n + 2) rest
            let g :: rest := rest | none
            let some ⟨true, p⟩ := parseGuard g | none
            let rest ← expectAll ["bra", labelToken (n + 1), ";"] rest
            let (bt, rest, n2) ← parseStmts fuel n1 rest
            let rest ← expectAll ["bra", labelToken n, ";", labelToken (n + 1), ":"] rest
            pure (.while_ ct p bt, rest, n2)
          else none
      | t :: rest =>
          match parseGuard t, rest with
          | some g, op :: rest => do
              let (i, rest) ← parseInstr op rest
              pure (.instr (some g) i, rest, n)
          | none, _ => do
              let (i, rest) ← parseInstr t rest
              pure (.instr none i, rest, n)
          | some _, [] => none
      | [] => none

  /-- Statements whose labels are numbered from `n`, up to the end of the list, the tokens after
  them, and the next label number. -/
  def parseStmts : Nat → Nat → List String → Option (List Stmt × List String × Nat)
    | 0, _, _ => none
    | fuel + 1, n, ts =>
      if stops n ts then some ([], ts, n)
      else do
        let (s, rest, n1) ← parseStmt fuel n ts
        let (ss, rest, n2) ← parseStmts fuel n1 rest
        pure (s :: ss, rest, n2)
end

/-- The parameters `i` and later, up to `)`: the number of parameters and the tokens after `)`. -/
def parseParams : Nat → Nat → List String → Option (Nat × List String)
  | 0, _, _ => none
  | fuel + 1, i, ".param" :: ".u64" :: b :: rest =>
      if b = paramToken i then
        match rest with
        | "," :: rest => parseParams fuel (i + 1) rest
        | ")" :: rest => some (i + 1, rest)
        | _ => none
      else none
  | _ + 1, _, _ => none

/-- The declarations of registers `i` and later of a class, and the tokens after them. -/
def parseRegs (cls : String) (name : Nat → String) : Nat → Nat → List String →
    Option (Nat × List String)
  | 0, _, _ => none
  | fuel + 1, i, ts =>
      if [".reg", cls, name i, ";"].isPrefixOf ts then parseRegs cls name fuel (i + 1) (ts.drop 4)
      else some (i, ts)

def parseModule (ts : List String) : Option Module := do
  let fuel := ts.length + 1
  let ".version" :: "7.0" :: ".target" :: "sm_80" :: ".address_size" :: "64" :: ".visible" ::
    ".entry" :: "main" :: "(" :: rest := ts | none
  let (params, rest) ← parseParams fuel 0 rest
  let "{" :: rest := rest | none
  let (regs32, rest) ← parseRegs ".b32" w32Token fuel 0 rest
  let (regs64, rest) ← parseRegs ".b64" w64Token fuel 0 rest
  let (regsF, rest) ← parseRegs ".f32" fToken fuel 0 rest
  let (preds, rest) ← parseRegs ".pred" predToken fuel 0 rest
  let (body, rest, _) ← parseStmts fuel 0 rest
  let ["ret", ";", "}"] := rest | none
  pure { inputs := params - 1, regs32, regs64, regsF, preds, body }

/-- The kernel a text holds. -/
def Module.parse (text : String) : Option Module := parseModule (lex text)

end LeanExe.PTX
