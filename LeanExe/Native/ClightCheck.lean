import LeanExe.Native.CText

/-!
The per-build check of the printed C text: a reader of the Coq file that `clightgen` writes for
it, and a comparison of the Clight program in that file with the translation.  The reader
accepts the terms that `clightgen` prints for the translator's programs: statements,
expressions, and types of `Clight.lean`, lists, pairs, and records, with identifiers named by
the file's `Definition _x : ident := $"x".` lines and the temporaries that `clightgen` creates
named by `Definition _t'k : ident := n%positive.` lines.

The comparison covers the whole program (`LeanExe/Native/Proof/Whole.lean`): CompCert's
external declarations, which come first, the translation's definitions in order, and the
program's `main`.  Each global variable and each internal function of the translation must
appear under its name with the same definition, and `__builtin_fsqrt` must be declared as the
translation declares it.  A temporary is read back through `tempName`, and the temporaries of
calls are compared up to renaming: both programs number them in order of first occurrence in
the body.  When the check passes, the program of the file is the whole program `wholeProgram pre
[] t` with its identifiers renamed injectively, by name for globals and per function for
temporaries, where `pre` holds the external declarations, and `pre` meets `WholeOk`.  The
reader is not verified, and a file it cannot read fails the check.
-/

namespace LeanExe.Native.ClightCheck

open LClight

/-! ## Tokens and terms -/

inductive Tok where
  | word (s : String)
  | num (n : Int)
  | str (s : String)
  | sym (s : String)
  deriving Repr, BEq, Inhabited

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '.'

/-- The tokens of `s`.  A word may contain dots, as `Int64.repr` does; a dot that ends a word
is the end of a sentence. -/
partial def tokenize (s : String) : Except String (Array Tok) :=
  go s.toList #[]
where
  go : List Char → Array Tok → Except String (Array Tok)
    | [], acc => pure acc
    | '(' :: '*' :: rest, acc => skipComment rest 1 acc
    | c :: rest, acc =>
        if c.isWhitespace then go rest acc
        else if c == '"' then
          let (body, after) := rest.span (· != '"')
          match after with
          | _ :: after' => go after' (acc.push (.str (String.ofList body)))
          | [] => throw "an unterminated string"
        else if c.isDigit then
          let (ds, after) := (c :: rest).span Char.isDigit
          go after (acc.push (.num (String.ofList ds).toNat!))
        else if c == '-' && (rest.head?.map Char.isDigit).getD false then
          let (ds, after) := rest.span Char.isDigit
          go after (acc.push (.num (-((String.ofList ds).toNat! : Int))))
        else if c.isAlpha || c == '_' then
          let (w, after) := (c :: rest).span isWordChar
          if w.getLast? == some '.' then
            go after ((acc.push (.word (String.ofList w.dropLast))).push (.sym "."))
          else go after (acc.push (.word (String.ofList w)))
        else
          match c, rest with
          | ':', ':' :: r => go r (acc.push (.sym "::"))
          | ':', '=' :: r => go r (acc.push (.sym ":="))
          | '{', '|' :: r => go r (acc.push (.sym "{|"))
          | '|', '}' :: r => go r (acc.push (.sym "|}"))
          | _, r => go r (acc.push (.sym (String.singleton c)))
  skipComment : List Char → Nat → Array Tok → Except String (Array Tok)
    | [], _, _ => throw "an unterminated comment"
    | '*' :: ')' :: rest, 1, acc => go rest acc
    | '*' :: ')' :: rest, d, acc => skipComment rest (d - 1) acc
    | '(' :: '*' :: rest, d, acc => skipComment rest (d + 1) acc
    | _ :: rest, d, acc => skipComment rest d acc

/-- A Coq term as `clightgen` prints it. -/
inductive Term where
  | atom (s : String)
  | num (n : Int)
  | str (s : String)
  | app (f : String) (args : List Term)
  | list (items : List Term)
  | tuple (items : List Term)
  | record (fields : List (String × Term))
  deriving Repr, Inhabited

abbrev P := StateT Nat (Except String)

def peek (toks : Array Tok) : P (Option Tok) := do pure toks[(← get)]?

def advance : P Unit := modify (· + 1)

def expectSym (toks : Array Tok) (s : String) : P Unit := do
  match ← peek toks with
  | some (.sym s') => if s == s' then advance else throw s!"expected {s}, found {s'}"
  | t => throw s!"expected {s}, found {repr t}"

def startsPrimary : Option Tok → Bool
  | some (.word _) | some (.num _) | some (.str _) | some (.sym "(") | some (.sym "{|")
  | some (.sym "$") => true
  | _ => false

mutual
  /-- A term: applications separated by `::`, which build a list ending in `nil`, and by `,`,
  which build a tuple. -/
  partial def term (toks : Array Tok) : P Term := do
    let first ← cons toks
    let mut items := #[first]
    while (← peek toks) == some (.sym ",") do
      advance
      items := items.push (← cons toks)
    if items.size == 1 then pure first else pure (.tuple items.toList)

  partial def cons (toks : Array Tok) : P Term := do
    let first ← application toks
    let mut items := #[first]
    while (← peek toks) == some (.sym "::") do
      advance
      items := items.push (← application toks)
    if items.size == 1 then pure first
    else
      match items.back? with
      | some (.atom "nil") => pure (.list items.pop.toList)
      | _ => throw "a list that does not end in nil"

  partial def application (toks : Array Tok) : P Term := do
    let head ← primary toks
    let mut args := #[]
    while startsPrimary (← peek toks) do
      args := args.push (← primary toks)
    if args.isEmpty then pure head
    else
      match head with
      | .atom f => pure (.app f args.toList)
      | _ => throw "an application whose head is not a name"

  partial def recordFields (toks : Array Tok) (acc : Array (String × Term)) :
      P (Array (String × Term)) := do
    match ← peek toks with
    | some (.sym "|}") => advance; pure acc
    | some (.word f) =>
        advance
        expectSym toks ":="
        let v ← term toks
        match ← peek toks with
        | some (.sym ";") => advance; recordFields toks (acc.push (f, v))
        | some (.sym "|}") => advance; pure (acc.push (f, v))
        | t => throw s!"a record field followed by {repr t}"
    | t => throw s!"a record with {repr t}"

  partial def primary (toks : Array Tok) : P Term := do
    match ← peek toks with
    | some (.word w) => advance; pure (.atom w)
    | some (.num n) =>
        advance
        if (← peek toks) == some (.sym "%") then
          advance
          advance
        pure (.num n)
    | some (.str s) => advance; pure (.str s)
    | some (.sym "$") =>
        advance
        match ← peek toks with
        | some (.str s) => advance; pure (.str s)
        | _ => throw "$ without a string"
    | some (.sym "(") =>
        advance
        let t ← term toks
        expectSym toks ")"
        pure t
    | some (.sym "{|") =>
        advance
        pure (.record (← recordFields toks #[]).toList)
    | t => throw s!"a term starting with {repr t}"
end

/-- The position of the next `:=` from `j`. -/
partial def findDef (toks : Array Tok) (j : Nat) : Nat :=
  if j < toks.size then
    match toks[j]! with
    | .sym ":=" => j
    | _ => findDef toks (j + 1)
  else j

/-- The sentences `Definition name [: type] := term.` of the file, by name.  A sentence whose
term the reader does not accept is left out. -/
partial def definitions (toks : Array Tok) (i : Nat := 0) (acc : List (String × Term) := []) :
    List (String × Term) :=
  if h : i < toks.size then
    match toks[i], toks[i + 1]? with
    | .word "Definition", some (.word name) =>
        let j := findDef toks (i + 2)
        match (term toks).run (j + 1) with
        | .ok (t, k) =>
            match toks[k]? with
            | some (.sym ".") => definitions toks (k + 1) (acc ++ [(name, t)])
            | _ => definitions toks (k + 1) acc
        | .error _ => definitions toks (j + 1) acc
    | _, _ => definitions toks (i + 1) acc
  else acc

/-! ## From terms to Clight -/

/-- The names of the file: `_x` is the source name `x`, or the temporary `k` that `clightgen`
created. -/
inductive Name where
  | source (s : String)
  | created (k : Nat)

structure Names where
  names : List (String × Name)
  /-- Our identifier of a global or function name. -/
  globals : List (String × ident)

/-- Our identifier of a temporary, the inverse of `tempName`. -/
def tempOfName (s : String) : Option ident :=
  if s == "brk" then some brkId
  else
    match s.toList with
    | 'l' :: ds => (String.ofList ds).toNat?.map localId
    | 's' :: rest =>
        let (ds, after) := rest.span Char.isDigit
        match (String.ofList ds).toNat?, after with
        | some h, ['_', 'i'] => some (slotId h .i32)
        | some h, ['_', 'l'] => some (slotId h .i64)
        | some h, ['_', 'f'] => some (slotId h .f32)
        | some h, ['_', 'd'] => some (slotId h .f64)
        | _, _ => none
    | _ => none

/-- The identifier of a temporary that `clightgen` created, before renaming. -/
def createdTemp (k : Nat) : ident := callId (1000000 + k)

def Names.temp (n : Names) (s : String) : Except String ident :=
  match n.names.lookup s with
  | some (.source x) =>
      match tempOfName x with
      | some id => pure id
      | none => throw s!"the temporary {x} is not one the translator names"
  | some (.created k) => pure (createdTemp k)
  | none => throw s!"the identifier {s} has no definition"

def Names.global (n : Names) (s : String) : Except String ident :=
  match n.names.lookup s with
  | some (.source x) =>
      match n.globals.lookup x with
      | some id => pure id
      | none => throw s!"the global {x} is not one of the translation"
  | _ => throw s!"the global {s} has no source name"

partial def toType : Term → Except String type
  | .atom "tvoid" => pure .Tvoid
  | .atom "tint" => pure (.Tint .I32 .Signed noattr)
  | .atom "tuint" => pure (.Tint .I32 .Unsigned noattr)
  | .atom "tlong" => pure (.Tlong .Signed noattr)
  | .atom "tulong" => pure (.Tlong .Unsigned noattr)
  | .atom "tschar" => pure (.Tint .I8 .Signed noattr)
  | .atom "tshort" => pure (.Tint .I16 .Signed noattr)
  | .atom "tushort" => pure (.Tint .I16 .Unsigned noattr)
  | .atom "tbool" => pure (.Tint .IBool .Unsigned noattr)
  | .app "tvolatile" [t] => do
      match ← toType t with
      | .Tint sz sg _ => pure (.Tint sz sg { attr_volatile := true, attr_alignas := none })
      | .Tlong sg _ => pure (.Tlong sg { attr_volatile := true, attr_alignas := none })
      | .Tfloat sz _ => pure (.Tfloat sz { attr_volatile := true, attr_alignas := none })
      | t => throw s!"a volatile type {repr t}"
  | .atom "tuchar" => pure (.Tint .I8 .Unsigned noattr)
  | .atom "tfloat" => pure (.Tfloat .F32 noattr)
  | .atom "tdouble" => pure (.Tfloat .F64 noattr)
  | .app "tptr" [t] => do pure (.Tpointer (← toType t) noattr)
  | .app "tarray" [t, .num n] => do pure (.Tarray (← toType t) n noattr)
  | .app "Tfunction" [args, res, .atom "cc_default"] => do
      let as ← match args with
        | .list items => items.mapM toType
        | .atom "nil" => pure []
        | _ => throw "the parameter types of a function type"
      pure (.Tfunction as (← toType res) cc_default)
  | t => throw s!"the type {repr t}"

def toList : Term → Except String (List Term)
  | .list items => pure items
  | .atom "nil" => pure []
  | t => throw s!"a list, not {repr t}"

def toInt32 : Term → Except String UInt32
  | .app "Int.repr" [.num n] => pure (UInt32.ofInt n)
  | t => throw s!"the int {repr t}"

def toInt64 : Term → Except String UInt64
  | .app "Int64.repr" [.num n] => pure (UInt64.ofInt n)
  | t => throw s!"the long {repr t}"

def binopOf : String → Except String binary_operation
  | "Oadd" => pure .Oadd | "Osub" => pure .Osub | "Omul" => pure .Omul | "Odiv" => pure .Odiv
  | "Omod" => pure .Omod | "Oand" => pure .Oand | "Oor" => pure .Oor | "Oxor" => pure .Oxor
  | "Oshl" => pure .Oshl | "Oshr" => pure .Oshr | "Oeq" => pure .Oeq | "One" => pure .One
  | "Olt" => pure .Olt | "Ogt" => pure .Ogt | "Ole" => pure .Ole | "Oge" => pure .Oge
  | s => throw s!"the operator {s}"

def unopOf : String → Except String unary_operation
  | "Onotbool" => pure .Onotbool | "Onotint" => pure .Onotint | "Oneg" => pure .Oneg
  | "Oabsfloat" => pure .Oabsfloat
  | s => throw s!"the operator {s}"

partial def toExpr (n : Names) : Term → Except String expr
  | .app "Econst_int" [i, t] => do pure (.Econst_int (← toInt32 i) (← toType t))
  | .app "Econst_long" [i, t] => do pure (.Econst_long (← toInt64 i) (← toType t))
  | .app "Econst_float" [.app "Float.of_bits" [i], t] => do
      pure (.Econst_float (← toInt64 i) (← toType t))
  | .app "Econst_single" [.app "Float32.of_bits" [i], t] => do
      pure (.Econst_single (← toInt32 i) (← toType t))
  | .app "Etempvar" [.atom x, t] => do pure (.Etempvar (← n.temp x) (← toType t))
  | .app "Evar" [.atom x, t] => do pure (.Evar (← n.global x) (← toType t))
  | .app "Ederef" [a, t] => do pure (.Ederef (← toExpr n a) (← toType t))
  | .app "Eaddrof" [a, t] => do pure (.Eaddrof (← toExpr n a) (← toType t))
  | .app "Eunop" [.atom op, a, t] => do pure (.Eunop (← unopOf op) (← toExpr n a) (← toType t))
  | .app "Ebinop" [.atom op, a, b, t] => do
      pure (.Ebinop (← binopOf op) (← toExpr n a) (← toExpr n b) (← toType t))
  | .app "Ecast" [a, t] => do pure (.Ecast (← toExpr n a) (← toType t))
  | t => throw s!"the expression {repr t}"

partial def toStmt (n : Names) : Term → Except String statement
  | .atom "Sskip" => pure .Sskip
  | .atom "Sbreak" => pure .Sbreak
  | .atom "Scontinue" => pure .Scontinue
  | .app "Sreturn" [.atom "None"] => pure (.Sreturn none)
  | .app "Sreturn" [.app "Some" [e]] => do pure (.Sreturn (some (← toExpr n e)))
  | .app "Sset" [.atom x, e] => do pure (.Sset (← n.temp x) (← toExpr n e))
  | .app "Sassign" [a, b] => do pure (.Sassign (← toExpr n a) (← toExpr n b))
  | .app "Scall" [dest, f, args] => do
      let d ← match dest with
        | .atom "None" => pure none
        | .app "Some" [.atom x] => do pure (some (← n.temp x))
        | _ => throw "the destination of a call"
      pure (.Scall d (← toExpr n f) (← (← toList args).mapM (toExpr n)))
  | .app "Ssequence" [a, b] => do pure (.Ssequence (← toStmt n a) (← toStmt n b))
  | .app "Sifthenelse" [c, a, b] => do
      pure (.Sifthenelse (← toExpr n c) (← toStmt n a) (← toStmt n b))
  | .app "Sloop" [a, b] => do pure (.Sloop (← toStmt n a) (← toStmt n b))
  | t => throw s!"the statement {repr t}"

def toBool : Term → Except String Bool
  | .atom "true" => pure true
  | .atom "false" => pure false
  | t => throw s!"the boolean {repr t}"

def field (fs : List (String × Term)) (f : String) : Except String Term :=
  match fs.lookup f with
  | some t => pure t
  | none => throw s!"the record has no field {f}"

def toBinding (n : Names) : Term → Except String (ident × type)
  | .tuple [.atom x, t] => do pure (← n.temp x, ← toType t)
  | t => throw s!"the binding {repr t}"

def toFunction (n : Names) : Term → Except String function
  | .record fs => do
      let cc ← field fs "fn_callconv"
      match cc with
      | .atom "cc_default" => pure ()
      | _ => throw "a calling convention other than cc_default"
      pure { fn_return := ← toType (← field fs "fn_return")
             fn_callconv := cc_default
             fn_params := ← (← toList (← field fs "fn_params")).mapM (toBinding n)
             fn_vars := ← (← toList (← field fs "fn_vars")).mapM (toBinding n)
             fn_temps := ← (← toList (← field fs "fn_temps")).mapM (toBinding n)
             fn_body := ← toStmt n (← field fs "fn_body") }
  | t => throw s!"the function {repr t}"

def toInitData : Term → Except String init_data
  | .app "Init_int32" [i] => do pure (.Init_int32 (← toInt32 i))
  | .app "Init_int64" [i] => do pure (.Init_int64 (← toInt64 i))
  | .app "Init_space" [.num n] => pure (.Init_space n)
  | t => throw s!"the initializer {repr t}"

def toVar : Term → Except String (globvar type)
  | .record fs => do
      pure { gvar_info := ← toType (← field fs "gvar_info")
             gvar_init := ← (← toList (← field fs "gvar_init")).mapM toInitData
             gvar_readonly := ← toBool (← field fs "gvar_readonly")
             gvar_volatile := ← toBool (← field fs "gvar_volatile") }
  | t => throw s!"the variable {repr t}"

/-! ## Comparison -/

def exprEq : expr → expr → Bool
  | .Econst_int a t, .Econst_int b u => a == b && t == u
  | .Econst_long a t, .Econst_long b u => a == b && t == u
  | .Econst_float a t, .Econst_float b u => a == b && t == u
  | .Econst_single a t, .Econst_single b u => a == b && t == u
  | .Etempvar a t, .Etempvar b u => a == b && t == u
  | .Evar a t, .Evar b u => a == b && t == u
  | .Ederef a t, .Ederef b u => exprEq a b && t == u
  | .Eaddrof a t, .Eaddrof b u => exprEq a b && t == u
  | .Eunop o a t, .Eunop p b u => o == p && exprEq a b && t == u
  | .Ebinop o a1 a2 t, .Ebinop p b1 b2 u => o == p && exprEq a1 b1 && exprEq a2 b2 && t == u
  | .Ecast a t, .Ecast b u => exprEq a b && t == u
  | _, _ => false

def exprsEq : List expr → List expr → Bool
  | [], [] => true
  | a :: as, b :: bs => exprEq a b && exprsEq as bs
  | _, _ => false

def stmtEq : statement → statement → Bool
  | .Sskip, .Sskip => true
  | .Sbreak, .Sbreak => true
  | .Scontinue, .Scontinue => true
  | .Sreturn none, .Sreturn none => true
  | .Sreturn (some a), .Sreturn (some b) => exprEq a b
  | .Sset x a, .Sset y b => x == y && exprEq a b
  | .Sassign a1 a2, .Sassign b1 b2 => exprEq a1 b1 && exprEq a2 b2
  | .Scall d f as, .Scall e g bs => d == e && exprEq f g && exprsEq as bs
  | .Ssequence a1 a2, .Ssequence b1 b2 => stmtEq a1 b1 && stmtEq a2 b2
  | .Sifthenelse c a1 a2, .Sifthenelse d b1 b2 => exprEq c d && stmtEq a1 b1 && stmtEq a2 b2
  | .Sloop a1 a2, .Sloop b1 b2 => stmtEq a1 b1 && stmtEq a2 b2
  | _, _ => false

/-- The call temporaries of a body in order of first occurrence. -/
def callTemps (s : statement) : List ident :=
  (assigned s).foldl (fun acc (id, _) => if id % 8 == 6 && !acc.contains id then acc ++ [id] else acc) []

def renameExpr (r : ident → ident) : expr → expr
  | .Etempvar x t => .Etempvar (r x) t
  | .Ederef a t => .Ederef (renameExpr r a) t
  | .Eaddrof a t => .Eaddrof (renameExpr r a) t
  | .Eunop o a t => .Eunop o (renameExpr r a) t
  | .Ebinop o a b t => .Ebinop o (renameExpr r a) (renameExpr r b) t
  | .Ecast a t => .Ecast (renameExpr r a) t
  | e => e

def renameStmt (r : ident → ident) : statement → statement
  | .Sreturn (some a) => .Sreturn (some (renameExpr r a))
  | .Sset x a => .Sset (r x) (renameExpr r a)
  | .Sassign a b => .Sassign (renameExpr r a) (renameExpr r b)
  | .Scall d f as => .Scall (d.map r) (renameExpr r f) (as.map (renameExpr r))
  | .Ssequence a b => .Ssequence (renameStmt r a) (renameStmt r b)
  | .Sifthenelse c a b => .Sifthenelse (renameExpr r c) (renameStmt r a) (renameStmt r b)
  | .Sloop a b => .Sloop (renameStmt r a) (renameStmt r b)
  | s => s

/-- The function with its call temporaries renamed to `callId 0`, `callId 1`, … in order of first
occurrence. -/
def canonical (f : function) : function :=
  let order := callTemps f.fn_body
  let r (x : ident) : ident :=
    match order.idxOf? x with
    | some k => callId k
    | none => x
  { f with fn_body := renameStmt r f.fn_body, fn_temps := f.fn_temps.map fun (x, t) => (r x, t) }

def bindingsEq (a b : List (ident × type)) : Bool :=
  a.length == b.length && (a.zip b).all fun ((x, t), (y, u)) => x == y && t == u

def functionEq (f g : function) : Bool :=
  let f := canonical f
  let g := canonical g
  f.fn_return == g.fn_return && f.fn_callconv == g.fn_callconv &&
    bindingsEq f.fn_params g.fn_params && bindingsEq f.fn_vars g.fn_vars &&
    bindingsEq f.fn_temps g.fn_temps && stmtEq f.fn_body g.fn_body

def varEq (v w : globvar type) : Bool :=
  v.gvar_info == w.gvar_info && v.gvar_init == w.gvar_init &&
    v.gvar_readonly == w.gvar_readonly && v.gvar_volatile == w.gvar_volatile

def toXtype : Term → Except String xtype
  | .atom "AST.Xfloat" => pure .Xfloat
  | .atom "AST.Xsingle" => pure .Xsingle
  | .atom "AST.Xint" => pure .Xint
  | .atom "AST.Xlong" => pure .Xlong
  | .atom "AST.Xvoid" => pure .Xvoid
  | .atom "AST.Xbool" => pure .Xbool
  | .atom "AST.Xint8signed" => pure .Xint8signed
  | .atom "AST.Xint8unsigned" => pure .Xint8unsigned
  | .atom "AST.Xint16signed" => pure .Xint16signed
  | .atom "AST.Xint16unsigned" => pure .Xint16unsigned
  | .atom "AST.Xptr" => pure .Xptr
  | .atom "AST.Xany32" => pure .Xany32
  | .atom "AST.Xany64" => pure .Xany64
  | t => throw s!"the type of a signature {repr t}"

/-- A calling convention: `cc_default`, or a record as `clightgen` prints a variadic one. -/
def toCC : Term → Except String calling_convention
  | .atom "cc_default" => pure cc_default
  | .record fs => do
      let va ← match ← field fs "cc_vararg" with
        | .atom "None" => pure none
        | .app "Some" [.num n] => pure (some n)
        | t => throw s!"the field cc_vararg {repr t}"
      pure { cc_vararg := va, cc_unproto := ← toBool (← field fs "cc_unproto")
             cc_structret := ← toBool (← field fs "cc_structret") }
  | t => throw s!"the calling convention {repr t}"

def toSignature : Term → Except String signature
  | .app "mksignature" [args, res, cc] => do
      pure { sig_args := ← (← toList args).mapM toXtype, sig_res := ← toXtype res
             sig_cc := ← toCC cc }
  | t => throw s!"the signature {repr t}"

/-- An external function as `global_definitions` lists it: a built-in, run-time, or external
function of CompCert. -/
def toExternalDef : Term → Except String (fundef function)
  | .app "Gfun" [.app "External" [.app kind [.str name, sg], targs, tres, cc]] => do
      let ef ← match kind with
        | "EF_builtin" => pure (external_function.EF_builtin name (← toSignature sg))
        | "EF_runtime" => pure (external_function.EF_runtime name (← toSignature sg))
        | "EF_external" => pure (external_function.EF_external name (← toSignature sg))
        | k => throw s!"the external function kind {k}"
      pure (.External ef (← (← toList targs).mapM toType) (← toType tres) (← toCC cc))
  | t => throw s!"the external function {repr t}"

/-- An external function compared with another: kind, name, signature, types, and calling
convention. -/
def externalEq : fundef function → fundef function → Bool
  | .External ef as r cc, .External ef' as' r' cc' => ef == ef' && as == as' && r == r' && cc == cc'
  | _, _ => false

/-- The entries of `global_definitions` in order, each a name and its definition. -/
def globalEntries (t : Term) : Except String (List (String × Term)) := do
  (← toList t).mapM fun e =>
    match e with
    | .tuple [.atom x, g] => pure (x, g)
    | e => throw s!"an entry of global_definitions {repr e}"

/-- The identifier that the whole program gives the `j`-th of CompCert's declarations other than
`__builtin_fsqrt`: `4 j + 5`, which no identifier of a translation takes. -/
def preId (j : Nat) : ident := 4 * j + 5

/-- Whether the list has no repeated element. -/
def nodupB [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- The differences between the whole program that the Coq file `text` of `clightgen` describes
and the whole program of the translation `t`, or none.  The file's `global_definitions` must list
CompCert's external declarations, then the translation's definitions but `__builtin_fsqrt` in
order, and nothing after them.  Each external declaration must be a built-in, run-time, or
external function, and `__builtin_fsqrt` must be declared as the translation declares it.  Each
variable and internal function must equal the translation's under its name, with the
temporaries of calls compared up to renaming.  The program has no composite types, and its
`main` is the name `main`.  The names of the entries are distinct, and so are the identifiers
that the whole program gives them, `preId j` for the external declarations, `sqrtId` for
`__builtin_fsqrt`, and the translation's own; the program of the file is then the whole program
of `wholeDefs` with its identifiers renamed injectively. -/
def check (t : Translation) (text : String) : Except String (List String) := do
  let toks ← tokenize text
  let defs := definitions toks
  let names : List (String × Name) := defs.filterMap fun (d, term) =>
    if d.startsWith "_" then
      match term with
      | .str s => some (d, .source s)
      | .num k => if d.startsWith "_t'" then some (d, .created k.toNat) else none
      | _ => none
    else none
  let n : Names := { names, globals := t.names.map fun (id, s) => (s, id) }
  let some gdTerm := defs.lookup "global_definitions"
    | throw "the file has no global_definitions"
  let entries ← globalEntries gdTerm
  let source (x : String) : Option String :=
    match names.lookup x with
    | some (.source s) => some s
    | _ => none
  let tdefs := t.cprogram.prog_defs.filter fun d => d.1 != sqrtId
  let tnames := tdefs.map fun d => t.gname d.1
  let isT (x : String) : Bool := match source x with
    | some s => tnames.contains s
    | none => false
  let firstT := entries.findIdx fun e => isT e.1
  let pre := entries.take firstT
  let mid := (entries.drop firstT).take tdefs.length
  let post := (entries.drop firstT).drop tdefs.length
  let mut errors : Array String := #[]
  -- The order of the translation's definitions.
  let midNames := mid.map fun e => (source e.1).getD e.1
  if midNames != tnames then
    errors := errors.push s!"the definitions are not in the translation's order: {midNames}"
  for (x, _) in post do
    errors := errors.push s!"{(source x).getD x}: a definition after the translation's"
  -- CompCert's declarations, and the identifiers that the whole program gives them.
  let mut preIds : List ident := []
  let mut sqrtSeen := false
  let mut j := 0
  for (x, g) in pre do
    let s := (source x).getD x
    match toExternalDef g with
    | .error e => errors := errors.push s!"{s}: {e}"
    | .ok fd =>
        if s == "__builtin_fsqrt" then
          sqrtSeen := true
          preIds := preIds ++ [sqrtId]
          if !externalEq fd sqrtFun then
            errors := errors.push s!"{s}: the built-in declarations differ"
        else
          preIds := preIds ++ [preId j]
          j := j + 1
  if !sqrtSeen then
    errors := errors.push "__builtin_fsqrt: clightgen declares no such built-in"
  -- The translation's definitions.
  for ((_, g), (id, d)) in mid.zip tdefs do
    let name := t.gname id
    match d, g with
    | .Gvar v, .app "Gvar" [.atom vx] =>
        match defs.lookup vx with
        | none => errors := errors.push s!"{name}: clightgen defines no variable"
        | some term =>
            match toVar term with
            | .error e => errors := errors.push s!"{name}: {e}"
            | .ok w => if !varEq v w then errors := errors.push s!"{name}: the variables differ"
    | .Gfun (.Internal f), .app "Gfun" [.app "Internal" [.atom fx]] =>
        match defs.lookup fx with
        | none => errors := errors.push s!"{name}: clightgen defines no function"
        | some term =>
            match toFunction n term with
            | .error e => errors := errors.push s!"{name}: {e}"
            | .ok g => if !functionEq f g then errors := errors.push s!"{name}: the functions differ"
    | _, _ => errors := errors.push s!"{name}: the kinds of definition differ"
  -- Distinct names and identifiers, no composite types, and `main`.
  if !nodupB (entries.map fun e => (source e.1).getD e.1) then
    errors := errors.push "two entries of global_definitions have one name"
  if !nodupB (preIds ++ tdefs.map (·.1)) then
    errors := errors.push "two definitions of the whole program have one identifier"
  match defs.lookup "composites" with
  | some (.atom "nil") => pure ()
  | _ => errors := errors.push "the program has composite types"
  match defs.lookup "prog" with
  | some (.app "mkprogram" [.atom "composites", .atom "global_definitions", .atom "public_idents",
      .atom m, _]) =>
      if source m != some "main" then errors := errors.push "the program's main is not main"
  | _ => errors := errors.push "the file has no program in the form of mkprogram"
  pure errors.toList

end LeanExe.Native.ClightCheck
