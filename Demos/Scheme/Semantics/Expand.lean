module

public import Demos.Scheme.Semantics.Syntax

@[expose] public section

/-! The reference expander: a datum of the program to the core syntax of §7.2.1, by the rewrite
rules of §7.3 for the derived forms and by the rules of §4.2.6 and §7.1.4 for quasiquotation.
Each function applies one rule and expands the core forms that it produces, so the result equals
the expansion of the rewritten datum.

The rules bind temporaries only around a body that names nothing but the temporaries, or, for
`letrec`, around the assignments of the group's variables.  A temporary of a fixed index for each
role of a rule is therefore fresh in its region: no identifier denotes a temporary, and an inner
rule that binds the same index encloses no reference to the outer one.  `<memv>` and the
procedures of quasiquotation are constants that denote the standard procedures, so no binding of
the program captures them.  `begin` follows the rule `(begin sequence) ≡ ((lambda () sequence))`,
and `(cond)` is a constant of the unspecified value, as §7.3 permits. -/

namespace Demos.Scheme.Semantics

/-- The syntax errors. -/
inductive SyntaxError where
  /-- `()` as an expression (§4.1.3). -/
  | emptyCombination
  /-- A vector as an expression. -/
  | vector
  /-- A combination that is no proper list. -/
  | improper
  /-- A syntactic keyword as a variable (§2.1). -/
  | keyword (s : Sym)
  /-- A form whose keyword `s` it does not fit. -/
  | badForm (s : Sym)
  /-- A non-essential form, which the profile omits: `if` with one arm, a `=>` clause, `let*`,
  `do`, named `let`, `delay`, or the procedure shorthand of `define`. -/
  | unsupported (s : Sym)
  /-- A variable bound twice by one `lambda`, `let`, or `letrec`. -/
  | duplicate (s : Sym)
  /-- A datum that occurs twice among the clauses of one `case`. -/
  | duplicateDatum
  /-- A definition where an expression is required. -/
  | definition
  /-- `else`, `=>`, `unquote`, or `unquote-splicing` as the keyword of an expression. -/
  | misplaced (s : Sym)
  /-- `quasiquote`, `unquote`, or `unquote-splicing` in a template position that §7.1.4 does not
  give them. -/
  | template
  deriving DecidableEq, Repr

/-- The keyword with the spelling `s`. -/
def kw (s : String) : Sym := bytes s

def tempVar (n : Nat) : Expr := .var (.temp n)

/-- `(let ((v init) …) body)` as the rule of §7.3 rewrites it:
`((lambda (v …) body) init …)`. -/
def letCore (vars : List Var) (inits : List Expr) (body : List Expr) (last : Expr) : Expr :=
  .app (.lam vars none body last) inits

/-- `(lambda () e)`. -/
def thunkCore (e : Expr) : Expr := .lam [] none [] e

/-- `(begin sequence)` by its rule: `((lambda () sequence))`. -/
def beginCore (body : List Expr) (last : Expr) : Expr := .app (.lam [] none body last) []

/-- A call of a standard procedure that a rule names. -/
def callPrim (p : Prim) (args : List Expr) : Expr := .app (.const (.prim p)) args

def quoteCore (d : Datum) : Expr := .const (.datum d)

/-- `(or test1 test2 …)` by its rule, with `x` and `thunk` the temporaries 0 and 1:
`(let ((x test1) (thunk (lambda () (or test2 …)))) (if x x (thunk)))`. -/
def orCore (first rest : Expr) : Expr :=
  letCore [.temp 0, .temp 1] [first, thunkCore rest] [] (.ite (tempVar 0) (tempVar 0)
    (.app (tempVar 1) []))

/-- `(and test1 test2 …)` by its rule:
`(let ((x test1) (thunk (lambda () (and test2 …)))) (if x (thunk) x))`. -/
def andCore (first rest : Expr) : Expr :=
  letCore [.temp 0, .temp 1] [first, thunkCore rest] [] (.ite (tempVar 0) (.app (tempVar 1) [])
    (tempVar 0))

/-- `(letrec ((v init) …) body)` by its rule:
`(let ((v <undefined>) …) (let ((temp init) …) (set! v temp) …) body)`, with the temporaries
0 to n − 1.  With no bindings the rule's second `let` would have no body, and the form is
`(let () body)`. -/
def letrecCore (vars : List Sym) (inits : List Expr) (body : List Expr) (last : Expr) : Expr :=
  match vars with
  | [] => letCore [] [] body last
  | _ :: _ =>
    let temps := (List.range vars.length).map Var.temp
    let sets := (vars.zip temps).map fun (v, t) => Expr.set (.id v) (.var t)
    letCore (vars.map .id) (vars.map fun _ => .const .undefined)
      (letCore temps inits sets.dropLast (sets.getLastD (.const .unspecified)) :: body) last

/-- The first spelling that occurs twice in a list. -/
def firstDup : List Sym → Option Sym
  | [] => none
  | s :: rest => if rest.contains s then some s else firstDup rest

/-- The variables of a `lambda`'s formals (§4.1.4): the fixed ones and the rest variable. -/
def lambdaFormals : Datum → Except SyntaxError (List Sym × Option Sym)
  | .nil => .ok ([], none)
  | .sym s => if isKeyword s then .error (.keyword s) else .ok ([], some s)
  | .pair (.sym s) rest =>
    if isKeyword s then .error (.keyword s) else
    match lambdaFormals rest with
    | .ok (fs, r) => .ok (s :: fs, r)
    | .error e => .error e
  | _ => .error (.badForm (kw "lambda"))

/-- The data of the clauses of a `case`, before an `else` clause. -/
def caseData : Datum → List Datum
  | .pair (.pair data _) more => (data.toList?.getD []) ++ caseData more
  | _ => []

/-- The atoms among the data, which `eqv?` compares by value.  Two compound literals are distinct
objects. -/
def atomsOf (ds : List Datum) : List Datum := ds.filter fun d => !d.compound

/-- Whether a datum occurs twice among the atoms of a list. -/
def hasDupAtom : List Datum → Bool
  | [] => false
  | d :: rest => rest.contains d || hasDupAtom rest

mutual

/-- The core expression of a datum (§7.1.3).  A combination whose operator is a syntactic
keyword is the special form of that keyword. -/
def expand : Datum → Except SyntaxError Expr
  | .sym s => if isKeyword s then .error (.keyword s) else .ok (.var (.id s))
  | .nil => .error .emptyCombination
  | .vec _ => .error .vector
  | .pair (.sym s) rest =>
    if !isKeyword s then
      match expandArgs rest with
      | .ok args => .ok (.app (.var (.id s)) args)
      | .error e => .error e
    else
      if s == kw "quote" then
        match rest with
        | .pair d .nil => .ok (quoteCore d)
        | _ => .error (.badForm s)
      else if s == kw "lambda" then
        match rest with
        | .pair formals body =>
          match lambdaFormals formals, expandBody s body with
          | .ok (fs, r), .ok (cs, l) =>
            match firstDup (fs ++ r.toList) with
            | some v => .error (.duplicate v)
            | none => .ok (.lam (fs.map .id) (r.map .id) cs l)
          | .error e, _ => .error e
          | _, .error e => .error e
        | _ => .error (.badForm s)
      else if s == kw "if" then
        match rest with
        | .pair c (.pair t (.pair e .nil)) =>
          match expand c, expand t, expand e with
          | .ok x, .ok y, .ok z => .ok (.ite x y z)
          | .error err, _, _ => .error err
          | _, .error err, _ => .error err
          | _, _, .error err => .error err
        | .pair _ (.pair _ .nil) => .error (.unsupported s)
        | _ => .error (.badForm s)
      else if s == kw "set!" then
        match rest with
        | .pair (.sym x) (.pair e .nil) =>
          if isKeyword x then .error (.keyword x) else
          match expand e with
          | .ok y => .ok (.set (.id x) y)
          | .error err => .error err
        | _ => .error (.badForm s)
      else if s == kw "begin" then
        match expandBody s rest with
        | .ok (cs, l) => .ok (beginCore cs l)
        | .error e => .error e
      else if s == kw "let" then
        match rest with
        | .pair (.sym _) _ => .error (.unsupported s)
        | .pair bindings body =>
          match expandBindings s bindings, expandBody s body with
          | .ok (vs, inits), .ok (cs, l) =>
            match firstDup vs with
            | some v => .error (.duplicate v)
            | none => .ok (letCore (vs.map .id) inits cs l)
          | .error e, _ => .error e
          | _, .error e => .error e
        | _ => .error (.badForm s)
      else if s == kw "letrec" then
        match rest with
        | .pair bindings body =>
          match expandBindings s bindings, expandBody s body with
          | .ok (vs, inits), .ok (cs, l) =>
            match firstDup vs with
            | some v => .error (.duplicate v)
            | none => .ok (letrecCore vs inits cs l)
          | .error e, _ => .error e
          | _, .error e => .error e
        | _ => .error (.badForm s)
      else if s == kw "and" then expandAnd rest
      else if s == kw "or" then expandOr rest
      else if s == kw "cond" then
        match rest with
        | .pair _ _ => expandCond rest
        | _ => .error (.badForm s)
      else if s == kw "case" then
        match rest with
        | .pair key clauses =>
          if clauses == .nil then .error (.badForm s)
          else if hasDupAtom (atomsOf (caseData clauses)) then .error .duplicateDatum else
          match expand key, expandCase 1 clauses with
          | .ok k, .ok (thunks, body) =>
            .ok (letCore (.temp 0 :: (List.range thunks.length).map (fun i => .temp (i + 1)))
              (k :: thunks) [] body)
          | .error e, _ => .error e
          | _, .error e => .error e
        | _ => .error (.badForm s)
      else if s == kw "quasiquote" then
        match rest with
        | .pair t .nil => qq 1 t
        | _ => .error (.badForm s)
      else if s == kw "define" then .error .definition
      else if s == kw "delay" || s == kw "do" || s == kw "let*" then .error (.unsupported s)
      else .error (.misplaced s)
  | .pair f rest =>
    match expand f, expandArgs rest with
    | .ok fe, .ok args => .ok (.app fe args)
    | .error e, _ => .error e
    | _, .error e => .error e
  | .bool b => .ok (quoteCore (.bool b))
  | .int n => .ok (quoteCore (.int n))
  | .char c => .ok (quoteCore (.char c))
  | .str s => .ok (quoteCore (.str s))

/-- The operands of a combination: a proper list of expressions. -/
def expandArgs : Datum → Except SyntaxError (List Expr)
  | .nil => .ok []
  | .pair a d =>
    match expand a, expandArgs d with
    | .ok x, .ok xs => .ok (x :: xs)
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error .improper

/-- A body or sequence of the form with keyword `k`: a proper list of one or more expressions, as
the commands and the last expression. -/
def expandBody (k : Sym) : Datum → Except SyntaxError (List Expr × Expr)
  | .pair e .nil =>
    match expand e with
    | .ok x => .ok ([], x)
    | .error err => .error err
  | .pair e more =>
    match expand e, expandBody k more with
    | .ok x, .ok (cs, l) => .ok (x :: cs, l)
    | .error err, _ => .error err
    | _, .error err => .error err
  | _ => .error (.badForm k)

/-- The bindings of a `let` or `letrec` with keyword `k` (§4.2.2): the variables and the
expanded initializers. -/
def expandBindings (k : Sym) : Datum → Except SyntaxError (List Sym × List Expr)
  | .nil => .ok ([], [])
  | .pair (.pair (.sym v) (.pair init .nil)) more =>
    if isKeyword v then .error (.keyword v) else
    match expand init, expandBindings k more with
    | .ok x, .ok (vs, xs) => .ok (v :: vs, x :: xs)
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error (.badForm k)

/-- `(or test …)` by the rules of §7.3. -/
def expandOr : Datum → Except SyntaxError Expr
  | .nil => .ok (quoteCore (.bool false))
  | .pair t .nil => expand t
  | .pair t more =>
    match expand t, expandOr more with
    | .ok x, .ok y => .ok (orCore x y)
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error .improper

/-- `(and test …)` by the rules of §7.3. -/
def expandAnd : Datum → Except SyntaxError Expr
  | .nil => .ok (quoteCore (.bool true))
  | .pair t .nil => expand t
  | .pair t more =>
    match expand t, expandAnd more with
    | .ok x, .ok y => .ok (andCore x y)
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error .improper

/-- The clauses of a `cond` by the rules of §7.3:
`(cond (test sequence) clause …) ≡ (if test (begin sequence) (cond clause …))`,
`(cond (test) clause …) ≡ (or test (cond clause …))`, `(cond (else sequence)) ≡
(begin sequence)`, and `(cond)` is a constant of the unspecified value. -/
def expandCond : Datum → Except SyntaxError Expr
  | .nil => .ok (.const .unspecified)
  | .pair (.pair test seq) more =>
    if test == .sym (kw "else") then
      if more == .nil then
        match expandBody (kw "cond") seq with
        | .ok (cs, l) => .ok (beginCore cs l)
        | .error e => .error e
      else .error (.badForm (kw "cond"))
    else match seq with
      | .nil =>
        match expand test, expandCond more with
        | .ok x, .ok y => .ok (orCore x y)
        | .error e, _ => .error e
        | _, .error e => .error e
      | .pair (.sym s) _ =>
        if s == kw "=>" then .error (.unsupported s)
        else match expand test, expandBody (kw "cond") seq, expandCond more with
          | .ok x, .ok (cs, l), .ok y => .ok (.ite x (beginCore cs l) y)
          | .error e, _, _ => .error e
          | _, .error e, _ => .error e
          | _, _, .error e => .error e
      | _ =>
        match expand test, expandBody (kw "cond") seq, expandCond more with
        | .ok x, .ok (cs, l), .ok y => .ok (.ite x (beginCore cs l) y)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
  | _ => .error (.badForm (kw "cond"))

/-- The clauses of a `case` from the `i`-th by the rule of §7.3, with the key in temporary 0 and
the thunk of the `i`-th clause in temporary `i`: the thunks, and the `cond` whose clause `i` is
`((<memv> key '(d …)) (thunk))`, with `(else (elsethunk))` for an `else` clause. -/
def expandCase (i : Nat) : Datum → Except SyntaxError (List Expr × Expr)
  | .nil => .ok ([], .const .unspecified)
  | .pair (.pair data seq) more =>
    if data == .sym (kw "else") then
      if more == .nil then
        match expandBody (kw "case") seq with
        | .ok (cs, l) => .ok ([.lam [] none cs l], beginCore [] (.app (tempVar i) []))
        | .error e => .error e
      else .error (.badForm (kw "case"))
    else if data.toList?.isNone then .error (.badForm (kw "case"))
    else match expandBody (kw "case") seq, expandCase (i + 1) more with
      | .ok (cs, l), .ok (ts, rest) =>
        .ok (.lam [] none cs l :: ts,
          .ite (callPrim .memv [tempVar 0, quoteCore data]) (beginCore [] (.app (tempVar i) []))
            rest)
      | .error e, _ => .error e
      | _, .error e => .error e
  | _ => .error (.badForm (kw "case"))

/-- A template at nesting depth `D` (§4.2.6, §7.1.4), as an expression that builds its object.
An unquotation at depth 1 is its expression, and a splicing unquotation at depth 1 appends its
list.  A list template builds fresh pairs with `cons`, a vector template applies `list->vector` to
the list of its elements, and an atom is quoted. -/
def qq (D : Nat) : Datum → Except SyntaxError Expr
  | .pair a rest =>
    let pairCore := match qq D a, qq D rest with
      | .ok x, .ok y => .ok (callPrim .cons [x, y])
      | .error err, _ => .error err
      | _, .error err => .error err
    match a with
    | .sym s =>
      if s == kw "unquote" then
        match rest with
        | .pair e .nil =>
          if D == 1 then expand e
          else match qq (D - 1) e with
            | .ok x => .ok (callPrim .list [quoteCore (.sym s), x])
            | .error err => .error err
        | _ => .error .template
      else if s == kw "quasiquote" then
        match rest with
        | .pair e .nil =>
          match qq (D + 1) e with
          | .ok x => .ok (callPrim .list [quoteCore (.sym s), x])
          | .error err => .error err
        | _ => .error .template
      else if s == kw "unquote-splicing" then .error .template
      else pairCore
    | .pair (.sym s) (.pair e .nil) =>
      if s == kw "unquote-splicing" then
        if D == 1 then
          match expand e, qq D rest with
          | .ok x, .ok y => .ok (callPrim .append [x, y])
          | .error err, _ => .error err
          | _, .error err => .error err
        else match qq (D - 1) e, qq D rest with
          | .ok x, .ok y => .ok (callPrim .cons [callPrim .list [quoteCore (.sym s), x], y])
          | .error err, _ => .error err
          | _, .error err => .error err
      else pairCore
    | _ => pairCore
  | .vec elems =>
    match qq D elems with
    | .ok x => .ok (callPrim .listToVector [x])
    | .error err => .error err
  | .sym s =>
    if s == kw "quasiquote" || s == kw "unquote" || s == kw "unquote-splicing" then
      .error .template
    else .ok (quoteCore (.sym s))
  | d => .ok (quoteCore d)


end

mutual

/-- Whether a datum is a definition (§5.2, §7.1.5): `(define …)` or a `begin` of
definitions. -/
def isDefinition : Datum → Bool
  | .pair (.sym s) rest => s == kw "define" || (s == kw "begin" && allDefinitions rest)
  | _ => false

def allDefinitions : Datum → Bool
  | .nil => true
  | .pair d more => isDefinition d && allDefinitions more
  | _ => false

end

mutual

/-- The top-level forms of one datum of a program (§5.1, §5.2).  A `begin` of definitions is
the sequence of its definitions, and any other datum is an expression. -/
def expandTop : Datum → Except SyntaxError (List TopForm)
  | .pair (.sym s) rest =>
    if s == kw "define" then
      match rest with
      | .pair (.sym x) (.pair e .nil) =>
        if isKeyword x then .error (.keyword x) else
        match expand e with
        | .ok y => .ok [.define x y]
        | .error err => .error err
      | .pair (.pair _ _) _ => .error (.unsupported s)
      | _ => .error (.badForm s)
    else if s == kw "begin" && allDefinitions rest then expandTops rest
    else match expand (.pair (.sym s) rest) with
      | .ok e => .ok [.expr e]
      | .error err => .error err
  | d =>
    match expand d with
    | .ok e => .ok [.expr e]
    | .error err => .error err

def expandTops : Datum → Except SyntaxError (List TopForm)
  | .nil => .ok []
  | .pair d more =>
    match expandTop d, expandTops more with
    | .ok a, .ok b => .ok (a ++ b)
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error (.badForm (kw "begin"))

end

end Demos.Scheme.Semantics
