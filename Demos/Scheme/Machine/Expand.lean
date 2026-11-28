module

public import Demos.Scheme.Machine.Code

@[expose] public section

/-! The expander of the executable interpreter.  It follows the reference expander of
`Demos/Scheme/Semantics/Expand.lean` function by function, with each pending computation in a frame
of the arena: the rules of §7.3 for the derived forms and of §4.2.6 and §7.1.4 for quasiquotation,
the same core syntax, and the same order of its checks, so a malformed program gives the same first
error.  A scope is a chain of entries whose keys are symbols and the temporaries of the rules, and
a variable becomes its lexical address in the scope, or its symbol at the top level.

The mode `EXPAND` expands the datum `x` in the scope `env`, the modes `EXP_OR`, `EXP_AND`,
`EXP_COND`, `EXP_QQ`, and `CASECL` run the reference's `expandOr`, `expandAnd`, `expandCond`, `qq`
at the depth `nargs`, and the walk of `expandCase`, and `EXPANDED` returns the code `val` to the
frame on top.  A list frame expands a list of expressions into a chain and returns the token
`LISTDONE`, or `LISTIMPROPER` at a tail that is no list, to the frame below it, which owns the
list. -/

namespace Demos.Scheme.Machine

def EXP_OR : UInt64 := 11
def EXP_AND : UInt64 := 12
def EXP_COND : UInt64 := 13
def EXP_QQ : UInt64 := 14
def CASECL : UInt64 := 15
def TOPWALK : UInt64 := 16
def TOPCODE : UInt64 := 17

/-- The tokens that a list frame returns. -/
def LISTDONE : UInt64 := 6
def LISTIMPROPER : UInt64 := 14

def X_LIST : UInt64 := 16
def X_APPOP : UInt64 := 17
def X_ARGS : UInt64 := 18
def X_LAMBDA : UInt64 := 19
def X_BEGIN : UInt64 := 20
def X_IF : UInt64 := 21
def X_SET : UInt64 := 22
def X_LET : UInt64 := 23
def X_BIND : UInt64 := 24
def X_LETREC : UInt64 := 25
def X_OR : UInt64 := 26
def X_CONDIF : UInt64 := 27
def X_CASE : UInt64 := 28
def X_CASEWALK : UInt64 := 29
def X_QQCONS : UInt64 := 30
def X_QQAPPEND : UInt64 := 31
def X_QQWRAP : UInt64 := 32
def X_QQVEC : UInt64 := 33
def X_TOPONE : UInt64 := 34
def X_TOPDEF : UInt64 := 35
def X_TOPWALK : UInt64 := 36
def X_SCOPE : UInt64 := 37

/-- `X_OR`'s flag in its count: the second operand is an `or`, an `and`, or a `cond`. -/
def F_OR : UInt64 := 0
def F_AND : UInt64 := 1
def F_COND : UInt64 := 2

/-- A frame with a count. -/
def pushFrameN (m : Machine) (sub n b c d : UInt64) : Machine :=
  let m := alloc m (mkKind K_FRAME sub n) m.k b c d
  { m with k := m.val }

/-- The machine with the top frame removed. -/
def popFrame (m : Machine) : Machine :=
  let next := fa m.heap m.k
  { m with k := next }

/-- The code `v` returned to the frame on top. -/
def expanded (m : Machine) (v : UInt64) : Machine := { m with val := v, mode := EXPANDED }

/-- The syntax error `entry` with the keyword code or symbol `detail`. -/
@[inline] def syntaxError (m : Machine) (entry detail : UInt64) : Machine :=
  fail m (S_SYNTAX + entry) detail

/-- The scope with the key `key` first. -/
@[inline] def scopeWith (m : Machine) (scope key : UInt64) : Machine :=
  alloc m (mkKind K_FRAME X_SCOPE 0) scope key 0 0

/-- The position of `key` in the scope, or the scope's length when it holds no such key. -/
def lookupScope (heap : Array Slot) (scope key : UInt64) : UInt64 × Bool :=
  let r := LeanExe.repeatWhile 16777216 (scope, (0 : UInt64))
    (fun s => s.1 != NONE && fb heap s.1 != key) fun s => (fa heap s.1, s.2 + 1)
  (r.2, r.1 != NONE)

/-- The code of a reference to the variable `key` in the scope `env`. -/
def varCode (m : Machine) (key : UInt64) : Machine :=
  let r := lookupScope m.heap m.env key
  if r.2 then node m C_LREF r.1 0 0 else node m C_GREF key 0 0

/-- The length of a list, up to its first object that is no pair. -/
def listLength (heap : Array Slot) (l : UInt64) : UInt64 :=
  (LeanExe.repeatWhile 16777216 (l, (0 : UInt64)) (fun s => isPair heap s.1)
    fun s => (fb heap s.1, s.2 + 1)).2

/-- Element `i` of a list. -/
@[inline] def listAt (heap : Array Slot) (l i : UInt64) : UInt64 :=
  fa heap (LeanExe.repeatWhile i l (fun _ => true) fun l => fb heap l)

/-- The scope `scope` with the variables of the first `n` bindings of `l` before it, the first at
position 0. -/
def scopeWithBindings (m : Machine) (scope l n : UInt64) : Machine :=
  let st := LeanExe.loop n (m, scope) fun j st =>
    let m := scopeWith st.1 st.2 (fa st.1.heap (listAt st.1.heap l (n - 1 - j)))
    let v := m.val
    (m, v)
  { st.1 with val := st.2 }

/-- The variable of the first of the first `n` bindings of `l` whose variable occurs again among
them, or `NONE`. -/
def firstDuplicate (heap : Array Slot) (l n : UInt64) : UInt64 :=
  let i := LeanExe.repeatWhile n (0 : UInt64)
    (fun i => i < n && !(LeanExe.repeatWhile n (i + 1)
      (fun j => j < n && fa heap (listAt heap l j) != fa heap (listAt heap l i))
      (fun j => j + 1) < n))
    fun i => i + 1
  if i < n then fa heap (listAt heap l i) else NONE

/-- The frame `fr` with the count `n` in its kind word. -/
def setCount (m : Machine) (fr sub n : UInt64) : Machine :=
  let s := slotAt m.heap fr
  let s' : Slot := ⟨mkKind K_FRAME sub n, s.a, s.b, s.c, s.d⟩
  { m with heap := m.heap.set! (fr >>> 3).toNat s' }

/-- The variable of a binding `(v init)`. -/
@[inline] def bindingVar (heap : Array Slot) (b : UInt64) : UInt64 := fa heap b

/-- Whether a binding has the form `(v init)` with a symbol `v`. -/
@[inline] def bindingShape (heap : Array Slot) (b : UInt64) : Bool :=
  isPair heap b && isKind heap (fa heap b) K_SYMBOL && isPair heap (fb heap b) &&
    fb heap (fb heap b) == NILV

/-! ## Lists of expressions -/

/-- The expansion of the list of expressions `l` into the chain whose first cell `cell` holds, with
the frame of its owner already on top: the first expression, or the token `LISTIMPROPER` for a list
that is no pair.  The owner checks that a body is not empty. -/
def startList (m : Machine) (cell l : UInt64) : Machine :=
  if isPair m.heap l then
    let m := pushFrame m X_LIST (fb m.heap l) cell m.env
    let first := fa m.heap l
    { m with x := first, mode := EXPAND }
  else expanded m LISTIMPROPER

/-- A body of one or more expressions into the chain of the lambda node `lam`, or the syntax error
`bad form` of the keyword `kw` for an empty body. -/
def startBody (m : Machine) (lam body kw : UInt64) : Machine :=
  if isPair m.heap body then
    let m := node m C_CHAIN 0 NONE 0
    let cell := m.val
    startList (setC m lam cell) cell body
  else syntaxError m M_BADFORM kw

/-- The list frame on top receives an expression's code. -/
def listNext (m : Machine) : Machine :=
  let fr := m.k
  let cell := fc m.heap fr
  let m := setA m cell m.val
  let rem := fb m.heap fr
  if rem == NILV then expanded (popFrame m) LISTDONE
  else if isPair m.heap rem then
    let m := node m C_CHAIN 0 NONE 0
    let next := m.val
    let m := setB m cell next
    let m := setC (setB m fr (fb m.heap rem)) fr next
    let first := fa m.heap rem
    let env := fd m.heap fr
    { m with x := first, env := env, mode := EXPAND }
  else expanded (popFrame m) LISTIMPROPER

/-! ## Bindings of `let` and `letrec` -/

/-- The bindings `bs` of a `let` or `letrec` with keyword `kw`, whose owner frame is on top and
holds the chain of the initializers in field `c`: the initializers in the scope `env`. -/
def startBindings (m : Machine) (bs kw : UInt64) : Machine :=
  if bs == NILV then expanded m LISTDONE
  else if isPair m.heap bs && bindingShape m.heap (fa m.heap bs) then
    let b := fa m.heap bs
    let v := fa m.heap b
    if keywordOf m.heap v != 0 then syntaxError m M_KEYWORD (keywordOf m.heap v)
    else
      let m := node m C_CHAIN 0 NONE 0
      let cell := m.val
      let m := setC m m.k cell
      let m := pushFrameN m X_BIND kw (fb m.heap bs) cell m.env
      let init := fa m.heap (fb m.heap b)
      { m with x := init, mode := EXPAND }
  else syntaxError m M_BADFORM kw

/-- The binding frame on top receives an initializer's code. -/
def bindNext (m : Machine) : Machine :=
  let fr := m.k
  let kw := countOf (slotAt m.heap fr).kind
  let cell := fc m.heap fr
  let m := setA m cell m.val
  let rem := fb m.heap fr
  if rem == NILV then expanded (popFrame m) LISTDONE
  else if isPair m.heap rem && bindingShape m.heap (fa m.heap rem) then
    let b := fa m.heap rem
    let v := fa m.heap b
    if keywordOf m.heap v != 0 then syntaxError m M_KEYWORD (keywordOf m.heap v)
    else
      let m := node m C_CHAIN 0 NONE 0
      let next := m.val
      let m := setB m cell next
      let m := setC (setB m fr (fb m.heap rem)) fr next
      let init := fa m.heap (fb m.heap b)
      let env := fd m.heap fr
      { m with x := init, env := env, mode := EXPAND }
  else syntaxError m M_BADFORM kw

/-- The number of bindings of the form `(v init)` before the first that has another form. -/
def bindingPrefix (heap : Array Slot) (bs : UInt64) : UInt64 :=
  (LeanExe.repeatWhile 16777216 (bs, (0 : UInt64))
    (fun s => isPair heap s.1 && bindingShape heap (fa heap s.1)) fun s => (fb heap s.1, s.2 + 1)).2

/-! ## Special forms -/

/-- The parse of `lambda`'s formals (§4.1.4): the number of fixed variables, whether a rest
variable follows, and 0, or the syntax error's entry and its keyword code. -/
def parseFormals (heap : Array Slot) (f : UInt64) : UInt64 × Bool × UInt64 × UInt64 :=
  let r := LeanExe.repeatWhile 16777216 (f, (0 : UInt64), (0 : UInt64), (0 : UInt64))
    (fun s => s.2.2.1 == 0 && isPair heap s.1)
    fun s =>
      let v := fa heap s.1
      if isKind heap v K_SYMBOL then
        if keywordOf heap v != 0 then (s.1, s.2.1, M_KEYWORD, keywordOf heap v)
        else (fb heap s.1, s.2.1 + 1, 0, 0)
      else (s.1, s.2.1, M_BADFORM, KW_LAMBDA)
  if r.2.2.1 != 0 then (r.2.1, false, r.2.2.1, r.2.2.2)
  else if r.1 == NILV then (r.2.1, false, 0, 0)
  else if isKind heap r.1 K_SYMBOL then
    if keywordOf heap r.1 != 0 then (r.2.1, true, M_KEYWORD, keywordOf heap r.1)
    else (r.2.1, true, 0, 0)
  else (r.2.1, false, M_BADFORM, KW_LAMBDA)

/-- The formal at position `i` of the formals `f`, the rest variable at position `n`. -/
def formalAt (heap : Array Slot) (f n i : UInt64) : UInt64 :=
  let t := LeanExe.repeatWhile i f (fun _ => true) fun l => fb heap l
  if i < n then fa heap t else t

/-- `lambda` (§4.1.4): the formals, then the body in the scope that binds them. -/
def expandLambda (m : Machine) (form : UInt64) : Machine :=
  let rest := fb m.heap form
  if !isPair m.heap rest then syntaxError m M_BADFORM KW_LAMBDA
  else
    let formals := fa m.heap rest
    let p := parseFormals m.heap formals
    if p.2.2.1 != 0 then syntaxError m p.2.2.1 p.2.2.2
    else
      let n := p.1
      let total := if p.2.1 then n + 1 else n
      let st := LeanExe.loop total (m, m.env) fun j st =>
        let m := scopeWith st.1 st.2 (formalAt st.1.heap formals n (total - 1 - j))
        let v := m.val
        (m, v)
      let m := node st.1 C_LAMBDA n (if p.2.1 then 1 else 0) NONE
      let lam := m.val
      let m := pushFrame { m with env := st.2 } X_LAMBDA lam formals 0
      startBody m lam (fb m.heap rest) KW_LAMBDA

/-- The duplicate check of a `lambda`'s formals after its body: the first formal that occurs again,
the rest variable included. -/
def lambdaDone (m : Machine) : Machine :=
  let fr := m.k
  let lam := fb m.heap fr
  let formals := fc m.heap fr
  let n := fa m.heap lam
  let total := if fb m.heap lam == 1 then n + 1 else n
  let dup := LeanExe.repeatWhile total (0 : UInt64)
    (fun i => i < total && !(LeanExe.repeatWhile total (i + 1)
      (fun j => j < total && formalAt m.heap formals n j != formalAt m.heap formals n i)
      (fun j => j + 1) < total))
    fun i => i + 1
  if dup < total then syntaxError m M_DUPLICATE (formalAt m.heap formals n dup)
  else expanded (popFrame m) lam

/-- `if` (§4.1.5): the test, the consequent, and the alternative.  The form with one arm is not
essential. -/
def expandIf (m : Machine) (form : UInt64) : Machine :=
  let h := m.heap
  let rest := fb h form
  if isPair h rest && isPair h (fb h rest) && isPair h (fb h (fb h rest)) &&
      fb h (fb h (fb h rest)) == NILV then
    let m := node m C_CHAIN 0 NONE 0
    let cell := m.val
    let m := node m C_IF cell 0 0
    let m := pushFrame m X_IF m.val 0 0
    startList m cell rest
  else if isPair h rest && isPair h (fb h rest) && fb h (fb h rest) == NILV then
    syntaxError m M_UNSUPPORTED KW_IF
  else syntaxError m M_BADFORM KW_IF

/-- `set!` (§4.1.6). -/
def expandSet (m : Machine) (form : UInt64) : Machine :=
  let h := m.heap
  let rest := fb h form
  if isPair h rest && isKind h (fa h rest) K_SYMBOL && isPair h (fb h rest) &&
      fb h (fb h rest) == NILV then
    let v := fa h rest
    if keywordOf h v != 0 then syntaxError m M_KEYWORD (keywordOf h v)
    else
      let r := lookupScope h m.env v
      let m := if r.2 then node m C_LSET r.1 0 0 else node m C_GSET v 0 0
      let m := pushFrame m X_SET m.val 0 0
      let e := fa m.heap (fb m.heap rest)
      { m with x := e, mode := EXPAND }
  else syntaxError m M_BADFORM KW_SET

/-- `let` (§4.2.2): the bindings, then the body in the scope of their variables, then the
duplicate check, as `((lambda (v …) body) init …)`.  Named `let` is not essential. -/
def expandLet (m : Machine) (form : UInt64) : Machine :=
  let rest := fb m.heap form
  if isPair m.heap rest && isKind m.heap (fa m.heap rest) K_SYMBOL then
    syntaxError m M_UNSUPPORTED KW_LET
  else if isPair m.heap rest then
    let m := pushFrameN m X_LET 0 form NONE m.env
    startBindings m (fa m.heap rest) KW_LET
  else syntaxError m M_BADFORM KW_LET

/-- `letrec` (§4.2.2): the initializers in the scope of the group's variables, then the body. -/
def expandLetrec (m : Machine) (form : UInt64) : Machine :=
  let rest := fb m.heap form
  if isPair m.heap rest then
    let bs := fa m.heap rest
    let n := bindingPrefix m.heap bs
    let m := scopeWithBindings m m.env bs n
    let scope := m.val
    let m := pushFrameN { m with env := scope } X_LETREC 0 form NONE scope
    startBindings m bs KW_LETREC
  else syntaxError m M_BADFORM KW_LETREC

/-- The atoms among the data of a `case`'s clauses, as the reference's `caseData`, which `eqv?`
compares by value: numbers, characters, booleans, the empty list, and symbols. -/
@[inline] def isAtomDatum (heap : Array Slot) (v : UInt64) : Bool :=
  !isRef v || isKind heap v K_SYMBOL

/-- Whether `d` is an element of the list `l`. -/
def memList (heap : Array Slot) (l d : UInt64) : Bool :=
  (LeanExe.repeatWhile 16777216 (l, false) (fun u => !u.2 && isPair heap u.1)
    fun u => (fb heap u.1, fa heap u.1 == d)).2

def isProperList (heap : Array Slot) (l : UInt64) : Bool :=
  LeanExe.repeatWhile 16777216 l (fun l => isPair heap l) (fun l => fb heap l) == NILV

/-- Whether `d` occurs in the proper datum list of a clause of `cls`, among the clauses that the
reference's `caseData` reads. -/
def inLaterClauses (heap : Array Slot) (cls d : UInt64) : Bool :=
  (LeanExe.repeatWhile 16777216 (cls, false)
    (fun u => !u.2 && isPair heap u.1 && isPair heap (fa heap u.1))
    fun u =>
      let dl := fa heap (fa heap u.1)
      (fb heap u.1, isProperList heap dl && memList heap dl d)).2

/-- Whether an atom occurs twice among the data of the clauses `cls`. -/
def caseDuplicate (heap : Array Slot) (cls : UInt64) : Bool :=
  (LeanExe.repeatWhile 16777216 (cls, false)
    (fun s => !s.2 && isPair heap s.1 && isPair heap (fa heap s.1))
    fun s =>
      let data := fa heap (fa heap s.1)
      let found := isProperList heap data &&
        (LeanExe.repeatWhile 16777216 (data, false) (fun t => !t.2 && isPair heap t.1)
          fun t =>
            let d := fa heap t.1
            (fb heap t.1, isAtomDatum heap d &&
              (memList heap (fb heap t.1) d || inLaterClauses heap (fb heap s.1) d))).2
      (fb heap s.1, found)).2

/-- `case` (§4.2.1, §7.3): the duplicate check of the data, the key, then the clauses. -/
def expandCase (m : Machine) (form : UInt64) : Machine :=
  let rest := fb m.heap form
  if isPair m.heap rest then
    let clauses := fb m.heap rest
    if clauses == NILV then syntaxError m M_BADFORM KW_CASE
    else if caseDuplicate m.heap clauses then syntaxError m M_DUPDATUM 0
    else
      let m := node m C_CHAIN 0 NONE m.env
      let m := pushFrameN m X_CASE 0 form 0 m.val
      let key := fa m.heap rest
      { m with x := key, mode := EXPAND }
  else syntaxError m M_BADFORM KW_CASE

/-- The special form with keyword `kw`. -/
def expandForm (m : Machine) (kw form : UInt64) : Machine :=
  let h := m.heap
  let rest := fb h form
  if kw == KW_QUOTE then
    if isPair h rest && fb h rest == NILV then
      let m := node m C_CONST (fa h rest) 0 0
      expanded m m.val
    else syntaxError m M_BADFORM kw
  else if kw == KW_LAMBDA then expandLambda m form
  else if kw == KW_IF then expandIf m form
  else if kw == KW_SET then expandSet m form
  else if kw == KW_BEGIN then
    let m := node m C_LAMBDA 0 0 NONE
    let lam := m.val
    let m := pushFrame m X_BEGIN lam KW_BEGIN 0
    startBody m lam rest KW_BEGIN
  else if kw == KW_LET then expandLet m form
  else if kw == KW_LETREC then expandLetrec m form
  else if kw == KW_AND then { m with x := rest, mode := EXP_AND }
  else if kw == KW_OR then { m with x := rest, mode := EXP_OR }
  else if kw == KW_COND then
    if isPair h rest then { m with x := rest, mode := EXP_COND } else syntaxError m M_BADFORM kw
  else if kw == KW_CASE then expandCase m form
  else if kw == KW_QUASIQUOTE then
    if isPair h rest && fb h rest == NILV then
      let template := fa h rest
      { m with x := template, nargs := 1, mode := EXP_QQ }
    else syntaxError m M_BADFORM kw
  else if kw == KW_DEFINE then syntaxError m M_DEFINITION 0
  else if kw == KW_DELAY || kw == KW_DO || kw == KW_LETSTAR then syntaxError m M_UNSUPPORTED kw
  else syntaxError m M_MISPLACED kw

/-- One step of `EXPAND`: the datum `x` in the scope `env` (§7.1.3). -/
def expandStep (m : Machine) : Machine :=
  let h := m.heap
  let d := m.x
  if isKind h d K_SYMBOL then
    if keywordOf h d != 0 then syntaxError m M_KEYWORD (keywordOf h d)
    else
      let m := varCode m d
      expanded m m.val
  else if isPair h d then
    let f := fa h d
    if isKind h f K_SYMBOL then
      if keywordOf h f != 0 then expandForm m (keywordOf h f) d
      else
        let m := varCode m f
        let m := node m C_APP m.val NONE 0
        let app := m.val
        if fb m.heap d == NILV then expanded m app
        else
          let m := node m C_CHAIN 0 NONE 0
          let cell := m.val
          let m := setB m app cell
          let m := pushFrame m X_ARGS app 0 0
          startList m cell (fb m.heap d)
    else
      let m := node m C_APP 0 NONE 0
      let m := pushFrame m X_APPOP m.val (fb m.heap d) m.env
      { m with x := f }
  else if d == NILV then syntaxError m M_EMPTY 0
  else if isKind h d K_VECTOR then syntaxError m M_VECTOR 0
  else
    let m := node m C_CONST d 0 0
    expanded m m.val

/-! ## `or`, `and`, `cond`, `case`, and quasiquotation -/

/-- One step of `EXP_OR` or `EXP_AND`: the tests `x` (§7.3). -/
def expandOrAnd (m : Machine) (flag : UInt64) : Machine :=
  let l := m.x
  if l == NILV then
    let m := node m C_CONST (if flag == F_AND then TRUE else FALSE) 0 0
    expanded m m.val
  else if isPair m.heap l then
    let first := fa m.heap l
    if fb m.heap l == NILV then { m with x := first, mode := EXPAND }
    else
      let m := pushFrameN m X_OR flag (fb m.heap l) 0 m.env
      { m with x := first, mode := EXPAND }
  else syntaxError m M_IMPROPER 0

/-- One step of `EXP_COND`: the clauses `x` (§7.3). -/
def expandCondStep (m : Machine) : Machine :=
  let h := m.heap
  let l := m.x
  if l == NILV then
    let m := node m C_CONST UNSPEC 0 0
    expanded m m.val
  else if isPair h l && isPair h (fa h l) then
    let clause := fa h l
    let test := fa h clause
    let seq := fb h clause
    if keywordOf h test == KW_ELSE then
      if fb h l == NILV then
        let m := node m C_LAMBDA 0 0 NONE
        let lam := m.val
        let m := pushFrame m X_BEGIN lam KW_COND 0
        startBody m lam seq KW_COND
      else syntaxError m M_BADFORM KW_COND
    else if seq == NILV then
      let m := pushFrameN m X_OR F_COND (fb h l) 0 m.env
      { m with x := test, mode := EXPAND }
    else if isPair h seq && keywordOf h (fa h seq) == KW_ARROW then
      syntaxError m M_UNSUPPORTED KW_ARROW
    else
      let m := node m C_CHAIN 0 NONE 0
      let c3 := m.val
      let m := node m C_CHAIN 0 c3 0
      let c2 := m.val
      let m := node m C_CHAIN 0 c2 0
      let m := node m C_IF m.val 0 0
      let m := pushFrameN m X_CONDIF 0 l m.val m.env
      { m with x := test, mode := EXPAND }
  else syntaxError m M_BADFORM KW_COND

/-- One step of `CASECL`: the next clause of the walk on top (§7.3's rule of `case`): its body as
a thunk. -/
def caseClause (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let l := s.b
  if l == NILV then expanded { m with k := s.a } LISTDONE
  else if isPair m.heap l && isPair m.heap (fa m.heap l) then
    let clause := fa m.heap l
    let data := fa m.heap clause
    let seq := fb m.heap clause
    let more := fb m.heap l
    let isElse := keywordOf m.heap data == KW_ELSE
    let proper := isProperList m.heap data
    if isElse && more != NILV then syntaxError m M_BADFORM KW_CASE
    else if !isElse && !proper then syntaxError m M_BADFORM KW_CASE
    else
      let m := node m C_LAMBDA 0 0 NONE
      let lam := m.val
      let m := node m C_CHAIN lam NONE 0
      let cell := m.val
      let m := setB (setC (setB m s.c cell) fr cell) fr more
      startBody { m with env := s.d } lam seq KW_CASE
  else syntaxError m M_BADFORM KW_CASE

/-- The `cond` of a `case` with `n` clauses and the key in temporary 0 (§7.3): clause `i` from 1
tests `(memv key '(d …))` and calls the thunk in temporary `i`, and an `else` clause calls its
thunk. -/
def caseBody (m : Machine) (clauses n : UInt64) : Machine :=
  let st := LeanExe.loop n (m, (0 : UInt64)) fun j st =>
    let i := n - j
    let m := st.1
    let clause := listAt m.heap clauses (i - 1)
    let data := fa m.heap clause
    -- the call of the thunk, as (begin (thunk))
    let m := node m C_LREF i 0 0
    let m := node m C_APP m.val NONE 0
    let m := node m C_CHAIN m.val NONE 0
    let m := beginCore m m.val
    let call := m.val
    if keywordOf m.heap data == KW_ELSE then (m, call)
    else
      let rest := st.2
      let m := if rest == 0 then node m C_CONST UNSPEC 0 0 else { m with val := rest }
      let rest := m.val
      let m := node m C_LREF 0 0 0
      let key := m.val
      let m := node m C_CONST data 0 0
      let m := callPrim2 m P_MEMV key m.val
      let test := m.val
      let m := node m C_CHAIN rest NONE 0
      let m := node m C_CHAIN call m.val 0
      let m := node m C_CHAIN test m.val 0
      let m := node m C_IF m.val 0 0
      let v := m.val
      (m, v)
  if st.2 == 0 then node st.1 C_CONST UNSPEC 0 0 else { st.1 with val := st.2 }

/-- One step of `EXP_QQ`: the template `x` at the depth `nargs` (§4.2.6, §7.1.4). -/
def expandQQ (m : Machine) : Machine :=
  let h := m.heap
  let t := m.x
  let depth := m.nargs
  if isPair h t then
    let a := fa h t
    let rest := fb h t
    let kw := keywordOf h a
    let one := isPair h rest && fb h rest == NILV
    let e := if isPair h rest then fa h rest else NONE
    let splice := isPair h a && keywordOf h (fa h a) == KW_UNQUOTE_SPLICING && isPair h (fb h a) &&
      fb h (fb h a) == NILV
    let spliced := if splice then fa h (fb h a) else NONE
    let spliceSym := if splice then fa h a else NONE
    if kw == KW_UNQUOTE then
      if !one then syntaxError m M_TEMPLATE 0
      else if depth == 1 then { m with x := e, mode := EXPAND }
      else
        let m := pushFrame m X_QQWRAP a 0 0
        { m with x := e, nargs := depth - 1 }
    else if kw == KW_QUASIQUOTE then
      if !one then syntaxError m M_TEMPLATE 0
      else
        let m := pushFrame m X_QQWRAP a 0 0
        { m with x := e, nargs := depth + 1 }
    else if kw == KW_UNQUOTE_SPLICING then syntaxError m M_TEMPLATE 0
    else if splice then
      if depth == 1 then
        let m := pushFrameN m X_QQAPPEND depth rest 0 m.env
        { m with x := spliced, mode := EXPAND }
      else
        let m := pushFrameN m X_QQCONS depth rest 0 m.env
        let m := pushFrame m X_QQWRAP spliceSym 0 0
        { m with x := spliced, nargs := depth - 1 }
    else
      let m := pushFrameN m X_QQCONS depth rest 0 m.env
      { m with x := a }
  else if isKind h t K_VECTOR then
    -- the list of the vector's elements
    let n := fa h t
    let st := LeanExe.loop n (m, NILV) fun j st =>
      let m := alloc st.1 (mkKind K_PAIR 0 0) (vectorRef st.1.heap t (n - 1 - j)) st.2 0 0
      let v := m.val
      (m, v)
    let m := pushFrame st.1 X_QQVEC 0 0 0
    { m with x := st.2 }
  else
    let kw := keywordOf h t
    if kw == KW_QUASIQUOTE || kw == KW_UNQUOTE || kw == KW_UNQUOTE_SPLICING then
      syntaxError m M_TEMPLATE 0
    else
      let m := node m C_CONST t 0 0
      expanded m m.val

/-! ## The frames that receive a code

Each function reads the frame on top and every other word it needs before its first write, so the
compiled code changes the arena in place. -/

/-- `X_APPOP` receives the operator's code, and the operands follow. -/
def retAppOp (m : Machine) : Machine :=
  let s := slotAt m.heap m.k
  let app := s.b
  let args := s.c
  let m := setA { m with k := s.a } app m.val
  if args == NILV then expanded m app
  else
    let m := node m C_CHAIN 0 NONE 0
    let cell := m.val
    let m := setB m app cell
    let m := pushFrame { m with env := s.d } X_ARGS app 0 0
    startList m cell args

/-- `X_LET` receives the end of its bindings, then the end of its body. -/
def retLet (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let form := s.b
  let rest := fb m.heap form
  let bs := fa m.heap rest
  let body := fb m.heap rest
  let n := listLength m.heap bs
  let dup := firstDuplicate m.heap bs n
  if countOf s.kind == 0 then
    let m := scopeWithBindings m s.d bs n
    let scope := m.val
    let m := node m C_LAMBDA n 0 NONE
    let lam := m.val
    let m := setD (setCount m fr X_LET 1) fr lam
    startBody { m with env := scope } lam body KW_LET
  else if m.val == LISTIMPROPER then syntaxError m M_BADFORM KW_LET
  else if dup != NONE then syntaxError m M_DUPLICATE dup
  else
    let m := node { m with k := s.a } C_APP s.d s.c 0
    expanded m m.val

/-- `X_LETREC` receives the end of its bindings, then the end of its body. -/
def retLetrec (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let form := s.b
  let rest := fb m.heap form
  let bs := fa m.heap rest
  let body := fb m.heap rest
  let n := listLength m.heap bs
  let dup := firstDuplicate m.heap bs n
  let firstCell := fc m.heap s.d
  let holderBody := fc m.heap s.c
  if countOf s.kind == 0 then
    if n == 0 then
      let m := node m C_LAMBDA 0 0 NONE
      let lam := m.val
      let m := setD (setC (setCount m fr X_LETREC 1) fr lam) fr lam
      startBody { m with env := s.d } lam body KW_LETREC
    else
      -- the inner call: ((lambda (temp …) (set! v temp) …) init …)
      let st := LeanExe.loop n (m, NONE) fun j st =>
        let i := n - 1 - j
        let m := node st.1 C_LREF i 0 0
        let m := node m C_LSET (n + i) m.val 0
        let m := node m C_CHAIN m.val st.2 0
        let v := m.val
        (m, v)
      let m := node st.1 C_LAMBDA n 0 st.2
      let m := node m C_APP m.val s.c 0
      let m := node m C_CHAIN m.val NONE 0
      let m := node m C_LAMBDA n 0 m.val
      let outer := m.val
      let m := node m C_LAMBDA 0 0 NONE
      let holder := m.val
      let m := setD (setC (setCount m fr X_LETREC 1) fr holder) fr outer
      startBody { m with env := s.d } holder body KW_LETREC
  else if m.val == LISTIMPROPER then syntaxError m M_BADFORM KW_LETREC
  else if dup != NONE then syntaxError m M_DUPLICATE dup
  else
    let m := { m with k := s.a }
    if n == 0 then
      let m := node m C_APP s.d NONE 0
      expanded m m.val
    else
      let m := setB m firstCell holderBody
      let st := LeanExe.loop n (m, NONE) fun _ st =>
        let m := node st.1 C_CONST UNDEF 0 0
        let m := node m C_CHAIN m.val st.2 0
        let v := m.val
        (m, v)
      let m := node st.1 C_APP s.d st.2 0
      expanded m m.val

/-- `X_CONDIF` receives the code of its test, then the end of its sequence, then the code of the
remaining clauses. -/
def retCondIf (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let l := s.b
  let ifNode := s.c
  let c1 := fa m.heap ifNode
  let c2 := fb m.heap c1
  let c3 := fb m.heap c2
  let seq := fb m.heap (fa m.heap l)
  let more := fb m.heap l
  let lamBody := fc m.heap (fa m.heap c2)
  let phase := countOf s.kind
  let v := m.val
  if phase == 0 then
    let m := setA m c1 v
    let m := node m C_LAMBDA 0 0 NONE
    let lam := m.val
    let m := setCount (setA m c2 lam) fr X_CONDIF 1
    startBody { m with env := s.d } lam seq KW_COND
  else if phase == 1 then
    if v == LISTIMPROPER then syntaxError m M_BADFORM KW_COND
    else
      let m := beginCore m lamBody
      let m := setCount (setA m c2 m.val) fr X_CONDIF 2
      { m with x := more, env := s.d, mode := EXP_COND }
  else
    let m := setA { m with k := s.a } c3 v
    expanded m ifNode

/-- `X_CASE` receives the key's code, then the end of the walk of its clauses. -/
def retCase (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let clauses := fb m.heap (fb m.heap s.b)
  let n := listLength m.heap clauses
  let thunks := fb m.heap s.d
  let scope := fc m.heap s.d
  if m.val == LISTDONE then
    let m := caseBody { m with k := s.a } clauses n
    let m := node m C_CHAIN m.val NONE 0
    let m := node m C_LAMBDA (n + 1) 0 m.val
    let lam := m.val
    let m := node m C_CHAIN s.c thunks 0
    let m := node m C_APP lam m.val 0
    expanded m m.val
  else
    let m := setC m fr m.val
    let m := pushFrameN m X_CASEWALK 1 clauses s.d scope
    { m with mode := CASECL }

/-- A frame of quasiquotation, `X_QQCONS` or `X_QQAPPEND`, receives the code of the car, then that
of the cdr. -/
def retQQPair (m : Machine) (append : Bool) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  if s.c == 0 then
    { (setC m fr m.val) with x := s.b, env := s.d, nargs := countOf s.kind, mode := EXP_QQ }
  else
    let m := callPrim2 { m with k := s.a } (if append then P_APPEND else P_CONS) s.c m.val
    expanded m m.val

/-- `X_TOPDEF` receives the code of a definition's expression. -/
def retTopDef (m : Machine) : Machine :=
  let s := slotAt m.heap m.k
  let next := s.a
  let walk := next != NONE && subAt m.heap next == X_TOPWALK
  let last := if walk then fc m.heap next else NONE
  let m := node { m with k := next } C_GDEF s.b m.val 0
  let m := node m C_CHAIN m.val NONE 0
  let cell := m.val
  if walk then { (setC (setB m last cell) next cell) with mode := TOPWALK }
  else { m with mode := TOPCODE }

/-- `EXPANDED`: the frame on top receives the code or token `val`. -/
def expandReturn (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let sub := subOf s.kind
  let v := m.val
  if sub == X_LIST then listNext m
  else if sub == X_BIND then bindNext m
  else if sub == X_APPOP then retAppOp m
  else if sub == X_ARGS then
    if v == LISTIMPROPER then syntaxError m M_IMPROPER 0 else expanded { m with k := s.a } s.b
  else if sub == X_LAMBDA then
    if v == LISTIMPROPER then syntaxError m M_BADFORM KW_LAMBDA else lambdaDone m
  else if sub == X_BEGIN then
    let body := fc m.heap s.b
    if v == LISTIMPROPER then syntaxError m M_BADFORM s.c
    else
      let m := beginCore { m with k := s.a } body
      expanded m m.val
  else if sub == X_IF then expanded { m with k := s.a } s.b
  else if sub == X_SET then
    let m := setB { m with k := s.a } s.b v
    expanded m s.b
  else if sub == X_LET then retLet m
  else if sub == X_LETREC then retLetrec m
  else if sub == X_OR then
    let flag := countOf s.kind
    if s.c == 0 then
      { (setC m fr v) with
        x := s.b
        env := s.d
        mode := if flag == F_AND then EXP_AND else if flag == F_COND then EXP_COND else EXP_OR }
    else
      let m := { m with k := s.a }
      let m := if flag == F_AND then andCore m s.c v else orCore m s.c v
      expanded m m.val
  else if sub == X_CONDIF then retCondIf m
  else if sub == X_CASE then retCase m
  else if sub == X_CASEWALK then
    if v == LISTIMPROPER then syntaxError m M_BADFORM KW_CASE else { m with mode := CASECL }
  else if sub == X_QQCONS then retQQPair m false
  else if sub == X_QQAPPEND then retQQPair m true
  else if sub == X_QQWRAP then
    let m := node { m with k := s.a } C_CONST s.b 0 0
    let m := callPrim2 m P_LIST m.val v
    expanded m m.val
  else if sub == X_QQVEC then
    let m := callPrim1 { m with k := s.a } P_LISTTOVECTOR v
    expanded m m.val
  else if sub == X_TOPONE then
    let m := node { m with k := s.a } C_CHAIN v NONE 0
    { m with mode := TOPCODE }
  else if sub == X_TOPDEF then retTopDef m
  else fail m S_SYNTAX 0

/-! ## Top-level forms -/

/-- Whether a list holds only definitions (§5.2, §7.1.5): forms `(define …)` and `begin`s of
definitions, as the reference's `allDefinitions`.  The walk keeps the pending lists in pairs above
`top`, which it releases afterwards. -/
def allDefinitions (m : Machine) (l : UInt64) : Machine × Bool :=
  let top := m.top
  let st := LeanExe.repeatWhile m.cap (m, l, NILV, (0 : UInt64))
    (fun s => s.2.2.2 == 0 && s.1.status == 0)
    fun s =>
      let m := s.1
      let cur := s.2.1
      let stack := s.2.2.1
      if isPair m.heap cur then
        let e := fa m.heap cur
        let kw := if isPair m.heap e then keywordOf m.heap (fa m.heap e) else 0
        let rest := fb m.heap cur
        if kw == KW_DEFINE then (m, rest, stack, 0)
        else if kw == KW_BEGIN then
          let inner := fb m.heap e
          let m := alloc m (mkKind K_PAIR 0 0) rest stack 0 0
          let v := m.val
          (m, inner, v, 0)
        else (m, cur, stack, 2)
      else if cur == NILV then
        if stack == NILV then (m, cur, stack, 1) else (m, fa m.heap stack, fb m.heap stack, 0)
      else (m, cur, stack, 2)
  ({ st.1 with top := top }, st.2.2.2 == 1)

/-- The top-level forms of the datum `d` (§5.1, §5.2): a definition, the definitions of a `begin`
of definitions, or an expression.  The mode `TOPCODE` then holds their chain in `val`. -/
def topExpand (m : Machine) (d : UInt64) : Machine :=
  let h := m.heap
  let kw := if isPair h d then keywordOf h (fa h d) else 0
  let rest := if isPair h d then fb h d else NONE
  let shaped := isPair h rest && isKind h (fa h rest) K_SYMBOL && isPair h (fb h rest) &&
    fb h (fb h rest) == NILV
  let shorthand := isPair h rest && isPair h (fa h rest)
  let v := if shaped then fa h rest else NONE
  let vkw := keywordOf h v
  let e := if shaped then fa h (fb h rest) else NONE
  if kw == KW_DEFINE then
    if shaped then
      if vkw != 0 then syntaxError m M_KEYWORD vkw
      else
        let m := pushFrame m X_TOPDEF v 0 0
        { m with x := e, env := NONE, mode := EXPAND }
    else if shorthand then syntaxError m M_UNSUPPORTED KW_DEFINE
    else syntaxError m M_BADFORM KW_DEFINE
  else
    let r := if kw == KW_BEGIN then allDefinitions m rest else (m, false)
    let m := r.1
    if r.2 then
      let m := node m C_CHAIN 0 NONE 0
      let m := pushFrame m X_TOPWALK rest m.val m.val
      { m with mode := TOPWALK }
    else
      let m := pushFrame m X_TOPONE 0 0 0
      { m with x := d, env := NONE, mode := EXPAND }

/-- One step of `TOPWALK`: the next definition of a `begin` of definitions, in the order of the
reference's `expandTops`.  The walk's frame holds the rest of the current list, the last cell of the
chain after the first cell in field `d`, and in its count nothing; pending lists wait in pairs on
the frame's list in field `d` of the first cell. -/
def topWalk (m : Machine) : Machine :=
  let h := m.heap
  let fr := m.k
  let s := slotAt h fr
  let cur := s.b
  let first := s.d
  let e := if isPair h cur then fa h cur else NONE
  let more := if isPair h cur then fb h cur else NONE
  let rest := if isPair h e then fb h e else NONE
  let isBegin := isPair h e && keywordOf h (fa h e) == KW_BEGIN
  let shaped := isPair h rest && isKind h (fa h rest) K_SYMBOL && isPair h (fb h rest) &&
    fb h (fb h rest) == NILV
  let shorthand := isPair h rest && isPair h (fa h rest)
  let v := if shaped then fa h rest else NONE
  let vkw := keywordOf h v
  let init := if shaped then fa h (fb h rest) else NONE
  let pending := fc h first
  let resumed := if isPair h pending then fa h pending else NONE
  let below := if isPair h pending then fb h pending else NONE
  let chain := fb h first
  if isPair h cur then
    if isBegin then
      -- the pending rest of this list waits on the first cell's field c
      let m := alloc m (mkKind K_PAIR 0 0) more pending 0 0
      setB (setC m first m.val) fr rest
    else
      let m := setB m fr more
      if shaped then
        if vkw != 0 then syntaxError m M_KEYWORD vkw
        else
          let m := pushFrame m X_TOPDEF v 0 0
          { m with x := init, env := NONE, mode := EXPAND }
      else if shorthand then syntaxError m M_UNSUPPORTED KW_DEFINE
      else syntaxError m M_BADFORM KW_DEFINE
  else if pending != 0 && pending != NONE then setC (setB m fr resumed) first below
  else { m with k := s.a, val := chain, mode := TOPCODE }

end Demos.Scheme.Machine
