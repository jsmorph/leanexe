module

public import Demos.Scheme.Machine.Numeric
public import Demos.Scheme.Machine.Expand

@[expose] public section

/-! The evaluator of the executable interpreter: the rules of the reference machine
(`Demos.Scheme.Semantics.step`) over code, environments, and frames in the arena.  An environment
is a chain of cells, one location for each variable, and a continuation is the chain of frames
from `k`, which no rule changes, so an escape procedure that holds a frame chain resumes the work
as it was at its capture, as often as it is called.

The mode `EVAL` evaluates the code `x` in the environment `env`, `APPLY` applies the procedure
`val` to the arguments `args`, a list whose last argument is first, with `nargs` elements, and
`RETURN` passes `val` to the frame on top.  The frames of a call are `E_FN` while the operator is
evaluated, then `E_FNV`, which holds the operator's value, below `E_ARG`, which holds the operands
still to evaluate and the values so far.  A call in tail position, the last expression of a body,
and an arm of `if` get the continuation of their context. -/

namespace Demos.Scheme.Machine

def E_FN : UInt64 := 64
def E_FNV : UInt64 := 65
def E_ARG : UInt64 := 66
def E_IF : UInt64 := 67
def E_SEQ : UInt64 := 68
def E_LSET : UInt64 := 69
def E_GSET : UInt64 := 70
def E_GDEF : UInt64 := 71
def E_TOP : UInt64 := 72
def E_TOPX : UInt64 := 73
def E_TOPC : UInt64 := 74
def E_MAP : UInt64 := 75
def E_FOREACH : UInt64 := 76

/-- The error `entry` of the class *error*. -/
@[inline] def runError (m : Machine) (entry detail : UInt64) : Machine :=
  fail m (S_ERROR + entry) detail

/-- The value `v` returned to the frame on top. -/
def returnVal (m : Machine) (v : UInt64) : Machine := { m with val := v, mode := RETURN }

/-- The cell at position `i` of the environment `env`. -/
@[inline] def cellAt (heap : Array Slot) (env i : UInt64) : UInt64 :=
  LeanExe.repeatWhile i env (fun _ => true) fun c => fb heap c

/-- Whether a value is a procedure: a standard procedure, a closure, or an escape procedure. -/
@[inline] def isProcedure (heap : Array Slot) (v : UInt64) : Bool :=
  isPrim v || isKind heap v K_CLOSURE || isKind heap v K_ESCAPE

/-- The evaluation of a body, the chain `body`, in `env`: its commands with `E_SEQ` frames, then its
last expression with the body's continuation. -/
def enterBody (m : Machine) (body env : UInt64) : Machine :=
  let m := if fb m.heap body == NONE then m else pushFrame m E_SEQ (fb m.heap body) env 0
  let first := fa m.heap body
  { m with x := first, env := env, mode := EVAL }

/-- One step of `EVAL`: the code `x` in `env`. -/
def evalStep (m : Machine) : Machine :=
  let c := m.x
  let s := slotAt m.heap c
  let sub := subOf s.kind
  if sub == C_CONST then returnVal m s.a
  else if sub == C_LREF then
    let v := fa m.heap (cellAt m.heap m.env s.a)
    if v == UNDEF then runError m M_UNDEFINED 0 else returnVal m v
  else if sub == C_GREF then
    let v := fb m.heap s.a
    if v == UNBOUND then runError m M_UNBOUND s.a
    else if v == UNDEF then runError m M_UNDEFINED 0
    else returnVal m v
  else if sub == C_APP then
    let m := pushFrame m E_FN s.b m.env 0
    { m with x := s.a }
  else if sub == C_LAMBDA then
    let m := alloc m (mkKind K_CLOSURE 0 0) c m.env 0 0
    returnVal m m.val
  else if sub == C_IF then
    let test := fa m.heap s.a
    let m := pushFrame m E_IF s.a m.env 0
    { m with x := test }
  else if sub == C_LSET then
    let m := pushFrame m E_LSET s.a m.env 0
    { m with x := s.b }
  else if sub == C_GSET then
    let m := pushFrame m E_GSET s.a 0 0
    { m with x := s.b }
  else if sub == C_GDEF then
    let m := pushFrame m E_GDEF s.a 0 0
    { m with x := s.b }
  else fail m S_ERROR 0

/-- A list of fresh mutable pairs of the elements of `l` in reverse order, before `tail`. -/
def reverseOnto (m : Machine) (l tail : UInt64) : Machine :=
  let st := LeanExe.repeatWhile 16777216 (m, l, tail) (fun s => s.1.status == 0 && isPair s.1.heap s.2.1)
    fun s =>
      let x := fa s.1.heap s.2.1
      let next := fb s.1.heap s.2.1
      let m := alloc s.1 (mkKind K_PAIR 0 0 ||| MUTABLE) x s.2.2 0 0
      let v := m.val
      (m, next, v)
  { st.1 with val := st.2.2 }

/-- The application of a closure: its fixed variables bound to fresh cells that hold the
arguments, and its rest variable to a fresh list of the surplus arguments (§4.1.4), then its
body. -/
def applyClosure (m : Machine) (f : UInt64) : Machine :=
  let h := m.heap
  let lam := fa h f
  let cenv := fb h f
  let n := fa h lam
  let rest := fb h lam == 1
  let body := fc h lam
  if (!rest && m.nargs != n) || (rest && m.nargs < n) then runError m M_ARITY 0
  else
    -- the surplus arguments, last first, become the rest list in order
    let surplus := m.nargs - n
    let st := LeanExe.loop (if rest then surplus else 0) (m, m.args, NILV) fun _ s =>
      let x := fa s.1.heap s.2.1
      let next := fb s.1.heap s.2.1
      let m := alloc s.1 (mkKind K_PAIR 0 0 ||| MUTABLE) x s.2.2 0 0
      let v := m.val
      (m, next, v)
    let m := st.1
    let fixedArgs := if rest then st.2.1 else m.args
    let m := if rest then alloc m (mkKind K_CELL 0 0) st.2.2 cenv 0 0 else { m with val := cenv }
    let st := LeanExe.loop n (m, fixedArgs, m.val) fun _ s =>
      let x := fa s.1.heap s.2.1
      let next := fb s.1.heap s.2.1
      let m := alloc s.1 (mkKind K_CELL 0 0) x s.2.2 0 0
      let v := m.val
      (m, next, v)
    enterBody st.1 body st.2.2

/-- The arguments of a call of `map` or `for-each` from the lists `lists`: the cars of the lists,
last first, as the arguments, and a fresh list of their cdrs, in `aux`. -/
def carsAndCdrs (m : Machine) (lists : UInt64) : Machine :=
  let st := LeanExe.repeatWhile 16777216 (m, lists, NILV, (0 : UInt64))
    (fun s => s.1.status == 0 && isPair s.1.heap s.2.1)
    fun s =>
      let l := fa s.1.heap s.2.1
      let x := fa s.1.heap l
      let next := fb s.1.heap s.2.1
      let m := alloc s.1 (mkKind K_PAIR 0 0 ||| MUTABLE) x s.2.2.1 0 0
      let v := m.val
      (m, next, v, s.2.2.2 + 1)
  let m := { st.1 with args := st.2.2.1, nargs := st.2.2.2 }
  -- the cdrs in the order of the lists
  let m := reverseOnto m lists NILV
  let st := LeanExe.repeatWhile 16777216 (m, m.val, NILV) (fun s => s.1.status == 0 && isPair s.1.heap s.2.1)
    fun s =>
      let x := fb s.1.heap (fa s.1.heap s.2.1)
      let next := fb s.1.heap s.2.1
      let m := alloc s.1 (mkKind K_PAIR 0 0 ||| MUTABLE) x s.2.2 0 0
      let v := m.val
      (m, next, v)
  { st.1 with aux := st.2.2 }

/-- The next call of `map`'s procedure `f` on the cars of the lists, or the list of the results
`done`, last first, when every list has ended (§6.9); lists that end at different elements, or a
list that ends in another object, are an error. -/
def mapNext (m : Machine) (f lists done : UInt64) (isMap : Bool) : Machine :=
  let h := m.heap
  let allPairs := LeanExe.repeatWhile 16777216 lists (fun l => isPair h l && isPair h (fa h l))
    (fun l => fb h l) == NILV
  let allNil := LeanExe.repeatWhile 16777216 lists (fun l => isPair h l && fa h l == NILV)
    (fun l => fb h l) == NILV
  if allPairs then
    let m := carsAndCdrs m lists
    let m := if isMap then pushFrame m E_MAP f m.aux done else pushFrame m E_FOREACH f m.aux 0
    { m with val := f, mode := APPLY }
  else if allNil then
    if isMap then
      let m := reverseOnto m done NILV
      returnVal m m.val
    else returnVal m UNSPEC
  else runError m M_TYPE 0

/-! ## Standard procedures -/

/-- The essential arities of the standard procedures (§6): the least and the greatest number of
arguments. -/
def primArity (p : UInt64) : UInt64 × UInt64 :=
  if p == P_EQ || p == P_EQV || p == P_CONS || p == P_SETCAR || p == P_SETCDR ||
      p == P_LISTREF || p == P_MEMQ || p == P_MEMV || p == P_ASSQ || p == P_ASSV ||
      p == P_APPLY || p == N_QUOTIENT || p == N_REMAINDER || p == N_MODULO then (2, 2)
  else if p == P_LIST || p == P_APPEND || p == N_ADD || p == N_MUL || p == N_GCD ||
      p == N_LCM then (0, 16777216)
  else if p == N_MAX || p == N_MIN then (1, 16777216)
  else if (N_EQ ≤ p && p ≤ N_GE) || p == P_MAP || p == P_FOREACH then (2, 16777216)
  else if p == N_SUB || p == N_DIV then (1, 2)
  else (1, 1)

/-- The length of a proper list, and whether the list is proper: a list that reaches `()` within
the arena's number of pairs. -/
def properLength (heap : Array Slot) (cap l : UInt64) : UInt64 × Bool :=
  let r := LeanExe.repeatWhile (cap + 1) (l, (0 : UInt64)) (fun s => isPair heap s.1)
    fun s => (fb heap s.1, s.2 + 1)
  (r.2, r.1 == NILV)

/-- The first pair of a proper list whose car is `x`, or `#f`. -/
def memFind (heap : Array Slot) (x l : UInt64) : UInt64 :=
  let r := LeanExe.repeatWhile 16777216 l (fun l => isPair heap l && fa heap l != x)
    fun l => fb heap l
  if isPair heap r then r else FALSE

/-- The first element of a proper list of pairs whose car is `x`, or `#f`. -/
def assFind (heap : Array Slot) (x l : UInt64) : UInt64 :=
  let r := LeanExe.repeatWhile 16777216 l (fun l => isPair heap l && fa heap (fa heap l) != x)
    fun l => fb heap l
  if isPair heap r then fa heap r else FALSE

/-- Whether every element of a proper list is a pair. -/
def allPairs (heap : Array Slot) (l : UInt64) : Bool :=
  LeanExe.repeatWhile 16777216 l (fun l => isPair heap l && isPair heap (fa heap l))
    (fun l => fb heap l) == NILV

/-- The value after the operations of a composition of `car`s and `cdr`s with code `256 + q`, or
the error for an object on the way that is no pair. -/
def cxrWalk (heap : Array Slot) (q x : UInt64) : UInt64 × Bool :=
  let r := LeanExe.repeatWhile 8 (q, x, true) (fun s => s.2.2 && s.1 > 1)
    fun s =>
      if isPair heap s.2.1 then
        (s.1 >>> 1, if s.1 &&& 1 == 1 then fa heap s.2.1 else fb heap s.2.1, true)
      else (s.1, s.2.1, false)
  (r.2.1, r.2.2)

/-- `append` (§6.3): fresh copies of the lists before the last argument, which the result shares. -/
def appendLists (m : Machine) : Machine :=
  if m.nargs == 0 then returnVal m NILV
  else
    let h := m.heap
    let firsts := fb h m.args
    let ok := LeanExe.repeatWhile 16777216 firsts
      (fun l => isPair h l && (properLength h m.cap (fa h l)).2) (fun l => fb h l) == NILV
    if !ok then runError m M_TYPE 0
    else
      let last := fa h m.args
      let st := LeanExe.repeatWhile 16777216 (m, firsts, last)
        (fun s => s.1.status == 0 && isPair s.1.heap s.2.1)
        fun s =>
          let l := fa s.1.heap s.2.1
          let next := fb s.1.heap s.2.1
          let m := reverseOnto s.1 l NILV
          let m := reverseOnto m m.val s.2.2
          let v := m.val
          (m, next, v)
      returnVal st.1 st.2.2

/-- A standard procedure other than `apply`, `map`, `for-each`, and
`call-with-current-continuation`, on arguments that meet its arity (§6). -/
def applySimple (m : Machine) (p : UInt64) : Machine :=
  let h := m.heap
  let rest := if isPair h m.args then fb h m.args else NILV
  let x := if isPair h m.args then fa h m.args else NILV
  let y := if isPair h rest then fa h rest else NILV
  -- `x` is the last argument and `y` the one before it
  if p == P_NOT then returnVal m (boolV (x == FALSE))
  else if p == P_ISBOOLEAN then returnVal m (boolV (x == FALSE || x == TRUE))
  else if p == P_EQ || p == P_EQV then returnVal m (boolV (x == y))
  else if p == P_ISPAIR then returnVal m (boolV (isPair h x))
  else if p == P_CONS then
    let m := alloc m (mkKind K_PAIR 0 0 ||| MUTABLE) y x 0 0
    returnVal m m.val
  else if p == P_CAR then if isPair h x then returnVal m (fa h x) else runError m M_TYPE 0
  else if p == P_CDR then if isPair h x then returnVal m (fb h x) else runError m M_TYPE 0
  else if p == P_SETCAR || p == P_SETCDR then
    if !isPair h y then runError m M_TYPE 0
    else if !isMutable h y then runError m M_IMMUTABLE 0
    else returnVal (if p == P_SETCAR then setA m y x else setB m y x) UNSPEC
  else if p == P_ISNULL then returnVal m (boolV (x == NILV))
  else if p == P_ISLIST then returnVal m (boolV (properLength h m.cap x).2)
  else if p == P_LIST then
    let m := reverseOnto m m.args NILV
    returnVal m m.val
  else if p == P_LENGTH then
    let r := properLength h m.cap x
    if r.2 then returnVal m (mkFix r.1.toInt64) else runError m M_TYPE 0
  else if p == P_APPEND then appendLists m
  else if p == P_REVERSE then
    if (properLength h m.cap x).2 then
      let m := reverseOnto m x NILV
      returnVal m m.val
    else runError m M_TYPE 0
  else if p == P_LISTREF then
    if !isFix x then runError m M_TYPE 0
    else
      let r := properLength h m.cap y
      let i := fixVal x
      if !r.2 then runError m M_TYPE 0
      else if i < 0 || i.toUInt64 ≥ r.1 then runError m M_INDEX 0
      else returnVal m (fa h (cellAt h y i.toUInt64))
  else if p == P_MEMQ || p == P_MEMV then
    if (properLength h m.cap x).2 then returnVal m (memFind h y x) else runError m M_TYPE 0
  else if p == P_ASSQ || p == P_ASSV then
    if (properLength h m.cap x).2 && allPairs h x then returnVal m (assFind h y x)
    else runError m M_TYPE 0
  else if P_NUM ≤ p && p ≤ N_ROUND then
    let m := Numeric.apply m p
    { m with mode := RETURN }
  else if p == P_ISPROCEDURE then returnVal m (boolV (isProcedure h x))
  else if p == P_ISVECTOR then returnVal m (boolV (isKind h x K_VECTOR))
  else if p == P_LISTTOVECTOR then
    if (properLength h m.cap x).2 then
      let m := listToVector m x MUTABLE
      returnVal m m.val
    else runError m M_TYPE 0
  else if p ≥ P_CXR then
    let r := cxrWalk h (p - P_CXR) x
    if r.2 then returnVal m r.1 else runError m M_TYPE 0
  else runError m M_NOTPROC 0

/-- A call of the standard procedure `p` (§6.9 for `apply`, `map`, `for-each`, and
`call-with-current-continuation`). -/
def applyPrim (m : Machine) (p : UInt64) : Machine :=
  let h := m.heap
  let ar := primArity p
  if m.nargs < ar.1 || m.nargs > ar.2 then runError m M_ARITY 0
  else if p == P_APPLY then
    let f := fa h (fb h m.args)
    let lst := fa h m.args
    let r := properLength h m.cap lst
    if !isProcedure h f || !r.2 then runError m M_TYPE 0
    else
      let m := reverseOnto m lst NILV
      { m with val := f, args := m.val, nargs := r.1, mode := APPLY }
  else if p == P_CALLCC then
    let f := fa h m.args
    if !isProcedure h f then runError m M_TYPE 0
    else
      let m := alloc m (mkKind K_ESCAPE 0 0) m.k 0 0 0
      let m := alloc m (mkKind K_PAIR 0 0) m.val NILV 0 0
      { m with val := f, args := m.val, nargs := 1, mode := APPLY }
  else if p == P_MAP || p == P_FOREACH then
    let m := reverseOnto m m.args NILV
    let f := fa m.heap m.val
    let lists := fb m.heap m.val
    if !isProcedure m.heap f then runError m M_TYPE 0
    else mapNext m f lists NILV (p == P_MAP)
  else applySimple m p

/-- One step of `APPLY`: the procedure `val` on the arguments. -/
def applyStep (m : Machine) : Machine :=
  let h := m.heap
  let f := m.val
  if isPrim f then applyPrim m (primCode f)
  else if isKind h f K_CLOSURE then applyClosure m f
  else if isKind h f K_ESCAPE then
    if m.nargs == 1 then
      let v := fa h m.args
      let saved := fa h f
      { m with val := v, k := saved, mode := RETURN }
    else runError m M_ARITY 0
  else runError m M_NOTPROC 0

/-! ## Frames -/

/-- One step of `RETURN`: the frame on top receives `val`.  With no frame, the run's value is
`val`, which the printer writes. -/
def returnStep (m : Machine) : Machine :=
  let fr := m.k
  let v := m.val
  if fr == NONE then { m with x := v, aux := DONE, mode := PRINT }
  else
    let s := slotAt m.heap fr
    let sub := subOf s.kind
    let next := s.a
    -- the words of the frame's targets, read before the first write
    let chained := sub == E_FN || sub == E_ARG || sub == E_TOP || sub == E_TOPC
    let first := if chained then fa m.heap s.b else 0
    let rest := if chained then fb m.heap s.b else 0
    let fnv := if sub == E_ARG then fb m.heap next else 0
    let below := if sub == E_ARG then fa m.heap next else 0
    let thenArm := if sub == E_IF then fa m.heap (fb m.heap s.b) else 0
    let elseArm := if sub == E_IF then fa m.heap (fb m.heap (fb m.heap s.b)) else 0
    let cell := if sub == E_LSET then cellAt m.heap s.c s.b else 0
    let global := if sub == E_GSET then fb m.heap s.b else 0
    let m := { m with k := next }
    if sub == E_FN then
      if s.b == NONE then { m with args := NILV, nargs := 0, mode := APPLY }
      else
        let m := pushFrame m E_FNV v 0 0
        let m := pushFrameN m E_ARG 0 rest s.c NILV
        { m with x := first, env := s.c, mode := EVAL }
    else if sub == E_ARG then
      let n := countOf s.kind + 1
      let m := alloc m (mkKind K_PAIR 0 0) v s.d 0 0
      let done := m.val
      if s.b == NONE then { m with val := fnv, k := below, args := done, nargs := n, mode := APPLY }
      else
        let m := pushFrameN m E_ARG n rest s.c done
        { m with x := first, env := s.c, mode := EVAL }
    else if sub == E_IF then
      { m with x := if v == FALSE then elseArm else thenArm, env := s.c, mode := EVAL }
    else if sub == E_SEQ then enterBody m s.b s.c
    else if sub == E_LSET then returnVal (setA m cell v) UNSPEC
    else if sub == E_GSET then
      if global == UNBOUND then runError m M_UNBOUND s.b else returnVal (setB m s.b v) UNSPEC
    else if sub == E_GDEF then returnVal (setB m s.b v) UNSPEC
    else if sub == E_TOP then
      if isPair m.heap s.b then
        let m := pushFrame m E_TOPX rest v 0
        topExpand m first
      else returnVal m v
    else if sub == E_TOPC then
      if s.b == NONE then
        let m := pushFrame m E_TOP s.c 0 0
        returnVal m v
      else
        let m := pushFrame m E_TOPC rest s.c 0
        { m with x := first, env := NONE, mode := EVAL }
    else if sub == E_MAP then
      let m := alloc m (mkKind K_PAIR 0 0) v s.d 0 0
      mapNext m s.b s.c m.val true
    else if sub == E_FOREACH then mapNext m s.b s.c NILV false
    else fail m S_ERROR 0

/-- In mode 2, the chain of a datum's forms in `val` replaces the frame `E_TOPX` that holds the
value of the earlier forms: the forms run in order. -/
def topRun (m : Machine) : Machine :=
  let s := slotAt m.heap m.k
  let m := pushFrame { m with k := s.a } E_TOPC m.val s.b 0
  returnVal m s.c

/-- The start of the evaluation in mode 2: the program's data in a frame `E_TOP`. -/
def startEval (m : Machine) : Machine :=
  let m := pushFrame m E_TOP m.forms 0 0
  returnVal m UNSPEC

end Demos.Scheme.Machine
