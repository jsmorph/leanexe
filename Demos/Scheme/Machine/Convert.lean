module

public import Demos.Scheme.Machine.Expand

@[expose] public section

/-! The external form of the code, which the export writes in mode 1 to test the expander against
the reference expander: each node becomes a list whose first element is a tag, 0 for a constant,
1 for a variable of a `lambda` with its position, 2 for a top-level variable with its symbol, 3 and
4 for the two forms of `set!`, 5 for a top-level definition, 6 for `if`, 7 for `lambda` with its
number of fixed variables and `#t` for a rest variable, 8 for a call, and 9 for a standard
procedure that a rule names, with its code.  The conversion keeps its pending work in frames. -/

namespace Demos.Scheme.Machine

def CONV : UInt64 := 18
def CONVK : UInt64 := 19
def M1NEXT : UInt64 := 20

def V_SUB : UInt64 := 52
def V_TOP : UInt64 := 53

/-- The list of the atoms `a`, `b`, and `c`, of which the first `n` count, with its last pair in
`aux`; its reference becomes `val`. -/
def prefixList (m : Machine) (n a b c : UInt64) : Machine :=
  let m := alloc m (mkKind K_PAIR 0 0) (if n == 1 then a else if n == 2 then b else c) NILV 0 0
  let last := m.val
  let m := if n ≥ 3 then alloc m (mkKind K_PAIR 0 0) b m.val 0 0 else m
  let m := if n ≥ 2 then alloc m (mkKind K_PAIR 0 0) a m.val 0 0 else m
  { m with aux := last }

/-- One step of `CONV`: the node `x`. -/
def convStep (m : Machine) : Machine :=
  let h := m.heap
  let c := m.x
  let sub := subAt h c
  let a := fa h c
  let b := fb h c
  let body := fc h c
  -- the prefix, its length, and the chain of the codes after it
  let m :=
    if sub == C_CONST then
      if isPrim a then prefixList m 2 (mkFix 9) (mkFix (primCode a).toInt64) 0
      else prefixList m 2 (mkFix 0) a 0
    else if sub == C_LREF then prefixList m 2 (mkFix 1) (mkFix a.toInt64) 0
    else if sub == C_GREF then prefixList m 2 (mkFix 2) a 0
    else if sub == C_LSET then prefixList m 2 (mkFix 3) (mkFix a.toInt64) 0
    else if sub == C_GSET then prefixList m 2 (mkFix 4) a 0
    else if sub == C_GDEF then prefixList m 2 (mkFix 5) a 0
    else if sub == C_IF then prefixList m 1 (mkFix 6) 0 0
    else if sub == C_LAMBDA then prefixList m 3 (mkFix 7) (mkFix a.toInt64) (boolV (b == 1))
    else prefixList m 1 (mkFix 8) 0 0
  let head := m.val
  let last := m.aux
  let m :=
    if sub == C_LSET || sub == C_GSET || sub == C_GDEF then node m C_CHAIN b NONE 0
    else if sub == C_IF then { m with val := a }
    else if sub == C_LAMBDA then { m with val := body }
    else if sub == C_APP then node m C_CHAIN a b 0
    else { m with val := NONE }
  let subs := m.val
  if subs == NONE then { m with val := head, mode := CONVK }
  else
    let m := pushFrame m V_SUB (fb m.heap subs) last head
    { m with x := fa m.heap subs }

/-- One step of `CONVK`: the frame on top receives the list `val`. -/
def convReturn (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let rem := s.b
  let next := fa m.heap rem
  let after := fb m.heap rem
  if subOf s.kind == V_SUB then
    let m := alloc m (mkKind K_PAIR 0 0) m.val NILV 0 0
    let p := m.val
    let m := setC (setB m s.c p) fr p
    if rem == NONE then { m with k := s.a, val := s.d }
    else { (setB m fr after) with x := next, mode := CONV }
  else { m with x := m.val, aux := LINE, mode := PRINT }

/-- One step of `M1NEXT`: the next code of the chain of a datum's forms in the frame on top. -/
def m1Next (m : Machine) : Machine :=
  let fr := m.k
  let s := slotAt m.heap fr
  let rem := s.b
  let next := fa m.heap rem
  let after := fb m.heap rem
  if rem == NONE then { m with k := s.a, mode := TOP }
  else { (setB m fr after) with x := next, mode := CONV }

end Demos.Scheme.Machine
