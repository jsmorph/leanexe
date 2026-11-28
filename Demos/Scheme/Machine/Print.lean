module

public import Demos.Scheme.Machine.Text

@[expose] public section

/-! The printer of the executable interpreter: the written form of a value (§6.10.3) in the output
buffer, one atom or one step through a list or a vector at each step of the machine, with the
pending work in frames.  The forms are those of the reference semantics's `writeVal`, with
`#<procedure>` and `#<unspecified>` for the objects without a standard representation.  The
printer writes nothing past the output buffer's capacity and reports the outcome *output limit*
instead, so a circular structure ends the run there. -/

namespace Demos.Scheme.Machine

def P_TAIL : UInt64 := 48
def P_VEC : UInt64 := 49
def P_CLOSE : UInt64 := 50

/-- The machine with the byte `b` written, or the outcome *output limit*. -/
def emit (m : Machine) (b : UInt64) : Machine :=
  if m.outLen < m.outCap then { m with out := m.out.set! m.outLen.toNat b, outLen := m.outLen + 1 }
  else fail m S_OUTPUT 0

/-- The machine with the bytes of the table's entry `entry` written. -/
def emitEntry (names : Array UInt64) (m : Machine) (entry : UInt64) : Machine :=
  let len := names[(entry * 6 + 1).toNat]!
  LeanExe.loop len m fun i m =>
    emit m ((names[(entry * 6 + 2 + i / 8).toNat]! >>> (8 * (i % 8))) &&& 255)

/-- The machine with the decimal digits of `n` written, after a minus sign when `n` is
negative. -/
def emitInt (m : Machine) (n : Int64) : Machine :=
  let m := if n < 0 then emit m 45 else m
  let mag := if n < 0 then (0 - n).toUInt64 else n.toUInt64
  let base := m.outLen
  let nd := LeanExe.repeatWhile 20 ((1 : UInt64), mag / 10) (fun s => s.2 != 0)
    (fun s => (s.1 + 1, s.2 / 10)) |>.1
  if base + nd > m.outCap then fail m S_OUTPUT 0
  else
    let st := LeanExe.loop nd (m.out, mag) fun j st =>
      (st.1.set! (base + nd - 1 - j).toNat (48 + st.2 % 10), st.2 / 10)
    { m with out := st.1, outLen := base + nd }

/-- The machine with the bytes of the string `s` written, each double quote and backslash after a
backslash when `quoted`. -/
def emitString (m : Machine) (s : UInt64) (quoted : Bool) : Machine :=
  LeanExe.loop (fa m.heap s) m fun i m =>
    let b := stringByte m.heap s i
    let m := if quoted && (b == 34 || b == 92) then emit m 92 else m
    emit m b

/-- The written form of an atom: a value that holds no other value to write. -/
def emitAtom (names : Array UInt64) (m : Machine) (v : UInt64) : Machine :=
  if isFix v then emitInt m (fixVal v)
  else if v == FALSE then emit (emit m 35) 102
  else if v == TRUE then emit (emit m 35) 116
  else if v == NILV then emit (emit m 40) 41
  else if v == UNSPEC then emitEntry names m M_T_UNSPEC
  else if v == UNDEF then emitEntry names m M_T_UNDEF
  else if isChar v then
    if charCode v == 32 then emitEntry names m M_T_SPACE
    else if charCode v == 10 then emitEntry names m M_T_NEWLINE
    else emit (emit (emit m 35) 92) (charCode v)
  else if isPrim v then emitEntry names m M_T_PROC
  else
    let kind := kindAt m.heap v
    if kind == K_SYMBOL then emitString m (fa m.heap v) false
    else if kind == K_STRING then emit (emitString (emit m 34) v true) 34
    else emitEntry names m M_T_PROC

/-- One step of the printer on the value `x`: an atom, or the start of a list or a vector. -/
def printStep (names : Array UInt64) (m : Machine) : Machine :=
  let v := m.x
  let car := if isRef v then fa m.heap v else 0
  let cdr := if isRef v then fb m.heap v else 0
  let first := if isKind m.heap v K_VECTOR && car != 0 then vectorRef m.heap v 0 else 0
  if isPair m.heap v then
    let m := pushFrame (emit m 40) P_TAIL cdr 0 0
    { m with x := car }
  else if isKind m.heap v K_VECTOR then
    let m := emit (emit m 35) 40
    if car == 0 then { (emit m 41) with mode := PRINTK }
    else
      let m := pushFrame m P_VEC v 1 0
      { m with x := first }
  else { (emitAtom names m v) with mode := PRINTK }

/-- One step of the printer's frames: the next element of a list or a vector, a closing
parenthesis, or, when no printer's frame remains on top, the mode in `aux`. -/
def printFrame (m : Machine) : Machine :=
  let fr := m.k
  if fr == NONE then { m with mode := m.aux }
  else
    let s := slotAt m.heap fr
    let sub := subOf s.kind
    let rest := s.b
    let restCar := if isPair m.heap rest then fa m.heap rest else 0
    let restCdr := if isPair m.heap rest then fb m.heap rest else 0
    let len := if sub == P_VEC then fa m.heap rest else 0
    let elem := if sub == P_VEC && s.c < len then vectorRef m.heap rest s.c else 0
    if sub == P_TAIL then
      if rest == NILV then { (emit m 41) with k := s.a }
      else if isPair m.heap rest then
        let m := setB (emit m 32) fr restCdr
        { m with x := restCar, mode := PRINT }
      else
        let m := emit (emit (emit m 32) 46) 32
        let s' : Slot := ⟨mkKind K_FRAME P_CLOSE 0, s.a, s.b, s.c, s.d⟩
        { m with heap := m.heap.set! (fr >>> 3).toNat s', x := rest, mode := PRINT }
    else if sub == P_VEC then
      if s.c == len then { (emit m 41) with k := s.a }
      else
        let m := setC (emit m 32) fr (s.c + 1)
        { m with x := elem, mode := PRINT }
    else if sub == P_CLOSE then { (emit m 41) with k := s.a }
    else { m with mode := m.aux }

end Demos.Scheme.Machine
