import LeanExe.Smalltalk.Arena

namespace LeanExe.Smalltalk.Runtime
open Arena

@[inline] def classAt (p : Array UInt64) (c i : UInt64) : UInt64 := read p (8 + 4 * (c - 1) + i)
@[inline] def methodAt (p : Array UInt64) (m i : UInt64) : UInt64 :=
  read p (8 + 4 * read p 0 + 6 * (m - 1) + i)
@[inline] def codeAt (p : Array UInt64) (pc i : UInt64) : UInt64 :=
  read p (8 + 4 * read p 0 + 6 * read p 1 + 4 * pc + i)
@[inline] def dead : UInt64 := 18446744073709551615

def walk (s : Array UInt64) (head count : UInt64) : UInt64 :=
  LeanExe.loop (min count (read s 14)) head fun _ h =>
    if kind s h == 7 then field s h 3 else 0
def lexical (s : Array UInt64) (head count : UInt64) : UInt64 :=
  LeanExe.loop (min count (read s 14)) head fun _ h =>
    if kind s h == 5 then field s h 5 else 0
def localSlot (s : Array UInt64) (act index depth : UInt64) : UInt64 :=
  let a := lexical s act depth
  let head := if kind s a == 5 then field s a 6 else 0
  let h := walk s head index
  if index ≥ read s 14 || depth ≥ read s 14 || kind s h != 7 then 0 else h
def self (s : Array UInt64) (act : UInt64) : UInt64 :=
  let h := localSlot s act 0 0
  if h == 0 then 0 else field s h 2
def home (p s : Array UInt64) (act : UInt64) : UInt64 :=
  (LeanExe.loop (read s 14) (act, (0 : UInt64)) fun _ st =>
    let a := st.1
    let m := if kind s a == 5 then field s a 2 else 0
    let found := a != 0 && m != 0 && methodAt p m 1 != 0
    (if st.2 != 0 || found || a == 0 then 0 else field s a 5,
      if st.2 != 0 then st.2 else if found then a else 0)).2
def onChain (s : Array UInt64) (target : UInt64) : Bool :=
  (LeanExe.loop (read s 14) (read s 2, false) fun _ st =>
    (if kind s st.1 == 5 then field s st.1 4 else 0,
      st.2 || (st.1 != 0 && st.1 == target))).2
def objectClass (p s : Array UInt64) (h : UInt64) : UInt64 :=
  let tag := kind s h
  if tag == 1 then read p 6
  else if h == 1 then read p 4
  else if h == 2 || h == 3 then read p 5
  else if tag == 4 then field s h 2
  else if tag == 6 then read p 7
  else if tag == 8 then field s h 3 else 0
def lookup (p : Array UInt64) (owner selector : UInt64) : UInt64 :=
  let count := read p 1
  (LeanExe.loop (read p 0 * (count + 1)) (owner, (0 : UInt64), (0 : UInt64)) fun _ st =>
    let c := st.1
    let i := st.2.1
    let result := st.2.2
    let found := c != 0 && i < count && methodAt p (i + 1) 0 == c &&
      methodAt p (i + 1) 1 == selector
    (if result != 0 || c == 0 then c else if i == count then classAt p c 0 else c,
      if i == count then 0 else i + 1,
      if result != 0 then result else if found then i + 1 else 0)).2.2

def programTablesValid (p : Array UInt64) : Bool :=
  let classes := read p 0
  let methods := read p 1
  let validClasses := LeanExe.loop classes true fun i ok =>
    let c := i + 1
    let parent := classAt p c 0
    let inherited := if parent == 0 then true else if parent < c then
      classAt p parent 2 ≤ classAt p c 2 else false
    ok && parent < c && classAt p c 1 > 0 && classAt p c 1 ≤ classes &&
      classAt p c 2 ≤ 1048576 && classAt p c 3 == 0 &&
      inherited
  let validMethods := LeanExe.loop methods true fun i ok =>
    let m := i + 1
    ok && methodAt p m 0 > 0 && methodAt p m 0 ≤ classes &&
      methodAt p m 2 > 0 && methodAt p m 2 ≤ 1048576 && methodAt p m 3 ≤ 1048576 &&
      methodAt p m 4 < read p 2 && methodAt p m 5 ≤ 8
  validClasses && validMethods && methodAt p (read p 3) 2 == 1 && methodAt p (read p 3) 1 != 0
def programValid (p : Array UInt64) : Bool :=
  let n := if p.size ≥ 8 then read p 0 else 0
  let m := if p.size ≥ 8 then read p 1 else 0
  let count := if p.size ≥ 8 then read p 2 else 0
  let entry := if p.size ≥ 8 then read p 3 else 0
  let shape := n > 0 && n ≤ 1048576 && m > 0 && m ≤ 1048576 &&
    count > 0 && count ≤ 1048576 && entry > 0 && entry ≤ m &&
    p.size.toUInt64 == 8 + 4 * n + 6 * m + 4 * count
  let classes := if shape then read p 4 > 0 && read p 4 ≤ n && read p 5 > 0 &&
    read p 5 ≤ n && read p 6 > 0 && read p 6 ≤ n && read p 7 > 0 && read p 7 ≤ n else false
  let valid := LeanExe.loop (if shape then n + m else 0) true fun i ok =>
    if i < n then
      let c := i + 1
      let parent := classAt p c 0
      let inherited := if parent == 0 then true else if parent < c then
        classAt p parent 2 ≤ classAt p c 2 else false
      ok && parent < c && classAt p c 1 > 0 && classAt p c 1 ≤ n &&
        classAt p c 2 ≤ 1048576 && classAt p c 3 == 0 &&
        inherited
    else
      let id := i - n + 1
      ok && methodAt p id 0 > 0 && methodAt p id 0 ≤ n && methodAt p id 2 > 0 &&
        methodAt p id 2 ≤ 1048576 && methodAt p id 3 ≤ 1048576 &&
        methodAt p id 4 < count && methodAt p id 5 ≤ 8
  let entryOK := if shape then methodAt p entry 2 == 1 && methodAt p entry 1 != 0 else false
  shape && classes && valid && entryOK

def advance (s : Array UInt64) (stack : UInt64) : Array UInt64 :=
  let act := read s 2
  let pc := field s act 3 + 1
  write (write s (address act + 3) pc) (address act + 7) stack
def pushReady (s : Array UInt64) (value : UInt64) : Array UInt64 :=
  let act := read s 2
  let rest := field s act 7
  let s := allocate s 7 value rest 0 0 0 0
  let h := read s 10
  advance s h
def push (s : Array UInt64) (value : UInt64) : Array UInt64 :=
  let s := reserve s 1
  if read s 0 == 4 then s else pushReady s value
def literalReady (s : Array UInt64) (tag a b : UInt64) : Array UInt64 :=
  let s := allocate s tag a b 0 0 0 0
  let value := read s 10
  pushReady s value
def literal (s : Array UInt64) (tag a b : UInt64) : Array UInt64 :=
  let s := reserve s 2
  if read s 0 == 4 then s else literalReady s tag a b
def pop (s : Array UInt64) : Array UInt64 :=
  let stack := field s (read s 2) 7
  if kind s stack != 7 then fail s 4 else advance s (field s stack 3)
def loadSlot (s : Array UInt64) (slot : UInt64) : Array UInt64 :=
  let value := field s slot 2
  if slot == 0 then fail s 2 else push s value
def storeSlot (s : Array UInt64) (slot : UInt64) : Array UInt64 :=
  let stack := field s (read s 2) 7
  let value := field s stack 2
  let rest := field s stack 3
  if slot == 0 then fail s 2 else if kind s stack != 7 then fail s 4
  else advance (write s (address slot + 2) value) rest
def fieldSlot (s : Array UInt64) (index : UInt64) : UInt64 :=
  let receiver := self s (read s 2)
  let head := if kind s receiver == 4 then field s receiver 3 else 0
  let slot := walk s head index
  if index ≥ read s 14 || kind s slot != 7 then 0 else slot

def bindOne (s : Array UInt64) (args arity locals receiver i : UInt64) : Array UInt64 :=
  let index := arity + locals - 1 - i
  let h := walk s args (if index < arity then arity - 1 - index else 0)
  let value := if index == 0 then receiver else if index < arity then field s h 2 else 1
  let rest := read s 19
  let s := allocate s 7 value rest 0 0 0 0
  let head := read s 10
  write s 19 head
def bindNext (s : Array UInt64) (args arity locals receiver i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, bindOne s args arity locals receiver i)
def enterReady (p s : Array UInt64) (method args receiver caller lex : UInt64) : Array UInt64 :=
  let arity := methodAt p method 2
  let locals := methodAt p method 3
  let pc := methodAt p method 4
  let count := arity + locals
  let s := write s 19 0
  let (_, s) := LeanExe.repeatWhile count ((0 : UInt64), s)
    (fun (i, _) => i < count) (fun (i, s) => bindNext s args arity locals receiver i)
  let slots := read s 19
  let s := allocate s 5 method pc caller lex slots 0
  let act := read s 10
  write (write s 2 act) 19 0
def fillOne (s : Array UInt64) : Array UInt64 :=
  let rest := read s 19
  let s := allocate s 7 1 rest 0 0 0 0
  let h := read s 10
  write s 19 h
def fillNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 := (i + 1, fillOne s)
def newReady (s : Array UInt64) (classId metaId fields : UInt64) : Array UInt64 :=
  let s := write s 19 0
  let (_, s) := LeanExe.repeatWhile fields ((0 : UInt64), s)
    (fun (i, _) => i < fields) (fun (i, s) => fillNext s i)
  let head := read s 19
  let s := allocate s 4 classId head metaId 0 0 0
  write s 19 0
def bootReady (p s : Array UInt64) : Array UInt64 :=
  let method := read p 3
  let owner := methodAt p method 0
  let fields := classAt p owner 2
  let s := newReady s owner (classAt p owner 1) fields
  let receiver := read s 10
  enterReady p s method 0 receiver 0 0
def bootValid (p s : Array UInt64) : Array UInt64 :=
  let m := read p 3
  let need := classAt p (methodAt p m 0) 2 + methodAt p m 2 + methodAt p m 3 + 2
  let s := reserve s need
  if read s 0 == 4 then s else bootReady p s
def boot (p s : Array UInt64) : Array UInt64 :=
  let valid := programValid p
  if !valid || read s 2 != 0 || read s 0 != 0 then fail s 10 else bootValid p s

def retire (s : Array UInt64) (act : UInt64) : Array UInt64 :=
  write (write (write s (address act + 3) dead) (address act + 4) 0) (address act + 7) 0
def unwindNext (s : Array UInt64) (stop cursor : UInt64) : UInt64 × Array UInt64 :=
  let next := field s cursor 4
  (if cursor == stop then 0 else next, retire s cursor)
def returnCallerReady (s : Array UInt64) (caller value : UInt64) : Array UInt64 :=
  let rest := field s caller 7
  let s := allocate s 7 value rest 0 0 0 0
  let h := read s 10
  write (write s 2 caller) (address caller + 7) h
def returnCaller (s : Array UInt64) (caller value : UInt64) : Array UInt64 :=
  if caller == 0 then write (write (write s 0 3) 2 0) 7 value
  else returnCallerReady s caller value
def returnReady (s : Array UInt64) (stop caller value : UInt64) : Array UInt64 :=
  let cap := read s 14
  let current := read s 2
  let (_, s) := LeanExe.repeatWhile cap (current, s)
    (fun (cursor, _) => cursor != 0) (fun (cursor, s) => unwindNext s stop cursor)
  returnCaller s caller value
def returnReserved (s : Array UInt64) (stop caller value : UInt64) : Array UInt64 :=
  let s := reserve s (if caller == 0 then 0 else 1)
  if read s 0 == 4 then s else returnReady s stop caller value
def ret (p s : Array UInt64) (nonlocal : UInt64) : Array UInt64 :=
  let current := read s 2
  let stack := field s current 7
  let lexicalHome := home p s current
  let stop := if nonlocal == 0 then current else lexicalHome
  let active := onChain s stop
  let caller := field s stop 4
  let value := field s stack 2
  if kind s stack != 7 then fail s 4 else
  if kind s stop != 5 || field s stop 3 == dead || !active then fail s 7
  else returnReserved s stop caller value

def sendMethodReady (p s : Array UInt64) (method arity receiver lex : UInt64) : Array UInt64 :=
  let current := read s 2
  let args := field s current 7
  let rest := walk s args arity
  let s := advance s rest
  enterReady p s method args receiver current lex
def callMethod (p s : Array UInt64) (method arity receiver lex : UInt64) : Array UInt64 :=
  let need := methodAt p method 2 + methodAt p method 3 + 1
  let s := reserve s need
  if read s 0 == 4 then s else sendMethodReady p s method arity receiver lex

@[inline] def sign (w : UInt64) : UInt64 := w >>> 63
def arithmeticOK (op : UInt64) (s : Array UInt64) (a b : UInt64) : Bool :=
  let x := field s a 2
  let y := field s b 2
  let sum := x + y
  let diff := x - y
  kind s a == 1 && kind s b == 1 &&
    (op != 2 || sign x != sign y || sign sum == sign x) &&
    (op != 3 || sign x == sign y || sign diff == sign x)
def primitiveValue (op : UInt64) (s : Array UInt64) (a b : UInt64) : UInt64 :=
  let x := field s a 2
  let y := field s b 2
  let same := a == b || (kind s a == 1 && kind s b == 1 && x == y) ||
    (kind s a == 8 && kind s b == 8 && x == y)
  if op == 2 then x + y else if op == 3 then x - y
  else if op == 4 then if (x ^^^ 0x8000000000000000) < (y ^^^ 0x8000000000000000) then 3 else 2
  else if op == 5 then if x == y then 3 else 2
  else if same then 3 else 2
def finishPrimitive (s : Array UInt64) (arity value : UInt64) : Array UInt64 :=
  let act := read s 2
  let rest := walk s (field s act 7) arity
  pushReady (write s (address act + 7) rest) value
def binaryReady (s : Array UInt64) (op a b : UInt64) : Array UInt64 :=
  let value := primitiveValue op s a b
  let s := allocate s 1 value 0 0 0 0 0
  let result := read s 10
  finishPrimitive s 2 result
def primitiveBinaryReady (s : Array UInt64) (op a b : UInt64) : Array UInt64 :=
  let value := primitiveValue op s a b
  if op == 2 || op == 3 then binaryReady s op a b else finishPrimitive s 2 value
def primitiveBinary (s : Array UInt64) (op a b : UInt64) : Array UInt64 :=
  let s := reserve s 2
  if read s 0 == 4 then s else primitiveBinaryReady s op a b

def primitiveNewReady (p s : Array UInt64) (receiver : UInt64) : Array UInt64 :=
  let classId := field s receiver 2
  let s := newReady s classId (classAt p classId 1) (classAt p classId 2)
  let value := read s 10
  finishPrimitive s 1 value
def primitiveNew (p s : Array UInt64) (receiver : UInt64) : Array UInt64 :=
  let need := classAt p (field s receiver 2) 2 + 2
  let s := reserve s need
  if read s 0 == 4 then s else primitiveNewReady p s receiver
def primitiveCollect (s : Array UInt64) (receiver : UInt64) : Array UInt64 :=
  let s := collect s
  let s := reserve s 1
  if read s 0 == 4 then s else finishPrimitive s 1 receiver
def dispatchBlock (p s : Array UInt64) (receiver arity : UInt64) : Array UInt64 :=
  let method := field s receiver 2
  let lex := field s receiver 3
  let receiver := self s lex
  if method == 0 || method > read p 1 then fail s 10 else
  if methodAt p method 2 != arity then fail s 6 else callMethod p s method arity receiver lex
def dispatch (p s : Array UInt64) (method arity receiver : UInt64) : Array UInt64 :=
  let op := methodAt p method 5
  let stack := field s (read s 2) 7
  let arg := field s stack 2
  let okay := arithmeticOK op s receiver arg
  if op == 7 && kind s receiver == 6 then dispatchBlock p s receiver arity
  else if op == 1 && arity == 1 && kind s receiver == 8 then primitiveNew p s receiver
  else if op ≥ 2 && op ≤ 6 && arity == 2 && (op == 6 || okay) then primitiveBinary s op receiver arg
  else if op == 8 && arity == 1 then primitiveCollect s receiver
  else callMethod p s method arity receiver 0
def send (p s : Array UInt64) (selector nargs super : UInt64) : Array UInt64 :=
  let act := read s 2
  let slot := walk s (field s act 7) nargs
  let receiver := if kind s slot == 7 then field s slot 2 else 0
  let classId := objectClass p s receiver
  let owner := methodAt p (field s act 2) 0
  let start := if super == 0 then classId else classAt p owner 0
  let method := lookup p start selector
  if selector == 0 || nargs ≥ read s 14 then fail s 10 else
  if kind s slot != 7 then fail s 4 else
  if method == 0 then fail s 5 else
  if methodAt p method 2 != nargs + 1 then fail s 6 else dispatch p s method (nargs + 1) receiver
def branch (p s : Array UInt64) (target : UInt64) : Array UInt64 :=
  let act := read s 2
  let stack := field s act 7
  let value := if kind s stack == 7 then field s stack 2 else 0
  let rest := if kind s stack == 7 then field s stack 3 else 0
  let pc := field s act 3 + 1
  if target ≥ read p 2 then fail s 10 else if kind s stack != 7 then fail s 4
  else if value != 2 && value != 3 then fail s 8
  else write (write s (address act + 7) rest) (address act + 3) (if value == 2 then target else pc)
def accessLocal (s : Array UInt64) (op index depth : UInt64) : Array UInt64 :=
  let slot := localSlot s (read s 2) index depth
  if op == 2 then loadSlot s slot else storeSlot s slot
def accessField (s : Array UInt64) (op index : UInt64) : Array UInt64 :=
  let slot := fieldSlot s index
  if op == 4 then loadSlot s slot else storeSlot s slot

def execute (p s : Array UInt64) (op a b : UInt64) : Array UInt64 :=
  let act := read s 2
  let stack := field s act 7
  let top := field s stack 2
  if op == 0 then literal s 1 a 0
  else if op == 1 then if a ≤ 2 then push s (a + 1) else fail s 10
  else if op == 2 || op == 3 then accessLocal s op a b
  else if op == 4 || op == 5 then accessField s op a
  else if op == 6 then
    if a == 0 || a > read p 1 then fail s 10 else
    if methodAt p a 1 != 0 || methodAt p a 0 != methodAt p (field s act 2) 0 then fail s 10
    else literal s 6 a act
  else if op == 7 then
    if a == 0 || a > read p 0 then fail s 10 else literal s 8 a (classAt p a 1)
  else if op == 8 then if kind s stack != 7 then fail s 4 else push s top
  else if op == 9 then pop s
  else if op == 10 || op == 11 then send p s a b (op - 10)
  else if op == 12 || op == 13 then ret p s (op - 12)
  else if op == 14 then
    if a ≥ read p 2 then fail s 10 else write s (address act + 3) a
  else if op == 15 then branch p s a
  else fail s 10
def step (p s : Array UInt64) : Array UInt64 :=
  let act := read s 2
  if read s 0 != 0 then s else if kind s act != 5 then fail s 1 else
  if field s act 2 == 0 || field s act 2 > read p 1 || field s act 3 ≥ read p 2 then fail s 1 else
  let pc := field s act 3
  let op := codeAt p pc 0
  let a := codeAt p pc 1
  let b := codeAt p pc 2
  if codeAt p pc 3 != 0 ||
    (b != 0 && op != 2 && op != 3 && op != 10 && op != 11) ||
    (a != 0 && (op == 8 || op == 9 || op == 12 || op == 13)) then fail s 10
  else execute p s op a b
def runNext (p s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 := (i + 1, step p s)
def run (p s : Array UInt64) (fuel : UInt64) : Array UInt64 :=
  let (_, s) := LeanExe.repeatWhile fuel ((0 : UInt64), s)
    (fun (_, s) => read s 0 == 0) (fun (i, s) => runNext p s i)
  s
def resultWord (s : Array UInt64) : UInt64 :=
  let h := read s 7
  if kind s h == 1 || kind s h == 2 then field s h 2 else 0

end LeanExe.Smalltalk.Runtime
