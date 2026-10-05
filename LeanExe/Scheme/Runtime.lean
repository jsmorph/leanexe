import LeanExe.Scheme.Arena

/-!
Concrete VM. Code is a word array: instruction count, then four words per
instruction (opcode,a,b,c), followed by function descriptors. A descriptor holds
arity, formal names, capture count, and capture names. Captures share locations.
Opcodes: word, bool, unit, callcc, load, store, close, drop, jump, branch,
binary, call, tailcall, ret, global. `global` is initialization of a top-level binding.
Phases are exec=0, apply=1, returning=2, done=3, error=4.
-/

namespace LeanExe.Scheme.Runtime

open Arena

def wire (code : Array UInt64) (pc slot : UInt64) : UInt64 := read code (1 + 4 * pc + slot)
@[inline] def running (s : Array UInt64) : Bool := read s 0 < 3

def descriptorValid (code s : Array UInt64) (desc : UInt64) : Bool :=
  let size := code.size.toUInt64
  if size ≤ desc then false else
  let n := read code desc
  if read s 14 < n || size ≤ desc + 1 + n then false else
    let k := read code (desc + 1 + n)
    k ≤ read s 14 && desc + 2 + n + k ≤ size

def setExec (s : Array UInt64) (pc env stack : UInt64) : Array UInt64 :=
  let s := write (write (write (write s 0 0) 1 pc) 2 env) 3 stack
  write (write (write (write s 4 0) 5 0) 6 0) 7 0

def setApply (s : Array UInt64) (proc args n stack : UInt64) : Array UInt64 :=
  let s := write (write (write (write s 0 1) 2 0) 3 stack) 4 proc
  write (write (write s 5 args) 6 n) 7 0

def setReturn (s : Array UInt64) (value stack : UInt64) : Array UInt64 :=
  let s := write (write (write (write s 0 2) 2 0) 3 stack) 7 value
  write (write (write s 4 0) 5 0) 6 0

def boxLiteral (s : Array UInt64) (literal value : UInt64) : Array UInt64 :=
  if literal == 0 then allocate s 1 value 0 0 else s

def pushReady (s : Array UInt64) (literal value : UInt64) : Array UInt64 :=
  let rest := read s 3
  let s := boxLiteral s literal value
  let ref := if literal == 0 then read s 10
    else if literal == 1 then (if value == 0 then 1 else 2)
    else if literal == 2 then 3 else 4
  let s := operand s ref rest
  advance s (read s 10)

def pushLiteral (s : Array UInt64) (literal value : UInt64) : Array UInt64 :=
  let s := reserve s (if literal == 0 then 2 else 1)
  if read s 0 == 4 then s else pushReady s literal value

def reserveAccess (s : Array UInt64) (loc needsOperand : UInt64) : Array UInt64 :=
  if needsOperand != 0 && kind s (read s 3) != 7 then fail s 4 else
    if loc == 0 then fail s 2 else if kind s loc != 10 then fail s 3 else reserve s 1

def loadReady (s : Array UInt64) (loc : UInt64) : Array UInt64 :=
  let value := field s loc 2
  let rest := read s 3
  let s := operand s value rest
  advance s (read s 10)

def loadName (s : Array UInt64) (name : UInt64) : Array UInt64 :=
  let loc := lookup s (read s 2) name
  let s := reserveAccess s loc 0
  if read s 0 == 4 then s else loadReady s loc

def storeReady (s : Array UInt64) (loc : UInt64) : Array UInt64 :=
  let top := read s 3
  let value := field s top 2
  let rest := field s top 3
  let s := write s (address loc + 2) value
  let s := operand s 3 rest
  advance s (read s 10)

def storeName (s : Array UInt64) (name : UInt64) : Array UInt64 :=
  let loc := lookup s (read s 2) name
  let s := reserveAccess s loc 1
  if read s 0 == 4 then s else storeReady s loc

def captureFound (s : Array UInt64) (name loc : UInt64) : Array UInt64 :=
  let env := read s 19
  let s := allocate s 9 name loc env
  write s 19 (read s 10)

def captureOne (code : Array UInt64) (desc sourceEnv : UInt64)
    (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  if read s 0 == 4 then s else
    let n := read code desc
    let k := read code (desc + 1 + n)
    let name := read code (desc + 2 + n + k - 1 - i)
    let loc := lookup s sourceEnv name
    if loc == 0 then fail s 2 else captureFound s name loc

def captureNext (code : Array UInt64) (desc env : UInt64)
    (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, captureOne code desc env s i)

def reserveClose (code s : Array UInt64) (desc : UInt64) : Array UInt64 :=
  if !descriptorValid code s desc then fail s 10 else
    reserve s (read code (desc + 1 + read code desc) + 2)

def finishClose (s : Array UInt64) (entry desc rest : UInt64) : Array UInt64 :=
  let captured := read s 19
  let s := allocate s 5 entry desc captured
  let ref := read s 10
  let s := operand s ref rest
  let s := write s 19 0
  advance s (read s 10)

def closeReady (code : Array UInt64) (s : Array UInt64) (entry desc : UInt64) : Array UInt64 :=
  let n := read code desc
  let k := read code (desc + 1 + n)
  let env := read s 2
  let rest := read s 3
  let s := write s 19 0
  let (_, s) := LeanExe.repeatWhile k ((0 : UInt64), s)
    (fun (i, _) => i < k) (fun (i, s) => captureNext code desc env s i)
  if read s 0 == 4 then s else finishClose s entry desc rest

def close (code : Array UInt64) (s : Array UInt64) (entry desc : UInt64) : Array UInt64 :=
  let s := reserveClose code s desc
  if read s 0 == 4 then s else closeReady code s entry desc

def drop (s : Array UInt64) : Array UInt64 :=
  let top := read s 3
  if kind s top != 7 then fail s 4 else advance s (field s top 3)

def branch (s : Array UInt64) (target : UInt64) : Array UInt64 :=
  let top := read s 3
  if kind s top != 7 then fail s 4 else
    let value := field s top 2
    let rest := field s top 3
    let pc := if kind s value == 2 && field s value 2 == 0 then target else read s 1 + 1
    write (write s 1 pc) 3 rest

def reserveBinary (s : Array UInt64) (op : UInt64) : Array UInt64 :=
  let top := read s 3
  let below := field s top 3
  if kind s top != 7 || kind s below != 7 then fail s 5 else
    let right := field s top 2
    let left := field s below 2
    if kind s right != 1 || kind s left != 1 then fail s 5 else
      if 3 < op then fail s 10 else reserve s (if op < 2 then 2 else 1)

def boxBinary (s : Array UInt64) (op a b : UInt64) : Array UInt64 :=
  if op < 2 then allocate s 1 (if op == 0 then a + b else a - b) 0 0 else s

def binaryReady (s : Array UInt64) (op : UInt64) : Array UInt64 :=
  let top := read s 3
  let below := field s top 3
  let a := field s (field s below 2) 2
  let b := field s (field s top 2) 2
  let rest := field s below 3
  let s := boxBinary s op a b
  let value := if op < 2 then read s 10
    else if op == 2 then (if a < b then 2 else 1)
    else if a == b then 2 else 1
  let s := operand s value rest
  advance s (read s 10)

def binary (s : Array UInt64) (op : UInt64) : Array UInt64 :=
  let s := reserveBinary s op
  if read s 0 == 4 then s else binaryReady s op

def walkArgs (s : Array UInt64) (stack n : UInt64) : UInt64 :=
  LeanExe.loop n stack fun _ cursor =>
    if kind s cursor == 7 then field s cursor 3 else 0

def reserveEntry (s : Array UInt64) (n tail : UInt64) : Array UInt64 :=
  if read s 14 < n then fail s 4 else
    let procNode := walkArgs s (read s 3) n
    if kind s procNode != 7 then fail s 4 else
      if tail != 0 && !boundary s (field s procNode 3) then fail s 6
      else reserve s (if tail == 0 then 1 else 0)

def frameCall (s : Array UInt64) (tail pc env rest : UInt64) : Array UInt64 :=
  if tail == 0 then allocate s 8 pc env rest else s

def enterReady (s : Array UInt64) (n tail : UInt64) : Array UInt64 :=
  let original := read s 3
  let procNode := walkArgs s original n
  let rest := field s procNode 3
  let proc := field s procNode 2
  let args := if n == 0 then 0 else original
  let pc := read s 1 + 1
  let env := read s 2
  let s := frameCall s tail pc env rest
  let frame := if tail == 0 then read s 10 else rest
  setApply s proc args n frame

def enter (s : Array UInt64) (n tail : UInt64) : Array UInt64 :=
  let s := reserveEntry s n tail
  if read s 0 == 4 then s else enterReady s n tail

def ret (s : Array UInt64) : Array UInt64 :=
  let top := read s 3
  if kind s top != 7 then fail s 4 else
    let rest := field s top 3
    if !boundary s rest then fail s 6 else setReturn s (field s top 2) rest

/-- Initialization primitive; top-level bindings are explicit persistent roots. -/
def reserveGlobal (s : Array UInt64) : Array UInt64 :=
  if kind s (read s 3) != 7 then fail s 4 else reserve s 3

def globalReady (s : Array UInt64) (name : UInt64) : Array UInt64 :=
  let top := read s 3
  let value := field s top 2
  let rest := field s top 3
  let env := read s 16
  let s := allocate s 10 value 0 0
  let loc := read s 10
  let s := allocate s 9 name loc env
  let env := read s 10
  let s := write (write s 2 env) 16 env
  let s := operand s 3 rest
  advance s (read s 10)

def global (s : Array UInt64) (name : UInt64) : Array UInt64 :=
  let s := reserveGlobal s
  if read s 0 == 4 then s else globalReady s name

def bindReady (code : Array UInt64) (desc n : UInt64)
    (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  let args := read s 20
  let value := field s args 2
  let next := field s args 3
  let name := read code (desc + n - i)
  let env := read s 19
  let s := allocate s 10 value 0 0
  let loc := read s 10
  let s := allocate s 9 name loc env
  write (write s 19 (read s 10)) 20 next

def bindOne (code : Array UInt64) (desc n : UInt64)
    (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  if kind s (read s 20) != 7 then fail s 4 else bindReady code desc n s i

def bindNext (code : Array UInt64) (desc n : UInt64)
    (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, bindOne code desc n s i)

def reserveClosure (code s : Array UInt64) : Array UInt64 :=
  let desc := field s (read s 4) 3
  let n := read s 6
  if !boundary s (read s 3) then fail s 6 else
    if !descriptorValid code s desc then fail s 10 else
      if read code desc != n then fail s 8 else reserve s (2 * n)

def closureReady (code s : Array UInt64) : Array UInt64 :=
  let proc := read s 4
  let n := read s 6
  let desc := field s proc 3
  let entry := field s proc 2
  let captured := field s proc 4
  let args := read s 5
  let stack := read s 3
  let s := write (write s 19 captured) 20 args
  let (_, s) := LeanExe.repeatWhile n ((0 : UInt64), s)
    (fun (i, _) => i < n) (fun (i, s) => bindNext code desc n s i)
  let env := read s 19
  if read s 0 == 4 then s else setExec (write (write s 19 0) 20 0) entry env stack

def applyClosure (code s : Array UInt64) : Array UInt64 :=
  let s := reserveClosure code s
  if read s 0 == 4 then s else closureReady code s

def applyContinuation (s : Array UInt64) : Array UInt64 :=
  if read s 6 != 1 then fail s 8 else
    let proc := read s 4
    let args := read s 5
    let saved := field s proc 2
    if kind s args != 7 then fail s 4 else
      if !boundary s saved then fail s 6 else
        setReturn s (field s args 2) saved

def reserveCallcc (s : Array UInt64) : Array UInt64 :=
  if read s 6 != 1 then fail s 8 else
    if !boundary s (read s 3) then fail s 6 else
      if kind s (read s 5) != 7 then fail s 4 else reserve s 2

def callccReady (s : Array UInt64) : Array UInt64 :=
  let callback := field s (read s 5) 2
  let stack := read s 3
  let s := allocate s 6 stack 0 0
  let continuation := read s 10
  let s := operand s continuation 0
  setApply s callback (read s 10) 1 stack

def applyCallcc (s : Array UInt64) : Array UInt64 :=
  let s := reserveCallcc s
  if read s 0 == 4 then s else callccReady s

def apply (code : Array UInt64) (s : Array UInt64) : Array UInt64 :=
  let tag := kind s (read s 4)
  if tag == 5 then applyClosure code s
  else if tag == 6 then applyContinuation s
  else if tag == 4 then applyCallcc s
  else fail s 7

def reserveReturn (s : Array UInt64) : Array UInt64 :=
  if kind s (read s 3) != 8 then fail s 6 else reserve s 1

def returnReady (s : Array UInt64) : Array UInt64 :=
  let frame := read s 3
  let pc := field s frame 2
  let env := field s frame 3
  let rest := field s frame 4
  let value := read s 7
  let s := operand s value rest
  setExec s pc env (read s 10)

def deliverFrame (s : Array UInt64) : Array UInt64 :=
  let s := reserveReturn s
  if read s 0 == 4 then s else returnReady s

def deliver (s : Array UInt64) : Array UInt64 :=
  if read s 3 == 0 then write s 0 3 else deliverFrame s

def execute (code : Array UInt64) (s : Array UInt64) : Array UInt64 :=
  let pc := read s 1
  let size := code.size.toUInt64
  if size == 0 then fail s 10 else
  let count := read code 0
  if (size - 1) / 4 < count then fail s 10 else
    if count ≤ pc then fail s 1 else
      let op := wire code pc 0
      let a := wire code pc 1
      let b := wire code pc 2
      if op ≤ 3 then pushLiteral s op a
      else if op == 4 then loadName s a
      else if op == 5 then storeName s a
      else if op == 6 then close code s a b
      else if op == 7 then drop s
      else if op == 8 then write s 1 a
      else if op == 9 then branch s a
      else if op == 10 then binary s a
      else if op == 11 then enter s a 0
      else if op == 12 then enter s a 1
      else if op == 13 then ret s
      else if op == 14 then global s a
      else fail s 10

def step (code : Array UInt64) (s : Array UInt64) : Array UInt64 :=
  let phase := read s 0
  if phase == 0 then execute code s
  else if phase == 1 then apply code s
  else if phase == 2 then deliver s
  else s

def runNext (code s : Array UInt64) : UInt64 × Array UInt64 := (0, step code s)

def run (code : Array UInt64) (s : Array UInt64) (fuel : UInt64) : Array UInt64 :=
  let (_, s) := LeanExe.repeatWhile fuel ((0 : UInt64), s)
    (fun (_, s) => running s) (fun (_, s) => runNext code s)
  s

def resultWord (s : Array UInt64) : UInt64 :=
  if read s 0 == 3 && kind s (read s 7) == 1 then field s (read s 7) 2 else 0

end LeanExe.Scheme.Runtime
