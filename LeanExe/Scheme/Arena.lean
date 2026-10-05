import LeanExe.Build
import LeanExe.Loop
import LeanExe.RepeatWhile

/-!
One owned word array contains VM registers, fixed-size cells, and a preallocated
mark worklist. Handles are cell indices; zero is the empty environment/halt stack.
Kinds: 0 free, 1 word, 2 boolean, 3 unit, 4 call/cc, 5 closure, 6 continuation,
7 operand, 8 return frame, 9 environment binding, 10 mutable location.

Registers: 0 phase, 1 pc, 2 env, 3 stack, 4 procedure, 5 arguments, 6 arity,
7 result, 8 free head, 9 free count, 10 last allocation, 11 collection count,
12 stress collection, 13 peak cells, 14 capacity, 15 error, 16 globals,
17 allocation count, 18 work count. Cell layout: kind, mark, a, b, c.
-/

namespace LeanExe.Scheme.Arena

@[inline] def read (s : Array UInt64) (i : UInt64) : UInt64 := s[i.toNat]!
def write (s : Array UInt64) (i v : UInt64) : Array UInt64 := s.set! i.toNat v
@[inline] def address (h : UInt64) : UInt64 := 24 + 5 * (h - 1)
@[inline] def field (s : Array UInt64) (h i : UInt64) : UInt64 := read s (address h + i)
@[inline] def kind (s : Array UInt64) (h : UInt64) : UInt64 :=
  if h == 0 || read s 14 < h then 0 else field s h 0

def fail (s : Array UInt64) (reason : UInt64) : Array UInt64 :=
  write (write s 0 4) 15 reason

def seedCell (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  let h := i + 1
  let cap := read s 14
  let base := address h
  if h ≤ 4 then
    let tag := if h ≤ 2 then 2 else if h == 3 then 3 else 4
    let value := if h == 2 then 1 else 0
    write (write s base tag) (base + 2) value
  else
    write s (base + 2) (if h < cap then h + 1 else 0)

def seedNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, seedCell s i)

/-- Capacity is bounded so buffer sizes and offsets cannot wrap. -/
def init (capacity stress : UInt64) : Array UInt64 :=
  let cap := max 8 (min capacity 1048576)
  let s := LeanExe.build (24 + 6 * cap) fun _ => (0 : UInt64)
  let s := write (write (write (write s 14 cap) 12 stress) 8 5) 9 (cap - 4)
  let s := write s 13 4
  let (_, s) := LeanExe.repeatWhile cap ((0 : UInt64), s)
    (fun (i, _) => i < cap) (fun (i, s) => seedNext s i)
  s

def allocateCell (s : Array UInt64) (tag a b c : UInt64) : Array UInt64 :=
  let h := read s 8
  let next := field s h 2
  let count := read s 9 - 1
  let peak := max (read s 13) (read s 14 - count)
  let total := read s 17 + 1
  let base := address h
  let s := write (write (write (write (write s base tag) (base + 1) 0)
    (base + 2) a) (base + 3) b) (base + 4) c
  write (write (write (write (write s 8 next) 9 count) 10 h) 13 peak) 17 total

/-- Raw allocation never collects. A whole VM transition reserves first. -/

def allocate (s : Array UInt64) (tag a b c : UInt64) : Array UInt64 :=
  if read s 8 == 0 then fail s 9 else allocateCell s tag a b c

def clearMark (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  write s (address (i + 1) + 1) 0

def clearNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, clearMark s i)

/-- Mark before enqueueing: each cell occupies the worklist at most once. -/
def mark (s : Array UInt64) (h : UInt64) : Array UInt64 :=
  if h == 0 then s else
    if kind s h == 0 then fail s 3 else
      if field s h 1 != 0 then s else
        let n := read s 18
        let cap := read s 14
        if cap ≤ n then fail s 3 else
          write (write (write s (address h + 1) 1) (24 + 5 * cap + n) h) 18 (n + 1)

def markRoots (s : Array UInt64) : Array UInt64 :=
  let phase := read s 0
  let env := read s 2
  let stack := read s 3
  let proc := read s 4
  let args := read s 5
  let result := read s 7
  let globals := read s 16
  let s := mark (mark (mark (mark s 1) 2) 3) 4
  let s := mark (mark (mark s env) stack) globals
  if phase == 1 then mark (mark s proc) args
  else if phase == 2 || phase == 3 then mark s result
  else s

@[inline] def pending (s : Array UInt64) : Bool := read s 18 != 0 && read s 0 != 4

def scanCell (s : Array UInt64) : Array UInt64 :=
  let n := read s 18
  let h := read s (24 + 5 * read s 14 + n - 1)
  let tag := kind s h
  let a := field s h 2
  let b := field s h 3
  let c := field s h 4
  let s := write s 18 (n - 1)
  if tag == 5 then mark s c
  else if tag == 6 || tag == 10 then mark s a
  else if tag == 7 then mark (mark s a) b
  else if tag == 8 || tag == 9 then mark (mark s b) c
  else if tag ≤ 4 then s
  else fail s 3

def scanOne (s : Array UInt64) : Array UInt64 :=
  if read s 18 == 0 || read s 0 == 4 then s else scanCell s

def reclaim (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  let h := i + 1
  let head := read s 8
  let count := read s 9 + 1
  let base := address h
  let s := write (write (write (write s base 0) (base + 2) head)
    (base + 3) 0) (base + 4) 0
  write (write s 8 h) 9 count

def sweepCell (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  if field s (i + 1) 1 != 0 then s else reclaim s i

def sweepNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, sweepCell s i)

def scanNext (s : Array UInt64) : UInt64 × Array UInt64 := (0, scanOne s)

def finishCollection (s : Array UInt64) (cap count : UInt64) : Array UInt64 :=
  let s := write (write (write s 8 0) 9 0) 10 0
  let (_, s) := LeanExe.repeatWhile cap ((0 : UInt64), s)
    (fun (i, _) => i < cap) (fun (i, s) => sweepNext s i)
  write s 11 count

def collectReady (s : Array UInt64) : Array UInt64 :=
  let cap := read s 14
  let count := read s 11 + 1
  let (_, s) := LeanExe.repeatWhile cap ((0 : UInt64), s)
    (fun (i, _) => i < cap) (fun (i, s) => clearNext s i)
  let s := markRoots (write s 18 0)
  let (_, s) := LeanExe.repeatWhile cap ((0 : UInt64), s)
    (fun (_, s) => pending s) (fun (_, s) => scanNext s)
  if read s 0 == 4 || read s 18 != 0 then fail s 3 else finishCollection s cap count

/-- Stop-the-world collection; the worklist and free-list operations do not allocate. -/
def collect (s : Array UInt64) : Array UInt64 :=
  if read s 0 == 4 then s else collectReady s

def stressCollection (s : Array UInt64) (need : UInt64) : Array UInt64 :=
  if read s 0 != 4 && read s 12 != 0 && need != 0 then collect s else s

def spaceCollection (s : Array UInt64) (need : UInt64) : Array UInt64 :=
  if read s 0 != 4 && read s 9 < need then collect s else s

def reserve (s : Array UInt64) (need : UInt64) : Array UInt64 :=
  let s := stressCollection s need
  let s := spaceCollection s need
  if read s 0 == 4 then s else if read s 9 < need then fail s 9 else s

def lookup (s : Array UInt64) (env name : UInt64) : UInt64 :=
  let found := LeanExe.loop (read s 14) (env, (0 : UInt64)) fun _ state =>
    let (cursor, result) := state
    let keep := result != 0 || cursor == 0
    let valid := kind s cursor == 9
    let same := if valid then field s cursor 2 == name else false
    let next := if keep then cursor else if !valid || same then 0 else field s cursor 4
    let result := if keep then result else if same then field s cursor 3 else 0
    (next, result)
  found.2

@[inline] def boundary (s : Array UInt64) (stack : UInt64) : Bool :=
  stack == 0 || kind s stack == 8

def operand (s : Array UInt64) (value rest : UInt64) : Array UInt64 :=
  allocate s 7 value rest 0

def advance (s : Array UInt64) (stack : UInt64) : Array UInt64 :=
  let pc := read s 1 + 1
  write (write s 1 pc) 3 stack

end LeanExe.Scheme.Arena
