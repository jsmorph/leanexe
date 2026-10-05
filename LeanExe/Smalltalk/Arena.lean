import LeanExe.Build
import LeanExe.Loop
import LeanExe.RepeatWhile

/-! A nonmoving mark/sweep heap. One array holds 24 registers, eight-word cells,
and a capacity-sized worklist. Handles are indices, with zero meaning absent.
Cell kinds: 1 integer, 2 nil/bool, 4 object, 5 activation, 6 block, 7 link,
8 class object. Registers 19–23 are construction scratch, empty at safepoints. -/
namespace LeanExe.Smalltalk.Arena

@[inline] def read (s : Array UInt64) (i : UInt64) : UInt64 := s[i.toNat]!
def write (s : Array UInt64) (i v : UInt64) : Array UInt64 := s.set! i.toNat v
@[inline] def address (h : UInt64) : UInt64 := 24 + 8 * (h - 1)
@[inline] def field (s : Array UInt64) (h i : UInt64) : UInt64 := read s (address h + i)
@[inline] def kind (s : Array UInt64) (h : UInt64) : UInt64 :=
  if h == 0 || read s 14 < h then 0 else field s h 0
def fail (s : Array UInt64) (reason : UInt64) : Array UInt64 :=
  write (write s 0 4) 15 reason

def seedCell (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  let h := i + 1
  let cap := read s 14
  if h ≤ 3 then write (write s (address h) 2) (address h + 2) (h - 1)
  else write s (address h + 2) (if h < cap then h + 1 else 0)
def seedNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 := (i + 1, seedCell s i)
def init (capacity stress : UInt64) : Array UInt64 :=
  let cap := max 8 (min capacity 1048576)
  let s := LeanExe.build (24 + 9 * cap) fun _ => (0 : UInt64)
  let s := write (write (write (write (write s 14 cap) 12 stress) 8 4) 9 (cap - 3)) 13 3
  let (_, s) := LeanExe.repeatWhile cap ((0 : UInt64), s)
    (fun (i, _) => i < cap) (fun (i, s) => seedNext s i)
  s

def allocateCell (s : Array UInt64) (tag a b c d e f : UInt64) : Array UInt64 :=
  let h := read s 8
  let next := field s h 2
  let count := read s 9 - 1
  let peak := max (read s 13) (read s 14 - count)
  let total := read s 17 + 1
  let base := address h
  let s := write (write (write (write s base tag) (base + 1) 0) (base + 2) a) (base + 3) b
  let s := write (write (write (write s (base + 4) c) (base + 5) d) (base + 6) e) (base + 7) f
  write (write (write (write (write s 8 next) 9 count) 10 h) 13 peak) 17 total
def allocate (s : Array UInt64) (tag a b c d e f : UInt64) : Array UInt64 :=
  if read s 8 == 0 then fail s 9 else allocateCell s tag a b c d e f

def clearNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, write s (address (i + 1) + 1) 0)
def markReady (s : Array UInt64) (h : UInt64) : Array UInt64 :=
  let n := read s 18
  let cap := read s 14
  write (write (write s (address h + 1) 1) (24 + 8 * cap + n) h) 18 (n + 1)
def mark (s : Array UInt64) (h : UInt64) : Array UInt64 :=
  if h == 0 then s else
  if kind s h == 0 then fail s 3 else
  if field s h 1 != 0 then s else
  if read s 18 ≥ read s 14 then fail s 3 else markReady s h
def markRoots (s : Array UInt64) : Array UInt64 :=
  let current := read s 2
  let result := read s 7
  let external := read s 16
  mark (mark (mark (mark (mark (mark s 1) 2) 3) current) result) external
def scanCell (s : Array UInt64) : Array UInt64 :=
  let n := read s 18
  let h := read s (24 + 8 * read s 14 + n - 1)
  let tag := kind s h
  let a := field s h 2
  let b := field s h 3
  let c := field s h 4
  let d := field s h 5
  let e := field s h 6
  let f := field s h 7
  let s := write s 18 (n - 1)
  if tag == 4 || tag == 6 then mark s b
  else if tag == 5 then mark (mark (mark (mark s c) d) e) f
  else if tag == 7 then mark (mark s a) b
  else if tag == 1 || tag == 2 || tag == 8 then s
  else fail s 3
def scanNext (s : Array UInt64) : UInt64 × Array UInt64 := (0, scanCell s)
def reclaim (s : Array UInt64) (i : UInt64) : Array UInt64 :=
  let h := i + 1
  let head := read s 8
  let count := read s 9 + 1
  let base := address h
  let s := write (write (write (write s base 0) (base + 2) head) (base + 3) 0) (base + 4) 0
  let s := write (write (write s (base + 5) 0) (base + 6) 0) (base + 7) 0
  write (write s 8 h) 9 count
def sweepNext (s : Array UInt64) (i : UInt64) : UInt64 × Array UInt64 :=
  (i + 1, if field s (i + 1) 1 != 0 then s else reclaim s i)
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
    (fun (_, s) => read s 18 != 0 && read s 0 != 4) (fun (_, s) => scanNext s)
  if read s 0 == 4 || read s 18 != 0 then fail s 3 else finishCollection s cap count
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

end LeanExe.Smalltalk.Arena
