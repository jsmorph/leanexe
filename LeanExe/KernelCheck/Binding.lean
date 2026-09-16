import LeanExe.KernelCheck.Graph

namespace LeanExe.KernelCheck

def nodeTag (g : Array UInt64) (r : UInt64) : UInt64 := g[r.toNat * 3]!
def nodeA (g : Array UInt64) (r : UInt64) : UInt64 := g[r.toNat * 3 + 1]!
def nodeB (g : Array UInt64) (r : UInt64) : UInt64 := g[r.toNat * 3 + 2]!

structure Result where
  graph : Array UInt64
  root : UInt64
  status : UInt64
  fuel : Nat

def addNode (s : Result) (tag a b : UInt64) : Result :=
  let g := ((s.graph.push tag).push a).push b
  { s with graph := g, root := UInt64.ofNat (s.graph.size / 3) }

def packResult (s : Result) : Array UInt64 :=
  if s.status == 0 then #[0, s.root] ++ s.graph else #[s.status]

/-- Scope is checked at each occurrence, since a shared node may be reached
under different numbers of binders. Fuel counts visited occurrences. -/
def checkScope (g : Array UInt64) (root depth fuel : UInt64) : UInt64 := Id.run do
  if validateGraph g root != 0 then return 4
  let mut stack := #[root, depth]
  for _ in [:fuel.toNat] do
    if stack.isEmpty then return 0
    let d := stack.back!
    stack := stack.pop
    let r := stack.back!
    stack := stack.pop
    let tag := nodeTag g r
    if tag == 1 then
      if nodeA g r >= d then return 1
    else if tag == 2 || tag == 3 then
      if d == 18446744073709551615 then return 2
      stack := stack.push (nodeB g r) |>.push (d + 1)
      stack := stack.push (nodeA g r) |>.push d
  if stack.isEmpty then return 0 else return 5

/-- Internal operation on a validated graph. Frames are (root, cutoff, phase).
The explicit stack avoids using the runtime call stack for term traversal.
Fuel counts frames, including reconstruction; returned fuel is unspent. -/
def shiftCore (g : Array UInt64) (root cutoff delta : UInt64) (fuel : Nat) : Result := Id.run do
  let mut s : Result := ⟨g, root, 0, fuel⟩
  let mut stack := #[root, cutoff, 0]
  let mut values : Array UInt64 := #[]
  for _ in [:fuel] do
    if stack.isEmpty then return { s with root := values.back! }
    s := { s with fuel := s.fuel - 1 }
    let phase := stack.back!
    stack := stack.pop
    let cut := stack.back!
    stack := stack.pop
    let r := stack.back!
    stack := stack.pop
    let tag := nodeTag g r
    let a := nodeA g r
    let b := nodeB g r
    if phase == 1 then
      let body := values.back!
      values := values.pop
      let domain := values.back!
      values := values.pop
      s := addNode s tag domain body
      values := values.push s.root
    else if tag == 0 then
      values := values.push r
    else if tag == 1 then
      if a >= cut && delta != 0 then
        if a > 18446744073709551615 - delta then return { s with status := 2 }
        s := addNode s 1 (a + delta) 0
        values := values.push s.root
      else values := values.push r
    else
      if cut == 18446744073709551615 then return { s with status := 2 }
      stack := stack.push r |>.push cut |>.push 1
      stack := stack.push b |>.push (cut + 1) |>.push 0
      stack := stack.push a |>.push cut |>.push 0
  if stack.isEmpty then return { s with root := values.back! }
  else return { s with status := 5 }

def shiftGraph (g : Array UInt64) (root cutoff delta fuel : UInt64) : Array UInt64 :=
  if validateGraph g root != 0 then #[4]
  else packResult (shiftCore g root cutoff delta fuel.toNat)

end LeanExe.KernelCheck
