import LeanExe.KernelCheck.Reduce

namespace LeanExe.KernelCheck

/-- Beta conversion on validated types. Normalize each compared head, then
compare its children. Mismatches below neutral applications remain inconclusive
because full Lean conversion (notably proof irrelevance/eta) is not implemented. -/
def equalCore (initial : Result) (left right : UInt64) : Result := Id.run do
  let mut s := initial
  let mut stack := #[left, right]
  let mut uncertain := false
  for _ in [:initial.fuel] do
    if stack.isEmpty then return s
    if s.fuel == 0 then return { s with status := 5 }
    s := { s with fuel := s.fuel - 1 }
    let rightTerm := stack.back!
    stack := stack.pop
    let leftTerm := stack.back!
    stack := stack.pop
    s := whnfCore s leftTerm
    if s.status != 0 then return s
    let x := s.root
    s := whnfCore s rightTerm
    if s.status != 0 then return s
    let y := s.root
    let tag := nodeTag s.graph x
    if tag == 4 || nodeTag s.graph y == 4 then uncertain := true
    if tag != nodeTag s.graph y then return { s with status := if uncertain then 3 else 1 }
    if tag == 0 || tag == 1 then
      if nodeA s.graph x != nodeA s.graph y then
        return { s with status := if uncertain then 3 else 1 }
    else
      stack := stack.push (nodeB s.graph x) |>.push (nodeB s.graph y)
      stack := stack.push (nodeA s.graph x) |>.push (nodeA s.graph y)
  if stack.isEmpty then return s else return { s with status := 5 }

end LeanExe.KernelCheck
