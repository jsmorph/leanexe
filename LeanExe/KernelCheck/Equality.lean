import LeanExe.KernelCheck.Binding

namespace LeanExe.KernelCheck

/-- Structural comparison on validated terms. A mismatch below an application
is inconclusive until conversion is implemented. No hash shortcut. -/
def equalCore (initial : Result) (left right : UInt64) : Result := Id.run do
  let mut s := initial
  let mut stack := #[left, right]
  let mut uncertain := false
  for _ in [:initial.fuel] do
    if stack.isEmpty then return s
    if s.fuel == 0 then return { s with status := 5 }
    s := { s with fuel := s.fuel - 1 }
    let y := stack.back!
    stack := stack.pop
    let x := stack.back!
    stack := stack.pop
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
