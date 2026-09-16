import LeanExe.KernelCheck.Binding

namespace LeanExe.KernelCheck

/-- Remove the outermost binder: replace index 0 by argument, lift argument
under nested binders, and decrement indices referring beyond the removed one.
Internal inputs are structurally validated; open terms are allowed. -/
def instantiateCore (initial : Result) (root argument : UInt64) : Result := Id.run do
  let mut s := initial
  let mut stack := #[root, 0, 0]
  let mut values : Array UInt64 := #[]
  for _ in [:initial.fuel] do
    if stack.isEmpty then return { s with root := values.back! }
    if s.fuel == 0 then return { s with status := 5 }
    s := { s with fuel := s.fuel - 1 }
    let phase := stack.back!
    stack := stack.pop
    let depth := stack.back!
    stack := stack.pop
    let r := stack.back!
    stack := stack.pop
    let tag := nodeTag s.graph r
    let a := nodeA s.graph r
    let b := nodeB s.graph r
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
      if a < depth then values := values.push r
      else if a == depth then
        s := shiftCore s.graph argument 0 depth s.fuel
        if s.status != 0 then return s
        values := values.push s.root
      else
        s := addNode s 1 (a - 1) 0
        values := values.push s.root
    else
      let binder := tag == 2 || tag == 3
      if binder && depth == 18446744073709551615 then return { s with status := 2 }
      let bodyDepth := if binder then depth + 1 else depth
      stack := stack.push r |>.push depth |>.push 1
      stack := stack.push b |>.push bodyDepth |>.push 0
      stack := stack.push a |>.push depth |>.push 0
  if stack.isEmpty then return { s with root := values.back! }
  else return { s with status := 5 }

def instantiateGraph (g : Array UInt64) (root argument fuel : UInt64) : Array UInt64 :=
  if validateGraph g root != 0 || argument.toNat >= g.size / 3 then #[4]
  else packResult (instantiateCore ⟨g, root, 0, fuel.toNat⟩ root argument)

end LeanExe.KernelCheck
