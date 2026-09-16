import LeanExe.KernelCheck.Binding
import LeanExe.KernelCheck.Universe
import LeanExe.KernelCheck.Substitution
import LeanExe.KernelCheck.Equality

namespace LeanExe.KernelCheck

/-- Inference over a validated graph and admitted context. Frames hold
(term, phase, saved universe). Fuel counts all inference and shift frames;
no recursive runtime calls are needed for nested binders. -/
def inferCore (initialCtx : Array UInt64) (initial : Result) (r : UInt64) : Result := Id.run do
  let mut s := initial
  let mut ctx := initialCtx
  let mut stack := #[r, 0, 0]
  for _ in [:initial.fuel] do
    if stack.isEmpty then return s
    if s.fuel == 0 then return { s with status := 5 }
    s := { s with fuel := s.fuel - 1 }
    let saved := stack.back!
    stack := stack.pop
    let phase := stack.back!
    stack := stack.pop
    let term := stack.back!
    stack := stack.pop
    let tag := nodeTag s.graph term
    let a := nodeA s.graph term
    let b := nodeB s.graph term
    if phase == 1 then
      if nodeTag s.graph s.root != 0 then
        return { s with status := if nodeTag s.graph s.root == 4 then 3 else 1 }
      let u := nodeA s.graph s.root
      ctx := ctx.push a
      stack := stack.push term |>.push 2 |>.push u
      stack := stack.push b |>.push 0 |>.push 0
    else if phase == 2 then
      ctx := ctx.pop
      if tag == 2 then
        if nodeTag s.graph s.root != 0 then
          return { s with status := if nodeTag s.graph s.root == 4 then 3 else 1 }
        let v := nodeA s.graph s.root
        s := addNode s 0 (imaxLevel saved v) 0
      else
        s := addNode s 2 a s.root
    else if phase == 3 then
      if nodeTag s.graph s.root != 2 then
        return { s with status := if nodeTag s.graph s.root == 4 then 3 else 1 }
      stack := stack.push term |>.push 4 |>.push s.root
      stack := stack.push b |>.push 0 |>.push 0
    else if phase == 4 then
      s := equalCore s s.root (nodeA s.graph saved)
      if s.status != 0 then return s
      s := instantiateCore s (nodeB s.graph saved) b
      if s.status != 0 then return s
    else if tag == 0 then
      if a == 18446744073709551615 then return { s with status := 2 }
      s := addNode s 0 (a + 1) 0
    else if tag == 1 then
      if a.toNat >= ctx.size then return { s with status := 1 }
      let stored := ctx[ctx.size - 1 - a.toNat]!
      s := shiftCore s.graph stored 0 (a + 1) s.fuel
      if s.status != 0 then return s
    else if tag == 2 || tag == 3 then
      stack := stack.push term |>.push 1 |>.push 0
      stack := stack.push a |>.push 0 |>.push 0
    else if tag == 4 then
      stack := stack.push term |>.push 3 |>.push 0
      stack := stack.push a |>.push 0 |>.push 0
    else return { s with status := 3 }
  if stack.isEmpty then return s else return { s with status := 5 }

/-- Validate assumptions in order before exposing any open judgment. -/
def admitContext (g ctx : Array UInt64) (root : UInt64) (fuel : Nat) : Result := Id.run do
  let mut s : Result := ⟨g, root, 0, fuel⟩
  let mut admitted : Array UInt64 := #[]
  for ty in ctx do
    if ty.toNat >= g.size / 3 then return { s with status := 4 }
    s := inferCore admitted s ty
    if s.status != 0 then return s
    if nodeTag s.graph s.root != 0 then
      return { s with status := if nodeTag s.graph s.root == 4 then 3 else 1 }
    admitted := admitted.push ty
  return s

def inferOpen (g ctx : Array UInt64) (root fuel : UInt64) : Array UInt64 :=
  if validateGraph g root != 0 then #[4]
  else
    let s := admitContext g ctx root fuel.toNat
    if s.status != 0 then packResult s
    else packResult (inferCore ctx s root)

end LeanExe.KernelCheck
