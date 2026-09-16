import LeanExe.KernelCheck.Infer

namespace LeanExe.KernelCheck

/-- Structural comparison, complete for types in the admitted Sort/bvar/Pi/
lambda fragment. The graph must already be validated. No hash shortcut. -/
def equalCore (initial : Result) (left right : UInt64) : Result := Id.run do
  let mut s := initial
  let mut stack := #[left, right]
  for _ in [:initial.fuel] do
    if stack.isEmpty then return s
    if s.fuel == 0 then return { s with status := 5 }
    s := { s with fuel := s.fuel - 1 }
    let y := stack.back!
    stack := stack.pop
    let x := stack.back!
    stack := stack.pop
    let tag := nodeTag s.graph x
    if tag != nodeTag s.graph y then return { s with status := 1 }
    if tag == 0 || tag == 1 then
      if nodeA s.graph x != nodeA s.graph y then return { s with status := 1 }
    else
      stack := stack.push (nodeB s.graph x) |>.push (nodeB s.graph y)
      stack := stack.push (nodeA s.graph x) |>.push (nodeA s.graph y)
  if stack.isEmpty then return s else return { s with status := 5 }

def checkInContext (g ctx : Array UInt64) (term claimed fuel : UInt64) : UInt64 :=
  if validateGraph g term != 0 || claimed.toNat >= g.size / 3 then 4
  else
    let admitted := admitContext g ctx term fuel.toNat
    if admitted.status != 0 then admitted.status
    else
      let ty := inferCore ctx admitted claimed
      if ty.status != 0 then ty.status
      else if nodeTag ty.graph ty.root != 0 then 1
      else
        let actual := inferCore ctx ty term
        if actual.status != 0 then actual.status
        else (equalCore actual actual.root claimed).status

/-- Closed proof checking with no globals, universe parameters or axioms. -/
def checkProof (g : Array UInt64) (term claimed fuel : UInt64) : UInt64 :=
  checkInContext g #[] term claimed fuel

end LeanExe.KernelCheck
