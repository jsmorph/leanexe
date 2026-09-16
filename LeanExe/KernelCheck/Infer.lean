import LeanExe.KernelCheck.Binding
import LeanExe.KernelCheck.Universe

namespace LeanExe.KernelCheck

/-- M0.4 inference. Context entries are types in the preceding context,
ordered oldest first. Internal callers must validate structure and context. -/
def inferCore (ctx : Array UInt64) (s : Result) (r : UInt64) : Result :=
  if s.fuel == 0 then { s with status := 5 }
  else
    let s := { s with fuel := s.fuel - 1 }
    let tag := nodeTag s.graph r
    let a := nodeA s.graph r
    if tag == 0 then
      if a == 18446744073709551615 then { s with status := 2 }
      else addNode s 0 (a + 1) 0
    else if tag == 1 then
      if a.toNat >= ctx.size then { s with status := 1 }
      else
        let stored := ctx[ctx.size - 1 - a.toNat]!
        shiftCore s.graph stored 0 (a + 1) s.fuel
    else { s with status := 3 }

/-- Validate assumptions in order before exposing any open judgment. -/
def admitContext (g ctx : Array UInt64) (root : UInt64) (fuel : Nat) : Result := Id.run do
  let mut s : Result := ⟨g, root, 0, fuel⟩
  let mut admitted : Array UInt64 := #[]
  for ty in ctx do
    if ty.toNat >= g.size / 3 then return { s with status := 4 }
    s := inferCore admitted s ty
    if s.status != 0 then return s
    if nodeTag s.graph s.root != 0 then return { s with status := 1 }
    admitted := admitted.push ty
  return s

def inferOpen (g ctx : Array UInt64) (root fuel : UInt64) : Array UInt64 :=
  if validateGraph g root != 0 then #[4]
  else
    let s := admitContext g ctx root fuel.toNat
    if s.status != 0 then packResult s
    else packResult (inferCore ctx s root)

end LeanExe.KernelCheck
