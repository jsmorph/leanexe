import LeanExe.KernelCheck.Infer

namespace LeanExe.KernelCheck

def checkInContext (g ctx : Array UInt64) (term claimed fuel : UInt64) : UInt64 :=
  if validateGraph g term != 0 || claimed.toNat >= g.size / 3 then 4
  else
    let admitted := admitContext g ctx term fuel.toNat
    if admitted.status != 0 then admitted.status
    else
      let ty := inferCore ctx admitted claimed
      if ty.status != 0 then ty.status
      else if nodeTag ty.graph ty.root != 0 then
        if nodeTag ty.graph ty.root == 4 then 3 else 1
      else
        let actual := inferCore ctx ty term
        if actual.status != 0 then actual.status
        else (equalCore actual actual.root claimed).status

/-- Closed proof checking with no globals, universe parameters or axioms. -/
def checkProof (g : Array UInt64) (term claimed fuel : UInt64) : UInt64 :=
  checkInContext g #[] term claimed fuel

end LeanExe.KernelCheck
