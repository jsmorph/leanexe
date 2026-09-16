import LeanExe.KernelCheck.Check

namespace LeanExe.KernelCheck

example : ∀ p : Prop, p → p := fun p hp => hp
example : ∀ α : Type, α → α := fun α x => x

def implicationIdentityGraph : Array UInt64 :=
  #[0,0,0,1,0,0,1,1,0,2,1,2,2,0,3,3,1,1,3,0,5]

#guard checkProof implicationIdentityGraph 6 4 100 == 0
#guard checkProof implicationIdentityGraph 6 0 100 == 1
#guard checkProof implicationIdentityGraph 6 4 1 == 5
#guard checkProof implicationIdentityGraph 6 20 100 == 4

end LeanExe.KernelCheck
