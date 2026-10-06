import Project.Smalltalk.ProgramBounds

namespace Project.Smalltalk.CallBudget
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

def need (p : Array UInt64) (method : UInt64) : UInt64 := methodAt p method 2 + methodAt p method 3 + 1

theorem need_toNat {p : Array UInt64} {method : UInt64} (bounds : ProgramBounds.Method p method) :
    (need p method).toNat = (methodAt p method 2).toNat + (methodAt p method 3).toNat + 1 := by
  have arity := bounds.arityBound
  have locals := bounds.localsBound
  simp only [need, UInt64.toNat_add, UInt64.reduceToNat]
  omega

end Project.Smalltalk.CallBudget
