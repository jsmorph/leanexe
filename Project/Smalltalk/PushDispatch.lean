import LeanExe.Smalltalk.Runtime

namespace Project.Smalltalk.PushDispatch
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

theorem push_error (s : Array UInt64) (value : UInt64) (error : read (reserve s 1) 0 = 4) :
    push s value = reserve s 1 := by
  simp only [push, error, BEq.rfl, ite_true]

theorem push_success (s : Array UInt64) (value : UInt64) (success : read (reserve s 1) 0 ≠ 4) :
    push s value = pushReady (reserve s 1) value := by
  simp only [push, show (read (reserve s 1) 0 == 4) = false from beq_eq_false_iff_ne.mpr success,
    Bool.false_eq_true, ite_false]

end Project.Smalltalk.PushDispatch
