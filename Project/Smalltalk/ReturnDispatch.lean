import LeanExe.Smalltalk.Runtime

namespace Project.Smalltalk.ReturnDispatch
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

def cells (caller : UInt64) : UInt64 := if caller == 0 then 0 else 1

theorem returnReserved_eq (s : Array UInt64) (stop caller value : UInt64) :
    returnReserved s stop caller value =
      if read (reserve s (cells caller)) 0 == 4 then reserve s (cells caller)
      else returnReady (reserve s (cells caller)) stop caller value := rfl

end Project.Smalltalk.ReturnDispatch
