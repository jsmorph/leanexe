import Sail
import THE_MODULE_NAME.Defs
import THE_MODULE_NAME.SpecializationV1

/-!
The external functions of the arm-v9.4-a model that the slice calls and Sail's Lean library
lacks, after sail-arm's `lean/ArmExtras.lean` (whose imports and namespace follow a later Sail),
and stand-ins for the two functions that `fp-slice.isail` cuts from the slice.  The slice keeps
the declarations of AArch64_FPTrappedException and AArch32_FPTrappedException, which take the
floating-point trap, and drops their bodies, so the back end calls each as a pure function that
returns `Unit`.  The stand-ins return `()`: in the translation, a trapped floating-point exception
returns to its caller, where the specification takes an exception.  FPProcessException calls
them only when FPCR enables the trap of the exception.
-/

namespace THE_MODULE_NAME

abbrev sign_extend {w : Nat} (x : BitVec w) (w' : Nat) := Sail.BitVec.signExtend x w'

def AArch64_FPTrappedException (_is_ase : Bool) (_accumulated_exceptions : BitVec 8) : Unit := ()

def AArch32_FPTrappedException (_accumulated_exceptions : BitVec 8) : Unit := ()

end THE_MODULE_NAME
