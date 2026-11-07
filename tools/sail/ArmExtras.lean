import Sail
import THE_MODULE_NAME.Defs
import THE_MODULE_NAME.SpecializationV1

/-!
The external functions of the arm-v9.4-a model that the slice calls and Sail's Lean library
lacks, after sail-arm's `lean/ArmExtras.lean` (whose imports and namespace follow a later Sail).
-/

namespace THE_MODULE_NAME

abbrev sign_extend {w : Nat} (x : BitVec w) (w' : Nat) := Sail.BitVec.signExtend x w'

end THE_MODULE_NAME
