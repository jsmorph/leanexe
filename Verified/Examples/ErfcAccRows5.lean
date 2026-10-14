import Verified.Examples.ErfcAccPlan

/-!
The kernel's checks of rows 41 to 47 of `C2` (`ErfcAccPlan.rowOK`).
-/

namespace Verified.Examples.ErfcAccRows5

open Verified.Examples.ErfcAccPlan

theorem ok_41 : rowOK 41 := by decide +kernel
theorem ok_42 : rowOK 42 := by decide +kernel
theorem ok_43 : rowOK 43 := by decide +kernel
theorem ok_44 : rowOK 44 := by decide +kernel
theorem ok_45 : rowOK 45 := by decide +kernel
theorem ok_46 : rowOK 46 := by decide +kernel
theorem ok_47 : rowOK 47 := by decide +kernel

#print axioms ok_41
#print axioms ok_47

end Verified.Examples.ErfcAccRows5
