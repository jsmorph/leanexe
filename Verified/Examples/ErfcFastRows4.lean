import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 33 to 40 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows4

open Verified.Examples.ErfcFastPlan

theorem ok_33 : rowOK 33 := by decide +kernel
theorem ok_34 : rowOK 34 := by decide +kernel
theorem ok_35 : rowOK 35 := by decide +kernel
theorem ok_36 : rowOK 36 := by decide +kernel
theorem ok_37 : rowOK 37 := by decide +kernel
theorem ok_38 : rowOK 38 := by decide +kernel
theorem ok_39 : rowOK 39 := by decide +kernel
theorem ok_40 : rowOK 40 := by decide +kernel

#print axioms ok_33
#print axioms ok_40

end Verified.Examples.ErfcFastRows4
