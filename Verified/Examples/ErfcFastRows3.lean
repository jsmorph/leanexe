import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 25 to 32 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows3

open Verified.Examples.ErfcFastPlan

theorem ok_25 : rowOK 25 := by decide +kernel
theorem ok_26 : rowOK 26 := by decide +kernel
theorem ok_27 : rowOK 27 := by decide +kernel
theorem ok_28 : rowOK 28 := by decide +kernel
theorem ok_29 : rowOK 29 := by decide +kernel
theorem ok_30 : rowOK 30 := by decide +kernel
theorem ok_31 : rowOK 31 := by decide +kernel
theorem ok_32 : rowOK 32 := by decide +kernel

#print axioms ok_25
#print axioms ok_32

end Verified.Examples.ErfcFastRows3
