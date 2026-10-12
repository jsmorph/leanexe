import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 9 to 16 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows1

open Verified.Examples.ErfcFastPlan

theorem ok_9 : rowOK 9 := by decide +kernel
theorem ok_10 : rowOK 10 := by decide +kernel
theorem ok_11 : rowOK 11 := by decide +kernel
theorem ok_12 : rowOK 12 := by decide +kernel
theorem ok_13 : rowOK 13 := by decide +kernel
theorem ok_14 : rowOK 14 := by decide +kernel
theorem ok_15 : rowOK 15 := by decide +kernel
theorem ok_16 : rowOK 16 := by decide +kernel

#print axioms ok_9
#print axioms ok_16

end Verified.Examples.ErfcFastRows1
