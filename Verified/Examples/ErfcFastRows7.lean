import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 57 to 64 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows7

open Verified.Examples.ErfcFastPlan

theorem ok_57 : rowOK 57 := by decide +kernel
theorem ok_58 : rowOK 58 := by decide +kernel
theorem ok_59 : rowOK 59 := by decide +kernel
theorem ok_60 : rowOK 60 := by decide +kernel
theorem ok_61 : rowOK 61 := by decide +kernel
theorem ok_62 : rowOK 62 := by decide +kernel
theorem ok_63 : rowOK 63 := by decide +kernel
theorem ok_64 : rowOK 64 := by decide +kernel

#print axioms ok_57
#print axioms ok_64

end Verified.Examples.ErfcFastRows7
