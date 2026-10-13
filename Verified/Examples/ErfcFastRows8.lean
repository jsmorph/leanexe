import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 65 to 72 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows8

open Verified.Examples.ErfcFastPlan

theorem ok_65 : rowOK 65 := by decide +kernel
theorem ok_66 : rowOK 66 := by decide +kernel
theorem ok_67 : rowOK 67 := by decide +kernel
theorem ok_68 : rowOK 68 := by decide +kernel
theorem ok_69 : rowOK 69 := by decide +kernel
theorem ok_70 : rowOK 70 := by decide +kernel
theorem ok_71 : rowOK 71 := by decide +kernel
theorem ok_72 : rowOK 72 := by decide +kernel

#print axioms ok_65
#print axioms ok_72

end Verified.Examples.ErfcFastRows8
