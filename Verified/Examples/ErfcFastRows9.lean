import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 73 to 80 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows9

open Verified.Examples.ErfcFastPlan

theorem ok_73 : rowOK 73 := by decide +kernel
theorem ok_74 : rowOK 74 := by decide +kernel
theorem ok_75 : rowOK 75 := by decide +kernel
theorem ok_76 : rowOK 76 := by decide +kernel
theorem ok_77 : rowOK 77 := by decide +kernel
theorem ok_78 : rowOK 78 := by decide +kernel
theorem ok_79 : rowOK 79 := by decide +kernel
theorem ok_80 : rowOK 80 := by decide +kernel

#print axioms ok_73
#print axioms ok_80

end Verified.Examples.ErfcFastRows9
