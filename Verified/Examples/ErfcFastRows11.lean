import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 89 to 94 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows11

open Verified.Examples.ErfcFastPlan

theorem ok_89 : rowOK 89 := by decide +kernel
theorem ok_90 : rowOK 90 := by decide +kernel
theorem ok_91 : rowOK 91 := by decide +kernel
theorem ok_92 : rowOK 92 := by decide +kernel
theorem ok_93 : rowOK 93 := by decide +kernel
theorem ok_94 : rowOK 94 := by decide +kernel

#print axioms ok_89
#print axioms ok_94

end Verified.Examples.ErfcFastRows11
