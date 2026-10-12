import Verified.Examples.ErfcFastPlan

/-!
The kernel's checks of rows 31 to 46 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Verified.Examples.ErfcFastRows1

open Verified.Examples.ErfcFastPlan

theorem ok_31 : rowOK 31 := by decide +kernel
theorem ok_32 : rowOK 32 := by decide +kernel
theorem ok_33 : rowOK 33 := by decide +kernel
theorem ok_34 : rowOK 34 := by decide +kernel
theorem ok_35 : rowOK 35 := by decide +kernel
theorem ok_36 : rowOK 36 := by decide +kernel
theorem ok_37 : rowOK 37 := by decide +kernel
theorem ok_38 : rowOK 38 := by decide +kernel
theorem ok_39 : rowOK 39 := by decide +kernel
theorem ok_40 : rowOK 40 := by decide +kernel
theorem ok_41 : rowOK 41 := by decide +kernel
theorem ok_42 : rowOK 42 := by decide +kernel
theorem ok_43 : rowOK 43 := by decide +kernel
theorem ok_44 : rowOK 44 := by decide +kernel
theorem ok_45 : rowOK 45 := by decide +kernel
theorem ok_46 : rowOK 46 := by decide +kernel

#print axioms ok_31
#print axioms ok_46

end Verified.Examples.ErfcFastRows1
