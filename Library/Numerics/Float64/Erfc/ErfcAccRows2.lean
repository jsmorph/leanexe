import Library.Numerics.Float64.Erfc.ErfcAccPlan

/-!
The kernel's checks of rows 17 to 24 of `C2` (`ErfcAccPlan.rowOK`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccRows2

open Library.Numerics.Float64.Erfc.ErfcAccPlan

theorem ok_17 : rowOK 17 := by decide +kernel
theorem ok_18 : rowOK 18 := by decide +kernel
theorem ok_19 : rowOK 19 := by decide +kernel
theorem ok_20 : rowOK 20 := by decide +kernel
theorem ok_21 : rowOK 21 := by decide +kernel
theorem ok_22 : rowOK 22 := by decide +kernel
theorem ok_23 : rowOK 23 := by decide +kernel
theorem ok_24 : rowOK 24 := by decide +kernel

#print axioms ok_17
#print axioms ok_24

end Library.Numerics.Float64.Erfc.ErfcAccRows2
