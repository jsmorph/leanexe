import Library.Numerics.Float64.Erfc.ErfcAccPlan

/-!
The kernel's checks of rows 1 to 8 of `C2` (`ErfcAccPlan.rowOK`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccRows0

open Library.Numerics.Float64.Erfc.ErfcAccPlan

theorem ok_1 : rowOK 1 := by decide +kernel
theorem ok_2 : rowOK 2 := by decide +kernel
theorem ok_3 : rowOK 3 := by decide +kernel
theorem ok_4 : rowOK 4 := by decide +kernel
theorem ok_5 : rowOK 5 := by decide +kernel
theorem ok_6 : rowOK 6 := by decide +kernel
theorem ok_7 : rowOK 7 := by decide +kernel
theorem ok_8 : rowOK 8 := by decide +kernel

#print axioms ok_1
#print axioms ok_8

end Library.Numerics.Float64.Erfc.ErfcAccRows0
