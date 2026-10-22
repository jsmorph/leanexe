import Library.Numerics.Float64.Erfc.ErfcFastPlan

/-!
The kernel's checks of rows 49 to 56 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastRows6

open Library.Numerics.Float64.Erfc.ErfcFastPlan

theorem ok_49 : rowOK 49 := by decide +kernel
theorem ok_50 : rowOK 50 := by decide +kernel
theorem ok_51 : rowOK 51 := by decide +kernel
theorem ok_52 : rowOK 52 := by decide +kernel
theorem ok_53 : rowOK 53 := by decide +kernel
theorem ok_54 : rowOK 54 := by decide +kernel
theorem ok_55 : rowOK 55 := by decide +kernel
theorem ok_56 : rowOK 56 := by decide +kernel

#print axioms ok_49
#print axioms ok_56

end Library.Numerics.Float64.Erfc.ErfcFastRows6
