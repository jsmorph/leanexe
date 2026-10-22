import Library.Numerics.Float64.Erfc.ErfcFastPlan

/-!
The kernel's checks of rows 41 to 48 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastRows5

open Library.Numerics.Float64.Erfc.ErfcFastPlan

theorem ok_41 : rowOK 41 := by decide +kernel
theorem ok_42 : rowOK 42 := by decide +kernel
theorem ok_43 : rowOK 43 := by decide +kernel
theorem ok_44 : rowOK 44 := by decide +kernel
theorem ok_45 : rowOK 45 := by decide +kernel
theorem ok_46 : rowOK 46 := by decide +kernel
theorem ok_47 : rowOK 47 := by decide +kernel
theorem ok_48 : rowOK 48 := by decide +kernel

#print axioms ok_41
#print axioms ok_48

end Library.Numerics.Float64.Erfc.ErfcFastRows5
