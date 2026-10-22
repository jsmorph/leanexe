import Library.Numerics.Float64.Erfc.ErfcFastPlan

/-!
The kernel's checks of rows 81 to 88 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastRows10

open Library.Numerics.Float64.Erfc.ErfcFastPlan

theorem ok_81 : rowOK 81 := by decide +kernel
theorem ok_82 : rowOK 82 := by decide +kernel
theorem ok_83 : rowOK 83 := by decide +kernel
theorem ok_84 : rowOK 84 := by decide +kernel
theorem ok_85 : rowOK 85 := by decide +kernel
theorem ok_86 : rowOK 86 := by decide +kernel
theorem ok_87 : rowOK 87 := by decide +kernel
theorem ok_88 : rowOK 88 := by decide +kernel

#print axioms ok_81
#print axioms ok_88

end Library.Numerics.Float64.Erfc.ErfcFastRows10
