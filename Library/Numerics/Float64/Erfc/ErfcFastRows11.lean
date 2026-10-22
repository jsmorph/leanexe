import Library.Numerics.Float64.Erfc.ErfcFastPlan

/-!
The kernel's checks of rows 89 to 94 of `C` (`ErfcFastPlan.rowOK`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastRows11

open Library.Numerics.Float64.Erfc.ErfcFastPlan

theorem ok_89 : rowOK 89 := by decide +kernel
theorem ok_90 : rowOK 90 := by decide +kernel
theorem ok_91 : rowOK 91 := by decide +kernel
theorem ok_92 : rowOK 92 := by decide +kernel
theorem ok_93 : rowOK 93 := by decide +kernel
theorem ok_94 : rowOK 94 := by decide +kernel

#print axioms ok_89
#print axioms ok_94

end Library.Numerics.Float64.Erfc.ErfcFastRows11
