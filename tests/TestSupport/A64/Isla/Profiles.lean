import LeanExe.A64.Isla.Profile

/-!
The profiles `tcg` and `kvm` hold the settings of the `features` files as the files stand when this
module elaborates.  Lake builds `LeanExe/A64/Isla/Profile.lean` without tracking the files that
`isla_features%` reads, and `tests/isla/theorems.sh` elaborates this module on every run, so a
profile that an earlier version of a file built fails here.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64.Isla

/-- The profile `tcg` holds the settings of `tests/isla/tcg/features`. -/
theorem tcg_features : tcg.features = isla_features% "tests/isla/tcg/features" := rfl

/-- The profile `kvm` holds the settings of `tests/isla/kvm/features`. -/
theorem kvm_features : kvm.features = isla_features% "tests/isla/kvm/features" := rfl

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.tcg_features
#print axioms TestSupport.A64.Isla.kvm_features
