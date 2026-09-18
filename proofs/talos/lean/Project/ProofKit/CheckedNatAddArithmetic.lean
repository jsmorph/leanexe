import Project.Common

namespace Project.ProofKit.CheckedNatAdd

theorem guard_of_fits (left right : Nat) (hfit : left + right < UInt64.size) :
    ¬ UInt64.ofNat left + UInt64.ofNat right < UInt64.ofNat left := by
  rw [← UInt64.ofNat_add, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' hfit,
    UInt64.toNat_ofNat_of_lt' (show left < UInt64.size by omega)]
  omega

end Project.ProofKit.CheckedNatAdd
