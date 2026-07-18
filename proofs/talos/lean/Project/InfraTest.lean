import Project.Common

namespace Project.InfraTest

open Wasm Project.Common

example (g0 : UInt64) (h : g0.toNat + 112 < 4294967296) :
    (g0 + 56).toNat = g0.toNat + 56 := by u64_omega

example (g0 : UInt64) :
    g0 + 56 + 48 = UInt64.ofNat (g0.toNat + 104) := by u64_omega

example (k : Nat) :
    UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by u64_omega

example (k count : Nat) (hk : k < count) (hc : count < 4294967296) :
    ¬(UInt64.ofNat k ≥ UInt64.ofNat count) := by u64_omega

example (a b : UInt64) (h : a.toNat + 8 ≤ b.toNat) : a ≠ b := by
  u64_omega

example (y : UInt64) (hy : y ≠ 0) : 0 < y.toNat := by
  u64_omega at hy ⊢

example (l : List Value) (h : l.length = 26)
    (hv : l[3]? = some (.i64 7)) : l[3] = .i64 7 :=
  getElem_of_some hv

example (x : UInt64) (h : x.toNat + 1 < 18446744073709551616) :
    (x + 1).toNat = x.toNat + 1 := by u64_omega

end Project.InfraTest
