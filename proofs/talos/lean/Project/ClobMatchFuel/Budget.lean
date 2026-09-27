import Project.ClobMatchFuel.Allocation

/-!
# Match-loop allocation budget

The generated matcher can allocate one replacement book and one appended trade
array per running iteration.  These lemmas bound that growth with fixed source
length limits and account for the corresponding fuel decrement.
-/

namespace Project.ClobMatchFuel.Budget

open Project.Clob Project.ClobMatchFuel.Allocation

def stepBytes (bookLimit tradeLimit : Nat) : Nat :=
  96 + orderArrayBytes bookLimit + tradeArrayBytes tradeLimit

theorem fixedArrayBytes_mono {n m stride : Nat} (h : n ≤ m) :
    fixedArrayBytes n stride ≤ fixedArrayBytes m stride := by
  have hWords : n * stride ≤ m * stride := Nat.mul_le_mul_right stride h
  have hData : n * stride * 8 ≤ m * stride * 8 :=
    Nat.mul_le_mul_right 8 hWords
  simpa [fixedArrayBytes] using Nat.add_le_add_left hData 8

theorem fullStepBytes_le {bookLength tradeLength bookLimit tradeLimit : Nat}
    (hBook : bookLength ≤ bookLimit)
    (hTrade : tradeLength + 1 ≤ tradeLimit) :
    96 + orderArrayBytes (bookLength - 1) +
        tradeArrayBytes (tradeLength + 1) ≤
      stepBytes bookLimit tradeLimit := by
  unfold stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes
  omega

theorem partialStepBytes_le {bookLength tradeLength bookLimit tradeLimit : Nat}
    (hBook : bookLength ≤ bookLimit)
    (hTrade : tradeLength + 1 ≤ tradeLimit) :
    96 + orderArrayBytes bookLength + tradeArrayBytes (tradeLength + 1) ≤
      stepBytes bookLimit tradeLimit := by
  unfold stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes
  omega

theorem fuel_sub_one_toNat (fuel : UInt64) (hFuel : fuel ≠ 0) :
    (fuel - 1).toNat = fuel.toNat - 1 := by
  apply Project.Common.toNat_sub_le
  have hPositive : 0 < fuel.toNat := by
    by_contra h
    have hZero : fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  have hOne : (1 : UInt64).toNat = 1 := rfl
  rw [hOne]
  exact hPositive

theorem one_step_available {fuel g0 : UInt64}
    {bookLimit tradeLimit limit : Nat}
    (hFuel : fuel ≠ 0)
    (hBudget : g0.toNat + fuel.toNat * stepBytes bookLimit tradeLimit ≤ limit) :
    g0.toNat + stepBytes bookLimit tradeLimit ≤ limit := by
  have hFuelPositive : 0 < fuel.toNat := by
    by_contra h
    have hZero : fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  have hMul : stepBytes bookLimit tradeLimit ≤
      fuel.toNat * stepBytes bookLimit tradeLimit := by
    have := Nat.mul_le_mul_right (stepBytes bookLimit tradeLimit)
      (show 1 ≤ fuel.toNat by omega)
    simpa using this
  omega

theorem allocationTop_toNat (base need : UInt64) (needNat : Nat)
    (hNeed : need.toNat = needNat)
    (hFit32 : base.toNat + 48 + needNat < 4294967296) :
    (base + 48 + need).toNat = base.toNat + 48 + needNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add, hNeed]
  have h48 : (48 : UInt64).toNat = 48 := rfl
  rw [h48]
  have hSize : 4294967296 < UInt64.size := by
    rw [Project.Common.size_eq]
    omega
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem spend_step {fuel g0 g0Final : UInt64}
    {bookLimit tradeLimit limit : Nat}
    (hFuel : fuel ≠ 0)
    (hGrowth : g0Final.toNat ≤ g0.toNat + stepBytes bookLimit tradeLimit)
    (hBudget : g0.toNat + fuel.toNat * stepBytes bookLimit tradeLimit ≤ limit) :
    g0Final.toNat + (fuel - 1).toNat * stepBytes bookLimit tradeLimit ≤
      limit := by
  have hFuelNat : fuel.toNat = (fuel - 1).toNat + 1 := by
    rw [fuel_sub_one_toNat fuel hFuel]
    have hPositive : 0 < fuel.toNat := by
      by_contra h
      have hZero : fuel.toNat = 0 := by omega
      apply hFuel
      apply UInt64.toNat.inj
      simpa using hZero
    omega
  calc
    g0Final.toNat + (fuel - 1).toNat * stepBytes bookLimit tradeLimit ≤
        (g0.toNat + stepBytes bookLimit tradeLimit) +
          (fuel - 1).toNat * stepBytes bookLimit tradeLimit :=
      Nat.add_le_add_right hGrowth _
    _ = g0.toNat + fuel.toNat * stepBytes bookLimit tradeLimit := by
      rw [hFuelNat, Nat.add_mul]
      omega
    _ ≤ limit := hBudget

end Project.ClobMatchFuel.Budget
