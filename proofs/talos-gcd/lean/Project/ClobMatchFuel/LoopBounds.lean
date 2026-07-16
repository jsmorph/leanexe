import Project.ClobMatchFuel.LoopInvariant

/-!
# Match-loop step bounds

One remaining budget step bounds both replacement-array allocations.  The
derived facts cover the full-fill and partial-fill book sizes and their shared
trade append.  Branch composition consumes this record without repeating
fixed-array and `UInt64` normalization.
-/

namespace Project.ClobMatchFuel.LoopBounds

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.LoopInvariant

structure StepBounds (ctx : Context) (st : Store Unit)
    (data : RunningData) : Prop where
  ordersLength64 : data.orders.length < UInt64.size
  erasedLength64 : data.orders.length - 1 < UInt64.size
  orderWords64 : data.orders.length * 5 < UInt64.size
  fullBookBytes : orderArrayBytes (data.orders.length - 1) + 7 < UInt64.size
  partialBookBytes : orderArrayBytes data.orders.length + 7 < UInt64.size
  partialBookTotalU :
    (UInt64.ofNat data.orders.length * 5).toNat = data.orders.length * 5
  partialBookTotal64 : data.orders.length * 5 < UInt64.size
  tradeLength64 : data.tradeValues.length + 1 < UInt64.size
  tradeBytes : tradeArrayBytes (data.tradeValues.length + 1) + 7 < UInt64.size
  tradeTotalU :
    (UInt64.ofNat data.tradeValues.length * 4).toNat =
      data.tradeValues.length * 4
  tradeTotal64 : data.tradeValues.length * 4 < UInt64.size
  fullBookTop :
    (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1)).toNat =
      data.g0.toNat + 48 +
        (orderArrayBytesU (data.orders.length - 1)).toNat
  fullBookFit32 : data.g0.toNat + 48 +
    (orderArrayBytesU (data.orders.length - 1)).toNat < 4294967296
  fullBookFit : data.g0.toNat + 48 +
    (orderArrayBytesU (data.orders.length - 1)).toNat ≤ st.mem.pages * 65536
  partialBookTop :
    (data.g0 + 48 + orderArrayBytesU data.orders.length).toNat =
      data.g0.toNat + 48 + (orderArrayBytesU data.orders.length).toNat
  partialBookFit32 : data.g0.toNat + 48 +
    (orderArrayBytesU data.orders.length).toNat < 4294967296
  partialBookFit : data.g0.toNat + 48 +
    (orderArrayBytesU data.orders.length).toNat ≤ st.mem.pages * 65536
  tradeTopAtG0 :
    (data.g0 + 48 + tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
      data.g0.toNat + 48 +
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat
  tradeFit32AtG0 : data.g0.toNat + 48 +
    (tradeArrayBytesU (data.tradeValues.length + 1)).toNat < 4294967296
  tradeFitAtG0 : data.g0.toNat + 48 +
    (tradeArrayBytesU (data.tradeValues.length + 1)).toNat ≤
      st.mem.pages * 65536
  fullTradeTopAfterBook :
    (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
        tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
      (data.g0 + 48 +
        orderArrayBytesU (data.orders.length - 1)).toNat + 48 +
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat
  fullTradeFit32AfterBook :
    (data.g0 + 48 +
        orderArrayBytesU (data.orders.length - 1)).toNat + 48 +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat < 4294967296
  fullTradeFitAfterBook :
    (data.g0 + 48 +
        orderArrayBytesU (data.orders.length - 1)).toNat + 48 +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat ≤
        st.mem.pages * 65536
  partialTradeTopAfterBook :
    (data.g0 + 48 + orderArrayBytesU data.orders.length + 48 +
        tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
      (data.g0 + 48 + orderArrayBytesU data.orders.length).toNat + 48 +
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat
  partialTradeFit32AfterBook :
    (data.g0 + 48 + orderArrayBytesU data.orders.length).toNat + 48 +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat < 4294967296
  partialTradeFitAfterBook :
    (data.g0 + 48 + orderArrayBytesU data.orders.length).toNat + 48 +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat ≤
        st.mem.pages * 65536

theorem of_running (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) : StepBounds ctx st data := by
  have hFuelPositive : 0 < data.fuel.toNat := by
    by_contra h
    have hZero : data.fuel.toNat = 0 := by omega
    apply hFuel
    apply UInt64.toNat.inj
    simpa using hZero
  have hFuelSpent := facts.fuelSpent
  have hBookLength := facts.bookLength
  have hTradeLengthEq := facts.tradeLength
  have hAddressLimit := facts.addressLimit
  have hTradeLength : data.tradeValues.length + 1 ≤ ctx.tradeLimit := by
    rw [hTradeLengthEq]
    unfold Context.tradeLimit
    omega
  have hAvailable := Budget.one_step_available hFuel facts.budget
  have hAvailable' := hAvailable
  unfold Budget.stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes at hAvailable'
  have hLimitSize : ctx.limit < UInt64.size := by
    rw [size_eq]
    omega
  have hOrdersLength64 : data.orders.length < UInt64.size := by
    rw [size_eq]
    unfold Context.bookLimit at hBookLength hAvailable'
    omega
  have hErasedLength64 : data.orders.length - 1 < UInt64.size := by omega
  have hOrderWords64 : data.orders.length * 5 < UInt64.size := by
    rw [size_eq]
    unfold Context.bookLimit at hBookLength hAvailable'
    omega
  have hFullBookBytes : orderArrayBytes (data.orders.length - 1) + 7 <
      UInt64.size := by
    rw [size_eq]
    unfold Context.bookLimit at hBookLength hAvailable'
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hPartialBookBytes : orderArrayBytes data.orders.length + 7 <
      UInt64.size := by
    rw [size_eq]
    unfold Context.bookLimit at hBookLength hAvailable'
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hTradeLength64 : data.tradeValues.length + 1 < UInt64.size := by
    rw [size_eq]
    unfold Context.tradeLimit at hTradeLength hAvailable'
    omega
  have hTradeBytes : tradeArrayBytes (data.tradeValues.length + 1) + 7 <
      UInt64.size := by
    rw [size_eq]
    unfold Context.tradeLimit at hTradeLength hAvailable'
    unfold tradeArrayBytes fixedArrayBytes
    omega
  have hTradeTotal64 : data.tradeValues.length * 4 < UInt64.size := by
    rw [size_eq]
    unfold Context.tradeLimit at hTradeLength hAvailable'
    omega
  have hFullNeed : (orderArrayBytesU (data.orders.length - 1)).toNat =
      orderArrayBytes (data.orders.length - 1) :=
    fixedArrayBytesU_toNat (data.orders.length - 1) 5 hErasedLength64
      (by decide) (by
        change fixedArrayBytes (data.orders.length - 1) 5 + 7 <
          UInt64.size at hFullBookBytes
        omega)
  have hPartialNeed : (orderArrayBytesU data.orders.length).toNat =
      orderArrayBytes data.orders.length :=
    fixedArrayBytesU_toNat data.orders.length 5 hOrdersLength64
      (by decide) (by
        change fixedArrayBytes data.orders.length 5 + 7 < UInt64.size at hPartialBookBytes
        omega)
  have hTradeNeed :
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
        tradeArrayBytes (data.tradeValues.length + 1) :=
    fixedArrayBytesU_toNat (data.tradeValues.length + 1) 4 hTradeLength64
      (by decide) (by
        change fixedArrayBytes (data.tradeValues.length + 1) 4 + 7 <
          UInt64.size at hTradeBytes
        omega)
  have hFullBookFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (data.orders.length - 1)).toNat < 4294967296 := by
    rw [hFullNeed]
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hPartialBookFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU data.orders.length).toNat < 4294967296 := by
    rw [hPartialNeed]
    unfold orderArrayBytes fixedArrayBytes
    omega
  have hTradeFit32AtG0 : data.g0.toNat + 48 +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat < 4294967296 := by
    rw [hTradeNeed]
    unfold tradeArrayBytes fixedArrayBytes
    omega
  have hFullTradeFit32 : data.g0.toNat + 96 +
      (orderArrayBytesU (data.orders.length - 1)).toNat +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat <
        4294967296 := by
    rw [hFullNeed, hTradeNeed]
    unfold orderArrayBytes tradeArrayBytes fixedArrayBytes
    omega
  have hPartialTradeFit32 : data.g0.toNat + 96 +
      (orderArrayBytesU data.orders.length).toNat +
      (tradeArrayBytesU (data.tradeValues.length + 1)).toNat <
        4294967296 := by
    rw [hPartialNeed, hTradeNeed]
    unfold orderArrayBytes tradeArrayBytes fixedArrayBytes
    omega
  have hFullBookTop := Budget.allocationTop_toNat data.g0
    (orderArrayBytesU (data.orders.length - 1))
    (orderArrayBytes (data.orders.length - 1)) hFullNeed (by
      simpa [hFullNeed] using hFullBookFit32)
  have hPartialBookTop := Budget.allocationTop_toNat data.g0
    (orderArrayBytesU data.orders.length) (orderArrayBytes data.orders.length)
    hPartialNeed (by simpa [hPartialNeed] using hPartialBookFit32)
  have hTradeTop := Budget.allocationTop_toNat data.g0
    (tradeArrayBytesU (data.tradeValues.length + 1))
    (tradeArrayBytes (data.tradeValues.length + 1)) hTradeNeed
    (by simpa [hTradeNeed] using hTradeFit32AtG0)
  have hFullTradeFit32After :
      (data.g0 + 48 +
          orderArrayBytesU (data.orders.length - 1)).toNat + 48 +
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat <
          4294967296 := by
    rw [hFullBookTop, hTradeNeed]
    omega
  have hPartialTradeFit32After :
      (data.g0 + 48 + orderArrayBytesU data.orders.length).toNat + 48 +
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat <
          4294967296 := by
    rw [hPartialBookTop, hTradeNeed]
    omega
  have hFullTradeTop := Budget.allocationTop_toNat
    (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1))
    (tradeArrayBytesU (data.tradeValues.length + 1))
    (tradeArrayBytes (data.tradeValues.length + 1)) hTradeNeed
    (by simpa [hTradeNeed] using hFullTradeFit32After)
  have hPartialTradeTop := Budget.allocationTop_toNat
    (data.g0 + 48 + orderArrayBytesU data.orders.length)
    (tradeArrayBytesU (data.tradeValues.length + 1))
    (tradeArrayBytes (data.tradeValues.length + 1)) hTradeNeed
    (by simpa [hTradeNeed] using hPartialTradeFit32After)
  have hFit : data.g0.toNat + Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤
      st.mem.pages * 65536 := hAvailable.trans facts.memoryLimit
  refine {
    ordersLength64 := hOrdersLength64
    erasedLength64 := hErasedLength64
    orderWords64 := hOrderWords64
    fullBookBytes := hFullBookBytes
    partialBookBytes := hPartialBookBytes
    partialBookTotalU := ?_
    partialBookTotal64 := hOrderWords64
    tradeLength64 := hTradeLength64
    tradeBytes := hTradeBytes
    tradeTotalU := ?_
    tradeTotal64 := hTradeTotal64
    fullBookTop := by simpa [hFullNeed] using hFullBookTop
    fullBookFit32 := hFullBookFit32
    fullBookFit := ?_
    partialBookTop := by simpa [hPartialNeed] using hPartialBookTop
    partialBookFit32 := hPartialBookFit32
    partialBookFit := ?_
    tradeTopAtG0 := by simpa [hTradeNeed] using hTradeTop
    tradeFit32AtG0 := hTradeFit32AtG0
    tradeFitAtG0 := ?_
    fullTradeTopAfterBook := by simpa [hTradeNeed] using hFullTradeTop
    fullTradeFit32AfterBook := hFullTradeFit32After
    fullTradeFitAfterBook := ?_
    partialTradeTopAfterBook := by simpa [hTradeNeed] using hPartialTradeTop
    partialTradeFit32AfterBook := hPartialTradeFit32After
    partialTradeFitAfterBook := ?_ }
  · rw [UInt64.toNat_mul, toNat_ofNat_lt hOrdersLength64]
    change data.orders.length * 5 % UInt64.size = data.orders.length * 5
    exact Nat.mod_eq_of_lt hOrderWords64
  · rw [UInt64.toNat_mul]
    have hLength : data.tradeValues.length < UInt64.size := by omega
    rw [toNat_ofNat_lt hLength]
    change data.tradeValues.length * 4 % UInt64.size =
      data.tradeValues.length * 4
    exact Nat.mod_eq_of_lt hTradeTotal64
  · rw [hFullNeed]
    unfold Budget.stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes at hFit
    unfold orderArrayBytes fixedArrayBytes
    omega
  · rw [hPartialNeed]
    unfold Budget.stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes at hFit
    unfold orderArrayBytes fixedArrayBytes
    omega
  · rw [hTradeNeed]
    unfold Budget.stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes at hFit
    unfold tradeArrayBytes fixedArrayBytes
    omega
  · rw [hFullBookTop, hTradeNeed]
    unfold Budget.stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes at hFit
    unfold orderArrayBytes tradeArrayBytes fixedArrayBytes
    omega
  · rw [hPartialBookTop, hTradeNeed]
    unfold Budget.stepBytes orderArrayBytes tradeArrayBytes fixedArrayBytes at hFit
    unfold orderArrayBytes tradeArrayBytes fixedArrayBytes
    omega

end Project.ClobMatchFuel.LoopBounds
