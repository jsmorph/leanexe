import Project.ClobDepth.Model

/-!
# Source properties for `depth`

The price sequence records the first occurrence of each price on one side.
The quantity theorems state exact modular aggregation for every price and its
natural-number interpretation when the selected quantity sum fits `UInt64`.
-/

namespace Project.ClobDepth.Properties

open Project.Clob Project.ClobDepth.Model

def levelPrices (levels : List LevelL) : List UInt64 :=
  levels.map LevelL.lprice

def appendPrice (prices : List UInt64) (price : UInt64) : List UInt64 :=
  if price ∈ prices then prices else prices ++ [price]

def sidePriceStep (side : UInt64) (prices : List UInt64)
    (order : OrderL) : List UInt64 :=
  if order.oside = side then appendPrice prices order.oprice else prices

def sidePrices (book : List OrderL) (side : UInt64) : List UInt64 :=
  book.foldl (sidePriceStep side) []

def levelQtyAt : List LevelL → UInt64 → UInt64
  | [], _ => 0
  | level :: levels, price =>
      (if level.lprice = price then level.lqty else 0) +
        levelQtyAt levels price

def orderQtyAt : List OrderL → UInt64 → UInt64 → UInt64
  | [], _, _ => 0
  | order :: orders, side, price =>
      (if order.oside = side ∧ order.oprice = price then order.oqty else 0) +
        orderQtyAt orders side price

def orderQtyAtNat : List OrderL → UInt64 → UInt64 → Nat
  | [], _, _ => 0
  | order :: orders, side, price =>
      (if order.oside = side ∧ order.oprice = price then order.oqty.toNat else 0) +
        orderQtyAtNat orders side price

@[simp]
theorem levelPrices_addLevelL (levels : List LevelL) (price qty : UInt64) :
    levelPrices (addLevelL levels price qty) =
      appendPrice (levelPrices levels) price := by
  induction levels with
  | nil => simp [addLevelL, levelPrices, appendPrice]
  | cons level levels ih =>
      by_cases hPrice : level.lprice = price
      · simp [addLevelL, levelPrices, appendPrice, hPrice]
      · have hHead : price ≠ level.lprice := Ne.symm hPrice
        rw [show addLevelL (level :: levels) price qty =
          level :: addLevelL levels price qty by simp [addLevelL, hPrice]]
        change level.lprice :: levelPrices (addLevelL levels price qty) =
          appendPrice (level.lprice :: levelPrices levels) price
        rw [ih]
        by_cases hTail : price ∈ levelPrices levels
        · simp [appendPrice, hHead, hTail]
        · simp [appendPrice, hHead, hTail]

theorem levelPrices_fold (book : List OrderL) (side : UInt64)
    (levels : List LevelL) :
    levelPrices
        (book.foldl (fun current order =>
          if order.oside = side then
            addLevelL current order.oprice order.oqty
          else
            current) levels) =
      book.foldl (sidePriceStep side) (levelPrices levels) := by
  induction book generalizing levels with
  | nil => rfl
  | cons order book ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hSide : order.oside = side
      · simp [sidePriceStep, hSide]
      · simp [sidePriceStep, hSide]

theorem depthSideL_prices (book : List OrderL) (side : UInt64) :
    levelPrices (depthSideL book side) = sidePrices book side := by
  unfold depthSideL sidePrices
  change levelPrices
      (book.foldl (fun current order =>
        if order.oside = side then
          addLevelL current order.oprice order.oqty
        else
          current) []) =
    book.foldl (sidePriceStep side) (levelPrices [])
  exact levelPrices_fold book side []

theorem appendPrice_mem (prices : List UInt64) (price query : UInt64) :
    query ∈ appendPrice prices price ↔ query ∈ prices ∨ query = price := by
  by_cases hPrice : price ∈ prices
  · constructor
    · intro hQuery
      exact Or.inl (by simpa [appendPrice, hPrice] using hQuery)
    · intro hQuery
      rcases hQuery with hQuery | rfl
      · simpa [appendPrice, hPrice] using hQuery
      · simp [appendPrice, hPrice]
  · simp [appendPrice, hPrice]

theorem sidePrices_mem_from (book : List OrderL) (side query : UInt64)
    (prices : List UInt64) :
    query ∈ book.foldl (sidePriceStep side) prices ↔
      query ∈ prices ∨
        ∃ order ∈ book, order.oside = side ∧ order.oprice = query := by
  induction book generalizing prices with
  | nil => simp
  | cons order book ih =>
      rw [List.foldl_cons, ih]
      by_cases hSide : order.oside = side
      · rw [show sidePriceStep side prices order =
          appendPrice prices order.oprice by simp [sidePriceStep, hSide]]
        rw [appendPrice_mem]
        aesop
      · rw [show sidePriceStep side prices order = prices by
          simp [sidePriceStep, hSide]]
        aesop

theorem sidePrices_mem (book : List OrderL) (side query : UInt64) :
    query ∈ sidePrices book side ↔
      ∃ order ∈ book, order.oside = side ∧ order.oprice = query := by
  unfold sidePrices
  simpa using sidePrices_mem_from book side query []

theorem appendPrice_nodup {prices : List UInt64} {price : UInt64}
    (hPrices : prices.Nodup) : (appendPrice prices price).Nodup := by
  by_cases hPrice : price ∈ prices
  · simpa [appendPrice, hPrice] using hPrices
  · rw [appendPrice, if_neg hPrice, List.nodup_append]
    refine ⟨hPrices, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact fun h => hPrice (h ▸ ha)

theorem sidePrices_nodup_from (book : List OrderL) (side : UInt64)
    (prices : List UInt64) (hPrices : prices.Nodup) :
    (book.foldl (sidePriceStep side) prices).Nodup := by
  induction book generalizing prices with
  | nil => exact hPrices
  | cons order book ih =>
      rw [List.foldl_cons]
      apply ih
      by_cases hSide : order.oside = side
      · simpa [sidePriceStep, hSide] using appendPrice_nodup hPrices
      · simpa [sidePriceStep, hSide] using hPrices

theorem sidePrices_nodup (book : List OrderL) (side : UInt64) :
    (sidePrices book side).Nodup := by
  exact sidePrices_nodup_from book side [] (by simp)

theorem sidePrices_append_new (book : List OrderL) (order : OrderL)
    (side : UInt64) (hSide : order.oside = side)
    (hNew : order.oprice ∉ sidePrices book side) :
    sidePrices (book ++ [order]) side =
      sidePrices book side ++ [order.oprice] := by
  unfold sidePrices at hNew ⊢
  simp [List.foldl_append, sidePriceStep, hSide, appendPrice, hNew]

theorem sidePrices_append_seen (book : List OrderL) (order : OrderL)
    (side : UInt64) (hSeen : order.oprice ∈ sidePrices book side) :
    sidePrices (book ++ [order]) side = sidePrices book side := by
  unfold sidePrices at hSeen ⊢
  by_cases hSide : order.oside = side
  · simp [List.foldl_append, sidePriceStep, hSide, appendPrice, hSeen]
  · simp [List.foldl_append, sidePriceStep, hSide]

theorem sidePrices_append_other (book : List OrderL) (order : OrderL)
    (side : UInt64) (hSide : order.oside ≠ side) :
    sidePrices (book ++ [order]) side = sidePrices book side := by
  simp [sidePrices, List.foldl_append, sidePriceStep, hSide]

theorem addLevelL_qtyAt (levels : List LevelL) (price qty query : UInt64) :
    levelQtyAt (addLevelL levels price qty) query =
      levelQtyAt levels query + (if price = query then qty else 0) := by
  induction levels with
  | nil => simp [addLevelL, levelQtyAt]
  | cons level levels ih =>
      by_cases hLevel : level.lprice = price
      · by_cases hQuery : price = query
        · subst query
          rw [addLevelL, if_pos hLevel]
          simp [levelQtyAt, hLevel]
          ac_rfl
        · rw [addLevelL, if_pos hLevel]
          simp [levelQtyAt, hLevel, hQuery]
      · rw [addLevelL, if_neg hLevel]
        simp only [levelQtyAt, ih]
        ac_rfl

theorem levelQtyAt_fold (book : List OrderL) (side query : UInt64)
    (levels : List LevelL) :
    levelQtyAt
        (book.foldl (fun current order =>
          if order.oside = side then
            addLevelL current order.oprice order.oqty
          else
            current) levels) query =
      levelQtyAt levels query + orderQtyAt book side query := by
  induction book generalizing levels with
  | nil => simp [orderQtyAt]
  | cons order book ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hSide : order.oside = side
      · by_cases hPrice : order.oprice = query
        · simp [hSide, hPrice, orderQtyAt, addLevelL_qtyAt]
          ac_rfl
        · simp [hSide, hPrice, orderQtyAt, addLevelL_qtyAt]
      · simp [hSide, orderQtyAt]

theorem depthSideL_qtyAt (book : List OrderL) (side price : UInt64) :
    levelQtyAt (depthSideL book side) price = orderQtyAt book side price := by
  unfold depthSideL
  change levelQtyAt
      (book.foldl (fun current order =>
        if order.oside = side then
          addLevelL current order.oprice order.oqty
        else
          current) []) price = orderQtyAt book side price
  simpa [levelQtyAt] using levelQtyAt_fold book side price []

theorem orderQtyAt_toNat (book : List OrderL) (side price : UInt64)
    (hBound : orderQtyAtNat book side price < UInt64.size) :
    (orderQtyAt book side price).toNat = orderQtyAtNat book side price := by
  induction book with
  | nil => simp [orderQtyAt, orderQtyAtNat]
  | cons order book ih =>
      by_cases hMatch : order.oside = side ∧ order.oprice = price
      · rw [orderQtyAtNat, if_pos hMatch] at hBound
        rw [orderQtyAt, if_pos hMatch, UInt64.toNat_add,
          ih (by omega), Nat.mod_eq_of_lt hBound,
          orderQtyAtNat, if_pos hMatch]
      · rw [orderQtyAtNat, if_neg hMatch] at hBound
        have hTail : orderQtyAtNat book side price < UInt64.size := by
          omega
        rw [orderQtyAt, if_neg hMatch, UInt64.zero_add,
          orderQtyAtNat, if_neg hMatch, Nat.zero_add]
        exact ih hTail

theorem depthSideL_qtyAt_nat (book : List OrderL) (side price : UInt64)
    (hBound : orderQtyAtNat book side price < UInt64.size) :
    (levelQtyAt (depthSideL book side) price).toNat =
      orderQtyAtNat book side price := by
  rw [depthSideL_qtyAt, orderQtyAt_toNat book side price hBound]

end Project.ClobDepth.Properties
