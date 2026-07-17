import Project.ClobFindBest.Model

/-!
# Source model for `matchFuel`

The model follows the bounded source recursion over lists of orders and trades.
It preserves `UInt64` subtraction and the source branch order.  Allocation and
ownership remain properties of the generated-program theorem.
-/

namespace Project.ClobMatchFuel.Model

open Project.Clob Project.ClobFindBest.Model

structure MatchStateL where
  book : List OrderL
  trades : List TradeL
  remaining : UInt64
  deriving Inhabited

def fillTradeL (taker maker : OrderL) (qty : UInt64) : TradeL :=
  { ttakerId := taker.oid
    tmakerId := maker.oid
    tprice := maker.oprice
    tqty := qty }

def setQtyL : List OrderL → Nat → UInt64 → List OrderL
  | [], _, _ => []
  | order :: orders, 0, qty => { order with oqty := qty } :: orders
  | order :: orders, i + 1, qty => order :: setQtyL orders i qty

@[simp]
theorem setQtyL_length (orders : List OrderL) (i : Nat) (qty : UInt64) :
    (setQtyL orders i qty).length = orders.length := by
  induction orders generalizing i with
  | nil => simp [setQtyL]
  | cons order orders ih =>
      cases i <;> simp [setQtyL, ih]

theorem setQtyL_eq_set (orders : List OrderL) (i : Nat) (qty : UInt64)
    (hi : i < orders.length) :
    setQtyL orders i qty =
      orders.set i { orders[i]! with oqty := qty } := by
  induction orders generalizing i with
  | nil => simp at hi
  | cons order orders ih =>
      cases i with
      | zero => simp [setQtyL]
      | succ i =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
          simpa [setQtyL] using congrArg (List.cons order) (ih i hi)

theorem setQtyL_word (orders : List OrderL) (i j field : Nat)
    (qty : UInt64) (hi : i < orders.length) (hj : j < orders.length)
    (hfield : field < 5) :
    (setQtyL orders i qty)[j]!.word field =
      if i = j ∧ field = 4 then qty else orders[j]!.word field := by
  rw [setQtyL_eq_set orders i qty hi]
  by_cases hij : i = j
  · subst i
    rw [getElem!_pos _ j (by simpa using hj)]
    obtain rfl | rfl | rfl | rfl | rfl :
        field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 := by
      omega
    all_goals simp [getElem!_pos orders j hj, OrderL.word]
  · rw [getElem!_pos _ j (by simpa using hj),
      List.getElem_set_of_ne hij _ (by simpa using hj)]
    simp [hij, getElem!_pos orders j hj]

def matchFuelL : Nat → OrderL → MatchStateL → MatchStateL
  | 0, _, state => state
  | fuel + 1, taker, state =>
      if state.remaining = 0 then
        state
      else
        match findBestL state.book taker with
        | none => state
        | some i =>
            let maker := state.book[i]!
            if maker.oqty ≤ state.remaining then
              matchFuelL fuel taker
                { book := state.book.eraseIdx i
                  trades := state.trades ++ [fillTradeL taker maker maker.oqty]
                  remaining := state.remaining - maker.oqty }
            else
              { book := setQtyL state.book i (maker.oqty - state.remaining)
                trades := state.trades ++
                  [fillTradeL taker maker state.remaining]
                remaining := 0 }

def fullFillCountL : Nat → OrderL → MatchStateL → Nat
  | 0, _, _ => 0
  | fuel + 1, taker, state =>
      if state.remaining = 0 then
        0
      else
        match findBestL state.book taker with
        | none => 0
        | some i =>
            let maker := state.book[i]!
            if maker.oqty ≤ state.remaining then
              1 + fullFillCountL fuel taker
                { book := state.book.eraseIdx i
                  trades := state.trades ++ [fillTradeL taker maker maker.oqty]
                  remaining := state.remaining - maker.oqty }
            else
              0

@[simp]
theorem matchFuelL_succ_zero (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (hRemaining : state.remaining = 0) :
    matchFuelL (fuel + 1) taker state = state := by
  simp [matchFuelL, hRemaining]

theorem matchFuelL_succ_none (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (hRemaining : state.remaining ≠ 0)
    (hFind : findBestL state.book taker = none) :
    matchFuelL (fuel + 1) taker state = state := by
  simp [matchFuelL, hRemaining, hFind]

theorem matchFuelL_succ_full (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (i : Nat) (hRemaining : state.remaining ≠ 0)
    (hFind : findBestL state.book taker = some i)
    (hQty : state.book[i]!.oqty ≤ state.remaining) :
    matchFuelL (fuel + 1) taker state =
      matchFuelL fuel taker
        { book := state.book.eraseIdx i
          trades := state.trades ++
            [fillTradeL taker state.book[i]! state.book[i]!.oqty]
          remaining := state.remaining - state.book[i]!.oqty } := by
  rw [matchFuelL, if_neg hRemaining, hFind]
  simp only
  rw [if_pos hQty]

theorem matchFuelL_succ_partial (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (i : Nat) (hRemaining : state.remaining ≠ 0)
    (hFind : findBestL state.book taker = some i)
    (hQty : ¬state.book[i]!.oqty ≤ state.remaining) :
    matchFuelL (fuel + 1) taker state =
      { book := setQtyL state.book i
          (state.book[i]!.oqty - state.remaining)
        trades := state.trades ++
          [fillTradeL taker state.book[i]! state.remaining]
        remaining := 0 } := by
  rw [matchFuelL, if_neg hRemaining, hFind]
  simp only
  rw [if_neg hQty]

@[simp]
theorem fullFillCountL_succ_zero (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (hRemaining : state.remaining = 0) :
    fullFillCountL (fuel + 1) taker state = 0 := by
  simp [fullFillCountL, hRemaining]

theorem fullFillCountL_succ_none (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (hRemaining : state.remaining ≠ 0)
    (hFind : findBestL state.book taker = none) :
    fullFillCountL (fuel + 1) taker state = 0 := by
  simp [fullFillCountL, hRemaining, hFind]

theorem fullFillCountL_succ_full (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (i : Nat) (hRemaining : state.remaining ≠ 0)
    (hFind : findBestL state.book taker = some i)
    (hQty : state.book[i]!.oqty ≤ state.remaining) :
    fullFillCountL (fuel + 1) taker state =
      1 + fullFillCountL fuel taker
        { book := state.book.eraseIdx i
          trades := state.trades ++
            [fillTradeL taker state.book[i]! state.book[i]!.oqty]
          remaining := state.remaining - state.book[i]!.oqty } := by
  rw [fullFillCountL, if_neg hRemaining, hFind]
  simp only
  rw [if_pos hQty]

theorem fullFillCountL_succ_partial (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) (i : Nat) (hRemaining : state.remaining ≠ 0)
    (hFind : findBestL state.book taker = some i)
    (hQty : ¬state.book[i]!.oqty ≤ state.remaining) :
    fullFillCountL (fuel + 1) taker state = 0 := by
  rw [fullFillCountL, if_neg hRemaining, hFind]
  simp only
  rw [if_neg hQty]

theorem fullFillCountL_le (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) : fullFillCountL fuel taker state ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [fullFillCountL]
  | succ fuel ih =>
      by_cases hRemaining : state.remaining = 0
      · simp [fullFillCountL, hRemaining]
      · cases hFind : findBestL state.book taker with
        | none => simp [fullFillCountL, hRemaining, hFind]
        | some i =>
            by_cases hQty : state.book[i]!.oqty ≤ state.remaining
            · rw [fullFillCountL_succ_full fuel taker state i hRemaining
                hFind hQty]
              simpa [Nat.add_comm] using Nat.add_le_add_left (ih _) 1
            · rw [fullFillCountL_succ_partial fuel taker state i hRemaining
                hFind hQty]
              omega

theorem matchFuelL_length_bounds (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) :
    (matchFuelL fuel taker state).book.length ≤ state.book.length ∧
    (matchFuelL fuel taker state).trades.length ≤
      state.trades.length + fuel := by
  induction fuel generalizing state with
  | zero => simp [matchFuelL]
  | succ fuel ih =>
      by_cases hRemaining : state.remaining = 0
      · simp [matchFuelL, hRemaining]
      · cases hFind : findBestL state.book taker with
        | none => simp [matchFuelL, hRemaining, hFind]
        | some i =>
            have hi : i < state.book.length :=
              findBestL_some_lt state.book taker i hFind
            by_cases hQty : state.book[i]!.oqty ≤ state.remaining
            · rw [matchFuelL_succ_full fuel taker state i hRemaining hFind
                hQty]
              have hBounds := ih (state :=
                { book := state.book.eraseIdx i
                  trades := state.trades ++
                    [fillTradeL taker state.book[i]! state.book[i]!.oqty]
                  remaining := state.remaining - state.book[i]!.oqty })
              constructor
              · exact hBounds.1.trans (by
                  rw [List.length_eraseIdx_of_lt hi]
                  omega)
              · have hTrades := hBounds.2
                simp only [List.length_append, List.length_singleton] at hTrades
                omega
            · rw [matchFuelL_succ_partial fuel taker state i hRemaining
                hFind hQty]
              simp [setQtyL_length]

end Project.ClobMatchFuel.Model
