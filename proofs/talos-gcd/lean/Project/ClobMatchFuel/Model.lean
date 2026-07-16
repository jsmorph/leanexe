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

end Project.ClobMatchFuel.Model
