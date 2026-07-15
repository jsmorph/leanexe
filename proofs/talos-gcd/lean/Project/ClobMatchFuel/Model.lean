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
