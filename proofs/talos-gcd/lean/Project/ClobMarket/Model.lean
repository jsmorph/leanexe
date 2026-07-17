import Project.ClobLimit.Model

/-!
# Source model for `market`

The model applies the proved list matcher to a taker with an unlimited crossing
price.  It preserves the source validity branch and omits residual insertion.
Allocation and ownership remain properties of the artifact theorem.
-/

namespace Project.ClobMarket.Model

open Project.Clob Project.ClobPostOnly.Model Project.ClobLimit.Model
  Project.ClobMatchFuel.Properties

def unlimitedTakerL (order : OrderL) : OrderL :=
  if order.oside = 0 then
    { order with oprice := (0xFFFFFFFFFFFFFFFF : UInt64) }
  else
    { order with oprice := 0 }

def marketL (book : List OrderL) (order : OrderL) : OpResultL :=
  if validOrderL book order then
    let matched := runMatchL book (unlimitedTakerL order)
    { status := 0, book := matched.book, trades := matched.trades }
  else
    { status := 1, book := book, trades := [] }

@[simp]
theorem unlimitedTakerL_bid (order : OrderL) (hSide : order.oside = 0) :
    unlimitedTakerL order =
      { order with oprice := (0xFFFFFFFFFFFFFFFF : UInt64) } := by
  simp [unlimitedTakerL, hSide]

@[simp]
theorem unlimitedTakerL_ask (order : OrderL) (hSide : order.oside ≠ 0) :
    unlimitedTakerL order = { order with oprice := 0 } := by
  simp [unlimitedTakerL, hSide]

@[simp]
theorem unlimitedTakerL_oqty (order : OrderL) :
    (unlimitedTakerL order).oqty = order.oqty := by
  by_cases hSide : order.oside = 0 <;>
    simp [unlimitedTakerL, hSide]

@[simp]
theorem marketL_invalid (book : List OrderL) (order : OrderL)
    (hValid : ¬validOrderL book order) :
    marketL book order = { status := 1, book := book, trades := [] } := by
  simp [marketL, hValid]

theorem marketL_valid (book : List OrderL) (order : OrderL)
    (hValid : validOrderL book order) :
    marketL book order =
      { status := 0
        book := (runMatchL book (unlimitedTakerL order)).book
        trades := (runMatchL book (unlimitedTakerL order)).trades } := by
  simp [marketL, hValid]

theorem runMarketMatch_quantity_conservation (book : List OrderL)
    (order : OrderL) :
    orderQtyTotal (runMatchL book (unlimitedTakerL order)).book +
        tradeQtyTotal (runMatchL book (unlimitedTakerL order)).trades =
      orderQtyTotal book ∧
    (runMatchL book (unlimitedTakerL order)).remaining.toNat +
        tradeQtyTotal (runMatchL book (unlimitedTakerL order)).trades =
      order.oqty.toNat := by
  simpa only [unlimitedTakerL_oqty] using
    runMatchL_quantity_conservation book (unlimitedTakerL order)

end Project.ClobMarket.Model
