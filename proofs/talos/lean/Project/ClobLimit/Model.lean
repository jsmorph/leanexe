import Project.ClobMatchFuel.Properties
import Project.ClobPostOnly.Model

/-!
# Source model for `limit`

The model composes the proved list matcher with the source validity predicate.
It preserves the invalid, fully filled, and residual-order branches of the
export.  Allocation and ownership remain properties of the artifact theorem.
-/

namespace Project.ClobLimit.Model

open Project.Clob Project.ClobPostOnly.Model Project.ClobMatchFuel.Model
  Project.ClobMatchFuel.Properties

structure OpResultL where
  status : UInt64
  book : List OrderL
  trades : List TradeL
  deriving Inhabited

def runMatchL (book : List OrderL) (taker : OrderL) : MatchStateL :=
  matchFuelL (book.length + 1) taker
    { book := book, trades := [], remaining := taker.oqty }

def limitL (book : List OrderL) (order : OrderL) : OpResultL :=
  if validOrderL book order then
    let matched := runMatchL book order
    if matched.remaining = 0 then
      { status := 0, book := matched.book, trades := matched.trades }
    else
      { status := 0
        book := matched.book ++ [{ order with oqty := matched.remaining }]
        trades := matched.trades }
  else
    { status := 1, book := book, trades := [] }

@[simp]
theorem limitL_invalid (book : List OrderL) (order : OrderL)
    (hValid : ¬validOrderL book order) :
    limitL book order = { status := 1, book := book, trades := [] } := by
  simp [limitL, hValid]

theorem limitL_filled (book : List OrderL) (order : OrderL)
    (hValid : validOrderL book order)
    (hRemaining : (runMatchL book order).remaining = 0) :
    limitL book order =
      { status := 0
        book := (runMatchL book order).book
        trades := (runMatchL book order).trades } := by
  simp [limitL, hValid, hRemaining]

theorem limitL_residual (book : List OrderL) (order : OrderL)
    (hValid : validOrderL book order)
    (hRemaining : (runMatchL book order).remaining ≠ 0) :
    limitL book order =
      { status := 0
        book := (runMatchL book order).book ++
          [{ order with oqty := (runMatchL book order).remaining }]
        trades := (runMatchL book order).trades } := by
  simp [limitL, hValid, hRemaining]

theorem runMatchL_quantity_conservation (book : List OrderL)
    (taker : OrderL) :
    orderQtyTotal (runMatchL book taker).book +
        tradeQtyTotal (runMatchL book taker).trades = orderQtyTotal book ∧
    (runMatchL book taker).remaining.toNat +
        tradeQtyTotal (runMatchL book taker).trades = taker.oqty.toNat := by
  simpa [runMatchL, tradeQtyTotal] using
    matchFuelL_quantity_conservation (book.length + 1) taker
      { book := book, trades := [], remaining := taker.oqty }

end Project.ClobLimit.Model
