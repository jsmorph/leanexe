import Demos.OrderBook.Program
import Demos.OrderBook.Spec

/-! The specification's book that a book of [the program](Program.lean) represents.  The bids are
the chains of the levels of prices 1,023 down to 1 concatenated, and the asks the chains of the
levels of prices 1 to 1,023 concatenated.  An order's id, account, and quantity come from its slot,
and its side and price from its level. -/

namespace Demos.OrderBook.Abstract

open Program (Book)

/-- The orders of the chain from slot `s`, read for at most `fuel` slots, with side `side` and
price `price`. -/
def chain (b : Book) (side : Spec.Side) (price : Nat) : Nat → UInt64 → List Spec.Order
  | 0, _ => []
  | fuel + 1, s =>
    if s = 0 then []
    else ⟨b.oid[s.toNat]!, b.acct[s.toNat]!, side, price, b.qty[s.toNat]!.toNat⟩ ::
      chain b side price fuel b.nxt[s.toNat]!

/-- The index of the level of side `side` at `price`. -/
def levelIndex (side : Spec.Side) (price : Nat) : Nat :=
  match side with
  | .buy => price
  | .sell => 1024 + price

/-- The orders of side `side` at `price`: the chain of its level, read for at most 4,097 slots. -/
def levelOrders (b : Book) (side : Spec.Side) (price : Nat) : List Spec.Order :=
  chain b side price 4097 b.head[levelIndex side price]!

/-- The specification's book of `b`. -/
def toSpec (b : Book) : Spec.Book where
  bids := (List.range 1023).flatMap fun i => levelOrders b .buy (1023 - i)
  asks := (List.range 1023).flatMap fun i => levelOrders b .sell (i + 1)
  nextId := b.nextId

end Demos.OrderBook.Abstract
