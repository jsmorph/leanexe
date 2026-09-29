import LeanExe.Loop

namespace LeanExe.Examples.Clob

/-- Buys up to `qty` from the ask levels in array order, where level `i` offers
`askSizes[i]` at price `askPrices[i]`.  Returns the quantity filled and its
cost. -/
def marketBuy (askPrices askSizes : Array UInt64) (qty : UInt64) : Array UInt64 :=
  let (remaining, cost) := LeanExe.loop askPrices.size.toUInt64 (qty, (0 : UInt64))
    fun i (remaining, cost) =>
      let take := min remaining askSizes[i.toNat]!
      (remaining - take, cost + take * askPrices[i.toNat]!)
  #[qty - remaining, cost]

/-- The level sizes after `amount` is taken from level `k`. -/
def fillLevel (sizes : Array UInt64) (k amount : UInt64) : Array UInt64 :=
  sizes.set! k.toNat (sizes[k.toNat]! - amount)

/-- The book side with a new level of `size` at `price` inserted at position `k`,
as its prices and its sizes. -/
def insertLevel (prices sizes : Array UInt64) (k price size : UInt64) :
    Array UInt64 × Array UInt64 :=
  (prices.insertIdx! k.toNat price, sizes.insertIdx! k.toNat size)

/-- The bids after adding `size` at `price`: to the level with that price if it
exists, and otherwise to a new level at its sorted position.  The bids are sorted
by descending price, so the position is the number of levels with a higher
price. -/
def addBid (prices sizes : Array UInt64) (price size : UInt64) : Array UInt64 × Array UInt64 :=
  let k := LeanExe.loop prices.size.toUInt64 0 fun i k =>
    if prices[i.toNat]! > price then k + 1 else k
  if k < prices.size.toUInt64 ∧ prices[k.toNat]! = price then
    (prices, sizes.set! k.toNat (sizes[k.toNat]! + size))
  else
    (prices.insertIdx! k.toNat price, sizes.insertIdx! k.toNat size)

end LeanExe.Examples.Clob
