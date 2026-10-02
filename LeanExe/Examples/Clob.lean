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

/-- The book side with level `k` holding `size`, as its prices and its sizes. -/
def setLevel (prices sizes : Array UInt64) (k size : UInt64) : Array UInt64 × Array UInt64 :=
  (prices, sizes.set! k.toNat size)

/-- The position of `price` among the bids, sorted by descending price: the number
of levels with a higher price. -/
def findLevel (prices : Array UInt64) (price : UInt64) : UInt64 :=
  LeanExe.loop prices.size.toUInt64 0 fun i k =>
    if prices[i.toNat]! > price then k + 1 else k

/-- The book side without level `k`, as its prices and its sizes. -/
def removeLevel (prices sizes : Array UInt64) (k : UInt64) : Array UInt64 × Array UInt64 :=
  (prices.eraseIdxIfInBounds k.toNat, sizes.eraseIdxIfInBounds k.toNat)

/-- The bids after adding `size` at `price`: to the level with that price if it
exists, and otherwise to a new level at its sorted position. -/
def addBid (prices sizes : Array UInt64) (price size : UInt64) : Array UInt64 × Array UInt64 :=
  let k := findLevel prices price
  if k < prices.size.toUInt64 ∧ prices[k.toNat]! = price then
    setLevel prices sizes k (sizes[k.toNat]! + size)
  else insertLevel prices sizes k price size

/-- The bids after cancelling `size` at `price`: the level at that price loses
`size`, or is removed if it holds no more than `size`.  Without a level at that
price, the bids are unchanged. -/
def cancelBid (prices sizes : Array UInt64) (price size : UInt64) : Array UInt64 × Array UInt64 :=
  let k := findLevel prices price
  if k < prices.size.toUInt64 ∧ prices[k.toNat]! = price then
    if sizes[k.toNat]! ≤ size then removeLevel prices sizes k
    else setLevel prices sizes k (sizes[k.toNat]! - size)
  else (prices, sizes)

/-- The bids after command `kind`: kind 0 adds `size` at `price`, kind 1 cancels
`size` at `price`, and any other kind leaves the bids unchanged. -/
def applyCommand (prices sizes : Array UInt64) (kind price size : UInt64) :
    Array UInt64 × Array UInt64 :=
  if kind = 0 then addBid prices sizes price size
  else if kind = 1 then cancelBid prices sizes price size
  else (prices, sizes)

/-- The bids after the commands in `commands`, three words each: the kind, the price, and
the size, as `applyCommand` takes them. -/
def runCommands (prices sizes commands : Array UInt64) : Array UInt64 × Array UInt64 :=
  LeanExe.loop (commands.size.toUInt64 / 3) (prices, sizes) fun i (p, s) =>
    applyCommand p s commands[(3 * i).toNat]! commands[(3 * i + 1).toNat]!
      commands[(3 * i + 2).toNat]!

/-- `applyCommand`, with the best bid afterward, its price and size, appended to `out`.  An
empty book gives zeros. -/
def stepCommand (prices sizes out : Array UInt64) (kind price size : UInt64) :
    Array UInt64 × Array UInt64 × Array UInt64 :=
  let (p, s) := applyCommand prices sizes kind price size
  let bestPrice := p[(0 : UInt64).toNat]!
  let bestSize := s[(0 : UInt64).toNat]!
  let best := #[bestPrice, bestSize]
  (p, s, out ++ best)

/-- `runCommands`, with the best bid after each command appended to `out`. -/
def runOut (prices sizes out commands : Array UInt64) :
    Array UInt64 × Array UInt64 × Array UInt64 :=
  LeanExe.loop (commands.size.toUInt64 / 3) (prices, sizes, out) fun i (p, s, o) =>
    stepCommand p s o commands[(3 * i).toNat]! commands[(3 * i + 1).toNat]!
      commands[(3 * i + 2).toNat]!

/-- The total size of the levels priced at or above `limit`. -/
def depth (prices sizes : Array UInt64) (limit : UInt64) : UInt64 :=
  LeanExe.loop prices.size.toUInt64 0 fun i total =>
    if prices[i.toNat]! ≥ limit then total + sizes[i.toNat]! else total

end LeanExe.Examples.Clob
