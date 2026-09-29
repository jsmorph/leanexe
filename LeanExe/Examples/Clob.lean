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

end LeanExe.Examples.Clob
