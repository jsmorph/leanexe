import Verified.Reflect.Command
import Examples.Clob.Commands

/-! The twenty-sixth program of the verified compiler: the bid side of a central limit order book,
held as two arrays of words, the prices in descending order and the size at each price.  The
definitions are those of `Examples/Clob/Program.lean` with three changes.  `marketBuy` returns the
filled quantity and its cost as a pair, since the verified compiler has no array literals.  The
conditions of `addBid` and `cancelBid` compare words with `&&` and `==`.  `insertLevel` and
`removeLevel` use `LeanExe.insertAt` and `LeanExe.eraseAt`, which update an owned side in place,
so an insertion past the end leaves a side unchanged where `insertIdx!` panics.  `findLevel` gives
a position at most the size, so `addBid` and `cancelBid` insert and remove only in range.
`runCommands` over two chunks of commands, the first of whole commands, gives the book of one run,
and `runOut` leaves the book of `runCommands`.  Since the compiler's theorem states that the module
computes these definitions, both facts hold for the module's results. -/

namespace Verified.Examples.Clob

/-- Buys up to `qty` from the ask levels in array order, where level `i` offers `askSizes[i]` at
price `askPrices[i]`.  Returns the quantity filled and its cost. -/
def marketBuy (askPrices askSizes : Array UInt64) (qty : UInt64) : UInt64 × UInt64 :=
  let (remaining, cost) := LeanExe.loop askPrices.size.toUInt64 (qty, (0 : UInt64))
    fun i (remaining, cost) =>
      let take := min remaining askSizes[i.toNat]!
      (remaining - take, cost + take * askPrices[i.toNat]!)
  (qty - remaining, cost)

/-- The level sizes after `amount` is taken from level `k`. -/
def fillLevel (sizes : Array UInt64) (k amount : UInt64) : Array UInt64 :=
  sizes.set! k.toNat (sizes[k.toNat]! - amount)

/-- The level sizes after `a` and then `b` are taken from level `k`: the `let` binds the first
call's array, which the second call consumes. -/
def fillTwice (sizes : Array UInt64) (k a b : UInt64) : Array UInt64 :=
  let ys := fillLevel sizes k a
  fillLevel ys k b

/-- The level sizes after `a` is taken from level `k`, and the sizes before: the call consumes a
copy of the sizes, since the result uses them again. -/
def fillKeep (sizes : Array UInt64) (k a : UInt64) : Array UInt64 × Array UInt64 :=
  (fillLevel sizes k a, sizes)

/-- The book side with a new level of `size` at `price` inserted at position `k`, as its prices
and its sizes. -/
def insertLevel (prices sizes : Array UInt64) (k price size : UInt64) :
    Array UInt64 × Array UInt64 :=
  (LeanExe.insertAt prices k price, LeanExe.insertAt sizes k size)

/-- The book side with level `k` holding `size`, as its prices and its sizes. -/
def setLevel (prices sizes : Array UInt64) (k size : UInt64) : Array UInt64 × Array UInt64 :=
  (prices, sizes.set! k.toNat size)

/-- The position of `price` among the bids, sorted by descending price: the number of levels
with a higher price. -/
def findLevel (prices : Array UInt64) (price : UInt64) : UInt64 :=
  LeanExe.loop prices.size.toUInt64 0 fun i k =>
    if prices[i.toNat]! > price then k + 1 else k

/-- The book side without level `k`, as its prices and its sizes. -/
def removeLevel (prices sizes : Array UInt64) (k : UInt64) : Array UInt64 × Array UInt64 :=
  (LeanExe.eraseAt prices k, LeanExe.eraseAt sizes k)

/-- The bids after adding `size` at `price`: to the level with that price if it exists, and
otherwise to a new level at its sorted position. -/
def addBid (prices sizes : Array UInt64) (price size : UInt64) : Array UInt64 × Array UInt64 :=
  let k := findLevel prices price
  if k < prices.size.toUInt64 && prices[k.toNat]! == price then
    setLevel prices sizes k (sizes[k.toNat]! + size)
  else insertLevel prices sizes k price size

/-- The bids after cancelling `size` at `price`: the level at that price loses `size`, or is
removed if it holds no more than `size`.  Without a level at that price, the bids are unchanged. -/
def cancelBid (prices sizes : Array UInt64) (price size : UInt64) : Array UInt64 × Array UInt64 :=
  let k := findLevel prices price
  if k < prices.size.toUInt64 && prices[k.toNat]! == price then
    if sizes[k.toNat]! ≤ size then removeLevel prices sizes k
    else setLevel prices sizes k (sizes[k.toNat]! - size)
  else (prices, sizes)

/-- The bids after command `kind`: kind 0 adds `size` at `price`, kind 1 cancels `size` at
`price`, and any other kind leaves the bids unchanged. -/
def applyCommand (prices sizes : Array UInt64) (kind price size : UInt64) :
    Array UInt64 × Array UInt64 :=
  if kind = 0 then addBid prices sizes price size
  else if kind = 1 then cancelBid prices sizes price size
  else (prices, sizes)

/-- The bids after the commands in `commands`, three words each: the kind, the price, and the
size, as `applyCommand` takes them. -/
def runCommands (prices sizes commands : Array UInt64) : Array UInt64 × Array UInt64 :=
  LeanExe.loop (commands.size.toUInt64 / 3) (prices, sizes) fun i (p, s) =>
    applyCommand p s commands[(3 * i).toNat]! commands[(3 * i + 1).toNat]!
      commands[(3 * i + 2).toNat]!

/-- `applyCommand`, with the best bid afterward, its price and size, pushed onto `out`.  An empty
book gives zeros. -/
def stepCommand (prices sizes out : Array UInt64) (kind price size : UInt64) :
    Array UInt64 × Array UInt64 × Array UInt64 :=
  let (p, s) := applyCommand prices sizes kind price size
  let bestPrice := p[(0 : UInt64).toNat]!
  let bestSize := s[(0 : UInt64).toNat]!
  (p, s, (out.push bestPrice).push bestSize)

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

verified_compile compiled := [marketBuy, fillLevel, fillTwice, fillKeep, insertLevel, setLevel,
  findLevel, removeLevel, addBid, cancelBid, applyCommand, runCommands, stepCommand, runOut, depth]

open _root_.Examples.Clob (foldCommands foldCommands_append foldCommands_map)

theorem runCommands_eq_fold (prices sizes cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    runCommands prices sizes cs =
      foldCommands (fun c book => applyCommand book.1 book.2 c.1 c.2.1 c.2.2) cs
        (prices, sizes) := by
  have hn : (cs.size.toUInt64 / 3).toNat = cs.size / 3 := by
    rw [UInt64.toNat_div, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    rfl
  exact Nat.fold_congr hn _ _

theorem runOut_eq_fold (prices sizes out cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    runOut prices sizes out cs =
      foldCommands (fun c x => stepCommand x.1 x.2.1 x.2.2 c.1 c.2.1 c.2.2) cs
        (prices, sizes, out) := by
  have hn : (cs.size.toUInt64 / 3).toNat = cs.size / 3 := by
    rw [UInt64.toNat_div, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    rfl
  exact Nat.fold_congr hn _ _

/-- Running the commands in two chunks, the first of whole commands, gives the book of one run
over both chunks, so a host may pass the commands in chunks of any size. -/
theorem runCommands_append (prices sizes c1 c2 : Array UInt64) (h3 : c1.size % 3 = 0)
    (hs : (c1 ++ c2).size < 2 ^ 62) :
    runCommands (runCommands prices sizes c1).1 (runCommands prices sizes c1).2 c2 =
      runCommands prices sizes (c1 ++ c2) := by
  have hs' := hs
  rw [Array.size_append] at hs'
  rw [runCommands_eq_fold _ _ c2 (by omega), runCommands_eq_fold _ _ (c1 ++ c2) (by omega),
    runCommands_eq_fold _ _ c1 (by omega), Prod.mk.eta]
  exact foldCommands_append _ _ h3 hs

/-- The book that `runOut` leaves is the book of `runCommands`. -/
theorem runOut_book (prices sizes out cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    ((runOut prices sizes out cs).1, (runOut prices sizes out cs).2.1) =
      runCommands prices sizes cs := by
  rw [runOut_eq_fold _ _ _ _ hs, runCommands_eq_fold _ _ _ hs]
  exact foldCommands_map (fun x : Array UInt64 × Array UInt64 × Array UInt64 => (x.1, x.2.1))
    (fun _ _ => rfl) cs _

end Verified.Examples.Clob
