import Demos.OrderBook.Samples

/-! Prints each sample's records, the events that `Spec.step` gives for each shown record, and the
book before and after the shown records.  Run with `lake env lean --run`. -/

open Demos.OrderBook.Spec Demos.OrderBook.Samples

def words (ws : Array UInt64) : String := toString ws.toList

def sideName : Side → String
  | .buy => "buy"
  | .sell => "sell"

def rejectName : RejectReason → String
  | .malformed => "record not seven words"
  | .unknownKind => "unknown kind"
  | .badSide => "bad side"
  | .badTif => "bad time in force"
  | .badPrice => "price out of range"
  | .badQty => "quantity out of range"
  | .unknownOrder => "no resting order with the id"
  | .otherAccount => "order of another account"
  | .wouldCross => "post-only order would cross"
  | .notReduction => "new quantity not below the remaining quantity"

def cancelName : CancelReason → String
  | .requested => "requested"
  | .ioc => "IOC remainder"
  | .selfTrade => "self-trade prevention"
  | .bookFull => "book full"

def describe : Event → String
  | .accepted id tag => s!"accepted id {id} tag {tag}"
  | .rejected kind ref reason => s!"rejected kind {kind} ref {ref}: {rejectName reason}"
  | .trade maker taker price qty account remaining =>
    s!"trade maker {maker} taker {taker} price {price} qty {qty} maker account {account} maker remaining {remaining}"
  | .cancelled id remaining reason => s!"cancelled id {id} remaining {remaining}: {cancelName reason}"
  | .reduced id qty => s!"reduced id {id} to {qty}"

def showOrder (o : Order) : String :=
  s!"id {o.id} account {o.account} {sideName o.side} price {o.price} qty {o.qty}"

def showSide (name : String) (os : List Order) : IO Unit := do
  if os.length ≤ 12 then
    for o in os do IO.println s!"    {name} {showOrder o}"
  else
    for o in os.take 5 do IO.println s!"    {name} {showOrder o}"
    IO.println s!"    {name}s at positions 6 to {os.length - 3} not shown"
    for o in os.drop (os.length - 3) do IO.println s!"    {name} {showOrder o}"

def showBook (b : Book) : IO Unit := do
  let (bp, bq, ap, aq) := top b
  IO.println s!"  book: bid count {b.bids.length}, ask count {b.asks.length}, next id {b.nextId}, top bid {bp} qty {bq}, top ask {ap} qty {aq}"
  showSide "bid" b.bids
  showSide "ask" b.asks

def showEvents (es : List Event) : IO Unit := do
  for e in es do IO.println s!"    {describe e}    {words (encode e)}"

def main : IO Unit := do
  for s in samples do
    IO.println s!"== {s.name}"
    IO.println s!"  setup record count: {(records s.setup).length}"
    let mut b := (run empty s.setup).1
    showBook b
    for r in records s.shown do
      IO.println s!"> {words r}"
      let (b', es) := step b r
      showEvents es
      b := b'
    showBook b
  IO.println "== single records, each from the empty book"
  for r in single do
    IO.println s!"> {words r}"
    showEvents (step empty r).2
