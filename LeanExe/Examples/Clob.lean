namespace LeanExe.Examples.Clob

structure Order where
  id : UInt64
  trader : UInt64
  side : UInt64
  price : UInt64
  qty : UInt64
  deriving Inhabited

structure Trade where
  takerId : UInt64
  makerId : UInt64
  price : UInt64
  qty : UInt64
  deriving Inhabited

structure Level where
  price : UInt64
  qty : UInt64
  deriving Inhabited

structure OpResult where
  status : UInt64
  book : Array Order
  trades : Array Trade

structure CancelResult where
  status : UInt64
  book : Array Order

structure Quote where
  hasBid : UInt64
  bidPrice : UInt64
  bidQty : UInt64
  hasAsk : UInt64
  askPrice : UInt64
  askQty : UInt64

structure Depth where
  bids : Array Level
  asks : Array Level

def errOk : UInt64 := 0
def errInvalid : UInt64 := 1
def errWouldCross : UInt64 := 2
def errNotFound : UInt64 := 3

def validSide (s : UInt64) : Bool :=
  s == 0 || s == 1

def oppositeSide (s : UInt64) : UInt64 :=
  if s == 0 then 1 else 0

def hasId (b : Array Order) (id : UInt64) : Bool :=
  b.any (fun o => o.id == id)

def validOrder (b : Array Order) (o : Order) : Bool :=
  o.id != 0 && o.trader != 0 && validSide o.side && o.qty != 0 && !hasId b o.id

def crosses (taker maker : Order) : Bool :=
  if taker.side == 0 then maker.price <= taker.price else taker.price <= maker.price

def eligible (taker maker : Order) : Bool :=
  maker.side == oppositeSide taker.side && maker.trader != taker.trader && crosses taker maker

def betterPrice (taker candidate incumbent : Order) : Bool :=
  if taker.side == 0 then candidate.price < incumbent.price else incumbent.price < candidate.price

def findBestFuel : Nat -> Array Order -> Order -> Nat -> Option Nat -> Option Nat
  | 0, _, _, _, best => best
  | fuel + 1, b, taker, i, best =>
    if i < b.size then
      let o := b[i]!
      let best' :=
        match best with
        | none => if eligible taker o then some i else none
        | some j => if eligible taker o && betterPrice taker o b[j]! then some i else some j
      findBestFuel fuel b taker (i + 1) best'
    else
      best

def findBest (b : Array Order) (taker : Order) : Option Nat :=
  findBestFuel (b.size + 1) b taker 0 none

structure MatchState where
  book : Array Order
  trades : Array Trade
  remaining : UInt64

def matchFuel : Nat -> Order -> MatchState -> MatchState
  | 0, _, s => s
  | fuel + 1, taker, s =>
    if s.remaining == 0 then
      s
    else
      match findBest s.book taker with
      | none => s
      | some i =>
        let maker := s.book[i]!
        if maker.qty <= s.remaining then
          let s' : MatchState :=
            { book := s.book.eraseIdx! i
              trades := s.trades.push
                { takerId := taker.id, makerId := maker.id, price := maker.price, qty := maker.qty }
              remaining := s.remaining - maker.qty }
          matchFuel fuel taker s'
        else
          { book := s.book.set! i { maker with qty := maker.qty - s.remaining }
            trades := s.trades.push
              { takerId := taker.id, makerId := maker.id, price := maker.price, qty := s.remaining }
            remaining := 0 }

def runMatch (b : Array Order) (taker : Order) : MatchState :=
  matchFuel (b.size + 1) taker { book := b, trades := #[], remaining := taker.qty }

def limit (b : Array Order) (o : Order) : OpResult :=
  if validOrder b o then
    let s := runMatch b o
    if s.remaining == 0 then
      { status := errOk, book := s.book, trades := s.trades }
    else
      { status := errOk, book := s.book.push { o with qty := s.remaining }, trades := s.trades }
  else
    { status := errInvalid, book := b, trades := #[] }

def market (b : Array Order) (o : Order) : OpResult :=
  if validOrder b o then
    let taker := if o.side == 0 then { o with price := 0xFFFFFFFFFFFFFFFF } else { o with price := 0 }
    let s := runMatch b taker
    { status := errOk, book := s.book, trades := s.trades }
  else
    { status := errInvalid, book := b, trades := #[] }

def postOnly (b : Array Order) (o : Order) : OpResult :=
  if validOrder b o then
    match findBest b o with
    | some _ => { status := errWouldCross, book := b, trades := #[] }
    | none => { status := errOk, book := b.push o, trades := #[] }
  else
    { status := errInvalid, book := b, trades := #[] }

def cancel (b : Array Order) (id : UInt64) : CancelResult :=
  match b.findIdx? (fun o => o.id == id) with
  | some i => { status := errOk, book := b.eraseIdx! i }
  | none => { status := errNotFound, book := b }

def quoteStep (q : Quote) (o : Order) : Quote :=
  if o.side == 0 then
    if q.hasBid == 0 then
      { q with hasBid := 1, bidPrice := o.price, bidQty := o.qty }
    else if q.bidPrice < o.price then
      { q with bidPrice := o.price, bidQty := o.qty }
    else if o.price == q.bidPrice then
      { q with bidQty := q.bidQty + o.qty }
    else
      q
  else
    if q.hasAsk == 0 then
      { q with hasAsk := 1, askPrice := o.price, askQty := o.qty }
    else if o.price < q.askPrice then
      { q with askPrice := o.price, askQty := o.qty }
    else if o.price == q.askPrice then
      { q with askQty := q.askQty + o.qty }
    else
      q

def quote (b : Array Order) : Quote :=
  b.foldl (fun q o => quoteStep q o)
    { hasBid := 0, bidPrice := 0, bidQty := 0, hasAsk := 0, askPrice := 0, askQty := 0 }

def addLevel (ls : Array Level) (price qty : UInt64) : Array Level :=
  match ls.findIdx? (fun l => l.price == price) with
  | some i => ls.set! i { price := price, qty := ls[i]!.qty + qty }
  | none => ls.push { price := price, qty := qty }

def depthSide (b : Array Order) (side : UInt64) : Array Level :=
  b.foldl (fun ls o => if o.side == side then addLevel ls o.price o.qty else ls) #[]

def depth (b : Array Order) : Depth :=
  { bids := depthSide b 0, asks := depthSide b 1 }

def checksumBook (b : Array Order) : UInt64 :=
  b.foldl
    (fun acc o => ((((acc * 31 + o.id) * 31 + o.trader) * 31 + o.side) * 31 + o.price) * 31 + o.qty)
    7

def checksumTrades (ts : Array Trade) : UInt64 :=
  ts.foldl
    (fun acc t => (((acc * 31 + t.takerId) * 31 + t.makerId) * 31 + t.price) * 31 + t.qty)
    11

def checksumLevels (ls : Array Level) : UInt64 :=
  ls.foldl (fun acc l => (acc * 31 + l.price) * 31 + l.qty) 13

def scenario (seed : UInt64) : UInt64 :=
  let r1 := postOnly #[] { id := 1, trader := 10, side := 0, price := 100 + seed % 5, qty := 5 }
  let r2 := postOnly r1.book { id := 2, trader := 11, side := 0, price := 101, qty := 3 }
  let r3 := postOnly r2.book { id := 3, trader := 12, side := 1, price := 105, qty := 4 }
  let r4 := limit r3.book { id := 4, trader := 13, side := 1, price := 99, qty := 6 + seed % 3 }
  let r5 := market r4.book { id := 5, trader := 14, side := 0, price := 0, qty := 2 }
  let r6 := cancel r5.book 2
  let q := quote r6.book
  let d := depth r6.book
  let statuses :=
    ((((r1.status * 5 + r2.status) * 5 + r3.status) * 5 + r4.status) * 5 + r5.status) * 5 + r6.status
  let quoteSum :=
    ((((q.hasBid * 31 + q.bidPrice) * 31 + q.bidQty) * 31 + q.hasAsk) * 31 + q.askPrice) * 31 + q.askQty
  ((((checksumBook r6.book * 131 + checksumTrades r4.trades) * 131 + checksumTrades r5.trades) * 131
      + quoteSum) * 131 + checksumLevels d.bids) * 131 + checksumLevels d.asks * 131 + statuses

end LeanExe.Examples.Clob
