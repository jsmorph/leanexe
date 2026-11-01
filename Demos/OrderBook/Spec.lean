/-! The specification of the order book that [the requirements](requirements.md) describe.  The
book is two lists of resting orders in priority order, and a command is a function of the book and
its seven-word record.  The definitions state the requirements directly and refer to no
implementation. -/

namespace Demos.OrderBook.Spec

/-- Highest price tick.  Prices run from 1 to `maxPrice`. -/
def maxPrice : Nat := 1023

/-- Largest quantity.  Quantities run from 1 to `maxQty`. -/
def maxQty : Nat := 2 ^ 32 - 1

/-- Largest number of resting orders. -/
def capacity : Nat := 4096

inductive Side where
  | buy
  | sell
  deriving DecidableEq, Repr

inductive Tif where
  | gtc
  | ioc
  | postOnly
  deriving DecidableEq, Repr

/-- A resting order: its id, account, side, price, and remaining quantity. -/
structure Order where
  id : UInt64
  account : UInt64
  side : Side
  price : Nat
  qty : Nat
  deriving DecidableEq, Repr

/-- The bids, best first, the asks, best first, and the id that the next accepted order receives.
Within a side, an order at a better price comes first, and among orders at one price the order
accepted earlier comes first. -/
structure Book where
  bids : List Order
  asks : List Order
  nextId : UInt64
  deriving DecidableEq, Repr

/-- The book before any command: no orders, and the first accepted order receives id 1. -/
def empty : Book := { bids := [], asks := [], nextId := 1 }

inductive CancelReason where
  | requested
  | ioc
  | selfTrade
  | bookFull
  deriving DecidableEq, Repr

inductive RejectReason where
  | malformed
  | unknownKind
  | badSide
  | badTif
  | badPrice
  | badQty
  | unknownOrder
  | otherAccount
  | wouldCross
  | notReduction
  deriving DecidableEq, Repr

inductive Event where
  | accepted (id tag : UInt64)
  | rejected (kind ref : UInt64) (reason : RejectReason)
  | trade (maker taker : UInt64) (price qty : Nat) (makerAccount : UInt64) (makerRemaining : Nat)
  | cancelled (id : UInt64) (remaining : Nat) (reason : CancelReason)
  | reduced (id : UInt64) (qty : Nat)
  deriving DecidableEq, Repr

/-- Whether an incoming order on `side` with limit price `limit` accepts a resting order at
`price`: a buy accepts an ask at most its limit, and a sell accepts a bid at least its limit. -/
def acceptable (side : Side) (limit price : Nat) : Bool :=
  match side with
  | .buy => price ≤ limit
  | .sell => limit ≤ price

/-- Whether a resting price `p` on `side` is at least as good as a price `q` on the same side: at
least `q` for bids and at most `q` for asks. -/
def asGood (side : Side) (p q : Nat) : Bool :=
  match side with
  | .buy => q ≤ p
  | .sell => p ≤ q

/-- `o` placed into a side in priority order, behind every order whose price is at least as good as
its own, which puts it behind every order at its price. -/
def place (o : Order) : List Order → List Order
  | [] => [o]
  | r :: rs => if asGood o.side r.price o.price then r :: place o rs else o :: r :: rs

/-- The outcome of matching: the opposite side after the trades, the trade events in order, the
incoming order's remaining quantity, and whether matching stopped at a resting order of the
incoming order's account. -/
structure Fill where
  others : List Order
  trades : List Event
  remaining : Nat
  selfTrade : Bool

/-- Matching of an incoming order with id `taker`, account `account`, side `side`, and limit price
`limit`, with `qty` remaining, against the opposite side, first order first.  Matching continues
while the incoming order has a remaining quantity and the first opposite order has an acceptable
price.  It stops, leaving that order unchanged, when the order has the incoming order's account.
Otherwise the two trade the smaller remaining quantity at the resting order's price, and a resting
order with nothing left leaves the side. -/
def fill (taker account : UInt64) (side : Side) (limit : Nat) : Nat → List Order → Fill
  | qty, [] => ⟨[], [], qty, false⟩
  | qty, m :: ms =>
    if qty == 0 || !acceptable side limit m.price then ⟨m :: ms, [], qty, false⟩
    else if m.account = account then ⟨m :: ms, [], qty, true⟩
    else
      let q := min qty m.qty
      let t := Event.trade m.id taker m.price q m.account (m.qty - q)
      if q = m.qty then
        let r := fill taker account side limit (qty - q) ms
        ⟨r.others, t :: r.trades, r.remaining, r.selfTrade⟩
      else
        ⟨{ m with qty := m.qty - q } :: ms, [t], qty - q, false⟩

/-- The side opposite to an incoming order on `side`. -/
def opposite (b : Book) : Side → List Order
  | .buy => b.asks
  | .sell => b.bids

def setOpposite (b : Book) (side : Side) (os : List Order) : Book :=
  match side with
  | .buy => { b with asks := os }
  | .sell => { b with bids := os }

/-- `o` resting on its side. -/
def rest (b : Book) (o : Order) : Book :=
  match o.side with
  | .buy => { b with bids := place o b.bids }
  | .sell => { b with asks := place o b.asks }

/-- The number of resting orders. -/
def size (b : Book) : Nat := b.bids.length + b.asks.length

/-- An accepted incoming order with limit price `limit`: it receives the id `b.nextId`, its
`accepted` event comes first, it matches, and then its remainder is cancelled for self-trade
prevention, cancelled for IOC, resting at `limit`, or cancelled because the book is full, in that
order of precedence.  The capacity test counts the resting orders after matching.  A post-only
order reaches `submit` only when it crosses nothing, so it makes no trade and rests as a GTC order
would. -/
def submit (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64) (tif : Tif) :
    Book × List Event :=
  let id := b.nextId
  let b := { b with nextId := id + 1 }
  let f := fill id account side limit qty (opposite b side)
  let b := setOpposite b side f.others
  let events := Event.accepted id tag :: f.trades
  if f.remaining = 0 then (b, events)
  else if f.selfTrade then (b, events ++ [.cancelled id f.remaining .selfTrade])
  else if tif = .ioc then (b, events ++ [.cancelled id f.remaining .ioc])
  else if size b < capacity then (rest b ⟨id, account, side, limit, f.remaining⟩, events)
  else (b, events ++ [.cancelled id f.remaining .bookFull])

/-- The resting order with id `id`, if any.  In a stream of fewer than 2^64 - 1 accepted orders
the ids of resting orders are distinct, which `find`, `remove`, and `setQty` rely on. -/
def find (b : Book) (id : UInt64) : Option Order :=
  (b.bids ++ b.asks).find? (·.id == id)

/-- The book without the resting order with id `id`. -/
def remove (b : Book) (id : UInt64) : Book :=
  { b with bids := b.bids.filter (·.id != id), asks := b.asks.filter (·.id != id) }

/-- The book with the remaining quantity of the order with id `id` set to `qty`, in place, so the
order keeps its priority. -/
def setQty (b : Book) (id : UInt64) (qty : Nat) : Book :=
  let f (o : Order) : Order := if o.id = id then { o with qty := qty } else o
  { b with bids := b.bids.map f, asks := b.asks.map f }

def sideOf (w : UInt64) : Option Side :=
  if w = 0 then some .buy else if w = 1 then some .sell else none

def tifOf (w : UInt64) : Option Tif :=
  if w = 0 then some .gtc else if w = 1 then some .ioc else if w = 2 then some .postOnly else none

/-- Whether a word lies from `lo` to `hi`. -/
def inRange (lo hi : Nat) (w : UInt64) : Bool := lo ≤ w.toNat && w.toNat ≤ hi

def reject (b : Book) (kind ref : UInt64) (reason : RejectReason) : Book × List Event :=
  (b, [.rejected kind ref reason])

/-- Whether a post-only order on `side` at `price` would cross: the first opposite order has an
acceptable price. -/
def crosses (b : Book) (side : Side) (price : Nat) : Bool :=
  match opposite b side with
  | m :: _ => acceptable side price m.price
  | [] => false

/-- One command record.  The checks run in the order of the requirements' table, and the first
that fails rejects the command and leaves the book unchanged. -/
def step (b : Book) (r : Array UInt64) : Book × List Event :=
  if r.size ≠ 7 then reject b 0 0 .malformed
  else
    let kind := r[0]!
    if kind = 1 then
      -- limit: side, price, quantity, account, client tag, time in force
      let tag := r[5]!
      match sideOf r[1]!, tifOf r[6]! with
      | none, _ => reject b kind tag .badSide
      | some _, none => reject b kind tag .badTif
      | some side, some tif =>
        if !inRange 1 maxPrice r[2]! then reject b kind tag .badPrice
        else if !inRange 1 maxQty r[3]! then reject b kind tag .badQty
        else if tif == .postOnly && crosses b side r[2]!.toNat then reject b kind tag .wouldCross
        else submit b side r[2]!.toNat r[3]!.toNat r[4]! tag tif
    else if kind = 2 then
      -- market: side, quantity, account, client tag.  Every resting price lies from 1 to
      -- `maxPrice`, so a buy limit of `maxPrice` and a sell limit of 1 accept every price.
      let tag := r[4]!
      match sideOf r[1]! with
      | none => reject b kind tag .badSide
      | some side =>
        if !inRange 1 maxQty r[2]! then reject b kind tag .badQty
        else
          let limit := match side with
            | .buy => maxPrice
            | .sell => 1
          submit b side limit r[2]!.toNat r[3]! tag .ioc
    else if kind = 3 then
      -- cancel: order id, account
      let id := r[1]!
      match find b id with
      | none => reject b kind id .unknownOrder
      | some o =>
        if o.account ≠ r[2]! then reject b kind id .otherAccount
        else (remove b id, [.cancelled id o.qty .requested])
    else if kind = 4 then
      -- reduce: order id, account, new quantity
      let id := r[1]!
      match find b id with
      | none => reject b kind id .unknownOrder
      | some o =>
        if o.account ≠ r[2]! then reject b kind id .otherAccount
        -- A new quantity outside 1 to `maxQty` has the reason of any quantity out of range.
        else if !inRange 1 maxQty r[3]! then reject b kind id .badQty
        else if o.qty ≤ r[3]!.toNat then reject b kind id .notReduction
        else (setQty b id r[3]!.toNat, [.reduced id r[3]!.toNat])
    else reject b kind 0 .unknownKind

/-- The words read as consecutive seven-word records, the last of which may be shorter.  Words whose
number is a multiple of seven give no shorter record, and no words give no record. -/
def records (ws : List UInt64) : List (Array UInt64) := go ws #[]
where
  go : List UInt64 → Array UInt64 → List (Array UInt64)
    | [], acc => if acc.isEmpty then [] else [acc]
    | w :: ws, acc => if acc.size = 6 then acc.push w :: go ws #[] else go ws (acc.push w)

/-- A stream of command words: the book after each record in turn, and the events of all the
records in order. -/
def run (b : Book) (ws : List UInt64) : Book × List Event :=
  (records ws).foldl (fun (b, es) r => let (b', es') := step b r; (b', es ++ es')) (b, [])

def rejectCode : RejectReason → UInt64
  | .malformed => 1
  | .unknownKind => 2
  | .badSide => 3
  | .badTif => 4
  | .badPrice => 5
  | .badQty => 6
  | .unknownOrder => 7
  | .otherAccount => 8
  | .wouldCross => 9
  | .notReduction => 10

def cancelCode : CancelReason → UInt64
  | .requested => 1
  | .ioc => 2
  | .selfTrade => 3
  | .bookFull => 4

/-- An event's seven-word record. -/
def encode : Event → Array UInt64
  | .accepted id tag => #[1, id, tag, 0, 0, 0, 0]
  | .rejected kind ref reason => #[2, kind, ref, rejectCode reason, 0, 0, 0]
  | .trade maker taker price qty account remaining =>
    #[3, maker, taker, price.toUInt64, qty.toUInt64, account, remaining.toUInt64]
  | .cancelled id remaining reason => #[4, id, remaining.toUInt64, cancelCode reason, 0, 0, 0]
  | .reduced id qty => #[5, id, qty.toUInt64, 0, 0, 0, 0]

/-- The words of a list of events. -/
def encodeAll (es : List Event) : Array UInt64 :=
  es.foldl (fun ws e => ws ++ encode e) #[]

/-- The best price of a side, or 0 for an empty side. -/
def bestPrice : List Order → Nat
  | [] => 0
  | o :: _ => o.price

/-- The total remaining quantity of a side's orders at its best price, or 0 for an empty side. -/
def bestQty (os : List Order) : Nat :=
  ((os.filter (·.price == bestPrice os)).map (·.qty)).sum

/-- The top of the book, a query separate from the command stream: the best bid price and the
quantity at it, and the best ask price and the quantity at it.  On a valid book each total is at
most `capacity * maxQty`, which is below 2^44. -/
def top (b : Book) : Nat × Nat × Nat × Nat :=
  (bestPrice b.bids, bestQty b.bids, bestPrice b.asks, bestQty b.asks)

/-- Whether `os` is a side in priority order for `side`: each order's price is at least as good as
the price of every later order, and an order at the price of a later one has the smaller id, which
in a stream of fewer than 2^64 - 1 accepted orders means that it was accepted earlier. -/
def Ordered (side : Side) : List Order → Prop
  | [] => True
  | o :: os =>
    (∀ r ∈ os, asGood side o.price r.price = true ∧ (o.price = r.price → o.id < r.id)) ∧
      Ordered side os

/-- The books that the requirements describe: each side in priority order and holding orders of its
own side, prices from 1 to `maxPrice`, quantities from 1 to `maxQty`, ids from 1 to below `nextId`,
distinct ids, at most `capacity` orders, a best bid below the best ask when both sides hold orders,
and a next id of at least 1.  The matching and post-only rules of the requirements imply the
uncrossed book, and their limit of fewer than 2^64 - 1 accepted orders keeps `nextId` from 1 to
2^64 - 1.  A step that accepts an order keeps a book valid only when `nextId` lies below 2^64 - 1
before the step. -/
structure Valid (b : Book) : Prop where
  bidsOrdered : Ordered .buy b.bids
  asksOrdered : Ordered .sell b.asks
  bidSide : ∀ o ∈ b.bids, o.side = .buy
  askSide : ∀ o ∈ b.asks, o.side = .sell
  price : ∀ o ∈ b.bids ++ b.asks, 1 ≤ o.price ∧ o.price ≤ maxPrice
  qty : ∀ o ∈ b.bids ++ b.asks, 1 ≤ o.qty ∧ o.qty ≤ maxQty
  ids : ∀ o ∈ b.bids ++ b.asks, 0 < o.id.toNat ∧ o.id.toNat < b.nextId.toNat
  distinct : ((b.bids ++ b.asks).map (·.id)).Nodup
  bounded : b.bids.length + b.asks.length ≤ capacity
  notCrossed : ∀ bid ∈ b.bids.head?, ∀ ask ∈ b.asks.head?, bid.price < ask.price
  nextPositive : 0 < b.nextId.toNat

end Demos.OrderBook.Spec
