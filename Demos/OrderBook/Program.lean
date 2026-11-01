import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile

/-! The order book of [the specification](Spec.lean) in the verified compiler's dialect.  Slots 1
to 4,096 of five slot arrays hold the resting orders, and the orders of one side at one price form
a chain of slots in the order of acceptance, whose first and last slots a level array holds.  Level
`side * 1024 + price` holds the orders of side `side`, 0 for buy and 1 for sell, at `price`.
Matching, the post-only test, and the top of the book scan the levels from the edge of the band,
and cancel and reduce scan the slots for the order's id.  Commands and events are the seven-word
records of the requirements, and every value is a word.

A compiled function copies each array of a `Book` parameter that it updates or returns, since a
record parameter is borrowed.  The functions that change the book are therefore `@[inline]`
functions of `Book`, which unfold into their callers, and the program calls `fill`, `submit`, and
`step` through `fillArrays`, `submitArrays`, and `stepArrays`, which take the book's arrays one by
one, so that each caller gives the arrays up and each update changes an array in place.  The
read-only helpers take the arrays they read. -/

namespace Demos.OrderBook.Program

/-- Number of slots.  Slots run from 1 to `slots`, and slot 0 ends a chain. -/
def slots : UInt64 := 4096

/-- Highest price tick.  Prices run from 1 to `maxPrice`. -/
def maxPrice : UInt64 := 1023

/-- Largest quantity, 2^32 - 1. -/
def maxQty : UInt64 := 4294967295

/-- Largest number of resting orders. -/
def capacity : UInt64 := 4096

/-- Fuel of a scan of the slots from slot 1, which suffices because a search for an id stops after
slot 4,096 and a search for a free slot in a book of fewer than 4,096 orders passes at most 4,095
occupied slots. -/
def slotFuel : UInt64 := 4096

/-- Fuel of a walk along a chain, which suffices because a chain holds at most the 4,096 orders of
the book. -/
def chainFuel : UInt64 := 4096

/-- Fuel of a scan of one side's levels from the edge of the band, which suffices because the scan
passes at most the 1,023 prices of the band. -/
def bandFuel : UInt64 := 1023

/-- Fuel of matching, which suffices because matching skips at most 1,023 empty levels, one for each
price of the band, exhausts at most the 4,096 orders of the book, and ends with at most one partial
trade or stop for self-trade prevention. -/
def matchFuel : UInt64 := 5120

/-- The book.  Slot `s` of `oid`, `acct`, `qty`, `lvl`, and `nxt` holds an order's id, account,
remaining quantity, level, and the slot after it in its level's chain, or 0 at the end, and a slot
whose `oid` is 0 is free.  Level `l` of `head` and `tail` holds the first and last slots of its
chain, or 0 for an empty level.  `nextId` is the id of the next accepted order, and `count` the
number of resting orders. -/
structure Book where
  oid : Array UInt64
  acct : Array UInt64
  qty : Array UInt64
  lvl : Array UInt64
  nxt : Array UInt64
  head : Array UInt64
  tail : Array UInt64
  nextId : UInt64
  count : UInt64
  deriving Inhabited

/-- The empty book: every slot free, every level empty, and next id 1. -/
def init (_ : Unit) : Book :=
  ⟨LeanExe.build (slots + 1) fun _ => 0, LeanExe.build (slots + 1) fun _ => 0,
    LeanExe.build (slots + 1) fun _ => 0, LeanExe.build (slots + 1) fun _ => 0,
    LeanExe.build (slots + 1) fun _ => 0, LeanExe.build 2048 fun _ => 0,
    LeanExe.build 2048 fun _ => 0, 1, 0⟩

/-- The level of the orders of side `side` at `price`. -/
@[inline] def level (side price : UInt64) : UInt64 := side * 1024 + price

/-- Whether a word lies from `lo` to `hi`. -/
@[inline] def inRange (lo hi w : UInt64) : Bool := lo ≤ w && w ≤ hi

/-- Whether an incoming order on `side` with limit price `limit` accepts a resting order at
`price`: a buy accepts an ask at most its limit, and a sell accepts a bid at least its limit. -/
@[inline] def acceptable (side limit price : UInt64) : Bool :=
  if side == 0 then decide (price ≤ limit) else decide (limit ≤ price)

/-- `out` followed by the seven words of an event. -/
def emit (out : Array UInt64) (w0 w1 w2 w3 w4 w5 w6 : UInt64) : Array UInt64 :=
  ((((((out.push w0).push w1).push w2).push w3).push w4).push w5).push w6

/-- The slot of the order with id `id` in a book whose order ids are `oid`: the first slot from
slot 1 whose order id is `id`, or 0 when no slot holds `id` or when `id` is 0, the order id of a
free slot. -/
def findSlot (oid : Array UInt64) (id : UInt64) : UInt64 :=
  if id == 0 then 0
  else
    let s := LeanExe.repeatWhile slotFuel 1 (fun s => s ≤ slots && oid[s.toNat]! != id)
      fun s => s + 1
    if s ≤ slots then s else 0

/-- The first free slot from slot 1 in a book whose order ids are `oid`. -/
def freeSlot (oid : Array UInt64) : UInt64 :=
  LeanExe.repeatWhile slotFuel 1 (fun s => oid[s.toNat]! != 0) fun s => s + 1

/-- The slot before slot `s` in the chain of level `lv`, in a book whose chains have the first
slots `head` and the links `nxt`, or 0 when `s` is the first. -/
def predecessor (head nxt : Array UInt64) (lv s : UInt64) : UInt64 :=
  let h := head[lv.toNat]!
  if h == s then 0
  else
    LeanExe.repeatWhile chainFuel h (fun t => t != 0 && nxt[t.toNat]! != s)
      fun t => nxt[t.toNat]!

/-- The best price of side `side` in a book whose chains have the first slots `head`: the highest
bid or the lowest ask, or 0 for an empty side. -/
def bestPrice (head : Array UInt64) (side : UInt64) : UInt64 :=
  if side == 0 then
    LeanExe.repeatWhile bandFuel maxPrice
      (fun p => p != 0 && head[(level 0 p).toNat]! == 0) fun p => p - 1
  else
    let p := LeanExe.repeatWhile bandFuel 1
      (fun p => p ≤ maxPrice && head[(level 1 p).toNat]! == 0) fun p => p + 1
    if p ≤ maxPrice then p else 0

/-- The total remaining quantity of the orders of level `lv`, in a book whose chains have the
first slots `head` and the links `nxt`, and whose quantities are `qty`. -/
def levelQty (head nxt qty : Array UInt64) (lv : UInt64) : UInt64 :=
  (LeanExe.repeatWhile chainFuel (head[lv.toNat]!, (0 : UInt64)) (fun st => st.1 != 0)
    fun st => (nxt[st.1.toNat]!, st.2 + qty[st.1.toNat]!)).2

/-- The top of the book: the best bid price and the total quantity at it, and the best ask price
and the total quantity at it, with 0 for both values of an empty side. -/
def top (b : Book) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let bp := bestPrice b.head 0
  let ap := bestPrice b.head 1
  (bp, (if bp == 0 then 0 else levelQty b.head b.nxt b.qty (level 0 bp)), ap,
    if ap == 0 then 0 else levelQty b.head b.nxt b.qty (level 1 ap))

/-- Whether a post-only order on `side` at `price` would cross, in a book whose chains have the
first slots `head`: the first opposite order has an acceptable price. -/
def crosses (head : Array UInt64) (side price : UInt64) : Bool :=
  let p := bestPrice head (1 - side)
  p != 0 && acceptable side price p

/-- The book without the order in slot `s` of level `lv`, whose predecessor in the chain is slot
`pr`, or 0 when `s` is the first: the chain skips `s`, `s` becomes free, and the count falls by
one. -/
@[inline] def unlink (b : Book) (lv pr s : UInt64) : Book :=
  let nx := b.nxt[s.toNat]!
  let last := b.tail[lv.toNat]! == s
  { b with
    oid := b.oid.set! s.toNat 0
    nxt := if pr == 0 then b.nxt else b.nxt.set! pr.toNat nx
    head := if pr == 0 then b.head.set! lv.toNat nx else b.head
    tail := if last then b.tail.set! lv.toNat pr else b.tail
    count := b.count - 1 }

/-- The book with an order of id `id`, account `account`, and remaining quantity `q` in the first
free slot, at the end of the chain of side `side` at `price`. -/
@[inline] def place (b : Book) (side price id account q : UInt64) : Book :=
  let s := freeSlot b.oid
  let lv := level side price
  let h := b.head[lv.toNat]!
  let t := b.tail[lv.toNat]!
  { b with
    oid := b.oid.set! s.toNat id
    acct := b.acct.set! s.toNat account
    qty := b.qty.set! s.toNat q
    lvl := b.lvl.set! s.toNat lv
    nxt := (if h == 0 then b.nxt else b.nxt.set! t.toNat s).set! s.toNat 0
    head := if h == 0 then b.head.set! lv.toNat s else b.head
    tail := b.tail.set! lv.toNat s
    count := b.count + 1 }

/-- The state of matching: the book, the event words, the price of the opposite level that
matching has reached, the incoming order's remaining quantity, and whether matching stopped at a
resting order of the incoming order's account. -/
structure Matching where
  book : Book
  out : Array UInt64
  price : UInt64
  rem : UInt64
  selfTrade : Bool
  deriving Inhabited

/-- One iteration of matching for an incoming order with id `taker`, account `account`, and side
`side`.  At an empty level, matching moves to the next worse price.  Otherwise the level's first
order is the first opposite order, and the iteration does what one call of `Spec.fill` does to
it: matching stops for self-trade prevention when the order has the incoming order's account, and
otherwise the two trade the smaller remaining quantity at the level's price, and an order with
nothing left leaves the book. -/
@[inline] def matchStep (taker account side : UInt64) (m : Matching) : Matching :=
  let lv := level (1 - side) m.price
  let s := m.book.head[lv.toNat]!
  if s == 0 then { m with price := if side == 0 then m.price + 1 else m.price - 1 }
  else if m.book.acct[s.toNat]! == account then { m with selfTrade := true }
  else
    let mq := m.book.qty[s.toNat]!
    let q := min m.rem mq
    let out := emit m.out 3 m.book.oid[s.toNat]! taker m.price q m.book.acct[s.toNat]! (mq - q)
    let book := if q == mq then unlink m.book lv 0 s
      else { m.book with qty := m.book.qty.set! s.toNat (mq - q) }
    { m with book := book, out := out, rem := m.rem - q }

/-- Matching of an incoming order with id `taker`, account `account`, side `side`, limit price
`limit`, and quantity `q` against the opposite side, from the edge of the band, with the trade
events appended to `out`.  Matching continues while the order has a remaining quantity, has not
stopped for self-trade prevention, and has reached a level at an acceptable price. -/
@[inline] def fill (b : Book) (out : Array UInt64) (taker account side limit q : UInt64) :
    Matching :=
  LeanExe.repeatWhile matchFuel ⟨b, out, if side == 0 then 1 else maxPrice, q, false⟩
    (fun m => m.rem != 0 && !m.selfTrade && acceptable side limit m.price)
    fun m => matchStep taker account side m

/-- `fill` on the book of the given arrays, next id, and count, the form that `submit` calls. -/
def fillArrays (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (taker account side limit q : UInt64) : Matching :=
  fill ⟨oid, acct, qty, lvl, nxt, head, tail, nextId, count⟩ out taker account side limit q

/-- An accepted incoming order with limit price `limit`: it receives the id `b.nextId`, its
`accepted` event comes first, it matches, and then its remainder is cancelled for self-trade
prevention, cancelled for IOC, resting at `limit`, or cancelled because the book is full, in that
order of precedence.  The capacity test counts the resting orders after matching. -/
@[inline] def submit (b : Book) (out : Array UInt64) (side limit q account tag tif : UInt64) :
    Book × Array UInt64 :=
  let id := b.nextId
  let m := fillArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail (id + 1) b.count
    (emit out 1 id tag 0 0 0 0) id account side limit q
  if m.rem == 0 then (m.book, m.out)
  else if m.selfTrade then (m.book, emit m.out 4 id m.rem 3 0 0 0)
  else if tif == 1 then (m.book, emit m.out 4 id m.rem 2 0 0 0)
  else if m.book.count < capacity then (place m.book side limit id account m.rem, m.out)
  else (m.book, emit m.out 4 id m.rem 4 0 0 0)

/-- `submit` on the book of the given arrays, next id, and count, the form that `step` calls. -/
def submitArrays (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out : Array UInt64) (side limit q account tag tif : UInt64) : Book × Array UInt64 :=
  submit ⟨oid, acct, qty, lvl, nxt, head, tail, nextId, count⟩ out side limit q account tag tif

/-- A cancel of the order with id `id` in slot `s`: its `cancelled` event gives its remaining
quantity, and the order leaves its level's chain. -/
@[inline] def cancel (b : Book) (out : Array UInt64) (id s : UInt64) : Book × Array UInt64 :=
  let lv := b.lvl[s.toNat]!
  let pr := predecessor b.head b.nxt lv s
  let q := b.qty[s.toNat]!
  (unlink b lv pr s, emit out 4 id q 1 0 0 0)

/-- A reduction of the order with id `id` in slot `s` to the quantity `q`, in place, so the order
keeps its priority. -/
@[inline] def reduce (b : Book) (out : Array UInt64) (id s q : UInt64) : Book × Array UInt64 :=
  ({ b with qty := b.qty.set! s.toNat q }, emit out 5 id q 0 0 0 0)

/-- A rejection with the command's kind word, a reference word, and a reason. -/
@[inline] def reject (b : Book) (out : Array UInt64) (kind ref reason : UInt64) :
    Book × Array UInt64 :=
  (b, emit out 2 kind ref reason 0 0 0)

/-- Word `k` of the record at offset `o` of the stream `ws`. -/
@[inline] def word (ws : Array UInt64) (o k : UInt64) : UInt64 := ws[(o + k).toNat]!

/-- The command record at offset `o` of the stream `ws`, shorter than seven words when fewer than
seven words follow `o`, with its events appended to `out`.  The checks run in the order of
`Spec.step`, and the first that fails rejects the command and leaves the book unchanged.  Reasons
are the codes of `Spec.rejectCode` and `Spec.cancelCode`. -/
@[inline] def step (b : Book) (out ws : Array UInt64) (o : UInt64) : Book × Array UInt64 :=
  if ws.size.toUInt64 - o < 7 then reject b out 0 0 1
  else
    let kind := word ws o 0
    if kind == 1 then
      let side := word ws o 1
      let price := word ws o 2
      let q := word ws o 3
      let tag := word ws o 5
      let tif := word ws o 6
      if side > 1 then reject b out kind tag 3
      else if tif > 2 then reject b out kind tag 4
      else if !inRange 1 maxPrice price then reject b out kind tag 5
      else if !inRange 1 maxQty q then reject b out kind tag 6
      else if tif == 2 && crosses b.head side price then reject b out kind tag 9
      else
        submitArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count out side price
          q (word ws o 4) tag tif
    else if kind == 2 then
      let side := word ws o 1
      let q := word ws o 2
      let tag := word ws o 4
      if side > 1 then reject b out kind tag 3
      else if !inRange 1 maxQty q then reject b out kind tag 6
      else
        submitArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count out side
          (if side == 0 then maxPrice else 1) q (word ws o 3) tag 1
    else if kind == 3 then
      let id := word ws o 1
      let s := findSlot b.oid id
      if s == 0 then reject b out kind id 7
      else if b.acct[s.toNat]! != word ws o 2 then reject b out kind id 8
      else cancel b out id s
    else if kind == 4 then
      let id := word ws o 1
      let q := word ws o 3
      let s := findSlot b.oid id
      if s == 0 then reject b out kind id 7
      else if b.acct[s.toNat]! != word ws o 2 then reject b out kind id 8
      else if !inRange 1 maxQty q then reject b out kind id 6
      else if b.qty[s.toNat]! ≤ q then reject b out kind id 10
      else reduce b out id s q
    else reject b out kind 0 2

/-- `step` on the book of the given arrays, next id, and count, the form that `run` calls. -/
def stepArrays (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (out ws : Array UInt64) (o : UInt64) : Book × Array UInt64 :=
  step ⟨oid, acct, qty, lvl, nxt, head, tail, nextId, count⟩ out ws o

/-- The book after the command records of the stream `ws`, read at offsets 0, 7, 14, and so on,
from the book of the given arrays, next id, and count, and the words of the events of all the
records in order.  A final record of fewer than seven words is rejected as malformed. -/
def run (oid acct qty lvl nxt head tail : Array UInt64) (nextId count : UInt64)
    (ws : Array UInt64) : Book × Array UInt64 :=
  LeanExe.loop ((ws.size.toUInt64 + 6) / 7)
    ((⟨oid, acct, qty, lvl, nxt, head, tail, nextId, count⟩ : Book), (#[] : Array UInt64))
    fun i (b, out) =>
      stepArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count out ws (7 * i)

end Demos.OrderBook.Program
