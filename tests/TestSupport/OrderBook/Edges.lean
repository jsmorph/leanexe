import Demos.OrderBook.Samples

/-! Command streams for the input classes that [the samples](../../../Demos/OrderBook/Samples.lean)
leave uncovered, and for the program's own limits: top-of-book totals near 2^44, ids at or above
2^32 and near 2^64, event fields at their largest values, unknown kinds with nonzero words,
matching that nears its fuel, and walks along long chains.  Each stream starts from the empty book
with the given next id, so the streams with a next id other than 1 have no Python counterpart. -/

namespace TestSupport.OrderBook.Edges

open Demos.OrderBook.Samples

/-- Bit 63. -/
def bit63 : UInt64 := 9223372036854775808

/-- Largest quantity, 2^32 - 1. -/
def maxQty : UInt64 := 4294967295

/-- An edge stream: its name, the next id of its empty starting book, and its words. -/
structure Edge where
  name : String
  nextId : UInt64
  words : List UInt64

/-- `n` limit orders of one side at one price, of quantity `q`, from accounts 1 to 3 in turn, with
client tags 1 to `n`. -/
def many (n : Nat) (side price q : UInt64) : List UInt64 :=
  (List.range n).flatMap fun i =>
    limit side price q (i % 3 + 1).toUInt64 (i + 1).toUInt64 gtc

/-- 4,096 bids of the largest quantity at 700, then a post-only bid that finds the book full, a
cancel of the chain's last order by another account and by its own, a bid that rests in the freed
slot, a cancel in the middle of the chain, another bid that rests, a reduction of that bid by one,
and an IOC sell that finds no bid at its price, which leave a total of 4,096 * (2^32 - 1) - 1. -/
def bidTotal : List UInt64 :=
  many 4096 buy 700 maxQty ++ limit buy 700 1 9 5001 post ++ cancel 4096 2 ++ cancel 4096 1 ++
    limit buy 700 maxQty 9 5002 gtc ++ cancel 2000 2 ++ limit buy 700 maxQty 9 5003 gtc ++
    reduce 4099 9 (maxQty - 1) ++ limit sell 701 1 9 5004 ioc

/-- 4,096 asks of the largest quantity at 300 from accounts 7 and 7 with bit 63 in turn, then
market buys that exhaust a maker, trade part of the next, exhaust it and stop for self-trade
prevention, and a sell that rests at the end of the chain. -/
def askTotal : List UInt64 :=
  ((List.range 4096).flatMap fun i =>
    limit sell 300 maxQty (if i % 2 = 0 then 7 else 7 ||| bit63) (i + 1).toUInt64 gtc) ++
  market buy maxQty (7 ||| bit63) 6001 ++ market buy 5 7 6002 ++ market buy maxQty 7 6003 ++
  limit sell 300 maxQty 9 6004 gtc

/-- Orders whose ids run from 2^32 - 3 to 2^32 + 3, with cancels and reductions by ids whose low 32
bits equal those of a resting order's id. -/
def wideIds (n : UInt64) : List UInt64 :=
  limit sell 10 5 101 1001 gtc ++ limit sell 10 5 102 1002 gtc ++ limit sell 11 5 103 1003 gtc ++
    limit buy 9 5 104 1004 gtc ++ limit buy 9 5 105 1005 gtc ++ cancel 0 101 ++
    cancel (n + 4294967296) 101 ++ cancel ((n + 4) % 4294967296) 105 ++ reduce (n + 4) 105 2 ++
    cancel (n + 3) 104 ++ cancel (n + 3) 104 ++ market buy 7 106 1006 ++
    limit sell 8 20 107 1007 gtc ++ reduce (n + 6) 107 17 ++ cancel (n + 1) 102 ++
    cancel (n + 6) 107

/-- Eight accepted orders from next id `n`, with event fields at their largest values: quantities
of 2^32 - 1, prices 1 and 1,023, accounts and client tags of 2^64 - 1, and maker remaining
quantities of 2^32 - 2.  From `n = 2^64 - 9` the ids run to 2^64 - 2, and the next id ends at
2^64 - 1. -/
def largest (n : UInt64) : List UInt64 :=
  limit sell 1023 maxQty maxWord maxWord gtc ++ limit sell 1023 maxQty (maxWord ^^^ bit63) 1 gtc ++
    limit buy 1 maxQty 0 maxWord gtc ++ reduce n maxWord (maxQty - 1) ++
    market buy maxQty 5 maxWord ++ limit buy 1023 maxQty 6 maxWord ioc ++
    limit sell 1 maxQty 7 maxWord ioc ++ [maxWord, maxWord, maxWord, maxWord, maxWord, maxWord,
      maxWord] ++ limit sell 1 maxQty maxWord maxWord post ++ reduce (n + 6) maxWord maxQty ++
    reduce (n + 6) maxWord (maxQty - 1) ++ limit buy 1 maxQty 8 maxWord gtc ++
    cancel (n + 7) 8 ++ cancel maxWord maxWord

/-- From next id 2^64 - 2: a resting order with id 2^64 - 2, a taker with id 2^64 - 1 that
exhausts it, after which the next id is 0, and commands that accept no order.  The book after the
taker lies outside `Spec.Valid`, whose next id is positive. -/
def wrap : List UInt64 :=
  limit sell 1023 maxQty maxWord maxWord gtc ++ market buy maxQty 3 maxWord ++
    [maxWord, maxWord, maxWord, maxWord, maxWord, maxWord, maxWord] ++
    limit buy 1024 1 1 1 gtc ++ cancel 0 0 ++ reduce maxWord 0 1

/-- From next id 2^64 - 1: an order that rests with id 2^64 - 1, its cancel with a remaining
quantity of 2^32 - 1, and a reduction of the id that no longer rests. -/
def lastId : List UInt64 :=
  limit buy 5 maxQty maxWord maxWord gtc ++ cancel maxWord maxWord ++ reduce maxWord maxWord 1

/-- Records of unknown kinds whose other words are nonzero, among them kinds whose low 32 bits are
those of a known kind. -/
def unknownKinds : List UInt64 :=
  limit buy 10 5 101 1001 gtc ++ [6, maxWord, maxWord, maxWord, maxWord, maxWord, maxWord] ++
    [bit63, 1, 2, 3, 4, 5, 6] ++ [0, 0, 10, 5, 101, 1002, 0] ++
    [4294967297, 0, 10, 5, 101, 1003, 0] ++ [4294967299, 1, 101, 0, 0, 0, 0] ++
    [maxWord - 3, 1, 101, 1, 0, 0, 0] ++ [5, 1, 2, 3, 4, 5, 6] ++ cancel 1 101

/-- 4,096 bids of quantity 1 at price 1, and a market sell of 4,097 that skips 1,022 empty levels,
exhausts every bid, and skips once more, 5,119 iterations of matching. -/
def fuelSell : List UInt64 := many 4096 buy 1 1 ++ market sell 4097 9 9001

/-- 4,096 asks of quantity 1 at 1,023, and a GTC buy of 4,097 at 1,023 that skips 1,022 empty
levels, exhausts every ask, skips once more, and rests. -/
def fuelBuy : List UInt64 := many 4096 sell 1023 1 ++ limit buy 1023 4097 9 9001 gtc

/-- 4,095 asks of quantity 1 at 1,023 from account 1, an ask from account 2, and a market buy of
4,096 from account 2 that exhausts 4,095 asks and stops for self-trade prevention. -/
def fuelSelfTrade : List UInt64 :=
  ((List.range 4095).flatMap fun i => limit sell 1023 1 1 (i + 1).toUInt64 gtc) ++
    limit sell 1023 1 2 4096 gtc ++ market buy 4096 2 9001

/-- One chain of 300 bids at 50, cancels from its tail, middle, and head, a cancel by another
account, bids that rest in the freed slots, reductions, and a market sell through the chain. -/
def chainWalks : List UInt64 :=
  many 300 buy 50 10 ++ cancel 300 3 ++ cancel 299 2 ++ cancel 150 3 ++ cancel 1 1 ++
    cancel 2 3 ++ limit buy 50 7 4 3001 gtc ++ limit buy 50 8 4 3002 gtc ++
    limit buy 50 9 4 3003 gtc ++ limit buy 50 10 4 3004 gtc ++ cancel 301 4 ++ cancel 304 4 ++
    reduce 3 3 1 ++ reduce 303 4 2 ++ limit buy 50 11 4 3005 gtc ++ market sell 1500 5 3006 ++
    cancel 305 4 ++ limit buy 50 12 4 3007 gtc ++ market sell 1 5 3008

def edges : List Edge := [
  { name := "bid-total-near-2^44", nextId := 1, words := bidTotal },
  { name := "ask-total-near-2^44", nextId := 1, words := askTotal },
  { name := "ids-across-2^32", nextId := 4294967293, words := wideIds 4294967293 },
  { name := "largest-event-fields", nextId := 18446744073709551607,
    words := largest 18446744073709551607 },
  { name := "largest-fields-from-id-1", nextId := 1, words := largest 1 },
  { name := "id-wraps-to-0", nextId := 18446744073709551614, words := wrap },
  { name := "id-2^64-1-rests", nextId := 18446744073709551615, words := lastId },
  { name := "unknown-kinds-nonzero-words", nextId := 1, words := unknownKinds },
  { name := "matching-fuel-sell", nextId := 1, words := fuelSell },
  { name := "matching-fuel-buy", nextId := 1, words := fuelBuy },
  { name := "matching-fuel-self-trade", nextId := 1, words := fuelSelfTrade },
  { name := "chain-walks", nextId := 1, words := chainWalks }
]

end TestSupport.OrderBook.Edges
