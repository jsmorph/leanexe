import Demos.OrderBook.Spec

/-! Command streams that exercise each case of [the requirements](requirements.md).  Each sample
has a setup stream, whose events are not shown, and a stream whose events are shown.  Accounts are
101 to 104 and client tags are 1001 and up within each sample, except in the full books and in the
samples that test other words. -/

namespace Demos.OrderBook.Samples

def buy : UInt64 := 0
def sell : UInt64 := 1
def gtc : UInt64 := 0
def ioc : UInt64 := 1
def post : UInt64 := 2

/-- The largest word, 2^64 - 1. -/
def maxWord : UInt64 := 18446744073709551615

def limit (side price qty account tag tif : UInt64) : List UInt64 :=
  [1, side, price, qty, account, tag, tif]

def market (side qty account tag : UInt64) : List UInt64 := [2, side, qty, account, tag, 0, 0]

def cancel (id account : UInt64) : List UInt64 := [3, id, account, 0, 0, 0, 0]

def reduce (id account qty : UInt64) : List UInt64 := [4, id, account, qty, 0, 0, 0]

/-- 4,096 resting bids of quantity 1 from account 104, with client tags 1 to 4,096: four at each
price from 1 to 1,022 and eight at 1,023, added in order of rising price, with ids 1 to 4,096. -/
def fullBook : List UInt64 :=
  (List.range 4096).flatMap fun i =>
    limit buy (min 1023 (i / 4 + 1)).toUInt64 1 104 (i + 1).toUInt64 gtc

/-- 4,096 resting asks of quantity 1 from account 103, with client tags equal to their ids: four at
each price from 1,023 down to 2 and eight at 1, added in order of falling price, with ids 1 to
4,096. -/
def fullAsks : List UInt64 :=
  (List.range 4096).flatMap fun i =>
    limit sell (max 1 (1023 - i / 4)).toUInt64 1 103 (i + 1).toUInt64 gtc

/-- 2,044 resting bids from account 104, four at each price from 1 to 511, then 2,052 resting asks
from account 103, eight at 1,023 and four at each price from 1,022 down to 512, all of quantity 1
and added in this order, with ids 1 to 4,096 and client tags equal to the ids. -/
def mixedFullBook : List UInt64 :=
  ((List.range 2044).flatMap fun i =>
    limit buy (i / 4 + 1).toUInt64 1 104 (i + 1).toUInt64 gtc) ++
  ((List.range 2052).flatMap fun i =>
    let price := if i < 8 then 1023 else 1022 - (i - 8) / 4
    limit sell price.toUInt64 1 103 (2045 + i).toUInt64 gtc)

/-- A sample: its name, the setup stream, and the shown stream. -/
structure Sample where
  name : String
  setup : List UInt64
  shown : List UInt64

def samples : List Sample := [
  { name := "rest, then fill from an IOC sell and a market sell"
    setup := []
    shown := limit buy 10 100 101 1001 gtc ++ limit sell 10 40 102 1002 ioc ++
      market sell 100 103 1003 },
  { name := "price-time priority across two prices"
    setup := []
    shown := limit sell 10 50 101 1001 gtc ++ limit sell 10 50 102 1002 gtc ++
      limit sell 9 30 103 1003 gtc ++ limit buy 10 100 104 1004 gtc },
  { name := "a buy that sweeps two ask levels and stops at the third, then post-only orders"
    setup := limit sell 10 20 101 1001 gtc ++ limit sell 11 20 101 1002 gtc ++
      limit sell 12 20 101 1003 gtc
    shown := limit buy 11 60 102 1004 gtc ++ limit sell 11 5 103 1005 post ++
      limit sell 12 5 103 1006 post ++ limit buy 11 5 103 1007 post },
  { name := "a GTC sell across two bid levels that rests, and a market sell across two levels"
    setup := limit buy 12 10 101 1001 gtc ++ limit buy 11 10 102 1002 gtc ++
      limit buy 10 10 103 1003 gtc ++ limit buy 9 10 101 1004 gtc
    shown := limit sell 11 25 104 1005 gtc ++ market sell 15 104 1006 ++
      limit buy 11 2 102 1007 gtc },
  { name := "self-trade prevention after a fill and at the first order"
    setup := limit sell 10 30 101 1001 gtc ++ limit sell 10 30 102 1002 gtc
    shown := limit buy 10 50 102 1003 gtc ++ limit buy 10 10 101 1004 ioc ++
      limit buy 10 5 102 1005 gtc ++ market buy 5 102 1006 },
  { name := "self-trade prevention: stop before another account's order, no stop at an unacceptable price or once filled, IOC and post-only"
    setup := limit sell 10 5 101 1001 gtc ++ limit sell 10 5 102 1002 gtc ++
      limit sell 12 5 102 1003 gtc
    shown := limit buy 10 8 101 1004 gtc ++ limit buy 9 3 101 1005 gtc ++
      limit buy 10 5 102 1006 gtc ++ limit buy 12 4 102 1007 ioc ++
      limit buy 10 1 102 1008 post },
  { name := "self-trade prevention at a worse price after a trade, for IOC and market orders"
    setup := limit sell 10 5 103 1001 gtc ++ limit sell 11 5 102 1002 gtc ++
      limit sell 12 5 101 1003 gtc ++ limit sell 12 5 104 1004 gtc
    shown := limit buy 12 20 102 1005 ioc ++ market buy 20 101 1006 },
  { name := "IOC, market, and post-only orders against empty and short sides"
    setup := []
    shown := limit buy 10 5 101 1001 ioc ++ market sell 7 101 1002 ++ market buy 3 102 1003 ++
      limit sell 6 2 102 1004 post ++ limit buy 5 2 101 1005 post ++
      limit sell 20 3 102 1006 gtc ++ limit buy 25 10 101 1007 ioc ++
      limit buy 15 4 103 1008 gtc ++ market sell 10 104 1009 },
  { name := "placement between levels and behind an equal price, a cancel of the best ask, and a reduction and cancel of a bid"
    setup := limit buy 12 10 101 1001 gtc ++ limit buy 9 10 102 1002 gtc ++
      limit sell 20 10 103 1003 gtc ++ limit sell 25 10 104 1004 gtc
    shown := limit buy 10 5 103 1005 gtc ++ limit sell 22 5 101 1006 gtc ++
      limit buy 12 4 104 1007 gtc ++ cancel 3 103 ++ market sell 12 102 1008 ++
      reduce 7 104 1 ++ cancel 7 104 ++ limit buy 15 3 101 1009 post },
  { name := "a cancel behind and a reduction ahead at one price, then matching in priority order"
    setup := limit buy 10 5 101 1001 gtc ++ limit buy 10 5 102 1002 gtc ++
      limit buy 10 5 103 1003 gtc
    shown := cancel 2 102 ++ reduce 1 101 2 ++ reduce 99 101 0 ++ market sell 6 104 1004 },
  { name := "sell-side counterparts of self-trade, IOC, GTC, and market cases"
    setup := limit buy 10 5 101 1001 gtc ++ limit buy 10 5 102 1002 gtc ++
      limit buy 9 5 103 1003 gtc
    shown := limit sell 10 7 102 1004 gtc ++ market sell 3 102 1005 ++
      limit sell 9 1 102 1006 ioc ++ limit sell 9 12 104 1007 ioc ++ limit buy 8 4 101 1008 gtc ++
      limit sell 8 4 104 1009 gtc ++ limit sell 20 3 101 1010 gtc ++ market buy 5 102 1011 ++
      limit sell 5 1 104 1012 ioc },
  { name := "market orders at the band edges, the largest market quantity, large event fields, and a cancel after a fill"
    setup := limit sell 1023 5 101 1001 gtc ++ limit buy 1 5 101 1002 gtc
    shown := market buy 5 102 1003 ++ market sell 5 102 1004 ++
      limit sell 1023 4294967295 1099511627776 1005 gtc ++ market buy 4294967294 102 1006 ++
      market buy 4294967295 103 1007 ++ cancel 5 1099511627776 },
  { name := "words of 2^32 and above with valid low bits, accounts equal in their low 32 bits, kind 5, id 0, and an id that never rested"
    setup := limit sell 10 5 101 1001 gtc
    shown := [4294967297, 0, 0, 0, 0, 0, 0] ++ limit 4294967296 10 5 102 1002 gtc ++
      limit buy 10 5 102 1003 4294967296 ++ limit buy 4294967306 5 102 1004 gtc ++
      limit buy 1025 5 102 1005 gtc ++ limit buy 10 4294967301 102 1006 gtc ++
      market 4294967297 1 102 1007 ++ market buy 4294967297 102 1008 ++
      reduce 1 101 4294967297 ++ cancel 4294967297 101 ++ cancel 1 4294967397 ++
      limit buy 10 2 4294967397 1009 gtc ++ [5, 0, 0, 0, 0, 0, 0] ++ cancel 0 101 ++
      limit buy 15 1 102 1010 post ++ limit buy 0 1 102 1011 post ++
      limit buy 9 1 102 1012 ioc ++ cancel 3 102 },
  { name := "cancel and reduce by an account of 2^32 and above, account 0, tag 0, and the largest word"
    setup := limit sell 10 5 4294967397 0 gtc ++ limit sell 11 5 0 maxWord gtc
    shown := reduce 1 4294967397 3 ++ cancel 1 4294967397 ++ [maxWord, 0, 0, 0, 0, 0, 0] ++
      cancel maxWord 0 ++ limit buy 0 1 101 0 gtc ++ market buy 5 maxWord maxWord },
  { name := "words with bit 63 set, and kind, side, and time in force words whose low bits match valid values"
    setup := limit sell 10 5 101 1001 gtc
    shown := limit buy 9223372036854775818 5 102 1002 gtc ++
      limit buy 10 9223372036854775813 102 1003 gtc ++ limit buy maxWord 5 102 1004 gtc ++
      reduce 1 101 9223372036854775809 ++ [257, 0, 0, 0, 0, 0, 0] ++
      limit 256 10 5 102 1005 gtc ++ limit buy 10 5 102 1006 4294967297 ++
      [4294967298, 0, 0, 0, 0, 0, 0] ++ [4294967300, 0, 0, 0, 0, 0, 0] ++
      limit buy 10 5 102 1007 4294967298 },
  { name := "IOC orders that trade and stop at an unacceptable price or trade nothing, and a market sell stopped by self-trade after a trade"
    setup := limit sell 10 5 101 1001 gtc ++ limit sell 12 5 101 1002 gtc ++
      limit buy 8 5 102 1003 gtc ++ limit buy 7 5 103 1004 gtc
    shown := limit buy 11 8 104 1005 ioc ++ limit sell 9 4 104 1006 ioc ++
      limit sell 6 3 104 1007 ioc ++ market sell 8 103 1008 },
  { name := "reductions at the quantity limits, rejected reductions of a bid, and reductions of ids that are not resting"
    setup := limit buy 10 4294967295 101 1001 gtc ++ limit buy 10 5 102 1002 gtc
    shown := reduce 2 102 4294967295 ++ reduce 1 101 4294967294 ++ reduce 1 102 3 ++
      reduce 2 102 5 ++ reduce 0 101 1 ++ reduce 4294967296 101 1 ++ reduce maxWord 101 1 },
  { name := "an ask-side total above 2^32 and a maker account with bit 63 set"
    setup := []
    shown := limit sell 600 4294967295 9223372036854775908 1001 gtc ++
      limit sell 600 4294967295 102 1002 gtc ++ market buy 1 103 1003 },
  { name := "cancel: by another account, by the owner, twice, and of an unknown id"
    setup := limit buy 5 10 101 1001 gtc
    shown := cancel 1 102 ++ cancel 1 101 ++ cancel 1 101 ++ cancel 99 101 },
  { name := "reduce keeps priority, and rejected reductions"
    setup := limit sell 20 100 101 1001 gtc ++ limit sell 20 50 102 1002 gtc
    shown := reduce 1 101 40 ++ reduce 1 101 40 ++ reduce 1 101 0 ++ reduce 1 101 100 ++
      reduce 1 102 10 ++ reduce 7 101 1 ++ reduce 1 101 4294967296 ++
      market buy 60 103 1003 },
  { name := "field checks in order, and ids only for accepted orders"
    setup := []
    shown := [7, 0, 0, 0, 0, 0, 0] ++ limit 2 0 0 101 1001 gtc ++ limit buy 0 5 101 1002 3 ++
      limit buy 0 5 101 1003 gtc ++ limit buy 1024 5 101 1004 gtc ++
      limit buy 10 0 101 1005 gtc ++ limit buy 10 4294967296 101 1006 gtc ++
      limit buy 1023 4294967295 101 1007 gtc ++ limit sell 1 1 101 1008 gtc ++
      market 5 1 101 1009 ++ market sell 0 101 1010 ++ [1, 0, 10] },
  { name := "combined bad fields, kind 0, unused words, and words of 2^32 and above"
    setup := limit sell 10 20 101 1001 gtc
    shown := limit 2 10 5 102 1002 3 ++ limit buy 0 0 102 1003 gtc ++
      limit buy 10 0 102 1004 post ++ market 9 0 102 1005 ++ market buy 4294967296 102 1006 ++
      reduce 1 102 0 ++ reduce 1 102 999 ++ [0, 0, 0, 0, 0, 0, 0] ++
      [2, 0, 5, 102, 1007, 77, 88] ++ [4, 1, 101, 10, 9, 9, 9] ++
      limit sell 11 7 1099511627776 9223372036854775813 gtc ++
      market buy 2 4294967296 1008 ++ [3, 1, 101, 5, 6, 7, 8] },
  { name := "an empty stream"
    setup := limit buy 10 5 101 1001 gtc
    shown := [] },
  { name := "a stream of one short record of two words"
    setup := []
    shown := [1, 0] },
  { name := "a stream whose final record has one word"
    setup := []
    shown := limit buy 10 5 101 1001 gtc ++ [7] },
  { name := "a stream whose final record has four words"
    setup := []
    shown := limit buy 10 5 101 1001 gtc ++ [3, 1, 101, 0] },
  { name := "a stream whose final record has five words"
    setup := []
    shown := limit buy 10 5 101 1001 gtc ++ [3, 1, 101, 0, 0] },
  { name := "a stream whose final record has six words"
    setup := []
    shown := limit buy 10 5 101 1001 gtc ++ [3, 1, 101, 0, 0, 0] },
  { name := "three bids of the largest quantity at one price"
    setup := []
    shown := limit buy 500 4294967295 101 1001 gtc ++ limit buy 500 4294967295 102 1002 gtc ++
      limit buy 500 4294967295 103 1003 gtc ++ limit buy 499 1 103 1004 gtc },
  { name := "full book: GTC and post-only remainders cancelled, then room after a fill"
    setup := fullBook
    shown := limit buy 1 1 101 5001 gtc ++ limit buy 1 1 101 5002 post ++
      market sell 1 103 5003 ++ limit buy 1 1 101 5004 gtc ++ limit buy 1 1 101 5005 gtc },
  { name := "full book: IOC, market, and self-trade remainders, and a GTC sell that exhausts eight makers and rests"
    setup := fullBook
    shown := limit buy 1 1 101 5001 ioc ++ market buy 1 101 5002 ++
      limit sell 1023 1 104 5003 gtc ++ limit sell 1023 9 103 5004 gtc },
  { name := "full book of asks: sell-side IOC and market remainders, a buy-side self-trade remainder, and a GTC buy that exhausts eight makers and rests"
    setup := fullAsks
    shown := limit sell 1023 1 101 5001 ioc ++ market sell 1 101 5002 ++
      limit buy 1 1 103 5003 gtc ++ limit buy 1 9 101 5004 gtc },
  { name := "full book of asks: a rejected reduction, a cancel, a GTC sell that rests in the freed room, and another that finds the book full"
    setup := fullAsks
    shown := reduce 4096 103 1 ++ cancel 4096 103 ++ limit sell 1023 1 101 5001 gtc ++
      limit sell 1023 1 101 5002 gtc },
  { name := "full book with both sides: GTC orders of either side cancelled, then room after a fill"
    setup := mixedFullBook
    shown := limit sell 1000 1 101 5001 gtc ++ limit buy 100 1 101 5002 gtc ++
      market buy 1 102 5003 ++ limit sell 1000 1 101 5004 gtc ++ limit buy 100 1 101 5005 gtc },
  { name := "full book with both sides: post-only orders that cross and that do not, and a GTC buy that fills completely"
    setup := mixedFullBook
    shown := limit sell 511 1 101 5001 post ++ limit sell 1000 1 101 5002 post ++
      limit buy 512 1 101 5003 gtc }
]

/-- Records outside a stream: records of 0, 1, 6, 8, and 9 words, and a cancel of an id that no
order of the empty book has. -/
def single : List (Array UInt64) :=
  [#[], #[5], #[1, 0, 10, 5, 101, 1001], #[1, 0, 10, 5, 101, 1001, 0, 0],
    #[1, 0, 10, 5, 101, 1001, 0, 0, 0], #[3, 1, 101, 0, 0, 0, 0]]

end Demos.OrderBook.Samples
