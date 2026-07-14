import LeanExe.Examples.Clob

namespace LeanExe.Examples.Clob

def findBestBuy : Order :=
  { id := 90, trader := 90, side := 0, price := 100, qty := 5 }

def findBestSell : Order :=
  { id := 91, trader := 91, side := 1, price := 100, qty := 5 }

def findBestRejected : Array Order := #[
  { id := 1, trader := 1, side := 0, price := 50, qty := 1 },
  { id := 2, trader := 90, side := 1, price := 90, qty := 1 },
  { id := 3, trader := 3, side := 1, price := 101, qty := 1 }
]

def findBestBuys : Array Order := #[
  { id := 1, trader := 1, side := 1, price := 100, qty := 1 },
  { id := 2, trader := 2, side := 1, price := 99, qty := 1 },
  { id := 3, trader := 3, side := 1, price := 99, qty := 1 },
  { id := 4, trader := 4, side := 1, price := 100, qty := 1 },
  { id := 5, trader := 5, side := 0, price := 1, qty := 1 }
]

def findBestSells : Array Order := #[
  { id := 1, trader := 1, side := 0, price := 100, qty := 1 },
  { id := 2, trader := 2, side := 0, price := 101, qty := 1 },
  { id := 3, trader := 3, side := 0, price := 101, qty := 1 },
  { id := 4, trader := 4, side := 0, price := 99, qty := 1 },
  { id := 5, trader := 5, side := 1, price := 200, qty := 1 },
  { id := 6, trader := 91, side := 0, price := 200, qty := 1 }
]

#guard findBest #[] findBestBuy == none
#guard findBest findBestRejected findBestBuy == none
#guard findBest #[findBestRejected[0]!, findBestBuys[0]!] findBestBuy == some 1
#guard findBest findBestBuys findBestBuy == some 1
#guard findBest findBestSells findBestSell == some 1

def b1 : Array Order := (postOnly #[] { id := 1, trader := 10, side := 0, price := 100, qty := 5 }).book

#guard (postOnly #[] { id := 1, trader := 10, side := 0, price := 100, qty := 5 }).status == errOk
#guard b1.size == 1

#guard (postOnly #[] { id := 0, trader := 11, side := 1, price := 200, qty := 1 }).status == errInvalid
#guard (postOnly #[] { id := 2, trader := 0, side := 1, price := 200, qty := 1 }).status == errInvalid
#guard (postOnly b1 { id := 1, trader := 11, side := 1, price := 200, qty := 1 }).status == errInvalid
#guard (postOnly b1 { id := 2, trader := 11, side := 3, price := 200, qty := 1 }).status == errInvalid
#guard (postOnly b1 { id := 2, trader := 11, side := 1, price := 200, qty := 0 }).status == errInvalid
#guard (postOnly b1 { id := 2, trader := 11, side := 1, price := 100, qty := 3 }).status == errWouldCross
#guard (postOnly b1 { id := 2, trader := 11, side := 1, price := 105, qty := 3 }).status == errOk

def rLimit : OpResult := limit b1 { id := 2, trader := 11, side := 1, price := 100, qty := 3 }

#guard rLimit.status == errOk
#guard rLimit.book.size == 1
#guard rLimit.book[0]!.qty == 2
#guard rLimit.trades.size == 1
#guard rLimit.trades[0]!.takerId == 2
#guard rLimit.trades[0]!.makerId == 1
#guard rLimit.trades[0]!.price == 100
#guard rLimit.trades[0]!.qty == 3

def rMarket : OpResult := market b1 { id := 3, trader := 12, side := 1, price := 999, qty := 9 }

#guard rMarket.status == errOk
#guard rMarket.book.size == 0
#guard rMarket.trades.size == 1
#guard rMarket.trades[0]!.qty == 5

#guard (cancel b1 1).status == errOk
#guard (cancel b1 1).book.size == 0
#guard (cancel b1 9).status == errNotFound
#guard (cancel b1 9).book.size == 1

def rSameTrader : OpResult := limit b1 { id := 7, trader := 10, side := 1, price := 100, qty := 2 }

#guard rSameTrader.status == errOk
#guard rSameTrader.trades.size == 0
#guard rSameTrader.book.size == 2
#guard rSameTrader.book[1]!.id == 7
#guard rSameTrader.book[1]!.qty == 2

def b2 : Array Order := (postOnly b1 { id := 5, trader := 15, side := 0, price := 100, qty := 7 }).book

#guard b2.size == 2

def rFifo : OpResult := limit b2 { id := 6, trader := 20, side := 1, price := 100, qty := 4 }

#guard rFifo.trades.size == 1
#guard rFifo.trades[0]!.makerId == 1
#guard rFifo.book.size == 2
#guard rFifo.book[0]!.qty == 1

def q2 : Quote := quote b2

#guard q2.hasBid == 1
#guard q2.bidPrice == 100
#guard q2.bidQty == 12
#guard q2.hasAsk == 0

def b3 : Array Order := (postOnly b2 { id := 8, trader := 16, side := 1, price := 105, qty := 4 }).book

#guard b3.size == 3

def d3 : Depth := depth b3

#guard d3.bids.size == 1
#guard d3.bids[0]!.price == 100
#guard d3.bids[0]!.qty == 12
#guard d3.asks.size == 1
#guard d3.asks[0]!.price == 105
#guard d3.asks[0]!.qty == 4

def rBetter : OpResult := limit b3 { id := 9, trader := 21, side := 1, price := 99, qty := 1 }

#guard rBetter.trades.size == 1
#guard rBetter.trades[0]!.makerId == 1
#guard rBetter.trades[0]!.price == 100

end LeanExe.Examples.Clob
