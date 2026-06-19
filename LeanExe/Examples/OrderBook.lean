namespace LeanExe
namespace Examples.OrderBook

inductive Side where
  | buy
  | sell

structure RestingOrder where
  quantity : UInt64
  limitPrice : UInt64

structure Order where
  side : Side
  quantity : UInt64
  limitPrice : UInt64

structure Book where
  bestBid : RestingOrder
  bestAsk : RestingOrder

structure Trade where
  quantity : UInt64
  price : UInt64

def minQty (left right : UInt64) : UInt64 :=
  if left < right then
    left
  else
    right

def matchOrder (book : Book) (order : Order) : Option Trade :=
  match order.side with
  | .buy =>
      if order.limitPrice >= book.bestAsk.limitPrice then
        some
          { quantity := minQty order.quantity book.bestAsk.quantity
            price := book.bestAsk.limitPrice }
      else
        none
  | .sell =>
      if order.limitPrice <= book.bestBid.limitPrice then
        some
          { quantity := minQty order.quantity book.bestBid.quantity
            price := book.bestBid.limitPrice }
      else
        none

def sideFromFlag (flag : UInt64) : Side :=
  if flag == 0 then
    .buy
  else
    .sell

def bookFromFields (bidQuantity bidPrice askQuantity askPrice : UInt64) : Book :=
  { bestBid := { quantity := bidQuantity, limitPrice := bidPrice }
    bestAsk := { quantity := askQuantity, limitPrice := askPrice } }

def matchBook
    (bidQuantity bidPrice askQuantity askPrice side quantity limitPrice : UInt64) :
    Option Trade :=
  if side = 0 then
    if askPrice <= limitPrice then
      some
        { quantity := minQty quantity askQuantity
          price := askPrice }
    else
      none
  else
    if limitPrice <= bidPrice then
      some
        { quantity := minQty quantity bidQuantity
          price := bidPrice }
    else
      none

end Examples.OrderBook
end LeanExe
