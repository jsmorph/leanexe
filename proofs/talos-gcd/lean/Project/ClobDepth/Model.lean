import Project.Clob

/-!
# Source model for `depth`

The model scans orders in input order for each side.  It updates the first
level with a matching price or appends a new level.  Quantities use `UInt64`
addition, matching the source program's modular arithmetic.
-/

namespace Project.ClobDepth.Model

open Project.Clob

structure LevelL where
  lprice : UInt64
  lqty : UInt64
  deriving DecidableEq, Inhabited, Repr

structure DepthL where
  bids : List LevelL
  asks : List LevelL
  deriving DecidableEq, Repr

def addLevelL : List LevelL → UInt64 → UInt64 → List LevelL
  | [], price, qty => [{ lprice := price, lqty := qty }]
  | level :: levels, price, qty =>
      if level.lprice = price then
        { lprice := price, lqty := level.lqty + qty } :: levels
      else
        level :: addLevelL levels price qty

def depthSideL (book : List OrderL) (side : UInt64) : List LevelL :=
  book.foldl (fun levels order =>
    if order.oside = side then
      addLevelL levels order.oprice order.oqty
    else
      levels) []

def depthL (book : List OrderL) : DepthL :=
  { bids := depthSideL book 0, asks := depthSideL book 1 }

end Project.ClobDepth.Model
