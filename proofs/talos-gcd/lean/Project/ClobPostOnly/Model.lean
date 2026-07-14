import Project.ClobFindBest.Model

/-!
# Source model for `postOnly`

The model states order validity and the three source outcomes over the shared
CLOB order representation.  It preserves `UInt64` comparisons and delegates
crossing selection to the proved `findBestL` model.  Allocation and ownership
remain properties of the artifact theorem rather than this pure source model.
-/

namespace Project.ClobPostOnly.Model

open Project.Clob Project.ClobFindBest.Model

abbrev validSideL (side : UInt64) : Prop :=
  side = 0 ∨ side = 1

abbrev hasIdL (os : List OrderL) (id : UInt64) : Prop :=
  ∃ order ∈ os, order.oid = id

abbrev validOrderL (os : List OrderL) (order : OrderL) : Prop :=
  order.oid ≠ 0 ∧
  order.otrader ≠ 0 ∧
  validSideL order.oside ∧
  order.oqty ≠ 0 ∧
  ¬hasIdL os order.oid

inductive PostOnlyResultL where
  | invalid
  | wouldCross
  | appended
  deriving DecidableEq

def postOnlyL (os : List OrderL) (order : OrderL) : PostOnlyResultL :=
  if validOrderL os order then
    match findBestL os order with
    | some _ => .wouldCross
    | none => .appended
  else
    .invalid

def postOnlyStatusL : PostOnlyResultL → UInt64
  | .invalid => 1
  | .wouldCross => 2
  | .appended => 0

def postOnlyBookL (os : List OrderL) (order : OrderL) :
    PostOnlyResultL → List OrderL
  | .appended => os ++ [order]
  | _ => os

end Project.ClobPostOnly.Model
