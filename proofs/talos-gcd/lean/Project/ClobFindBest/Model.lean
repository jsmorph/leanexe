import Project.Clob

/-!
# Source model for `findBest`

These definitions restate the CLOB search over the proof workspace's shared
order representation.  They preserve `UInt64` comparisons and first-index
tie breaking.
-/

namespace Project.ClobFindBest.Model

open Project.Clob

def oppositeSideL (side : UInt64) : UInt64 :=
  if side = 0 then 1 else 0

abbrev crossesL (taker maker : OrderL) : Prop :=
  if taker.oside = 0 then maker.oprice ≤ taker.oprice
  else taker.oprice ≤ maker.oprice

abbrev eligibleL (taker maker : OrderL) : Prop :=
  maker.oside = oppositeSideL taker.oside ∧
  maker.otrader ≠ taker.otrader ∧
  crossesL taker maker

abbrev betterPriceL (taker candidate incumbent : OrderL) : Prop :=
  if taker.oside = 0 then candidate.oprice < incumbent.oprice
  else incumbent.oprice < candidate.oprice

def findBestFuelL : Nat → List OrderL → OrderL → Nat → Option Nat → Option Nat
  | 0, _, _, _, best => best
  | fuel + 1, os, taker, i, best =>
      if i < os.length then
        let candidate := os[i]!
        let best' :=
          match best with
          | none => if eligibleL taker candidate then some i else none
          | some j =>
              if eligibleL taker candidate ∧
                  betterPriceL taker candidate os[j]! then
                some i
              else
                some j
        findBestFuelL fuel os taker (i + 1) best'
      else
        best

def findBestL (os : List OrderL) (taker : OrderL) : Option Nat :=
  findBestFuelL (os.length + 1) os taker 0 none

def optionTag : Option Nat → UInt64
  | none => 0
  | some _ => 1

def optionPayload : Option Nat → UInt64
  | none => 0
  | some i => UInt64.ofNat i

def optionVals (value : Option Nat) : List Wasm.Value :=
  [.i64 (optionPayload value), .i64 (optionTag value)]

end Project.ClobFindBest.Model
