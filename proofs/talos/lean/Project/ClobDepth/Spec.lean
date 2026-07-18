import Project.ClobDepth.Func7

/-!
# Specification for `clob_depth`

`Func7.func7_terminates` proves the exported depth function for every
represented order book under the stated allocator and budget premises.  The
result owns both returned level arrays with the exact source side folds,
preserves the input orders array and all bytes below the initial heap top,
and states the exact allocator globals and page count.  The theorems below
restate the returned contents through `Model.depthL` and expose the source
aggregation facts: exact modular per-price quantities and their bounded
natural-number interpretation.
-/

namespace Project.ClobDepth.Spec

open Wasm Project.Clob Project.ClobDepth Project.ClobDepth.Model
  Project.ClobDepth.Properties Project.ClobDepth.Representation

theorem result_bids {st0 st : Store Unit} {os : List OrderL}
    {orders : UInt64} {g0n : Nat} {g2 : UInt64}
    (h : Func7.Result st0 st os orders g0n g2) :
    OwnedLevelArrayAt st
      (UInt64.ofNat (Func6Fold.foldRoot os 0 g0n os.length))
      (UInt64.ofNat (Func6Fold.foldCap os 0 os.length))
      (depthL os).bids :=
  h.bidsOwned

theorem result_asks {st0 st : Store Unit} {os : List OrderL}
    {orders : UInt64} {g0n : Nat} {g2 : UInt64}
    (h : Func7.Result st0 st os orders g0n g2) :
    OwnedLevelArrayAt st
      (UInt64.ofNat (Func6Fold.foldRoot os 1
        (Func6Fold.foldTop os 0 g0n os.length) os.length))
      (UInt64.ofNat (Func6Fold.foldCap os 1 os.length))
      (depthL os).asks :=
  h.asksOwned

theorem result_qtyAt (os : List OrderL) (side price : UInt64) :
    levelQtyAt (depthSideL os side) price = orderQtyAt os side price :=
  depthSideL_qtyAt os side price

theorem result_qtyAt_nat (os : List OrderL) (side price : UInt64)
    (hBound : orderQtyAtNat os side price < UInt64.size) :
    (levelQtyAt (depthSideL os side) price).toNat =
      orderQtyAtNat os side price :=
  depthSideL_qtyAt_nat os side price hBound

end Project.ClobDepth.Spec
