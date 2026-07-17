import Project.ClobMarket.ValidEntry
import Project.ClobMarket.Model

/-!
# Unlimited market price

The valid branch replaces a side-zero taker's price with the unsigned maximum
and every other side's price with zero.  This theorem executes that generated
condition and records the exact source-model taker.  The matcher call remains
outside this proof.
-/

namespace Project.ClobMarket.Price

open Wasm Project.Clob Project.ClobMarket Project.ClobMarket.Model

def priceFrame (book : UInt64) (order : OrderL) : Locals :=
  let taker := unlimitedTakerL order
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1,
      .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
      .i64 taker.oprice, .i64 taker.oqty] ++ List.replicate 36 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem priceProg_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q st
      (priceFrame book order) env) :
    wp Project.ClobMarket.«module» (Entry.priceProg ++ rest) Q st
      { ValidEntry.validFrame book order with values := [] } env := by
  simp only [Entry.priceProg, List.cons_append, List.nil_append]
  by_cases hSide : order.oside = 0
  · wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos hSide]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    simp only [Entry.bidPriceProg]
    wp_run
    simpa [ValidEntry.validFrame, priceFrame, unlimitedTakerL, hSide] using
      hNext
  · wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg hSide]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    simp only [Entry.askPriceProg]
    wp_run
    simpa [ValidEntry.validFrame, priceFrame, unlimitedTakerL, hSide] using
      hNext

end Project.ClobMarket.Price
