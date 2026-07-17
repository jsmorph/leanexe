import Project.ClobMarket.Price

/-!
# Exported matcher call

The valid path passes a zero owner, the input book, and the transformed taker
to function 18.  This theorem applies an arbitrary matcher postcondition at
the exact generated call boundary.  Result storage remains opaque.
-/

namespace Project.ClobMarket.Call

open Wasm Project.Clob Project.ClobMarket Project.ClobMarket.Model

def callFrame (book : UInt64) (order : OrderL) : Locals :=
  let taker := unlimitedTakerL order
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1,
      .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
      .i64 taker.oprice, .i64 taker.oqty, .i64 0, .i64 book,
      .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
      .i64 taker.oprice, .i64 taker.oqty] ++ List.replicate 29 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem callProg_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL)
    (P : Store Unit → List Value → Prop)
    (hCall : TerminatesWith (m := Project.ClobMarket.«module») (id := 18)
      (initial := st) (env := env)
      (Project.ClobLimit.RunMatchCorrect.runMatchArgs 0 book
        (unlimitedTakerL order)) P)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (st' : Store Unit) (values : List Value), P st' values →
      wp Project.ClobMarket.«module» rest Q st'
        { callFrame book order with values := values } env) :
    wp Project.ClobMarket.«module» (Entry.callProg ++ rest) Q st
      (Price.priceFrame book order) env := by
  have hCall' : TerminatesWith (m := Project.ClobMarket.«module»)
      (id := 18) (initial := st) (env := env)
      [.i64 order.oqty, .i64 (unlimitedTakerL order).oprice,
        .i64 (unlimitedTakerL order).oside,
        .i64 (unlimitedTakerL order).otrader,
        .i64 (unlimitedTakerL order).oid, .i64 book, .i64 0] P := by
    simpa [Project.ClobLimit.RunMatchCorrect.runMatchArgs] using hCall
  simp only [Entry.callProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, Price.priceFrame]
  refine wp_call_tw hCall' ?_
  intro st' values hPost
  simpa [callFrame] using hNext st' values hPost

end Project.ClobMarket.Call
