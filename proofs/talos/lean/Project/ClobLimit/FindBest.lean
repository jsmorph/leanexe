import Project.ClobLimit.SearchRegion
import Project.ClobMatchFuel.FindBest

/-!
# The embedded `findBest` fuel loop

Function 13 is the matching artifact's verified search loop with its closed
function region renamed.  Semantic transport preserves its owner-aware store
and result specification.
-/

namespace Project.ClobLimit.FindBest

open Wasm Project.Clob Project.ClobFindBest.Model
  Project.ClobLimit.SearchRegion

theorem func13_spec_owner (env : HostEnv Unit) (st : Store Unit)
    (owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := Project.ClobLimit.«module») (id := 13)
      (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 owner, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  Project.FunctionRegion.terminatesWith searchShift 8 (by simp [SearchDomain])
    (Project.ClobMatchFuel.FindBest.func8_spec_owner env st owner ptr os
      taker hlen hInput)

end Project.ClobLimit.FindBest
