import Project.ClobLimit.FindBest
import Project.ClobMatchFuel.FindBestWrapper

/-!
# The internal `findBest` wrapper

Function 14 is the matching artifact's verified search wrapper with its closed
function region renamed.  Semantic transport preserves both its owner-aware
and owner-zero specifications.
-/

namespace Project.ClobLimit.FindBestWrapper

open Wasm Project.Clob Project.ClobFindBest.Model
  Project.ClobLimit.SearchRegion

theorem func14_spec_owner (env : HostEnv Unit) (st : Store Unit)
    (owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := Project.ClobLimit.«module») (id := 14)
      (initial := st) (env := env)
      [.i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid, .i64 ptr, .i64 owner]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  Project.FunctionRegion.terminatesWith searchShift 9 (by simp [SearchDomain])
    (Project.ClobMatchFuel.FindBestWrapper.func9_spec_owner env st owner ptr
      os taker hlen hInput)

theorem func14_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := Project.ClobLimit.«module») (id := 14)
      (initial := st) (env := env)
      [.i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid, .i64 ptr, .i64 0]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  func14_spec_owner env st 0 ptr os taker hlen hInput

end Project.ClobLimit.FindBestWrapper
