import Project.ClobMatchFuel.FrozenHelpers
import Project.ClobMatchFuel.FrozenSearchRegion
import Project.ClobFindBest.FrozenLoop

namespace Project.ClobMatchFuel.Frozen.FindBest
open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobFindBest.Frozen.Model

theorem func8_spec_owner (env : HostEnv Unit) (st : Store Unit)
    (owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 owner, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  exact Project.FunctionRegion.terminatesWith SearchRegion.searchShift 7 (by simp [SearchRegion.SearchDomain])
    (Project.ClobFindBest.Frozen.Loop.func7_spec_owner env st owner ptr os taker hlen hInput)

theorem func8_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 0, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  func8_spec_owner env st 0 ptr os taker hlen hInput


end Project.ClobMatchFuel.Frozen.FindBest
