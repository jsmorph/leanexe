import Project.ClobMarket.ExportRegion
import Project.ClobLimit.ValidOrder
import Project.ClobLimit.Allocation

/-!
# Transported export helpers

The exported market function uses the same validity function and status
constants as the completed limit artifact.  These wrappers expose their exact
specifications in the market module.  Later branch proofs need no knowledge of
the source module or the transport certificate.
-/

namespace Project.ClobMarket.Helpers

open Wasm Project.Clob Project.ClobPostOnly.Model
  Project.ClobMarket.ExportRegion

theorem func6_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (order : OrderL)
    (hLength : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := Project.ClobMarket.«module») (id := 6)
      (initial := st) (env := env)
      [.i64 order.oqty, .i64 order.oprice, .i64 order.oside,
       .i64 order.otrader, .i64 order.oid, .i64 ptr, .i64 0]
      (fun st' values =>
        values = [.i64 (Project.ClobPostOnly.SearchHelpers.boolWord
          (validOrderL os order))] ∧ st' = st) :=
  Project.FunctionRegion.terminatesWith exportShift 6
    (by simp [ExportDomain])
    (Project.ClobLimit.ValidOrder.func6_spec env st ptr os order hLength
      hInput)

theorem func19_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := Project.ClobMarket.«module») (id := 19)
      (initial := st) (env := env) []
      (fun st' values => values = [.i64 0] ∧ st' = st) :=
  Project.FunctionRegion.terminatesWith exportShift 19
    (by simp [ExportDomain])
    (Project.ClobLimit.Allocation.func19_spec env st)

theorem func20_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := Project.ClobMarket.«module») (id := 20)
      (initial := st) (env := env) []
      (fun st' values => values = [.i64 1] ∧ st' = st) :=
  Project.FunctionRegion.terminatesWith exportShift 20
    (by simp [ExportDomain])
    (Project.ClobLimit.Allocation.func20_spec env st)

end Project.ClobMarket.Helpers
