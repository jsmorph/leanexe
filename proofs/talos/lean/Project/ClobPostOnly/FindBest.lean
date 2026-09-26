import Project.ClobFindBest.SearchLoop
import Project.ClobPostOnly.SearchHelpers

/-! The generated search uses the shared borrowed-owner loop proof. -/
namespace Project.ClobPostOnly.FindBest
open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobFindBest Project.ClobFindBest.Model
set_option maxRecDepth 16384

theorem func12_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 12) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 0, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func12Def)
  · simp [«module»]
  · change wp «module» func12 _ st (SearchLoop.entryFrame 0 ptr os taker) env
    rw [SearchProgram.postOnly]
    simpa only [List.append_nil] using
      (SearchLoop.body_spec «module» env st 10 21 0 ptr os taker hlen hInput
        (fun k _ => ClobPostOnly.SearchHelpers.func10_spec env st taker os[k]!) _ []
        (by
          intro final hValues
          wp_run_with [hValues]
          simp [func12Def, optionVals]))

#print axioms func12_spec

end Project.ClobPostOnly.FindBest
