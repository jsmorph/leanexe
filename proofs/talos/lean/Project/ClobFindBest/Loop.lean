import Project.ClobFindBest.SearchLoop
import Project.ClobFindBest.Helpers

/-! The generated search uses the shared borrowed-owner loop proof. -/
namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest Project.ClobFindBest.Model
set_option maxRecDepth 16384

theorem func7_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 7) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 0, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func7Def)
  · simp [«module»]
  · change wp «module» func7 _ st (SearchLoop.entryFrame 0 ptr os taker) env
    rw [SearchProgram.standalone]
    simpa only [List.append_nil] using
      (SearchLoop.body_spec «module» env st 5 12 0 ptr os taker hlen hInput
        (fun k _ => ClobFindBest.Helpers.func5_spec env st taker os[k]!) _ []
        (by
          intro final hValues
          wp_run_with [hValues]
          simp [func7Def, optionVals]))

#print axioms func7_spec

end Project.ClobFindBest.Loop
