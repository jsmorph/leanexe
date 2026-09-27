import Project.ClobFindBest.SearchLoop
import Project.ClobMatchFuel.Helpers

/-! The generated search uses the shared borrowed-owner loop proof. -/
namespace Project.ClobMatchFuel.FindBest
open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobFindBest Project.ClobFindBest.Model
set_option maxRecDepth 16384

theorem func8_spec_owner (env : HostEnv Unit) (st : Store Unit)
    (owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 owner, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for (f := func8Def)
  · simp [«module»]
  · change wp «module» func8 _ st (SearchLoop.entryFrame owner ptr os taker) env
    rw [SearchProgram.matchFuel]
    simpa only [List.append_nil] using
      (SearchLoop.body_spec «module» env st 6 18 owner ptr os taker hlen hInput
        (fun k _ => ClobMatchFuel.Helpers.func6_spec env st taker os[k]!) _ []
        (by
          intro final hValues
          wp_run_with [hValues]
          simp [func8Def, optionVals]))

#print axioms func8_spec_owner

theorem func8_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 0, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  func8_spec_owner env st 0 ptr os taker hlen hInput


end Project.ClobMatchFuel.FindBest
