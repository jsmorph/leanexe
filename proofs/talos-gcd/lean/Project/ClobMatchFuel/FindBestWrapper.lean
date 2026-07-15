import Project.ClobMatchFuel.FindBest

/-!
# The internal `findBest` wrapper

Function 9 derives the loop fuel from the represented order-array length.
It passes the source taker and initial empty result to function 8.  Its two
results use the same option ABI as the standalone `findBest` export.
-/

namespace Project.ClobMatchFuel.FindBestWrapper

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobFindBest.Model Project.ClobMatchFuel.FindBest

set_option maxHeartbeats 64000000

/-- The internal wrapper supplies the source fuel and returns its option ABI. -/
theorem func9_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 9) (initial := st) (env := env)
      [.i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid, .i64 ptr, .i64 0]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  have hHead := hInput.1.1
  have hHeadB := hInput.1.2
  have hlen64 : os.length + 1 < UInt64.size := by
    rw [size_eq]
    omega
  have haddNat : (UInt64.ofNat os.length + 1).toNat =
      os.length + 1 := by
    rw [toNat_add_one]
    · rw [toNat_ofNat_lt]
      rw [size_eq]
      omega
    · rw [toNat_ofNat_lt (by rw [size_eq]; omega), size_eq]
      omega
  have hadd : UInt64.ofNat os.length + 1 =
      UInt64.ofNat (os.length + 1) := by
    apply UInt64.toNat.inj
    rw [haddNat, toNat_ofNat_lt hlen64]
  have hnowrap : ¬UInt64.ofNat os.length + 1 < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, haddNat,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    omega
  apply TerminatesWith.of_wp_entry_for (f := func9Def)
  · simp [«module»]
  · change wp «module» func9 _ st
      { params := [.i64 0, .i64 ptr, .i64 taker.oid,
          .i64 taker.otrader, .i64 taker.oside, .i64 taker.oprice,
          .i64 taker.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func9
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnowrap])]
    norm_num
    rw [hadd]
    refine wp_call_tw (func8_spec env st ptr os taker hlen hInput) ?_
    rintro st' vs ⟨rfl, rfl⟩
    wp_run
    simp [func9Def, optionVals]

end Project.ClobMatchFuel.FindBestWrapper
