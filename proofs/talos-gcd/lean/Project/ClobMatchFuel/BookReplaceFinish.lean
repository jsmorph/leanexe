import Project.ClobMatchFuel.BookReplaceCopy

/-!
# Partial-fill book finalization

The partial-fill branch overwrites the copied maker through five generated
field stores and returns the fresh book root.  This proof identifies those
stores with `replaceOrderStore` and exposes the exact `setQtyL` result.
-/

namespace Project.ClobMatchFuel.BookReplaceFinish

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.BookReplaceStore
  Project.ClobMatchFuel.BookReplaceCopy

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_finish" "(" hParams:term "," hLocals:term ","
    hIndex:term "," hOid:term "," hTrader:term "," hSide:term ","
    hPrice:term "," hQty:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hIndex),
    ($hOid), ($hTrader), ($hSide), ($hPrice), ($hQty)])

def replaceResultFrame (base : Locals) (target : UInt64)
    (totalWords : Nat) : Locals :=
  { replaceCopyFrame base target totalWords with values := [.i64 target] }

def replaceFinishProg : Wasm.Program :=
  [
  .localGet 70,
  .localGet 67,
  .constI64 5,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 72,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 5,
  .mulI64,
  .constI64 2,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 73,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 5,
  .mulI64,
  .constI64 3,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 74,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 5,
  .mulI64,
  .constI64 4,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 75,
  .store64 0,
  .localGet 70,
  .localGet 67,
  .constI64 5,
  .mulI64,
  .constI64 5,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 76,
  .store64 0,
  .localGet 70
]

set_option Elab.async false in
theorem replaceFinishProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity qty : UInt64)
    (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hIndexLocal : base.locals[58]? = some (.i64 (UInt64.ofNat i)))
    (hOidLocal : base.locals[63]? = some (.i64 os[i]!.oid))
    (hTraderLocal : base.locals[64]? = some (.i64 os[i]!.otrader))
    (hSideLocal : base.locals[65]? = some (.i64 os[i]!.oside))
    (hPriceLocal : base.locals[66]? = some (.i64 os[i]!.oprice))
    (hQtyLocal : base.locals[67]? = some (.i64 qty))
    (hi : i < os.length)
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hInv : replaceCopyInv st0 base target source g2 arrayCapacity os st1
      (replaceCopyFrame base target (os.length * 5)))
    (hBook : OrdersAt st1 target os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone :
      OrdersAt (replaceOrderStore st1 target i os[i]! qty) target
          (Model.setQtyL os i qty) →
        FreshOrderArrayAt (replaceOrderStore st1 target i os[i]! qty)
          target arrayCapacity →
        wp «module» rest Q (replaceOrderStore st1 target i os[i]! qty)
          (replaceResultFrame base target (os.length * 5)) env) :
    wp «module» (replaceFinishProg ++ rest) Q st1
      (replaceCopyFrame base target (os.length * 5)) env := by
  obtain ⟨_, _, _, _, _, hFresh, _, _, _⟩ := hInv
  have hTotal64 : os.length * 5 < UInt64.size := by
    change os.length * 5 < 18446744073709551616
    omega
  have hLength64 : os.length < UInt64.size := by
    change os.length < 18446744073709551616
    omega
  have hTotalEq : UInt64.ofNat (os.length * 5) =
      UInt64.ofNat os.length * 5 := by
    apply UInt64.toNat.inj
    rw [toNat_ofNat_lt hTotal64, UInt64.toNat_mul,
      toNat_ofNat_lt hLength64]
    have h5 : (5 : UInt64).toNat = 5 := rfl
    rw [h5, Nat.mod_eq_of_lt hTotal64]
  have hIndexGet : base.locals[58] = .i64 (UInt64.ofNat i) := by
    apply Option.some.inj
    calc
      some base.locals[58] = base.locals[58]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat i)) := hIndexLocal
  have hOidGet : base.locals[63] = .i64 os[i]!.oid := by
    apply Option.some.inj
    calc
      some base.locals[63] = base.locals[63]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.oid) := hOidLocal
  have hTraderGet : base.locals[64] = .i64 os[i]!.otrader := by
    apply Option.some.inj
    calc
      some base.locals[64] = base.locals[64]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.otrader) := hTraderLocal
  have hSideGet : base.locals[65] = .i64 os[i]!.oside := by
    apply Option.some.inj
    calc
      some base.locals[65] = base.locals[65]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.oside) := hSideLocal
  have hPriceGet : base.locals[66] = .i64 os[i]!.oprice := by
    apply Option.some.inj
    calc
      some base.locals[66] = base.locals[66]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.oprice) := hPriceLocal
  have hQtyGet : base.locals[67] = .i64 qty := by
    apply Option.some.inj
    calc
      some base.locals[67] = base.locals[67]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 qty) := hQtyLocal
  simp only [replaceFinishProg, replaceCopyFrame, List.cons_append,
    List.nil_append]
  wp_run_finish (hParams, hLocals, hIndexGet, hOidGet, hTraderGet,
    hSideGet, hPriceGet, hQtyGet)
  try simp
  have hBound (field : Nat) (hfield : field < 5) :
      (target.toNat + (i * 5 + field + 1) * 8) % 4294967296 + 8 ≤
        st1.mem.pages * 65536 :=
    hBook.orderWord_bound i field hi hfield
  rw [if_neg (Nat.not_lt.mpr (hBound 0 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 1 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 2 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 3 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 4 (by omega)))]
  have hBookFinal :=
    ordersAt_replaceOrderStore st1 target os i qty hi hTarget32 hBook
  have hFreshFinal := freshOrderArrayAt_replaceOrderStore st1 target
    arrayCapacity os i qty hi hTarget48 hTarget32 hFresh
  simpa only [replaceOrderStore, replaceResultFrame, replaceCopyFrame,
    hTotalEq, List.getElem!_eq_getElem?_getD] using
      hDone hBookFinal hFreshFinal

end Project.ClobMatchFuel.BookReplaceFinish
