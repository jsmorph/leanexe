import Project.ClobLimit.InternalPartialBookCopy
import Project.ClobMatchFuel.BookReplaceStore

/-!
# Partial-book finalization

The partial-fill branch overwrites the copied maker through five generated
field stores and returns the replacement-book pointer.  The semantic store
facts come from the shared order-replacement proof.
-/

namespace Project.ClobLimit.InternalPartialBookFinish

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalPartialBookCopy
  Project.ClobMatchFuel.BookReplaceStore

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

def partialBookResultFrame (base : Locals) (target : UInt64)
    (totalWords : Nat) : Locals :=
  { partialBookCopyFrame base target totalWords with values := [.i64 target] }

def partialBookFinishProg : Wasm.Program :=
  [
  .localGet 60,
  .localGet 57,
  .constI64 5,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 62,
  .store64 0,
  .localGet 60,
  .localGet 57,
  .constI64 5,
  .mulI64,
  .constI64 2,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 63,
  .store64 0,
  .localGet 60,
  .localGet 57,
  .constI64 5,
  .mulI64,
  .constI64 3,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 64,
  .store64 0,
  .localGet 60,
  .localGet 57,
  .constI64 5,
  .mulI64,
  .constI64 4,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 65,
  .store64 0,
  .localGet 60,
  .localGet 57,
  .constI64 5,
  .mulI64,
  .constI64 5,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 66,
  .store64 0,
  .localGet 60
  ]

set_option Elab.async false in
theorem partialBookFinishProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity qty : UInt64)
    (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hIndexLocal : base.locals[46]? = some (.i64 (UInt64.ofNat i)))
    (hOidLocal : base.locals[51]? = some (.i64 os[i]!.oid))
    (hTraderLocal : base.locals[52]? = some (.i64 os[i]!.otrader))
    (hSideLocal : base.locals[53]? = some (.i64 os[i]!.oside))
    (hPriceLocal : base.locals[54]? = some (.i64 os[i]!.oprice))
    (hQtyLocal : base.locals[55]? = some (.i64 qty))
    (hi : i < os.length)
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hInv : partialBookCopyInv st0 base target source g2 arrayCapacity os st1
      (partialBookCopyFrame base target (os.length * 5)))
    (hBook : OrdersAt st1 target os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone :
      OrdersAt (replaceOrderStore st1 target i os[i]! qty) target
          (Project.ClobMatchFuel.Model.setQtyL os i qty) →
        FreshFixedArrayAt (replaceOrderStore st1 target i os[i]! qty)
          target arrayCapacity 5 →
        MemEqOutsideFlatWords st0
          (replaceOrderStore st1 target i os[i]! qty) target
          (os.length * 5) →
        wp «module» rest Q (replaceOrderStore st1 target i os[i]! qty)
          (partialBookResultFrame base target (os.length * 5)) env) :
    wp «module» (partialBookFinishProg ++ rest) Q st1
      (partialBookCopyFrame base target (os.length * 5)) env := by
  obtain ⟨_, _, _, _, _, hFresh, _, _, hOutside, _⟩ := hInv
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
  have hIndexGet : base.locals[46] = .i64 (UInt64.ofNat i) := by
    apply Option.some.inj
    calc
      some base.locals[46] = base.locals[46]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat i)) := hIndexLocal
  have hOidGet : base.locals[51] = .i64 os[i]!.oid := by
    apply Option.some.inj
    calc
      some base.locals[51] = base.locals[51]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.oid) := hOidLocal
  have hTraderGet : base.locals[52] = .i64 os[i]!.otrader := by
    apply Option.some.inj
    calc
      some base.locals[52] = base.locals[52]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.otrader) := hTraderLocal
  have hSideGet : base.locals[53] = .i64 os[i]!.oside := by
    apply Option.some.inj
    calc
      some base.locals[53] = base.locals[53]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.oside) := hSideLocal
  have hPriceGet : base.locals[54] = .i64 os[i]!.oprice := by
    apply Option.some.inj
    calc
      some base.locals[54] = base.locals[54]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 os[i]!.oprice) := hPriceLocal
  have hQtyGet : base.locals[55] = .i64 qty := by
    apply Option.some.inj
    calc
      some base.locals[55] = base.locals[55]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 qty) := hQtyLocal
  simp only [partialBookFinishProg, partialBookCopyFrame, List.cons_append,
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
  have hOutside1 := MemEqOutsideFlatWords.write64
    (slot := i * 5 + 1) (value := os[i]!.oid) hTarget32 (by omega)
      hOutside
  have hOutside2 := MemEqOutsideFlatWords.write64
    (slot := i * 5 + 2) (value := os[i]!.otrader) hTarget32 (by omega)
      hOutside1
  have hOutside3 := MemEqOutsideFlatWords.write64
    (slot := i * 5 + 3) (value := os[i]!.oside) hTarget32 (by omega)
      hOutside2
  have hOutside4 := MemEqOutsideFlatWords.write64
    (slot := i * 5 + 4) (value := os[i]!.oprice) hTarget32 (by omega)
      hOutside3
  have hOutside5 := MemEqOutsideFlatWords.write64
    (slot := i * 5 + 5) (value := qty) hTarget32 (by omega) hOutside4
  have hOutsideFinal : MemEqOutsideFlatWords st0
      (replaceOrderStore st1 target i os[i]! qty) target
      (os.length * 5) := by
    simpa only [replaceOrderStore] using hOutside5
  simpa only [replaceOrderStore, partialBookResultFrame,
    partialBookCopyFrame, hTotalEq, List.getElem!_eq_getElem?_getD] using
      hDone hBookFinal hFreshFinal hOutsideFinal

end Project.ClobLimit.InternalPartialBookFinish
