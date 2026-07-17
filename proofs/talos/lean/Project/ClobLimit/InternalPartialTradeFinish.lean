import Project.ClobLimit.InternalPartialTradeCopy
import Project.ClobMatchFuel.TradeAppendStore

/-!
# Partial-trade finalization

The partial-fill branch appends four prepared trade fields and returns the new
trade-array pointer.  The semantic store facts come from the shared append
proof.
-/

namespace Project.ClobLimit.InternalPartialTradeFinish

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalPartialTradeCopy
  Project.ClobMatchFuel.TradeAppendStore

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_finish" "(" hParams:term "," hLocals:term ","
    hLength:term "," hTaker:term "," hMaker:term ","
    hPrice:term "," hQty:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hLength),
    ($hTaker), ($hMaker), ($hPrice), ($hQty)])

def partialTradeResultFrame (base : Locals) (target : UInt64)
    (totalWords : Nat) : Locals :=
  { partialTradeCopyFrame base target totalWords with values := [.i64 target] }

def partialTradeFinishProg : Wasm.Program :=
  [
  .localGet 60,
  .localGet 57,
  .constI64 4,
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
  .constI64 4,
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
  .constI64 4,
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
  .constI64 4,
  .mulI64,
  .constI64 4,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 65,
  .store64 0,
  .localGet 60
  ]

set_option Elab.async false in
theorem partialTradeFinishProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity : UInt64)
    (ts : List TradeL) (trade : TradeL)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hLengthLocal : base.locals[46]? =
      some (.i64 (UInt64.ofNat ts.length)))
    (hTakerLocal : base.locals[51]? = some (.i64 trade.ttakerId))
    (hMakerLocal : base.locals[52]? = some (.i64 trade.tmakerId))
    (hPriceLocal : base.locals[53]? = some (.i64 trade.tprice))
    (hQtyLocal : base.locals[54]? = some (.i64 trade.tqty))
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat + ((ts.length + 1) * 4 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + ((ts.length + 1) * 4 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hSource : TradesAt st0 source ts)
    (hInv : partialTradeCopyInv st0 base target source g2 arrayCapacity
      (UInt64.ofNat (ts.length + 1)) ts st1
        (partialTradeCopyFrame base target (ts.length * 4)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone :
      TradesAt (appendTradeStore st1 target ts.length trade) target
          (ts ++ [trade]) →
        FreshFixedArrayAt (appendTradeStore st1 target ts.length trade)
          target arrayCapacity 4 →
        MemEqOutsideFlatWords st0
          (appendTradeStore st1 target ts.length trade) target
          ((ts.length + 1) * 4) →
        wp «module» rest Q (appendTradeStore st1 target ts.length trade)
          (partialTradeResultFrame base target (ts.length * 4)) env) :
    wp «module» (partialTradeFinishProg ++ rest) Q st1
      (partialTradeCopyFrame base target (ts.length * 4)) env := by
  obtain ⟨word, hword, hFrame, hPages, _, hFresh, hLength, _, hOutside,
    hCopied⟩ := hInv
  have hTotal64 : ts.length * 4 < UInt64.size := by
    change ts.length * 4 < 18446744073709551616
    omega
  have hLength64 : ts.length < UInt64.size := by
    change ts.length < 18446744073709551616
    omega
  have hWordU : UInt64.ofNat ts.length * 4 = UInt64.ofNat word := by
    have h := congrArg (fun s : Locals => s.locals[50]?) hFrame
    simpa [partialTradeCopyFrame, hLocals] using h
  have hWordEq : word = ts.length * 4 := by
    have h := congrArg UInt64.toNat hWordU
    rw [UInt64.toNat_mul, toNat_ofNat_lt hLength64,
      show (4 : UInt64).toNat = 4 by rfl, Nat.mod_eq_of_lt hTotal64,
      toNat_ofNat_lt (by omega)] at h
    omega
  subst word
  have hTotalEq : UInt64.ofNat (ts.length * 4) =
      UInt64.ofNat ts.length * 4 := by
    apply UInt64.toNat.inj
    rw [toNat_ofNat_lt hTotal64, UInt64.toNat_mul,
      toNat_ofNat_lt hLength64]
    have h4 : (4 : UInt64).toNat = 4 := rfl
    rw [h4, Nat.mod_eq_of_lt hTotal64]
  have hLengthGet : base.locals[46] = .i64 (UInt64.ofNat ts.length) := by
    apply Option.some.inj
    calc
      some base.locals[46] = base.locals[46]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat ts.length)) := hLengthLocal
  have hTakerGet : base.locals[51] = .i64 trade.ttakerId := by
    apply Option.some.inj
    calc
      some base.locals[51] = base.locals[51]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.ttakerId) := hTakerLocal
  have hMakerGet : base.locals[52] = .i64 trade.tmakerId := by
    apply Option.some.inj
    calc
      some base.locals[52] = base.locals[52]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.tmakerId) := hMakerLocal
  have hPriceGet : base.locals[53] = .i64 trade.tprice := by
    apply Option.some.inj
    calc
      some base.locals[53] = base.locals[53]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.tprice) := hPriceLocal
  have hQtyGet : base.locals[54] = .i64 trade.tqty := by
    apply Option.some.inj
    calc
      some base.locals[54] = base.locals[54]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 trade.tqty) := hQtyLocal
  simp only [partialTradeFinishProg, partialTradeCopyFrame, List.cons_append,
    List.nil_append]
  wp_run_finish (hParams, hLocals, hLengthGet, hTakerGet, hMakerGet,
    hPriceGet, hQtyGet)
  try simp
  have hBound (field : Nat) (hfield : field < 4) :
      (target.toNat + (ts.length * 4 + field + 1) * 8) % 4294967296 + 8 ≤
        st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), hPages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hBound 0 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 1 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 2 (by omega))),
    if_neg (Nat.not_lt.mpr (hBound 3 (by omega)))]
  have hTradesFinal := tradesAt_appendTradeStore st1 target ts trade
    hTarget32 (by simpa only [toUInt32_eq_ofNat] using hLength) (by
      rw [Nat.mod_eq_of_lt (by omega), hPages]
      omega)
    (by
      intro j hj field hfield
      exact (hCopied (j * 4 + field) (by omega)).trans
        (hSource.tradeWord_eq j field hj hfield))
    (by
      intro j hj field hfield
      rw [Nat.mod_eq_of_lt (by omega), hPages]
      omega)
  have hFreshFinal := freshTradeArrayAt_appendTradeStore st1 target
    arrayCapacity ts.length trade hTarget48 hTarget32 hFresh
  have hOutside1 := MemEqOutsideFlatWords.write64
    (slot := ts.length * 4 + 1) (value := trade.ttakerId) hTarget32
      (by omega) hOutside
  have hOutside2 := MemEqOutsideFlatWords.write64
    (slot := ts.length * 4 + 2) (value := trade.tmakerId) hTarget32
      (by omega) hOutside1
  have hOutside3 := MemEqOutsideFlatWords.write64
    (slot := ts.length * 4 + 3) (value := trade.tprice) hTarget32
      (by omega) hOutside2
  have hOutside4 := MemEqOutsideFlatWords.write64
    (slot := ts.length * 4 + 4) (value := trade.tqty) hTarget32
      (by omega) hOutside3
  have hOutsideFinal : MemEqOutsideFlatWords st0
      (appendTradeStore st1 target ts.length trade) target
      ((ts.length + 1) * 4) := by
    simpa only [appendTradeStore] using hOutside4
  simpa only [appendTradeStore, partialTradeResultFrame,
    partialTradeCopyFrame, hTotalEq] using
      hDone hTradesFinal hFreshFinal hOutsideFinal

end Project.ClobLimit.InternalPartialTradeFinish
