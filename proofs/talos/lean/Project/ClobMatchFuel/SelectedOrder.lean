import Project.ClobMatchFuel.Helpers

namespace Project.ClobMatchFuel.SelectedOrder

open Wasm Project.Common Project.Clob Project.ClobMatchFuel

def At (s : Locals) (maker : OrderL) : Prop :=
  s.locals[25]? = some (.i64 maker.oid) ∧
  s.locals[26]? = some (.i64 maker.otrader) ∧
  s.locals[27]? = some (.i64 maker.oside) ∧
  s.locals[28]? = some (.i64 maker.oprice) ∧
  s.locals[29]? = some (.i64 maker.oqty)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def loadProg : Wasm.Program :=
  [
  .localGet 15,
  .localSet 76,
  .localGet 33,
  .localSet 77,
  .localGet 77,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 76,
    .localGet 77,
    .constI64 5,
    .mulI64,
    .constI64 1,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [.unreachable] [] [.i64],
  .localSet 34,
  .localGet 15,
  .localSet 76,
  .localGet 33,
  .localSet 77,
  .localGet 77,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 76,
    .localGet 77,
    .constI64 5,
    .mulI64,
    .constI64 2,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [.unreachable] [] [.i64],
  .localSet 35,
  .localGet 15,
  .localSet 76,
  .localGet 33,
  .localSet 77,
  .localGet 77,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 76,
    .localGet 77,
    .constI64 5,
    .mulI64,
    .constI64 3,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [.unreachable] [] [.i64],
  .localSet 36,
  .localGet 15,
  .localSet 76,
  .localGet 33,
  .localSet 77,
  .localGet 77,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 76,
    .localGet 77,
    .constI64 5,
    .mulI64,
    .constI64 4,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [.unreachable] [] [.i64],
  .localSet 37,
  .localGet 15,
  .localSet 76,
  .localGet 33,
  .localSet 77,
  .localGet 77,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 76,
    .localGet 77,
    .constI64 5,
    .mulI64,
    .constI64 5,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [.unreachable] [] [.i64],
  .localSet 38
  ]

def loadLocals (base : Locals) (book : UInt64) (i : Nat)
    (maker : OrderL) : List Value :=
  let locals := base.locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 25 (.i64 maker.oid)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 26 (.i64 maker.otrader)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 27 (.i64 maker.oside)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 28 (.i64 maker.oprice)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  locals.set 29 (.i64 maker.oqty)

def loadFrame (base : Locals) (book : UInt64) (i : Nat)
    (maker : OrderL) : Locals :=
  { base with locals := loadLocals base book i maker, values := [] }

theorem loadProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hBook : base.get 15 = some (.i64 book))
    (hIndex : base.get 33 = some (.i64 (UInt64.ofNat i)))
    (hi : i < os.length) (hLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st (loadFrame base book i os[i]!) env) :
    wp «module» (loadProg ++ rest) Q st base env := by
  have hBookGet : base.locals[6] = .i64 book := by
    simpa [Locals.get, hParams, hLocals] using hBook
  have hIndexGet : base.locals[24] = .i64 (UInt64.ofNat i) := by
    simpa [Locals.get, hParams, hLocals] using hIndex
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt hLength64]
    exact hi
  have hFieldBound (field : Nat) (hfield : field < 5) :
      (book.toNat + (i * 5 + field + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 := hOrders.orderWord_bound i field hi hfield
  have hFieldRead (field : Nat) (hfield : field < 5) :
      st.mem.read64 (UInt32.ofNat
        ((book.toNat + (i * 5 + field + 1) * 8) % 4294967296)) =
        os[i]!.word field := by
    simpa only [orderWord] using hOrders.orderWord_eq i field hi hfield
  simp only [loadProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr hOrders.1.2), hOrders.1.1, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by decide)]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 0 (by omega))),
    hFieldRead 0 (by omega)]
  simp only [OrderL.word]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr hOrders.1.2), hOrders.1.1, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by decide)]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 1 (by omega))),
    hFieldRead 1 (by omega)]
  simp only [OrderL.word]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr hOrders.1.2), hOrders.1.1, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by decide)]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 2 (by omega))),
    hFieldRead 2 (by omega)]
  simp only [OrderL.word]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr hOrders.1.2), hOrders.1.1, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by decide)]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 3 (by omega))),
    hFieldRead 3 (by omega)]
  simp only [OrderL.word]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr hOrders.1.2), hOrders.1.1, if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by decide)]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  rw [if_neg (Nat.not_lt.mpr (hFieldBound 4 (by omega))),
    hFieldRead 4 (by omega)]
  simp only [OrderL.word]
  wp_run_with [hParams, hLocals, hValues, hBookGet, hIndexGet]
  simpa [loadFrame, loadLocals, List.getElem!_eq_getElem?_getD] using hDone

end Project.ClobMatchFuel.SelectedOrder
