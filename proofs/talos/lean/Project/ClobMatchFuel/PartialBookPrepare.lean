import Project.ClobMatchFuel.SelectedMaker
import Project.ClobMatchFuel.PartialBookUpdate

/-!
# Partial-fill book preparation

The partial-fill branch reads the selected maker before allocating a
replacement book.  It computes the reduced maker quantity and prepares the
book allocator's source, length, and copy locals.  This module proves that
instruction bridge against the represented source book.
-/

namespace Project.ClobMatchFuel.PartialBookPrepare

open Wasm Project.Common Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576


def partialBookPrefixProg : Wasm.Program :=
  [
  .localGet 15,
  .localSet 71,
  .localGet 33,
  .localSet 72,
  .localGet 71,
  .localSet 76,
  .localGet 72,
  .localSet 77,
  .localGet 34,
  .localSet 82,
  .localGet 35,
  .localSet 83,
  .localGet 36,
  .localSet 84,
  .localGet 37,
  .localSet 85,
  .localGet 38,
  .localGet 18,
  .subI64,
  .localSet 86,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .localSet 78,
  .localGet 77,
  .localGet 78,
  .ltUI64
  ]

def partialBookPrepareLocals (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 62 (.i64 book)
  let locals := locals.set 63 (.i64 (UInt64.ofNat i))
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 73 (.i64 os[i]!.oid)
  let locals := locals.set 74 (.i64 os[i]!.otrader)
  let locals := locals.set 75 (.i64 os[i]!.oside)
  let locals := locals.set 76 (.i64 os[i]!.oprice)
  let locals := locals.set 77 (.i64 (os[i]!.oqty - remaining))
  let locals := locals.set 69 (.i64 (UInt64.ofNat os.length))
  locals.set 70 (.i64 (UInt64.ofNat os.length * 5))

def partialBookPrepareFrame (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with
    locals := partialBookPrepareLocals base book remaining os i
    values := [] }

def partialBookGuardLocals (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : List Value :=
  let locals := base.locals.set 62 (.i64 book)
  let locals := locals.set 63 (.i64 (UInt64.ofNat i))
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 73 (.i64 os[i]!.oid)
  let locals := locals.set 74 (.i64 os[i]!.otrader)
  let locals := locals.set 75 (.i64 os[i]!.oside)
  let locals := locals.set 76 (.i64 os[i]!.oprice)
  let locals := locals.set 77 (.i64 (os[i]!.oqty - remaining))
  locals.set 69 (.i64 (UInt64.ofNat os.length))

def partialBookGuardFrame (base : Locals) (book remaining : UInt64)
    (os : List OrderL) (i : Nat) : Locals :=
  { base with
    locals := partialBookGuardLocals base book remaining os i
    values := [.i32 1] }

set_option Elab.async false in
theorem partialBookPrefixProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book remaining : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hBookLocal : base.locals[6]? = some (.i64 book))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hSelected : SelectedMaker.At base os[i]!)
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (partialBookGuardFrame base book remaining os i) env) :
    wp «module» (partialBookPrefixProg ++ rest) Q st base env := by
  obtain ⟨hId, hTrader, hSide, hPrice, hQty⟩ := hSelected
  have hId' := getElem_of_some hId
  have hTrader' := getElem_of_some hTrader
  have hSide' := getElem_of_some hSide
  have hPrice' := getElem_of_some hPrice
  have hQty' := getElem_of_some hQty
  have hBook' := getElem_of_some hBookLocal
  have hIndex' := getElem_of_some hIndexLocal
  have hRemaining' := getElem_of_some hRemainingLocal
  have hHead := hOrders.1.1
  have hSafe := Nat.not_lt.mpr hOrders.1.2
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt hOrdersLength64]
    exact hi
  simp only [partialBookPrefixProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hId', hTrader', hSide', hPrice', hQty',
    hBook', hIndex', hRemaining', hHead, hSafe, hIndexLt]
  simpa only [partialBookGuardFrame, partialBookGuardLocals,
    List.getElem!_eq_getElem?_getD] using hDone

#print axioms partialBookPrefixProg_spec
end Project.ClobMatchFuel.PartialBookPrepare
