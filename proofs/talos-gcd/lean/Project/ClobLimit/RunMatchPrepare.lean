import Project.ClobLimit.RunMatchEntry
import Interpreter.Wasm.Wp.Tactic

/-!
# `runMatch` argument preparation

Function 18 derives the internal matcher fuel from the represented book
length and copies the remaining arguments into local state.  This module
proves the exact frame and discharges the generated overflow check.
-/

namespace Project.ClobLimit.RunMatchPrepare

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def entryFrame (bookOwner book : UInt64) (taker : OrderL) : Locals :=
  { params :=
      [.i64 bookOwner, .i64 book, .i64 taker.oid, .i64 taker.otrader,
        .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty]
    locals := List.replicate 35 (.i64 0)
    values := [] }

def prepareLocals (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (os : List OrderL) : List Value :=
  let locals := base.locals.set 25 (.i64 book)
  let locals := locals.set 22 (.i64 (UInt64.ofNat os.length))
  let locals := locals.set 23 (.i64 1)
  let locals := locals.set 24 (.i64 (UInt64.ofNat (os.length + 1)))
  let locals := locals.set 0 (.i64 (UInt64.ofNat (os.length + 1)))
  let locals := locals.set 1 (.i64 taker.oid)
  let locals := locals.set 2 (.i64 taker.otrader)
  let locals := locals.set 3 (.i64 taker.oside)
  let locals := locals.set 4 (.i64 taker.oprice)
  let locals := locals.set 5 (.i64 taker.oqty)
  let locals := locals.set 7 (.i64 bookOwner)
  locals.set 8 (.i64 book)

def prepareFrame (bookOwner book : UInt64) (taker : OrderL)
    (os : List OrderL) : Locals :=
  let base := entryFrame bookOwner book taker
  { base with
    locals := prepareLocals base bookOwner book taker os
    values := [] }

set_option Elab.async false in
theorem prepareProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (bookOwner book : UInt64) (taker : OrderL) (os : List OrderL)
    (hLength : os.length < 4294967296)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (prepareFrame bookOwner book taker os) env) :
    wp «module» (RunMatchEntry.prepareProg ++ rest) Q st
      (entryFrame bookOwner book taker) env := by
  have hLengthU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hOutputU : (UInt64.ofNat (os.length + 1)).toNat = os.length + 1 :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hLengthAdd : UInt64.ofNat os.length + 1 =
      UInt64.ofNat (os.length + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hLengthU, size_eq]; omega), hLengthU,
      hOutputU]
  have hNoOverflow : ¬UInt64.ofNat (os.length + 1) <
      UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, hOutputU, hLengthU]
    omega
  have hLengthRead := hOrders.1.1
  have hLengthBound := hOrders.1.2
  simp only [RunMatchEntry.prepareProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, entryFrame]
  rw [if_neg (Nat.not_lt.mpr hLengthBound), hLengthRead]
  rw [hLengthAdd]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simpa using hNoOverflow)]
  wp_run
  exact hNext

end Project.ClobLimit.RunMatchPrepare
