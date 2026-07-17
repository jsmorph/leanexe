import Project.ClobLimit.InternalPartialBookPrepare
import Project.BranchPost

/-!
# Partial-fill book control

The generated bounds branch computes the book payload width before running an
opaque replacement-book update.  The branch returns the new book pointer and
then resumes its surrounding continuation.  This module proves that control
frame without elaborating the allocation and copy body.
-/

namespace Project.ClobLimit.InternalPartialBookControl

open Wasm Project.Clob Project.ClobLimit

def partialBookSuccessProg (updateProg : Wasm.Program) : Wasm.Program :=
  [
  .localGet 58,
  .constI64 5,
  .mulI64,
  .localSet 59
  ] ++ updateProg

def partialBookBranchProg (updateProg : Wasm.Program) : Wasm.Program :=
  InternalPartialBookPrepare.partialBookPrefixProg ++
    [.iff 0 1 (partialBookSuccessProg updateProg) [.unreachable]]

theorem partialBookSuccessProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book remaining : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (updateProg : Wasm.Program) (Q : Assertion Unit)
    (hDone : wp «module» updateProg Q st
      (InternalPartialBookPrepare.partialBookPrepareFrame base book remaining
        os i) env) :
    wp «module» (partialBookSuccessProg updateProg) Q st
      { (InternalPartialBookPrepare.partialBookGuardFrame base book remaining
          os i) with values := [] } env := by
  let guard :=
    { (InternalPartialBookPrepare.partialBookGuardFrame base book remaining
        os i) with values := [] }
  let total := UInt64.ofNat os.length * 5
  have hGet : guard.get 58 = some (.i64 (UInt64.ofNat os.length)) := by
    simp [guard, InternalPartialBookPrepare.partialBookGuardFrame,
      InternalPartialBookPrepare.partialBookGuardLocals, Locals.get, hParams,
      hLocals]
  have hSet :
      ({ guard with values := [.i64 total] }).set? 59 (.i64 total) =
        some { (InternalPartialBookPrepare.partialBookPrepareFrame base book
          remaining os i) with values := [.i64 total] } := by
    simp [guard, total,
      InternalPartialBookPrepare.partialBookGuardFrame,
      InternalPartialBookPrepare.partialBookGuardLocals,
      InternalPartialBookPrepare.partialBookPrepareFrame,
      InternalPartialBookPrepare.partialBookPrepareLocals, Locals.set?,
      hParams, hLocals]
  simp only [partialBookSuccessProg, List.cons_append, List.nil_append]
  change wp «module»
    (.localGet 58 :: .constI64 5 :: .mulI64 :: .localSet 59 :: updateProg)
    Q st guard env
  simp only [wp_localGet_cons, hGet, wp_constI64_cons, wp_mulI64_cons]
  change wp «module» (.localSet 59 :: updateProg) Q st
    { guard with values := [.i64 total] } env
  simp only [wp_localSet_cons, hSet]
  change wp «module» updateProg Q st
    { (InternalPartialBookPrepare.partialBookPrepareFrame base book remaining
        os i) with values := [] } env
  rw [Project.BranchPost.withValues_eq_self _ [] rfl]
  exact hDone

set_option Elab.async false in
theorem partialBookBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book remaining : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hBookLocal : base.params[7]? = some (.i64 book))
    (hIndexLocal : base.locals[14]? = some (.i64 (UInt64.ofNat i)))
    (hRemainingLocal : base.params[10]? = some (.i64 remaining))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st book os)
    (updateProg : Wasm.Program) (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» updateProg
      (Project.BranchPost.oneResultIffPost «module» env rest Q) st
      (InternalPartialBookPrepare.partialBookPrepareFrame base book remaining
        os i) env) :
    wp «module» (partialBookBranchProg updateProg ++ rest) Q st base env := by
  unfold partialBookBranchProg
  rw [List.append_assoc]
  apply InternalPartialBookPrepare.partialBookPrefixProg_spec env st base book
    remaining os i hParams hLocals hValues hBookLocal hIndexLocal
    hRemainingLocal hi hOrdersLength64 hOrders Q
      (.iff 0 1 (partialBookSuccessProg updateProg) [.unreachable] :: rest)
  apply Project.BranchPost.trueOneResultIff «module» env st
  · rfl
  apply partialBookSuccessProg_spec env st base book remaining os i hParams
    hLocals updateProg
  exact hDone

end Project.ClobLimit.InternalPartialBookControl
