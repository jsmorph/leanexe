import Project.ClobMatchFuel.PartialBookPrepare
import Project.ClobMatchFuel.BranchPost

/-!
# Partial-fill book control

The generated bounds branch computes the book payload width before running the
replacement-book update.  The branch returns the new book pointer and then
continues with the trade update.  This module composes that control frame while
keeping the replacement-book program opaque to the preparation proof.
-/

namespace Project.ClobMatchFuel.PartialBookControl

open Wasm Project.Clob Project.ClobMatchFuel

def partialBookSuccessProg : Wasm.Program :=
  [
  .localGet 68,
  .constI64 5,
  .mulI64,
  .localSet 69
  ] ++ PartialBookUpdate.partialBookUpdateProg

def partialBookBranchProg : Wasm.Program :=
  PartialBookPrepare.partialBookPrefixProg ++
    [.iff 0 1 partialBookSuccessProg [.unreachable]]

theorem partialBookSuccessProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book remaining : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (Q : Assertion Unit)
    (hDone : wp «module» PartialBookUpdate.partialBookUpdateProg Q st
      (PartialBookPrepare.partialBookPrepareFrame base book remaining os i) env) :
    wp «module» partialBookSuccessProg Q st
      { (PartialBookPrepare.partialBookGuardFrame base book remaining os i) with
        values := [] } env := by
  let guard :=
    { (PartialBookPrepare.partialBookGuardFrame base book remaining os i) with
      values := [] }
  let total := UInt64.ofNat os.length * 5
  have hGet : guard.get 68 = some (.i64 (UInt64.ofNat os.length)) := by
    simp [guard, PartialBookPrepare.partialBookGuardFrame,
      PartialBookPrepare.partialBookGuardLocals, Locals.get, hParams, hLocals]
  have hSet :
      ({ guard with values := [.i64 total] }).set? 69 (.i64 total) =
        some { (PartialBookPrepare.partialBookPrepareFrame base book remaining
          os i) with values := [.i64 total] } := by
    simp [guard, total, PartialBookPrepare.partialBookGuardFrame,
      PartialBookPrepare.partialBookGuardLocals,
      PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, Locals.set?, hParams,
      hLocals]
  simp only [partialBookSuccessProg, List.cons_append, List.nil_append]
  change wp «module»
    (.localGet 68 :: .constI64 5 :: .mulI64 :: .localSet 69 ::
      PartialBookUpdate.partialBookUpdateProg) Q st guard env
  simp only [wp_localGet_cons, hGet, wp_constI64_cons, wp_mulI64_cons]
  change wp «module» (.localSet 69 :: PartialBookUpdate.partialBookUpdateProg)
    Q st { guard with values := [.i64 total] } env
  simp only [wp_localSet_cons, hSet]
  change wp «module» PartialBookUpdate.partialBookUpdateProg Q st
    { (PartialBookPrepare.partialBookPrepareFrame base book remaining os i) with
      values := [] } env
  rw [BranchPost.withValues_eq_self _ [] rfl]
  exact hDone

set_option Elab.async false in
theorem partialBookBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book remaining : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hBookLocal : base.locals[6]? = some (.i64 book))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st book os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» PartialBookUpdate.partialBookUpdateProg
      (BranchPost.oneResultIffPost env rest Q) st
      (PartialBookPrepare.partialBookPrepareFrame base book remaining os i) env) :
    wp «module» (partialBookBranchProg ++ rest) Q st base env := by
  unfold partialBookBranchProg
  rw [List.append_assoc]
  apply PartialBookPrepare.partialBookPrefixProg_spec env st base book remaining
    os i hParams hLocals hValues hBookLocal hIndexLocal hRemainingLocal hi
    hOrdersLength64 hOrders Q
      (.iff 0 1 partialBookSuccessProg [.unreachable] :: rest)
  apply BranchPost.trueOneResultIff env st
  · rfl
  apply partialBookSuccessProg_spec env st base book remaining os i hParams
    hLocals
  exact hDone

end Project.ClobMatchFuel.PartialBookControl
