import Project.ClobLimit.LimitEntry
import Project.ClobLimit.ValidOrder

/-!
# Valid `limit` entry frame

The exported function copies its six parameters, calls the validity helper,
and leaves the valid-path condition on the operand stack.  This theorem ends
at that call boundary before either result branch enters elaboration.
-/

namespace Project.ClobLimit.LimitValidEntry

open Wasm Project.Clob Project.ClobLimit Project.ClobPostOnly.Model
  Project.ClobPostOnly.SearchHelpers

def validFrame (book : UInt64) (order : OrderL) : Locals :=
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1] ++
        List.replicate 45 (.i64 0)
    values := [.i32 1] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem entryProg_valid_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (os : List OrderL) (order : OrderL)
    (hLength : os.length < 4294967296)
    (hOrders : OrdersAt st book os)
    (hValid : validOrderL os order)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (validFrame book order) env) :
    wp «module» (LimitEntry.entryProg ++ rest) Q st
      (LimitEntry.entryFrame book order) env := by
  simp only [LimitEntry.entryProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, LimitEntry.entryFrame, LimitEntry.limitArgs, func21Def,
      Function.toLocals]
  refine wp_call_tw
    (ValidOrder.func6_spec env st book os order hLength hOrders) ?_
  rintro st1 values ⟨rfl, rfl⟩
  simp only [boolWord, if_pos hValid]
  wp_run
  simp
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run
  simpa [validFrame] using hNext

end Project.ClobLimit.LimitValidEntry
