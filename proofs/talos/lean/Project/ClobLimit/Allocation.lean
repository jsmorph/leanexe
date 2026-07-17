import Project.ClobLimit.Program
import Project.Clob
import Interpreter.Wasm.Wp.Call

/-!
# Allocation facts for `limit`

The invalid and filled branches return constant status words and an empty
trade array.  These definitions name that result shape and prove the generated
constant helpers.
-/

namespace Project.ClobLimit.Allocation

open Wasm Project.Clob Project.ClobLimit

abbrev FreshTradeArrayAt (st : Store Unit) (ptr : UInt64) : Prop :=
  FreshFixedArrayAt st ptr 8 4 ∧
  st.mem.read64 ptr.toUInt32 = 0

theorem func19_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 19) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 0] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func19Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func19 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func19
    wp_run
    simp [func19Def]

theorem func20_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 20) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 1] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func20Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func20 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func20
    wp_run
    simp [func20Def]

end Project.ClobLimit.Allocation
