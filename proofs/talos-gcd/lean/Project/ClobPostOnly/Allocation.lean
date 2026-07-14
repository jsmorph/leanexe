import Project.ClobPostOnly.Program
import Project.Clob
import Interpreter.Wasm.Wp.Call

/-!
# Allocation facts for `postOnly`

The public export returns fixed-width order and trade arrays.  This module
specializes the shared header predicate to their strides and proves the three
constant status helpers.  The instruction proof uses these facts for every
public result branch.
-/

namespace Project.ClobPostOnly.Allocation

open Wasm Project.Clob Project.ClobPostOnly

abbrev orderArrayBytes (n : Nat) : Nat :=
  fixedArrayBytes n 5

abbrev orderArrayBytesU (n : Nat) : UInt64 :=
  fixedArrayBytesU n 5

abbrev FreshOrderArrayAt (st : Store Unit) (ptr capacity : UInt64) : Prop :=
  FreshFixedArrayAt st ptr capacity 5

abbrev FreshTradeArrayAt (st : Store Unit) (ptr : UInt64) : Prop :=
  FreshFixedArrayAt st ptr 8 4 ∧
  st.mem.read64 ptr.toUInt32 = 0

theorem func14_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 14) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 2] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func14 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func14
    wp_run
    simp [func14Def]

theorem func15_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 15) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 0] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func15 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func15
    wp_run
    simp [func15Def]

theorem func16_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 16) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 1] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func16Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func16 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func16
    wp_run
    simp [func16Def]

end Project.ClobPostOnly.Allocation
