import Project.ClobCancel.Scan
import Interpreter.Wasm.Wp.Call

/-!
# The `cancel` theorem

`func3` scans once for the argument id and records the first matching index
plus one.  An absent id returns status three and the borrowed input pointer.
The found branch allocates a fresh array and copies every other order.
-/

namespace Project.ClobCancel.Spec

open Wasm Project.Common Project.ClobQuote.Step Project.ClobQuote.Spec
  Project.ClobCancel

set_option maxHeartbeats 64000000

theorem func1_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 0] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func1
    wp_run
    simp [func1Def]

theorem func2_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 2) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 3] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func2 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func2
    wp_run
    simp [func2Def]

/-- Canceling an absent id returns status three and the borrowed input
pointer, leaving the store unchanged. -/
@[spec_of "lean" "LeanExe.Examples.Clob.cancel"]
def CancelNotFoundSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr cid : UInt64)
    (os : List OrderL),
    os.length < 4294967296 →
    OrdersAt st ptr os →
    idIdx os cid = none →
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 cid, .i64 ptr]
      (fun st' vs => vs = [.i64 ptr, .i64 3] ∧ st' = st)

@[proves Project.ClobCancel.Spec.CancelNotFoundSpec]
theorem cancel_notFound : CancelNotFoundSpec := by
  intro env st ptr cid os hlen hIn hAbsent
  have hHead := hIn.1.1
  have hHeadB := hIn.1.2
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st
      { params := [.i64 ptr, .i64 cid],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func3
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine scanIndex_spec os hlen hIn ?_ ?_
    · intro _h f2 f3 f4 f5 f6
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      simp
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      refine wp_call_tw (func2_spec env st) ?_
      rintro st' vs ⟨rfl, rfl⟩
      wp_run
      simp [func3Def]
    · intro i hi
      rw [hAbsent] at hi
      cases hi

end Project.ClobCancel.Spec
