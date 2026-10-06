import Examples.Drone.Module
import Project.IR.Correct
import Project.IR.Run
import Project.IR.Words
import Project.IR.Loop
import Examples.Drone.Sqrt

/-! The compiled scalar functions of the drone planner compute their Lean definitions. -/

namespace Examples.Drone

open Wasm Project.Pipeline Project.IR Examples.Drone

def distanceTuple : UInt64 × UInt64 → UInt64 := fun (a, b) => distance a b

theorem distance_implements {a : Bool} : ImplementsPureA a drone.module 2 distanceTuple :=
  Func.implementsPureA drone.funcs 0 drone.distance.ir "distance" rfl distanceTuple
    (fun _ => rfl) fun ⟨x, y⟩ initial => by
      refine Stmt.run_triple ?_
      eval_body [drone.distance.ir, distanceTuple, distance]

def altitudeTuple : UInt64 × UInt64 → UInt64 := fun (floor, state) => altitude floor state

theorem altitude_implements {a : Bool} : ImplementsPureA a drone.module 3 altitudeTuple :=
  Func.implementsPureA drone.funcs 1 drone.altitude.ir "altitude" rfl altitudeTuple
    (fun _ => rfl) fun ⟨floor, state⟩ initial => by
      refine Stmt.run_triple ?_
      eval_body [drone.altitude.ir, altitudeTuple, altitude]

theorem speed_implements {a : Bool} : ImplementsPureA a drone.module 4 speed :=
  Func.implementsPureA drone.funcs 2 drone.speed.ir "speed" rfl speed
    (fun _ => rfl) fun state initial => by
      refine Stmt.run_triple ?_
      eval_body [drone.speed.ir, speed]

set_option maxHeartbeats 4000000 in
theorem ceilSqrt_implements {a : Bool} : ImplementsPureA a drone.module 5 ceilSqrt :=
  Func.implementsPureA drone.funcs 3 drone.ceilSqrt.ir "ceilSqrt" rfl ceilSqrt
    (fun _ => rfl) fun n initial => by
      refine Stmt.seq_run ?_
      eval_body [drone.ceilSqrt.ir]
      refine Stmt.seq_run ?_
      eval_body []
      refine (Stmt.loop_spec (vars := [1, 2]) (writes := [1, 2, 5, 6, 7])
        (init := ((0 : UInt64), (65536 : UInt64))) (n := 17) (sqrtStep n)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) ⟨_, rfl⟩
        (by simp [State.Holds, Scalar.values, State.get]) ?_).mono (fun _ _ h => h) ?_
      · rintro k ⟨lo, hi⟩ state hk hFrame hHolds hIndex hLimit
        have hLength : state.params.length + state.locals.length = 10 := by
          rw [hFrame.params, hFrame.locals]; rfl
        have h0 : state.get 0 = some (.i64 n) := (hFrame.get 0 (by decide) (by decide)).trans rfl
        have h12 : state.get 1 = some (.i64 lo) ∧ state.get 2 = some (.i64 hi) := by
          simpa [State.Holds, Scalar.values] using hHolds
        refine Stmt.run_triple ?_
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hLength, U64Op.apply, divU_eq, word_and,
          h0, h12.1, h12.2, ScalarType.value]
        refine ⟨?_, ?_⟩
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · simp [State.Holds, Scalar.values, sqrtStep, hLength]
      · rintro store state ⟨rfl, -, hHolds⟩
        have h1 : state.get 1 = some (.i64 (ceilSqrt n)) := by
          rw [ceilSqrt_loop]
          exact (by simpa [State.Holds, Scalar.values] using hHolds :
            _ ∧ state.get 2 = _).1
        simp only [State.get] at h1
        exact ⟨rfl, state, by simp [h1]⟩

theorem restSeconds_implements {a : Bool} : ImplementsPureA a drone.module 6 restSeconds :=
  Func.implementsPureA drone.funcs 4 drone.restSeconds.ir "restSeconds" rfl restSeconds
    (fun _ => rfl) fun dh initial => by
      have hC := ceilSqrt_implements (a := a)
      refine Stmt.seq_callPure hC rfl rfl rfl (x := (3 * dh + 1) / 2) ?_
      eval_body [drone.restSeconds.ir]
      refine Stmt.run_triple ?_
      eval_body [restSeconds, max_word]

def edgeTicksTuple : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → UInt64 :=
  fun (r0, r1, z0, z1, u, v) => edgeTicks r0 r1 z0 z1 u v

set_option maxHeartbeats 4000000 in
theorem edgeTicks_implements {a : Bool} : ImplementsPureA a drone.module 7 edgeTicksTuple :=
  Func.implementsPureA drone.funcs 5 drone.edgeTicks.ir "edgeTicks" rfl edgeTicksTuple
    (fun _ => rfl) fun ⟨r0, r1, z0, z1, u, v⟩ initial => by
      have hD := distance_implements (a := a)
      have hR := restSeconds_implements (a := a)
      refine Stmt.seq_callPure hD rfl rfl rfl (x := (z0, z1)) ?_
      eval_body [drone.edgeTicks.ir]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_callPure hD rfl rfl rfl (x := (u * u, v * v)) ?_
      eval_body [distanceTuple]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_callPure hR rfl rfl rfl (x := distance z0 z1) ?_
      eval_body [distanceTuple]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.run_triple ?_
      eval_body [edgeTicksTuple, edgeTicks, distanceTuple]
      simp only [← UInt64.not_lt]
      split_ifs <;> first | rfl | (exfalso; tauto)

end Examples.Drone
