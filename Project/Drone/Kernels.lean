import Project.Drone.Module
import Project.IR.Correct
import Project.IR.Run
import Project.IR.Loop
import Project.Drone.Sqrt

/-! The compiled scalar functions of the drone planner compute their Lean definitions. -/

namespace Project.Drone

open Wasm Project.Pipeline Project.IR LeanExe.Examples.Drone

/-! Words of Bool tests: the compiler computes `a && b` and `a || b` as the bitwise and and or
of two words that are 0 or 1, and tests the result against 1. -/

theorem word_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_or (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) ||| if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) = 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

/-- The IR's division and remainder test the divisor for 0, where Lean's give 0 and the
dividend. -/
theorem divU_eq (a b : UInt64) : (if b = 0 then 0 else a / b) = a / b := by
  split <;> simp_all

theorem remU_eq (a b : UInt64) : (if b = 0 then a else a % b) = a % b := by
  split <;> simp_all

/-- The lemmas that evaluate the expressions and statements of a compiled body. -/
macro "eval_drone" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
    Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get, State.update,
    State.setAll, U64Op.apply, Scalar.values, ScalarType.valueType, Expr.evalResults,
    ScalarType.value, Flat.flat, divU_eq, remU_eq, word_and, word_or, word_eq_one, $args,*])

def distanceTuple : UInt64 × UInt64 → UInt64 := fun (a, b) => distance a b

theorem distance_implements {a : Bool} : ImplementsPureA a drone.module 2 distanceTuple :=
  Func.implementsPureA drone.funcs 0 drone.distance.ir "distance" rfl distanceTuple
    (fun _ => rfl) fun ⟨x, y⟩ initial => by
      refine Stmt.run_triple ?_
      eval_drone [drone.distance.ir, distanceTuple, distance]

def altitudeTuple : UInt64 × UInt64 → UInt64 := fun (floor, state) => altitude floor state

theorem altitude_implements {a : Bool} : ImplementsPureA a drone.module 3 altitudeTuple :=
  Func.implementsPureA drone.funcs 1 drone.altitude.ir "altitude" rfl altitudeTuple
    (fun _ => rfl) fun ⟨floor, state⟩ initial => by
      refine Stmt.run_triple ?_
      eval_drone [drone.altitude.ir, altitudeTuple, altitude]

theorem speed_implements {a : Bool} : ImplementsPureA a drone.module 4 speed :=
  Func.implementsPureA drone.funcs 2 drone.speed.ir "speed" rfl speed
    (fun _ => rfl) fun state initial => by
      refine Stmt.run_triple ?_
      eval_drone [drone.speed.ir, speed]

set_option maxHeartbeats 4000000 in
theorem ceilSqrt_implements {a : Bool} : ImplementsPureA a drone.module 5 ceilSqrt :=
  Func.implementsPureA drone.funcs 3 drone.ceilSqrt.ir "ceilSqrt" rfl ceilSqrt
    (fun _ => rfl) fun n initial => by
      refine Stmt.seq_run ?_
      eval_drone [drone.ceilSqrt.ir]
      refine Stmt.seq_run ?_
      eval_drone []
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

theorem max_word (a b : UInt64) : max a b = if a ≤ b then b else a := rfl

theorem restSeconds_implements {a : Bool} : ImplementsPureA a drone.module 6 restSeconds :=
  Func.implementsPureA drone.funcs 4 drone.restSeconds.ir "restSeconds" rfl restSeconds
    (fun _ => rfl) fun dh initial => by
      have hC := ceilSqrt_implements (a := a)
      refine Stmt.seq_callPure hC rfl rfl rfl (x := (3 * dh + 1) / 2) ?_
      eval_drone [drone.restSeconds.ir]
      refine Stmt.run_triple ?_
      eval_drone [restSeconds, max_word]

def edgeTicksTuple : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → UInt64 :=
  fun (r0, r1, z0, z1, u, v) => edgeTicks r0 r1 z0 z1 u v

set_option maxHeartbeats 4000000 in
theorem edgeTicks_implements {a : Bool} : ImplementsPureA a drone.module 7 edgeTicksTuple :=
  Func.implementsPureA drone.funcs 5 drone.edgeTicks.ir "edgeTicks" rfl edgeTicksTuple
    (fun _ => rfl) fun ⟨r0, r1, z0, z1, u, v⟩ initial => by
      have hD := distance_implements (a := a)
      have hR := restSeconds_implements (a := a)
      refine Stmt.seq_callPure hD rfl rfl rfl (x := (z0, z1)) ?_
      eval_drone [drone.edgeTicks.ir]
      refine Stmt.seq_run ?_
      eval_drone []
      refine Stmt.seq_callPure hD rfl rfl rfl (x := (u * u, v * v)) ?_
      eval_drone [distanceTuple]
      refine Stmt.seq_run ?_
      eval_drone []
      refine Stmt.seq_callPure hR rfl rfl rfl (x := distance z0 z1) ?_
      eval_drone [distanceTuple]
      refine Stmt.seq_run ?_
      eval_drone []
      refine Stmt.seq_run ?_
      eval_drone []
      refine Stmt.run_triple ?_
      eval_drone [edgeTicksTuple, edgeTicks, distanceTuple]
      simp only [← UInt64.not_lt]
      split_ifs <;> first | rfl | (exfalso; tauto)

end Project.Drone
