import Project.Drone.Rows
import Project.Drone.Forward
import Project.IR.Read
import Project.IR.OneArray

/-! The compiled functions of the drone planner's forward pass compute their Lean definitions. -/

namespace Project.Drone

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Drone

/-- One step of `validHeights`'s loop. -/
def validStep (terrain : Array UInt64) (i : UInt64) (ok : Bool) : Bool :=
  ok && decide (terrain[i.toNat]! ≤ 1000000)

set_option maxHeartbeats 4000000 in
theorem validHeights_implementsA {a : Bool} :
    ImplementsA a drone.module 12 validHeights (fun _ _ _ => True)
      (fun _ heap store heap' final => heap' = heap ∧ final = store) := by
  refine Func.implementsA drone.funcs 10 drone.validHeights.ir "validHeights" rfl validHeights _
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro terrain heap initial _ - - ⟨ptr, rfl, hT⟩
  have hW := hT.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  set start := drone.validHeights.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat terrain.size))
  let s2 := s1.update 2 (.i64 1)
  show TripleA _ _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.const 1))
    (.loop 3 4 (.get 1) _))) 6 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  have hS2 : s2.params.length + s2.locals.length = 7 := by simp [s2, s1, hStart]
  refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5]) (init := true)
    (n := terrain.size.toUInt64) (validStep terrain) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega)
    ⟨s2, by simp [Expr.eval, s2, s1, hStart, State.get_update_ne, Nat.toUInt64]⟩
    (by simp [State.Holds, Scalar.values, Flat.flat, s2, s1, hStart]) ?_).mono
      (fun _ _ h => h) ?_
  · intro i ok state hi hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 7 := by
      rw [hFrame.params, hFrame.locals]; exact hS2
    have hS0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have hOk : state.get 2 = some (.i64 (cond ok 1 0)) := by
      simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
    have hRd : ∀ (k : UInt64) (st : State), st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 k st = some (terrain[k.toNat]!, st) :=
      fun _ _ h => Expr.readValue_at hW h
    refine Stmt.run_triple ?_
    eval_state [hLength, hIndex, hS0, hOk, hRd]
    refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, validStep]
  · rintro store state ⟨rfl, -, hHolds⟩
    refine ⟨rfl, _, state, ?_, rfl⟩
    have g2 : state.get 2 = some (.i64 (cond (validHeights terrain) 1 0)) := by
      rw [show validHeights terrain = LeanExe.loop terrain.size.toUInt64 true (validStep terrain)
        from rfl]
      simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
    simp [drone.validHeights.ir, Func.scratch, Expr.evalResults, Expr.eval, g2, Scalar.values,
      Flat.flat]

theorem validHeights_implements : Implements drone.module 12 validHeights :=
  (validHeights_implementsA (a := true)).implements

end Project.Drone
