import Examples.Euler.Faces
import Project.IR.OneArray

/-! The compiled reconstruction kernels of the reconstructed Euler solver compute their Lean
definitions. -/

namespace Examples.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Euler

instance : Flat Faces (UInt64 × Conserved × Conserved × Float) :=
  ⟨fun f => (f.status, f.left, f.right, f.factor)⟩

instance : Flat Slope (UInt64 × Conserved) := ⟨fun s => (s.status, s.state)⟩

/-- `eval_ir` with a larger step limit, for bodies that test several state guards. -/
macro "eval_ir_large" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { maxSteps := 2000000 }) [Stmt.run, Expr.eval, Func.state,
    Func.locals, Func.scratch, Func.width, Stmt.scratchWidth, Expr.scratchWidth,
    State.set?_eq_update, State.get, State.update, State.setAll, U64Op.apply, F64Op.apply,
    F64UnOp.apply, Scalar.values, ScalarType.valueType, Expr.evalResults, ScalarType.value,
    Flat.flat, divU_eq, remU_eq, -mul_ite, -ite_mul, $args,*])

/-- Two words of tests are equal when the tests agree. -/
theorem word_eq_word (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) = if q then 1 else 0) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

def slopeTuple : Conserved × Conserved × Conserved → Slope := fun (l, c, r) => slope l c r

set_option maxHeartbeats 4000000 in
theorem slope_implements {a : Bool} : ImplementsPureA a euler.module 37 slopeTuple :=
  Func.implementsPureA euler.funcs 35 euler.slope.ir "slope" rfl slopeTuple (fun _ => rfl)
    fun ⟨l, c, r⟩ initial => by
      refine Stmt.seq_run ?_
      eval_ir [euler.slope.ir]
      iterate 7 (refine Stmt.seq_run ?_; eval_ir [])
      refine Stmt.run_triple ?_
      eval_ir [slopeTuple, slope, finite, absBits, word_and, word_eq_one, F64Bits.toBits_sub,
        zero_toBits]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [ite_eq_left h]
        eval_ir [minmod, absBits, toBits_ite, F64Bits.toBits_sub, zero_toBits, word_eq_word]
      · rw [ite_eq_right h]
        eval_ir [zero_toBits]

def candidateTuple : Conserved × Conserved × Float → Faces :=
  fun (center, delta, factor) => candidate center delta factor

set_option maxHeartbeats 4000000 in
theorem candidate_implements {a : Bool} : ImplementsPureA a euler.module 38 candidateTuple :=
  Func.implementsPureA euler.funcs 36 euler.candidate.ir "candidate" rfl candidateTuple
    (fun _ => rfl) fun ⟨center, delta, factor⟩ initial => by
      let offset : Conserved := ⟨factor * delta.density, factor * delta.mx, factor * delta.my,
        factor * delta.energy⟩
      let left : Conserved := ⟨center.density - offset.density, center.mx - offset.mx,
        center.my - offset.my, center.energy - offset.energy⟩
      let right : Conserved := ⟨center.density + offset.density, center.mx + offset.mx,
        center.my + offset.my, center.energy + offset.energy⟩
      refine Stmt.seq_run ?_
      eval_ir [euler.candidate.ir]
      iterate 11 (refine Stmt.seq_run ?_; eval_ir [])
      refine Stmt.seq_callPure energyGuard_implements rfl rfl rfl
        (x := (left.density, left.mx, left.my, left.energy)) ?_
      eval_ir [energyGuardTuple, left, offset, F64Bits.toBits_sub, F64Bits.toBits_mul]
      refine Stmt.seq_callPure energyGuard_implements rfl rfl rfl
        (x := (right.density, right.mx, right.my, right.energy)) ?_
      eval_ir [energyGuardTuple, right, offset, F64Bits.toBits_add, F64Bits.toBits_mul]
      refine Stmt.run_triple ?_
      eval_ir [candidateTuple, candidate, finite, absBits, admissibleState, stateGuard,
        narrowGuard, positive, rejectedFaces, zeroState, word_and, word_or, word_eq_one, word_beq_one,
        cond_eq_ite, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, zero_toBits]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul]
      · eval_ir [h, zero_toBits, and_assoc]

def tryFactorTuple : Conserved × Conserved × Float → UInt64 × Float :=
  fun (center, delta, factor) => tryFactor center delta factor

set_option maxHeartbeats 2000000 in
theorem tryFactor_implements {a : Bool} : ImplementsPureA a euler.module 39 tryFactorTuple :=
  Func.implementsPureA euler.funcs 37 euler.tryFactor.ir "tryFactor" rfl tryFactorTuple
    (fun _ => rfl) fun ⟨center, delta, factor⟩ initial => by
      refine Stmt.seq_callPure candidate_implements rfl rfl rfl (x := (center, delta, factor)) ?_
      eval_ir [euler.tryFactor.ir, candidateTuple]
      refine Stmt.run_triple ?_
      eval_ir [tryFactorTuple, tryFactor]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, F64Bits.toBits_mul, half_toBits]

/-- `limitFactor` with its loop's test and step named. -/
theorem limitFactor_loop (trials : UInt64) (center delta : Conserved) :
    ∃ (cond : UInt64 × Float → Bool) (step : UInt64 × Float → UInt64 × Float),
      (∀ x, cond x = (x.1 != 0)) ∧ (∀ x, step x = tryFactor center delta x.2) ∧
      limitFactor trials center delta =
        LeanExe.repeatWhile trials ((1 : UInt64), (0.5 : Float)) cond step := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

def limitFactorTuple : UInt64 × Conserved × Conserved → UInt64 × Float :=
  fun (trials, center, delta) => limitFactor trials center delta

set_option maxHeartbeats 2000000 in
theorem limitFactor_implements {a : Bool} : ImplementsPureA a euler.module 40 limitFactorTuple :=
  Func.implementsPureA euler.funcs 38 euler.limitFactor.ir "limitFactor" rfl limitFactorTuple
    (fun _ => rfl) fun ⟨trials, center, delta⟩ initial => by
      obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := limitFactor_loop trials center delta
      set start := euler.limitFactor.ir.state (Scalar.values (trials, center, delta))
        with hStartDef
      have hStart : start.params.length + start.locals.length = 13 := rfl
      have hGet1 : start.get 1 = some (.f64 center.density.toBits) := rfl
      have hGet2 : start.get 2 = some (.f64 center.mx.toBits) := rfl
      have hGet3 : start.get 3 = some (.f64 center.my.toBits) := rfl
      have hGet4 : start.get 4 = some (.f64 center.energy.toBits) := rfl
      have hGet5 : start.get 5 = some (.f64 delta.density.toBits) := rfl
      have hGet6 : start.get 6 = some (.f64 delta.mx.toBits) := rfl
      have hGet7 : start.get 7 = some (.f64 delta.my.toBits) := rfl
      have hGet8 : start.get 8 = some (.f64 delta.energy.toBits) := rfl
      let s2 := (start.update 9 (.i64 1)).update 10 (.f64 (0.5 : Float).toBits)
      show TripleA _ _ (.seq (.assign 9 (.const 1)) (.seq (.assign 10 _)
        (Stmt.repeatWhile [9, 10] 11 12 (.get 0) _ 39 _))) 13 _ _
      refine Stmt.seq_run ⟨start.update 9 (.i64 1), by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
      refine Stmt.seq_run ⟨s2, by
        simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2, half_toBits], ?_⟩
      have hS2 : s2.params.length + s2.locals.length = 13 := by simp [s2, hStart]
      refine (Stmt.repeatWhile_pure_spec tryFactor_implements rfl rfl rfl (by decide)
        (by decide) (by omega) (n := trials) ⟨s2, by simp [Expr.eval, s2, hStartDef]; rfl⟩
        cond step (fun x => (center, delta, x.2)) (fun x => (hStepEq x).symm) (fun _ => rfl)
        (x0 := ((1 : UInt64), (0.5 : Float)))
        (by simp [State.Holds, s2, hStart, Scalar.values]) ?_ ?_).mono (fun _ _ h => h) ?_
      · rintro st ⟨a, b⟩ hHolds -
        have h9 : st.get 9 = some (.i64 a) := by
          simp [State.Holds, Scalar.values] at hHolds
          exact hHolds.1
        exact ⟨st, by by_cases ha : a = 0 <;> simp [Expr.eval, h9, hCondEq, ha]⟩
      · rintro st ⟨a, b⟩ hHolds hFrame
        have hG : ∀ j, j < 9 → st.get j = start.get j := fun j hj =>
          (hFrame.get j (by omega) (by simp; omega)).trans
            (by simp [s2]; rw [State.get_update_ne (by omega), State.get_update_ne (by omega)])
        have h10 : st.get 10 = some (.f64 b.toBits) := by
          simp [State.Holds, Scalar.values] at hHolds
          exact hHolds.2
        refine ⟨st, ?_⟩
        simp [Expr.evalResults, Expr.eval, hG 1 (by decide), hG 2 (by decide), hG 3 (by decide),
          hG 4 (by decide), hG 5 (by decide), hG 6 (by decide), hG 7 (by decide),
          hG 8 (by decide), h10, hGet1, hGet2, hGet3, hGet4, hGet5, hGet6, hGet7, hGet8,
          Scalar.values, Flat.flat]
      · rintro s st ⟨rfl, hHolds, -⟩
        refine ⟨rfl, _, st, ?_, rfl⟩
        rw [show limitFactorTuple (trials, center, delta) = _ from hDef]
        generalize LeanExe.repeatWhile trials ((1 : UInt64), (0.5 : Float)) cond step = R at hHolds
        obtain ⟨a, b⟩ := R
        simp [State.Holds, Scalar.values] at hHolds
        simp [euler.limitFactor.ir, Expr.evalResults, Expr.eval, hHolds.1, hHolds.2,
          Scalar.values]

def limitTuple : UInt64 × Conserved × Conserved → Faces :=
  fun (trials, center, delta) => limit trials center delta

set_option maxHeartbeats 2000000 in
theorem limit_implements {a : Bool} : ImplementsPureA a euler.module 41 limitTuple :=
  Func.implementsPureA euler.funcs 39 euler.limit.ir "limit" rfl limitTuple (fun _ => rfl)
    fun ⟨trials, center, delta⟩ initial => by
      let r := limitFactor trials center delta
      refine Stmt.seq_callPure limitFactor_implements rfl rfl rfl (x := (trials, center, delta)) ?_
      eval_ir [euler.limit.ir, limitFactorTuple]
      refine Stmt.ite_test (b := r.1 == 0) (by simp [Expr.eval, State.get, r]) (fun hR => ?_)
        (fun hR => ?_)
      · have hR' : (limitFactor trials center delta).1 = 0 := by simpa [r] using hR
        refine Stmt.callPure_last candidate_implements rfl rfl rfl (x := (center, delta, r.2)) ?_
        eval_ir [candidateTuple, limitTuple, limit, r, hR']
      · have hR' : ¬(limitFactor trials center delta).1 = 0 := by simpa [r] using hR
        refine Stmt.run_triple ?_
        eval_ir [limitTuple, limit, r, zero_toBits, hR']

def reconstructTuple : UInt64 × Conserved × Conserved × Conserved → Faces :=
  fun (trials, left, center, right) => reconstruct trials left center right

set_option maxHeartbeats 4000000 in
theorem reconstruct_implements {a : Bool} : ImplementsPureA a euler.module 42 reconstructTuple :=
  Func.implementsPureA euler.funcs 40 euler.reconstruct.ir "reconstruct" rfl reconstructTuple
    (fun _ => rfl) fun ⟨trials, left, center, right⟩ initial => by
      let delta := slope left center right
      refine Stmt.seq_callPure slope_implements rfl rfl rfl (x := (left, center, right)) ?_
      eval_ir [euler.reconstruct.ir, slopeTuple]
      refine Stmt.seq_callPure limit_implements rfl rfl rfl (x := (trials, center, delta.state)) ?_
      eval_ir [limitTuple, delta]
      refine Stmt.seq_callPure energyGuard_implements rfl rfl rfl
        (x := (left.density, left.mx, left.my, left.energy)) ?_
      eval_ir [energyGuardTuple]
      refine Stmt.seq_callPure energyGuard_implements rfl rfl rfl
        (x := (center.density, center.mx, center.my, center.energy)) ?_
      eval_ir [energyGuardTuple]
      refine Stmt.seq_callPure energyGuard_implements rfl rfl rfl
        (x := (right.density, right.mx, right.my, right.energy)) ?_
      eval_ir [energyGuardTuple]
      refine Stmt.run_triple ?_
      eval_ir_large [reconstructTuple, reconstruct, admissibleState, stateGuard, narrowGuard,
        positive, finite, absBits, rejectedFaces, zeroState, word_and, word_or, word_eq_one,
        word_beq_one, cond_eq_ite, zero_toBits, delta]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir_large [h]
      · eval_ir_large [h, zero_toBits, and_assoc]

def reconstructedStepTuple : UInt64 × Float × Conserved × Conserved × Conserved × Conserved ×
    Conserved → Updated :=
  fun (trials, ratio, farLeft, left, center, right, farRight) =>
    reconstructedStep trials ratio farLeft left center right farRight

set_option maxHeartbeats 8000000 in
theorem reconstructedStep_implements {a : Bool} : ImplementsPureA a euler.module 43 reconstructedStepTuple :=
  Func.implementsPureA euler.funcs 41 euler.reconstructedStep.ir "reconstructedStep" rfl
    reconstructedStepTuple (fun _ => rfl)
    fun ⟨trials, ratio, farLeft, left, center, right, farRight⟩ initial => by
      have hR := reconstruct_implements (a := a)
      let leftFaces := reconstruct trials farLeft left center
      let centerFaces := reconstruct trials left center right
      let rightFaces := reconstruct trials center right farRight
      refine Stmt.seq_callPure hR rfl rfl rfl (x := (trials, farLeft, left, center)) ?_
      eval_ir [euler.reconstructedStep.ir, reconstructTuple]
      refine Stmt.seq_callPure hR rfl rfl rfl (x := (trials, left, center, right)) ?_
      eval_ir [reconstructTuple]
      refine Stmt.seq_callPure hR rfl rfl rfl (x := (trials, center, right, farRight)) ?_
      eval_ir [reconstructTuple]
      refine Stmt.seq_callPure faceStep_implements rfl rfl rfl
        (x := (ratio, center.density, center.mx, center.my, center.energy,
          leftFaces.right.density, leftFaces.right.mx, leftFaces.right.my, leftFaces.right.energy,
          centerFaces.left.density, centerFaces.left.mx, centerFaces.left.my,
          centerFaces.left.energy, centerFaces.right.density, centerFaces.right.mx,
          centerFaces.right.my, centerFaces.right.energy, rightFaces.left.density,
          rightFaces.left.mx, rightFaces.left.my, rightFaces.left.energy)) ?_
      eval_ir [faceStepTuple, leftFaces, centerFaces, rightFaces]
      refine Stmt.run_triple ?_
      eval_ir [reconstructedStepTuple, reconstructedStep, rejectedCell, word_and, word_eq_one,
        zero_toBits, faceStepTuple, leftFaces, centerFaces, rightFaces]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

end Examples.Euler
