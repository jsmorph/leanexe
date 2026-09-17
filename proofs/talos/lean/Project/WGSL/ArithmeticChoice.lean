import Project.WGSL.ArithmeticStep
import Project.WGSL.MatrixView

namespace Project.WGSL.ArithmeticChoice
open LeanExe.WGSL MatrixView

set_option maxHeartbeats 20000

def step (fused : Bool) (acc x y : UInt32) : UInt32 :=
  select fused (Wasm.IEEE32.add acc (Wasm.IEEE32.mul x y)) (Binary32.fma x y acc)

theorem step_false (acc x y : UInt32) : step false acc x y =
    Wasm.IEEE32.add acc (Wasm.IEEE32.mul x y) := select_false _ _

theorem step_true (acc x y : UInt32) : step true acc x y = Binary32.fma x y acc := select_true _ _

theorem step_run (choice : Bool) (acc x y : UInt32) :
    Accumulate Binary32.semantics fusion acc x y (step choice acc x y) := by
  cases choice
  · rw [step_false]
    exact Accumulate.separate (product := Wasm.IEEE32.mul x y)
      (cm := ieeeChoice) (ca := ieeeChoice) True.intro rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  · rw [step_true]
    exact Accumulate.fused (c := ieeeChoice) True.intro rfl ⟨rfl, rfl⟩

theorem step_iff {acc x y result} :
    Accumulate Binary32.semantics fusion acc x y result ↔
      ∃ choice, result = step choice acc x y := by
  constructor
  · intro h
    cases h with
    | separate _ _ _ mul add =>
        refine ⟨false, ?_⟩
        rw [step_false]
        exact add.2.trans (congrArg (fun product => Wasm.IEEE32.add acc product) mul.2)
    | fused _ _ op =>
        refine ⟨true, ?_⟩
        rw [step_true]
        exact op.2
  · rintro ⟨choice, rfl⟩
    exact step_run choice acc x y


def evaluate (choices : Nat → Bool) (x : WordBuffer) (weights : Matrix)
    (col : Nat) : Nat → UInt32
  | 0 => 0
  | k + 1 => step (choices k) (evaluate choices x weights col k) (x k) (weights k col)

theorem evaluate_congr (a b : Nat → Bool) (x : WordBuffer) (weights : Matrix)
    (col k : Nat) : (∀ i, i < k → a i = b i) →
    evaluate a x weights col k = evaluate b x weights col k := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      simp only [evaluate]
      rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem evaluate_run (choices : Nat → Bool) (x : WordBuffer) (weights : Matrix)
    (col k : Nat) :
    ColumnRun Binary32.semantics fusion x weights col k (evaluate choices x weights col k) := by
  induction k with
  | zero => exact .zero
  | succ k ih => exact .next ih (step_run _ _ _ _)

/-- Every result admitted by the profile is exactly the result of a concrete
choice sequence, and every such sequence is admitted. No tolerance is used. -/
theorem fusion_iff_choices {x weights col k result} :
    ColumnRun Binary32.semantics fusion x weights col k result ↔
      ∃ choices, result = evaluate choices x weights col k := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨fun _ => false, rfl⟩
    | @next k acc result previous update ih =>
        obtain ⟨choices, ha⟩ := ih
        obtain ⟨choice, hr⟩ := step_iff.mp update
        let extended := fun i => if i = k then choice else choices i
        have hp : evaluate extended x weights col k = evaluate choices x weights col k := by
          apply evaluate_congr
          intro i hi
          simp only [extended, ite_eq_right (by omega : i ≠ k)]
        refine ⟨extended, ?_⟩
        rw [evaluate, hp, ← ha]
        rw [show extended k = choice from ite_eq_left rfl]
        exact hr
  · rintro ⟨choices, rfl⟩
    exact evaluate_run choices x weights col k

theorem separate_evaluate (x : WordBuffer) (weights : Matrix) (col k : Nat) :
    evaluate (fun _ => false) x weights col k = columnAccum Binary32.arithmetic x weights col k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [evaluate, columnAccum, ih, step_false, Binary32.arithmetic]

end Project.WGSL.ArithmeticChoice
