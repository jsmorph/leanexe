import Project.EulerReconstruction.LoopShape

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit

macro "limit_peel" : tactic => `(tactic|
  repeat first
  | wp_run [limitLoop, func38, Project.ProofKit.Annotation.resolve,
      Project.ProofKit.Annotation.descend, limitParams,
      Bind.bind, Pure.pure, Option.bind, Option.getD,
      List.length_set, List.getElem?_set, List.getElem?_cons_zero,
      List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff,
      Wasm.f64Mul, *]
  | (try simp only [Wasm.wp_iff_control_types]
     refine wp_iff_cons rfl ?_
     simp [boolWord, *, -UInt64.not_le]))

theorem limit_fuel_unfold (fuel : UInt64) (hFuel : fuel ≠ 0) :
    fuel.toNat = (fuel - 1).toNat + 1 := by
  have hPositive := UInt64.pos_iff_ne_zero.mpr hFuel
  have hOne : (1 : UInt64) ≤ fuel := by
    rw [UInt64.le_iff_toNat_le]
    have := UInt64.lt_iff_toNat_lt.mp hPositive
    simp only [UInt64.toNat_zero, UInt64.toNat_one] at *
    omega
  rw [UInt64.toNat_sub_of_le _ _ hOne]
  have := UInt64.lt_iff_toNat_lt.mp hPositive
  simp only [UInt64.toNat_zero, UInt64.toNat_one] at *
  omega

theorem limit_body_spec (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (fuel : UInt64) (center delta : State)
    (factor : UInt64) (output : Faces)
    (hFrame : LimitFrameAt frame fuel center delta factor output false)
    (hFuel : fuel ≠ 0) :
    wp Project.EulerReconstruction.«module» (limitLoop.drop 7)
      (BlockLoop.stepPost (limitInvariant initial center delta (limit fuel.toNat center delta factor))
        (limitDone initial center delta (limit fuel.toNat center delta factor)) (fun _ f => limitMeasure f)
        (limitMeasure frame)) initial frame env := by
  rw [hFrame.measure]
  simp only [Bool.false_eq_true, ite_false]
  rcases hFrame with ⟨hParams, hLocals, hValues, hStatus, hLd, hLx, hLy,
    hLe, hRd, hRx, hRy, hRe, hFactor, hDone⟩
  rcases frame with ⟨params, locals, values⟩
  dsimp only at hParams hLocals hValues ⊢
  subst params
  subst values
  limit_peel
  refine wp_call_tw (candidate_exact env initial center delta factor) ?_
  rintro st values ⟨hst, hValues⟩
  subst st
  simp only [facesValues] at hValues
  subst values
  by_cases hAccepted : (candidate center delta factor).status = 0
  all_goals limit_peel
  · change limitInvariant initial center delta (limit fuel.toNat center delta factor) _ _ ∧ _
    refine ⟨⟨rfl, fuel, factor, candidate center delta factor, true, ?_, ?_⟩, ?_⟩
    · constructor <;> simp_all [limitParams, List.length_set, boolWord]
    · simp [limit_fuel_unfold fuel hFuel, limit, hAccepted]
    · simp [limitMeasure, List.length_set, hLocals]
  · change limitInvariant initial center delta (limit fuel.toNat center delta factor) _ _ ∧ _
    refine ⟨⟨rfl, fuel - 1, IEEE64.mul 0x3FE0000000000000 factor,
      output, false, ?_, ?_⟩, ?_⟩
    · constructor <;> simp_all [limitParams, List.length_set, boolWord]
    · simp [limit_fuel_unfold fuel hFuel, limit, hAccepted]
    · obtain ⟨hIndex, hZero⟩ := List.getElem_of_getElem?
        (show locals[10]? = some (.i64 0) from hDone)
      simpa [limitMeasure, List.length_set, List.getElem?_set, hLocals, hZero,
        limitParams] using
        Nat.add_lt_add_right
          (Project.ProofKit.ScalarTransition.CounterTransition.decrement_toNat_lt hFuel) 1

#print axioms limit_fuel_unfold
#print axioms limit_body_spec

end Project.EulerReconstruction.Execution
