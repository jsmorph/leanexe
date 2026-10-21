import Verified.WGSL.Params

namespace Verified.WGSL

open LeanExe.WGSL

theorem args_holds (K : Spec) (hK : K.WF) (args : List Arg) (k n : Nat)
    (fits : K.Fits args n) (j : Nat) (arg : Arg) (harg : args[j]? = some arg) :
    argHolds arg j K.count (K.locals args k n) (Spec.arrays args) := by
  have hj := (List.getElem?_eq_some_iff.mp harg).1
  have hlen : args.length = K.kinds.length := by
    simpa only [List.length_map] using congrArg List.length fits.kinds
  have hi : j ≠ K.index := by have := hK.index; omega
  have hs : K.count.sizeLocal? ≠ some j := by
    cases hc : K.count with
    | param p => simp [Count.sizeLocal?]
    | size sizeSlot src =>
        have h := hK.count
        simp only [hc] at h
        intro hsome
        have heq : sizeSlot = j := Option.some.inj hsome
        omega
  cases arg with
  | word value => simp [argHolds, Spec.locals, hi, hs, harg]
  | float bits => simp [argHolds, Spec.locals, hi, hs, harg]
  | array xs =>
      refine ⟨by simp [Spec.arrays, harg], ?_⟩
      intro sizeSlot hc
      have hCount := fits.count
      rw [hc] at hCount
      obtain ⟨ys, hy, hSize⟩ := hCount
      rw [harg] at hy
      cases hy
      have hWF := hK.count
      rw [hc] at hWF
      simp [Spec.locals, hWF.2.2.1, hc, Count.sizeLocal?, hSize]

theorem arrays_above (args : List Arg) (base : Nat) (bound : args.length ≤ base) :
    ∀ j, base ≤ j → Spec.arrays args j = none := by
  intro j hj
  have hnone : args[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  simp [Spec.arrays, hnone]

theorem Params.initial_agrees (params : Params Γ) (K : Spec) (hK : K.WF)
    (env : Verified.Env Γ) (k n : Nat)
    (fits : K.Fits (params.args env) n) :
    (params.context K.count 0).Agrees env (K.locals (params.args env) k n)
      (Spec.arrays (params.args env)) := by
  apply params.context_agrees env K.count 0
  intro j arg hj
  simpa only [Nat.zero_add] using args_holds K hK (params.args env) k n fits j arg hj

end Verified.WGSL
