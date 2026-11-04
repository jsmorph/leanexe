import Verified.Kernel.Plan
import LeanExe.WGSL.Build

namespace Verified.WGSL

open Verified.Kernel

structure Kernel (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) extends KernelPlan count element where
  module : LeanExe.WGSL.Module
  wf : toKernelPlan.spec.WF
  translated : toKernelPlan.spec.wgsl = some module

def compileKernel (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) : Option (Kernel count element) := do
  let plan ← KernelPlan.ofBuild count element
  if hWF : plan.spec.wfb = true then
    match hModule : plan.spec.wgsl with
    | none => none
    | some m => some ⟨plan, m, plan.spec.wf_of_wfb hWF, hModule⟩
  else none

/-- A compiled kernel's plan is the one that `KernelPlan.ofBuild` returns. -/
theorem compileKernel_plan {count : Verified.Expr S Γ .word}
    {element : Verified.Expr S (.word :: Γ) (.elem e)} {k : Kernel count element}
    (h : compileKernel count element = some k) :
    KernelPlan.ofBuild count element = some k.toKernelPlan := by
  unfold compileKernel at h
  cases hp : KernelPlan.ofBuild count element with
  | none => simp [hp] at h
  | some plan =>
    simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        rfl
    · cases h

end Verified.WGSL
