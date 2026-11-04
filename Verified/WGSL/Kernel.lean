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

end Verified.WGSL
