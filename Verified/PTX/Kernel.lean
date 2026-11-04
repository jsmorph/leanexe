import Verified.Kernel.Plan
import LeanExe.PTX.Build

/-!
The PTX kernel of a build: the shared plan and its translation by `LeanExe.Source.Spec.ptx`.
`Kernel.executions_eq` states, for every consistent execution of a launch under the memory model
of `LeanExe.PTX.MemoryModel`, that no access of a thread is in a data race, that every thread
ends, and that the copy back reads the count followed by the source array's encoded elements.
-/

namespace Verified.PTX

open Verified.Kernel

structure Kernel (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) extends KernelPlan count element where
  module : LeanExe.PTX.Module
  wf : toKernelPlan.spec.WF
  translated : toKernelPlan.spec.ptx = some module

def compileKernel (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) : Option (Kernel count element) := do
  let plan ← KernelPlan.ofBuild count element
  if hWF : plan.spec.wfb = true then
    match hModule : plan.spec.ptx with
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

variable {countExpr : Verified.Expr S Γ .word}
  {element : Verified.Expr S (.word :: Γ) (.elem e)}

/-- A launch of a kernel with at least `n` threads under the memory model: a consistent execution
exists, and in every consistent execution no access of a thread is in a data race, every thread
ends, and the copy back reads the count followed by the source array's encoded elements. -/
theorem Kernel.executions_eq (kernel : Kernel countExpr element)
    (funs : Funs S) (env : Verified.Env Γ) (n : Nat)
    (fits : kernel.toKernelPlan.spec.Fits (kernel.params.args env) n)
    (ys : Array UInt64) (hys : ys.size = n) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : n ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    let L := LeanExe.PTX.buildLaunch kernel.module (kernel.params.args env) n ys blocks block
    (∃ E, L.Consistent E) ∧ ∀ E, L.Consistent E →
      L.NoDataRace E ∧ (∀ g, g < blocks * block → (L.events (E.oracle g) g).2 = true) ∧
        ∀ i, i < n + 1 →
          (#[UInt64.ofNat n] ++ ((Verified.Expr.build countExpr element).denote funs env).map
            kernel.output.encode)[i]? = some (E.observed i) := by
  intro L
  have hCount := kernel.counter.value funs env n (by
    cases hc : kernel.counter.count <;>
      simpa only [KernelPlan.spec, hc, FitsCount] using fits.count)
  have h := kernel.toKernelPlan.spec.ptx_executions kernel.wf kernel.translated
    (kernel.params.args env) n fits
    (fun k => kernel.output.encode (element.denote funs (.cons k env)))
    (fun k _ => kernel.toKernelPlan.element_denote kernel.wf funs env k n fits)
    ys hys blocks block hb hb32 hbl hcover hthreads
  simpa only [Verified.Expr.denote, hCount, build_map] using h

/-- The sequential run of a launch of a kernel with at least `n` threads leaves the count followed
by the source array's encoded elements, and distinct threads store to distinct words. -/
theorem Kernel.launch_eq (kernel : Kernel countExpr element)
    (funs : Funs S) (env : Verified.Env Γ) (n : Nat)
    (fits : kernel.toKernelPlan.spec.Fits (kernel.params.args env) n)
    (ys : Array UInt64) (hys : ys.size = n) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : n ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    let L := LeanExe.PTX.buildLaunch kernel.module (kernel.params.args env) n ys blocks block
    L.seq = some (#[UInt64.ofNat n] ++
        ((Verified.Expr.build countExpr element).denote funs env).map kernel.output.encode) ∧
      L.RaceFree := by
  intro L
  have hCount := kernel.counter.value funs env n (by
    cases hc : kernel.counter.count <;>
      simpa only [KernelPlan.spec, hc, FitsCount] using fits.count)
  have h := kernel.toKernelPlan.spec.ptx_launch kernel.wf kernel.translated
    (kernel.params.args env) n fits
    (fun k => kernel.output.encode (element.denote funs (.cons k env)))
    (fun k _ => kernel.toKernelPlan.element_denote kernel.wf funs env k n fits)
    ys hys blocks block hb hb32 hbl hcover hthreads
  simpa only [Verified.Expr.denote, hCount, build_map] using h

end Verified.PTX

#print axioms Verified.PTX.Kernel.executions_eq
#print axioms Verified.PTX.Kernel.launch_eq
