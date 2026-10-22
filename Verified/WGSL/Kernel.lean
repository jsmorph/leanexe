import Verified.WGSL.Lower
import Verified.WGSL.Initial
import Verified.WGSL.Counter
import Verified.WGSL.Output

namespace Verified.WGSL

def kernelContext (params : Params Γ) (count : LeanExe.WGSL.Count) : Context (.word :: Γ) :=
  .cons (.word (.get Γ.length)) (params.context count 0)

theorem kernelContext_bound (params : Params Γ) (count : LeanExe.WGSL.Count)
    (sizeBound : ∀ j, count.sizeLocal? = some j → j < Γ.length + 2) :
    (kernelContext params count).Bounded (Γ.length + 2) := by
  apply (params.context_bound count 0 (Γ.length + 2) (by omega) sizeBound).cons
  simp [Rep.locals, LeanExe.IR.Expr.denoteLocals]

structure KernelPlan (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) where
  params : Params Γ
  counter : Counter params count
  output : Output e
  code : Code (kernelContext params counter.count) (Γ.length + 2)
    (fun funs env => element.denote funs env)

def KernelPlan.spec {count : Verified.Expr S Γ .word}
    {element : Verified.Expr S (.word :: Γ) (.elem e)}
    (plan : KernelPlan count element) : LeanExe.WGSL.Spec where
  kinds := plan.params.kinds
  index := Γ.length
  count := plan.counter.count
  vars := plan.code.vars
  width := plan.code.next
  body := plan.code.body
  element := plan.output.word plan.code.result

structure Kernel (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) extends KernelPlan count element where
  module : LeanExe.WGSL.Module
  wf : toKernelPlan.spec.WF
  translated : toKernelPlan.spec.module = some module

def compileKernel (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) : Option (Kernel count element) := do
  let params ← Params.ofTypes Γ
  let counter ← Counter.ofExpr params count
  let output ← Demos.Drone.Output.ofElem e
  let code ← lower element (kernelContext params counter.count) (Γ.length + 2)
    (kernelContext_bound params counter.count counter.sizeBound)
  let plan : KernelPlan count element := { params, counter, output, code }
  if hWF : plan.spec.wfb = true then
    match hModule : plan.spec.module with
    | none => none
    | some m => some ⟨plan, m, plan.spec.wf_of_wfb hWF, hModule⟩
  else none

end Verified.WGSL
