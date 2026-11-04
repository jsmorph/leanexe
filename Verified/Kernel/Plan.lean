import Verified.Kernel.Lower
import Verified.Kernel.Initial
import Verified.Kernel.Counter
import Verified.Kernel.Output

/-!
The plan of a build kernel, which both GPU targets translate: the parameters, the count, the
output encoding, and the lowered code of the element, with the build record `KernelPlan.spec` of
`LeanExe.Source`.  `KernelPlan.element_denote` states that at every index below the count, the
record's statements and element give the encoded element of the Lean build.
-/

namespace Verified.Kernel

def kernelContext (params : Params Γ) (count : LeanExe.Source.Count) : Context (.word :: Γ) :=
  .cons (.word (.get Γ.length)) (params.context count 0)

theorem kernelContext_bound (params : Params Γ) (count : LeanExe.Source.Count)
    (sizeBound : ∀ j, count.sizeLocal? = some j → j < Γ.length + 2) :
    (kernelContext params count).Bounded (Γ.length + 2) := by
  apply (params.context_bound count 0 (Γ.length + 2) (by omega) sizeBound).cons
  simp [Rep.locals, LeanExe.Source.Expr.denoteLocals]

structure KernelPlan (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) where
  params : Params Γ
  counter : Counter params count
  output : Output e
  code : Code (kernelContext params counter.count) (Γ.length + 2)
    (fun funs env => element.denote funs env)

def KernelPlan.spec {count : Verified.Expr S Γ .word}
    {element : Verified.Expr S (.word :: Γ) (.elem e)}
    (plan : KernelPlan count element) : LeanExe.Source.Spec where
  kinds := plan.params.kinds
  index := Γ.length
  count := plan.counter.count
  vars := plan.code.vars
  width := plan.code.next
  body := plan.code.body
  element := plan.output.word plan.code.result

/-- The plan of the build of `count` elements `element`, or `none` when a parameter, the count,
the element type, or the element's expression is outside the lowered subset. -/
def KernelPlan.ofBuild (count : Verified.Expr S Γ .word)
    (element : Verified.Expr S (.word :: Γ) (.elem e)) : Option (KernelPlan count element) := do
  let params ← Params.ofTypes Γ
  let counter ← Counter.ofExpr params count
  let output ← Output.ofElem e
  let code ← lower element (kernelContext params counter.count) (Γ.length + 2)
    (kernelContext_bound params counter.count counter.sizeBound)
  pure { params, counter, output, code }

theorem Params.args_length (params : Params Γ) (env : Verified.Env Γ) :
    (params.args env).length = Γ.length := by
  simpa only [List.length_map, Params.kinds_length] using
    congrArg List.length (params.args_kinds env)

theorem build_map (n : UInt64) (f : UInt64 → α) (g : α → β) :
    (LeanExe.build n f).map g = LeanExe.build n (fun i => g (f i)) := by
  simp [LeanExe.build, Array.map_ofFn, Function.comp_def]

variable {countExpr : Verified.Expr S Γ .word}
  {element : Verified.Expr S (.word :: Γ) (.elem e)}

theorem KernelPlan.element_denote (plan : KernelPlan countExpr element) (wf : plan.spec.WF)
    (funs : Funs S) (env : Verified.Env Γ) (k n : Nat)
    (fits : plan.spec.Fits (plan.params.args env) n) :
    ∃ last, plan.spec.body.denote (LeanExe.Source.Spec.arrays (plan.params.args env))
        (plan.spec.locals (plan.params.args env) k n) = some last ∧
      plan.spec.element.denote last
        (LeanExe.Source.Spec.arrays (plan.params.args env)) =
          some (plan.output.encode (element.denote funs (.cons (UInt64.ofNat k) env))) := by
  have hParams := plan.params.initial_agrees plan.spec wf env k n fits
  have hIndex : (Rep.word (.get Γ.length)).Holds
      (plan.spec.locals (plan.params.args env) k n)
      (LeanExe.Source.Spec.arrays (plan.params.args env)) (UInt64.ofNat k) := by
    simp [Rep.Holds, LeanExe.Source.Expr.denote, LeanExe.Source.Spec.locals, KernelPlan.spec]
  obtain ⟨last, hBody, hValue⟩ := plan.code.correct
    (kernelContext_bound plan.params plan.counter.count plan.counter.sizeBound)
    funs (.cons (UInt64.ofNat k) env) _ _ (hParams.cons hIndex)
    (arrays_above (plan.params.args env) (Γ.length + 2) (by
      rw [Params.args_length]
      omega))
  exact ⟨last, hBody, plan.output.correct plan.code.result last _ _ hValue⟩

end Verified.Kernel
