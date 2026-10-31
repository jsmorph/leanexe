import Verified.WGSL.Kernel

namespace Verified.WGSL

variable {countExpr : Verified.Expr S Γ .word}
  {element : Verified.Expr S (.word :: Γ) (.elem e)}

theorem Params.args_length (params : Params Γ) (env : Verified.Env Γ) :
    (params.args env).length = Γ.length := by
  simpa only [List.length_map, Params.kinds_length] using
    congrArg List.length (params.args_kinds env)

theorem build_map (n : UInt64) (f : UInt64 → α) (g : α → β) :
    (LeanExe.build n f).map g = LeanExe.build n (fun i => g (f i)) := by
  simp [LeanExe.build, Array.map_ofFn, Function.comp_def]

theorem Kernel.element_denote (kernel : Kernel countExpr element)
    (funs : Funs S) (env : Verified.Env Γ) (k n : Nat)
    (fits : kernel.toKernelPlan.spec.Fits (kernel.params.args env) n) :
    ∃ last, kernel.toKernelPlan.spec.body.denote (LeanExe.WGSL.Spec.arrays (kernel.params.args env))
        (kernel.toKernelPlan.spec.locals (kernel.params.args env) k n) = some last ∧
      kernel.toKernelPlan.spec.element.denote last
        (LeanExe.WGSL.Spec.arrays (kernel.params.args env)) =
          some (kernel.output.encode (element.denote funs (.cons (UInt64.ofNat k) env))) := by
  have hParams := kernel.params.initial_agrees kernel.toKernelPlan.spec kernel.wf env k n fits
  have hIndex : (Rep.word (.get Γ.length)).Holds
      (kernel.toKernelPlan.spec.locals (kernel.params.args env) k n)
      (LeanExe.WGSL.Spec.arrays (kernel.params.args env)) (UInt64.ofNat k) := by
    simp [Rep.Holds, LeanExe.WGSL.Source.Expr.denote, LeanExe.WGSL.Spec.locals, KernelPlan.spec]
  obtain ⟨last, hBody, hValue⟩ := kernel.code.correct
    (kernelContext_bound kernel.params kernel.counter.count kernel.counter.sizeBound)
    funs (.cons (UInt64.ofNat k) env) _ _ (hParams.cons hIndex)
    (arrays_above (kernel.params.args env) (Γ.length + 2) (by
      rw [Params.args_length]
      omega))
  exact ⟨last, hBody, kernel.output.correct kernel.code.result last _ _ hValue⟩

theorem Kernel.dispatch_eq (kernel : Kernel countExpr element)
    (funs : Funs S) (env : Verified.Env Γ) (n : Nat)
    (fits : kernel.toKernelPlan.spec.Fits (kernel.params.args env) n)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n)
    (hL0 : output[0]? = some (UInt32.ofNat n)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n ≤ count) (h32 : count ≤ 2 ^ 32) :
    kernel.module.dispatch ((kernel.params.args env).map LeanExe.WGSL.Arg.buffer) output count =
        some (LeanExe.WGSL.arrayWords
          (((Verified.Expr.build countExpr element).denote funs env).map kernel.output.encode)) ∧
      kernel.module.RaceFree ((kernel.params.args env).map LeanExe.WGSL.Arg.buffer)
        output.size count := by
  have hCount := kernel.counter.value funs env n (by
    cases hc : kernel.counter.count <;>
      simpa only [KernelPlan.spec, hc, FitsCount] using fits.count)
  have h := kernel.toKernelPlan.spec.dispatch_eq kernel.wf kernel.module kernel.translated
    (kernel.params.args env) n fits
    (fun k => kernel.output.encode (element.denote funs (.cons k env)))
    (fun k _ => kernel.element_denote funs env k n fits) output hOut hL0 hL1 count hCover h32
  simpa only [Verified.Expr.denote, hCount, build_map] using h

end Verified.WGSL
