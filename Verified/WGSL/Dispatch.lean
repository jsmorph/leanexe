import Verified.WGSL.Kernel
import LeanExe.WGSL.MemoryModelProof

namespace Verified.WGSL

open Verified.Kernel

variable {countExpr : Verified.Expr S Γ .word}
  {element : Verified.Expr S (.word :: Γ) (.elem e)}

theorem Kernel.dispatch_eq (kernel : Kernel countExpr element)
    (funs : Funs S) (env : Verified.Env Γ) (n : Nat)
    (fits : kernel.toKernelPlan.spec.Fits (kernel.params.args env) n)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n)
    (hL0 : output[0]? = some (UInt32.ofNat n)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n ≤ count) (h32 : count ≤ 2 ^ 32) :
    kernel.module.dispatch ((kernel.params.args env).map LeanExe.Source.Arg.wgslBuffer) output count =
        some (LeanExe.WGSL.arrayWords
          (((Verified.Expr.build countExpr element).denote funs env).map kernel.output.encode)) ∧
      kernel.module.RaceFree ((kernel.params.args env).map LeanExe.Source.Arg.wgslBuffer)
        output.size count := by
  have hCount := kernel.counter.value funs env n (by
    cases hc : kernel.counter.count <;>
      simpa only [KernelPlan.spec, hc, FitsCount] using fits.count)
  have h := kernel.toKernelPlan.spec.wgsl_dispatch kernel.wf kernel.module kernel.translated
    (kernel.params.args env) n fits
    (fun k => kernel.output.encode (element.denote funs (.cons k env)))
    (fun k _ => kernel.toKernelPlan.element_denote kernel.wf funs env k n fits) output hOut hL0 hL1 count hCover h32
  simpa only [Verified.Expr.denote, hCount, build_map] using h

/-- The dispatch of a kernel under the memory model of `LeanExe.WGSL.MemoryModel`: a consistent
execution exists, and in every consistent execution there is no data race, every invocation ends,
and the reads after the dispatch return the source array's words. -/
theorem Kernel.executions_eq (kernel : Kernel countExpr element)
    (funs : Funs S) (env : Verified.Env Γ) (n : Nat)
    (fits : kernel.toKernelPlan.spec.Fits (kernel.params.args env) n)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n)
    (hL0 : output[0]? = some (UInt32.ofNat n)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n ≤ count) (h32 : count ≤ 2 ^ 32) :
    let d : LeanExe.WGSL.Dispatch :=
      ⟨kernel.module, (kernel.params.args env).map LeanExe.Source.Arg.wgslBuffer, output, count⟩
    (∃ E, d.Consistent E) ∧ ∀ E, d.Consistent E →
      d.NoDataRace E ∧ (∀ g, g < count → (d.events (E.oracle g) g).2 = true) ∧
        ∀ i, i < output.size →
          (LeanExe.WGSL.arrayWords (((Verified.Expr.build countExpr element).denote funs env).map
            kernel.output.encode))[i]? = some (E.observed i) := by
  intro d
  obtain ⟨h, hr⟩ := kernel.dispatch_eq funs env n fits output hOut hL0 hL1 count hCover h32
  refine ⟨d.execution_exists h hr, fun E hE => ?_⟩
  obtain ⟨hg, hrace, hobs⟩ := d.executions h hr E hE
  exact ⟨hrace, fun g hgc => (hg g hgc).2, hobs⟩

end Verified.WGSL

#print axioms Verified.WGSL.Kernel.executions_eq
