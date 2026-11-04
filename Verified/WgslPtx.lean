import Verified.WGSL.Compile
import Verified.PTX.Compile

/-!
A build that both the WGSL and the PTX compiler translate has one kernel plan, so its PTX record,
arguments, and encoding equal the WGSL ones.  The launch theorems of PTX kernels use this to take
the argument conditions that the WGSL dispatch theorems prove.
-/

namespace Verified

open Verified.Kernel

theorem PTX.Compiled.of_wgsl {source : Verified.Expr S Γ (.array e)} {cw : WGSL.Compiled source}
    {cp : PTX.Compiled source} (hw : WGSL.compile source = some cw)
    (hp : PTX.compile source = some cp) :
    cp.spec = cw.spec ∧ cp.args = cw.args ∧ cp.encode = cw.encode := by
  obtain ⟨cc, ce, hshape, kw⟩ := cw
  obtain ⟨cc', ce', hshape', kp⟩ := cp
  subst hshape
  cases hshape'
  simp only [WGSL.compile, Option.map_eq_some_iff, WGSL.Compiled.mk.injEq, heq_eq_eq,
    true_and] at hw
  simp only [PTX.compile, Option.map_eq_some_iff, PTX.Compiled.mk.injEq, heq_eq_eq,
    true_and] at hp
  obtain ⟨kw', hkw, rfl⟩ := hw
  obtain ⟨kp', hkp, rfl⟩ := hp
  have hplan : kp'.toKernelPlan = kw'.toKernelPlan :=
    Option.some.inj ((PTX.compileKernel_plan hkp).symm.trans (WGSL.compileKernel_plan hkw))
  refine ⟨?_, ?_, ?_⟩
  · simp only [PTX.Compiled.spec, WGSL.Compiled.spec]
    rw [hplan]
  · funext env
    simp only [PTX.Compiled.args, WGSL.Compiled.args]
    rw [congrArg KernelPlan.params hplan]
  · funext x
    simp only [PTX.Compiled.encode, WGSL.Compiled.encode]
    rw [congrArg KernelPlan.output hplan]

end Verified

#print axioms Verified.PTX.Compiled.of_wgsl
