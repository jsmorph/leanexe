import Verified.Examples.Wgsl

namespace Verified.Examples.Wgsl

theorem scale_encoding : scaleGpu.encode = fun x => x.toBits.toUInt64 := rfl
theorem branch_encoding : branchGpu.encode = fun x => x.toBits.toUInt64 := rfl
theorem flags_encoding : flagsGpu.encode = Verified.boolWord := rfl
theorem words_encoding : wordsGpu.encode = id := rfl

theorem scale_dispatch (gain : Float32) (xs : Array Float32) (n : Nat)
    (fits : scaleGpu.spec.Fits (scaleGpu.args (.cons gain (.cons xs .nil))) n)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n)
    (hL0 : output[0]? = some (UInt32.ofNat n)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n ≤ count) (h32 : count ≤ 2 ^ 32) :
    verifiedScaleKernel.dispatch
        ((scaleGpu.args (.cons gain (.cons xs .nil))).map LeanExe.WGSL.Arg.buffer) output count =
      some (LeanExe.WGSL.arrayWords ((scale gain xs).map fun x => x.toBits.toUInt64)) ∧
    verifiedScaleKernel.RaceFree
      ((scaleGpu.args (.cons gain (.cons xs .nil))).map LeanExe.WGSL.Arg.buffer) output.size count := by
  have hValue : compiled.scale.func.body.denote .nil (.cons gain (.cons xs .nil)) = scale gain xs :=
    compiled.scale.denote_eq gain xs
  have h := scaleGpu.dispatch_eq .nil (.cons gain (.cons xs .nil)) n fits output hOut hL0 hL1
    count hCover h32
  rw [← scale_encoding]
  exact ⟨h.1.trans (congrArg (fun result =>
    some (LeanExe.WGSL.arrayWords (result.map scaleGpu.encode))) hValue), h.2⟩

private def branchFuns := Funs.cons (g := compiled.scale.func.sig)
  (compiled.scale.func.denote .nil) .nil

theorem branch_dispatch (xs : Array Float32) (n limit : UInt64) (size : Nat)
    (fits : branchGpu.spec.Fits (branchGpu.args (.cons xs (.cons n (.cons limit .nil)))) size)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * size)
    (hL0 : output[0]? = some (UInt32.ofNat size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : size ≤ count) (h32 : count ≤ 2 ^ 32) :
    verifiedBranchKernel.dispatch
        ((branchGpu.args (.cons xs (.cons n (.cons limit .nil)))).map LeanExe.WGSL.Arg.buffer)
        output count =
      some (LeanExe.WGSL.arrayWords ((branchSum xs n limit).map fun x => x.toBits.toUInt64)) ∧
    verifiedBranchKernel.RaceFree
      ((branchGpu.args (.cons xs (.cons n (.cons limit .nil)))).map LeanExe.WGSL.Arg.buffer)
      output.size count := by
  have hValue : compiled.branchSum.func.body.denote branchFuns
      (.cons xs (.cons n (.cons limit .nil))) = branchSum xs n limit :=
    compiled.branchSum.denote_eq xs n limit
  have h := branchGpu.dispatch_eq branchFuns (.cons xs (.cons n (.cons limit .nil))) size fits
    output hOut hL0 hL1 count hCover h32
  rw [← branch_encoding]
  exact ⟨h.1.trans (congrArg (fun result =>
    some (LeanExe.WGSL.arrayWords (result.map branchGpu.encode))) hValue), h.2⟩

#print axioms scale_dispatch
#print axioms branch_dispatch

end Verified.Examples.Wgsl
