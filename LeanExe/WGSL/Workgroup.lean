import LeanExe.WGSL.Build

namespace LeanExe.WGSL

theorem Spec.module_workgroupSize {K : Spec} {m : Module} (h : K.module = some m) :
    m.workgroupSize = 64 := by
  unfold Spec.module at h
  cases h1 : trStmt K.layout K.body (1 + K.width) with
  | none => simp [h1] at h
  | some a =>
    cases h2 : trExpr K.layout K.element a.2 with
    | none => simp [h1, h2] at h
    | some b =>
      simp only [h1, h2, bind, Option.bind, pure, Option.some.injEq] at h
      rw [← h]

end LeanExe.WGSL
