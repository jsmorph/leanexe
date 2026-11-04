import LeanExe.WGSL.Build

namespace LeanExe.WGSL

theorem _root_.LeanExe.Source.Spec.wgsl_workgroupSize {K : Source.Spec} {m : Module} (h : K.wgsl = some m) :
    m.workgroupSize = 64 := by
  unfold Source.Spec.wgsl at h
  cases h1 : trStmt K.wgslLayout K.body (1 + K.width) with
  | none => simp [h1] at h
  | some a =>
    cases h2 : trExpr K.wgslLayout K.element a.2 with
    | none => simp [h1, h2] at h
    | some b =>
      simp only [h1, h2, bind, Option.bind, pure, Option.some.injEq] at h
      rw [← h]

end LeanExe.WGSL
