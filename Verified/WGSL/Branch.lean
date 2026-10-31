import Verified.WGSL.Binding

namespace Verified.WGSL

variable {t : Ty} {ctx : Context Γ} {base : Nat}

def branchBody (cell : Cell t) (slot : Nat) {value : Funs S → Verified.Env Γ → t.denote}
    (code : Code ctx base value) : LeanExe.WGSL.Source.Stmt :=
  .seq code.body (.assign slot (cell.input code.result))

theorem branchBody_writes (cell : Cell t) (slot : Nat)
    {value : Funs S → Verified.Env Γ → t.denote} (code : Code ctx base value) (j : Nat) :
    j ∈ (branchBody cell slot code).writes ↔ j ∈ code.body.writes ∨ j = slot := by
  simp [branchBody, LeanExe.WGSL.Source.Stmt.writes]

def Code.branch (cell : Cell t) {condition : Funs S → Verified.Env Γ → Bool}
    {yes no : Funs S → Verified.Env Γ → t.denote}
    (c : Code ctx base (t := .bool) condition)
    (a : Code ctx (c.next + 1) yes) (b : Code ctx a.next no) :
    Code ctx base (fun funs env => if condition funs env then yes funs env else no funs env) where
  next := b.next
  body := .seq c.body (.ite c.result.boolExpr (branchBody cell c.next a) (branchBody cell c.next b))
  result := cell.read c.next
  vars := c.vars ++ (c.next, cell.type) :: (a.vars ++ b.vars)
  grows := by have := c.grows; have := a.grows; have := b.grows; omega
  writes := by
    intro j hj
    simp only [LeanExe.WGSL.Source.Stmt.writes, List.mem_append] at hj
    have hc := c.grows
    have ha := a.grows
    have hb := b.grows
    rcases hj with hj | hj | hj
    · have := c.writes j hj; omega
    · rw [branchBody_writes] at hj
      rcases hj with hj | rfl
      · have := a.writes j hj; omega
      · omega
    · rw [branchBody_writes] at hj
      rcases hj with hj | rfl
      · have := b.writes j hj; omega
      · omega
  resultBound := by
    have := cell.readBound c.next
    have := a.grows
    have := b.grows
    omega
  correct := by
    intro ctxBound funs env locals arrays agree unused
    obtain ⟨middle, hc, hcv⟩ := c.correct ctxBound funs env locals arrays agree unused
    have hAgree := agree.frame ctxBound (c.frame hc)
    have hCond : c.result.boolExpr.denote middle arrays = some (condition funs env) := by
      cases hr : c.result
      simpa only [hr, Rep.Holds, Rep.boolExpr] using hcv
    have run : ∀ {branchBase : Nat} {value : Funs S → Verified.Env Γ → t.denote}
        (code : Code ctx branchBase value), base ≤ branchBase →
        ∃ last, (branchBody cell c.next code).denote arrays middle = some last ∧
          (cell.read c.next).Holds last arrays (value funs env) := by
      intro branchBase value code hBase
      obtain ⟨before, hBody, hValue⟩ := code.correct (ctxBound.mono hBase) funs env middle arrays
        hAgree (fun j hj => unused j (Nat.le_trans hBase hj))
      refine ⟨put before c.next (cell.type.value (cell.encode (value funs env))), ?_,
        cell.readHolds _ arrays c.next _ (by simp [put])⟩
      simp only [branchBody, LeanExe.WGSL.Source.Stmt.denote, hBody, Option.bind_some,
        unused c.next c.grows, ↓reduceIte, cell.inputHolds code.result before arrays _ hValue,
        Option.map_some]
      rfl
    cases hChoice : condition funs env
    · obtain ⟨last, hb, hv⟩ := run b (by have := c.grows; have := a.grows; omega)
      exact ⟨last, by simp [LeanExe.WGSL.Source.Stmt.denote, hc, hCond, hChoice, hb],
        by simpa [hChoice]⟩
    · obtain ⟨last, ha, hv⟩ := run a (by have := c.grows; omega)
      exact ⟨last, by simp [LeanExe.WGSL.Source.Stmt.denote, hc, hCond, hChoice, ha],
        by simpa [hChoice]⟩

end Verified.WGSL
