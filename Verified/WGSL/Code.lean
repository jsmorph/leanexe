import Verified.WGSL.Context
import LeanExe.IR.DenoteStmt

namespace Verified.WGSL

variable {s t u : Ty}

structure Code (ctx : Context Γ) (base : Nat) (value : Funs S → Verified.Env Γ → t.denote) where
  next : Nat
  body : LeanExe.IR.Stmt
  result : Rep t
  vars : List (Nat × LeanExe.IR.ScalarType)
  grows : base ≤ next
  writes : ∀ j ∈ body.writes, base ≤ j ∧ j < next
  resultBound : result.locals ≤ next
  correct : ctx.Bounded base → ∀ funs env locals arrays,
    ctx.Agrees env locals arrays → (∀ j, base ≤ j → arrays j = none) →
    ∃ last, body.denote arrays locals = some last ∧
      result.Holds last arrays (value funs env)

theorem Code.frame {ctx : Context Γ} {base : Nat}
    {value : Funs S → Verified.Env Γ → t.denote} (code : Code ctx base value)
    {locals last : Locals} {arrays : Arrays}
    (h : code.body.denote arrays locals = some last) :
    ∀ j, j < base → last j = locals j := by
  intro j hj
  exact LeanExe.IR.Stmt.denote_frame arrays code.body locals last h j
    (fun hw => by have := (code.writes j hw).1; omega)

def Code.atom {ctx : Context Γ} {base : Nat} {value : Funs S → Verified.Env Γ → t.denote}
    (rep : Rep t) (bound : rep.locals ≤ base)
    (h : ∀ funs env locals arrays, ctx.Agrees env locals arrays →
      rep.Holds locals arrays (value funs env)) : Code ctx base value where
  next := base
  body := .skip
  result := rep
  vars := []
  grows := Nat.le_refl _
  writes := by simp [LeanExe.IR.Stmt.writes]
  resultBound := bound
  correct := fun _ funs env locals arrays agree _ => ⟨locals, rfl, h funs env locals arrays agree⟩

def Code.map {ctx : Context Γ} {base : Nat}
    {value : Funs S → Verified.Env Γ → s.denote} (code : Code ctx base value)
    (op : s.denote → t.denote) (rep : Rep s → Rep t)
    (bound : ∀ r, (rep r).locals ≤ r.locals)
    (holds : ∀ r locals arrays x, r.Holds locals arrays x →
      (rep r).Holds locals arrays (op x)) :
    Code ctx base (fun funs env => op (value funs env)) where
  next := code.next
  body := code.body
  result := rep code.result
  vars := code.vars
  grows := code.grows
  writes := code.writes
  resultBound := Nat.le_trans (bound code.result) code.resultBound
  correct := by
    intro ctxBound funs env locals arrays agree unused
    obtain ⟨last, hBody, hValue⟩ := code.correct ctxBound funs env locals arrays agree unused
    exact ⟨last, hBody, holds code.result last arrays _ hValue⟩

def Code.map₂ {ctx : Context Γ} {base : Nat}
    {left : Funs S → Verified.Env Γ → s.denote}
    {right : Funs S → Verified.Env Γ → t.denote}
    (a : Code ctx base left) (b : Code ctx a.next right)
    (op : s.denote → t.denote → u.denote) (rep : Rep s → Rep t → Rep u)
    (bound : ∀ a b, (rep a b).locals ≤ max a.locals b.locals)
    (holds : ∀ a b locals arrays x y, a.Holds locals arrays x → b.Holds locals arrays y →
      (rep a b).Holds locals arrays (op x y)) :
    Code ctx base (fun funs env => op (left funs env) (right funs env)) where
  next := b.next
  body := .seq a.body b.body
  result := rep a.result b.result
  vars := a.vars ++ b.vars
  grows := Nat.le_trans a.grows b.grows
  writes := by
    intro j hj
    simp only [LeanExe.IR.Stmt.writes, List.mem_append] at hj
    rcases hj with hj | hj
    · have := a.writes j hj
      exact ⟨this.1, Nat.lt_of_lt_of_le this.2 b.grows⟩
    · have := b.writes j hj
      exact ⟨Nat.le_trans a.grows this.1, this.2⟩
  resultBound := Nat.le_trans (bound a.result b.result)
    (max_le (Nat.le_trans a.resultBound b.grows) b.resultBound)
  correct := by
    intro ctxBound funs env locals arrays agree unused
    obtain ⟨middle, ha, hva⟩ := a.correct ctxBound funs env locals arrays agree unused
    obtain ⟨last, hb, hvb⟩ := b.correct (ctxBound.mono a.grows) funs env middle arrays
      (agree.frame ctxBound (a.frame ha)) (fun j hj => unused j (Nat.le_trans a.grows hj))
    have hva' := hva.congr a.resultBound (b.frame hb)
    exact ⟨last, by simp [LeanExe.IR.Stmt.denote, ha, hb],
      holds a.result b.result last arrays _ _ hva' hvb⟩

def Code.bind {ctx : Context Γ} {base : Nat}
    {value : Funs S → Verified.Env Γ → s.denote}
    {bodyValue : Funs S → Verified.Env (s :: Γ) → t.denote}
    (a : Code ctx base value) (b : Code (.cons a.result ctx) a.next bodyValue) :
    Code ctx base (fun funs env => bodyValue funs (.cons (value funs env) env)) where
  next := b.next
  body := .seq a.body b.body
  result := b.result
  vars := a.vars ++ b.vars
  grows := Nat.le_trans a.grows b.grows
  writes := by
    intro j hj
    simp only [LeanExe.IR.Stmt.writes, List.mem_append] at hj
    rcases hj with hj | hj
    · have := a.writes j hj
      exact ⟨this.1, Nat.lt_of_lt_of_le this.2 b.grows⟩
    · have := b.writes j hj
      exact ⟨Nat.le_trans a.grows this.1, this.2⟩
  resultBound := b.resultBound
  correct := by
    intro ctxBound funs env locals arrays agree unused
    obtain ⟨middle, ha, hva⟩ := a.correct ctxBound funs env locals arrays agree unused
    obtain ⟨last, hb, hvb⟩ := b.correct
      ((ctxBound.mono a.grows).cons a.resultBound) funs (.cons (value funs env) env) middle
      arrays ((agree.frame ctxBound (a.frame ha)).cons hva)
      (fun j hj => unused j (Nat.le_trans a.grows hj))
    exact ⟨last, by simp [LeanExe.IR.Stmt.denote, ha, hb], hvb⟩

end Verified.WGSL
