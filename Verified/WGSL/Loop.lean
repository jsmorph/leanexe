import Verified.WGSL.LoopBody

namespace Verified.WGSL

open LeanExe.WGSL.Source

variable {t : Verified.Ty} {ctx : Verified.WGSL.Context Γ} {base : Nat}

def Code.loop (cell : Cell t) {count : Funs S → Verified.Env Γ → UInt64}
    {init : Funs S → Verified.Env Γ → t.denote}
    {step : Funs S → Verified.Env (t :: .word :: Γ) → t.denote}
    (a : Code ctx base (t := .word) count) (b : Code ctx a.next init)
    (c : Code (.cons (cell.read b.next) (.cons (.word (.get (b.next + 2))) ctx))
      (b.next + 3) step) :
    Code ctx base (fun funs env => LeanExe.loop (count funs env) (init funs env)
      fun k s => step funs (.cons s (.cons k env))) where
  next := c.next
  body := .seq a.body (.seq (branchBody cell b.next b)
    (Stmt.loop (b.next + 1) (b.next + 2) a.result.wordExpr (branchBody cell b.next c)))
  result := cell.read b.next
  vars := a.vars ++ b.vars ++ [(b.next, cell.type), (b.next + 1, .u64), (b.next + 2, .u64)] ++
    c.vars
  grows := by have := a.grows; have := b.grows; have := c.grows; omega
  writes := by
    intro j hj
    simp only [Stmt.loop, branchBody, Stmt.writes, List.mem_append, List.mem_singleton,
      or_assoc] at hj
    have ha := a.grows
    have hb := b.grows
    have hc := c.grows
    rcases hj with hj | hj | hj | hj | hj | hj | hj | hj
    · have := a.writes j hj; omega
    · have := b.writes j hj; omega
    · omega
    · omega
    · omega
    · have := c.writes j hj; omega
    · omega
    · omega
  resultBound := by have := cell.readBound b.next; have := c.grows; omega
  correct := by
    intro ctxBound funs env locals arrays agree unused
    obtain ⟨middle, ha, hva⟩ := a.correct ctxBound funs env locals arrays agree unused
    have hAgreeA := agree.frame ctxBound (a.frame ha)
    obtain ⟨start, hb, hInit⟩ := branchBody_run cell b (ctxBound.mono a.grows) funs env
      middle arrays hAgreeA (fun j hj => unused j (Nat.le_trans a.grows hj))
      (unused b.next (Nat.le_trans a.grows b.grows))
    have hFrame : ∀ j, j < a.next → start j = middle j := by
      intro j hj
      apply Stmt.denote_frame arrays (branchBody cell b.next b) middle start hb j
      rw [branchBody_writes]
      intro h
      rcases h with h | rfl
      · have := (b.writes j h).1; omega
      · have := b.grows; omega
    have hCount : a.result.wordExpr.denote start arrays = some (count funs env) := by
      have hBound : a.result.wordExpr.denoteLocals ≤ a.next := by
        cases hr : a.result
        simpa only [hr, Rep.locals, Rep.wordExpr] using a.resultBound
      rw [LeanExe.WGSL.Source.Expr.denote_congr a.result.wordExpr middle start arrays
        (fun j hj => hFrame j (by omega))]
      cases hr : a.result
      simpa only [hr, Rep.Holds, Rep.wordExpr] using hva
    obtain ⟨last, hLoop, hResult⟩ := loopBody_run cell b.next base
      (Nat.le_trans a.grows b.grows) ctxBound c funs env start arrays
      (hAgreeA.frame ctxBound (fun j hj => hFrame j (by have := a.grows; omega)))
      (fun j hj => unused j (Nat.le_trans (Nat.le_trans a.grows b.grows) hj))
      a.result.wordExpr (count funs env) (init funs env) hCount hInit
    exact ⟨last, by simp [Stmt.denote, ha, hb, hLoop], hResult⟩

end Verified.WGSL
