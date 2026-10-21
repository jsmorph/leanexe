import Verified.WGSL.Branch

namespace Verified.WGSL

open LeanExe.IR

variable {t : Verified.Ty} {ctx : Verified.WGSL.Context Γ}

theorem branchBody_run (cell : Cell t) {slot base : Nat}
    {value : Funs S → Verified.Env Γ → t.denote} (code : Code ctx base value)
    (ctxBound : ctx.Bounded base) (funs : Funs S) (env : Verified.Env Γ)
    (locals : Locals) (arrays : Arrays) (agree : ctx.Agrees env locals arrays)
    (unused : ∀ j, base ≤ j → arrays j = none) (hSlot : arrays slot = none) :
    ∃ last, (branchBody cell slot code).denote arrays locals = some last ∧
      last slot = some (cell.type.value (cell.encode (value funs env))) := by
  obtain ⟨before, hBody, hValue⟩ := code.correct ctxBound funs env locals arrays agree unused
  refine ⟨put before slot (cell.type.value (cell.encode (value funs env))), ?_, by simp [put]⟩
  simp only [branchBody, Stmt.denote, hBody, Option.bind_some, hSlot, ↓reduceIte,
    cell.inputHolds code.result before arrays _ hValue, Option.map_some]
  rfl

theorem loopBody_run (cell : Cell t) (slot base : Nat) (lower : base ≤ slot)
    (ctxBound : ctx.Bounded base)
    {value : Funs S → Verified.Env (t :: .word :: Γ) → t.denote}
    (code : Code (.cons (cell.read slot) (.cons (.word (.get (slot + 2))) ctx)) (slot + 3) value)
    (funs : Funs S) (env : Verified.Env Γ) (locals : Locals) (arrays : Arrays)
    (agree : ctx.Agrees env locals arrays) (unused : ∀ j, slot ≤ j → arrays j = none)
    (count : LeanExe.IR.Expr .u64) (n : UInt64) (init : t.denote)
    (hCount : count.denote locals arrays = some n)
    (hInit : locals slot = some (cell.type.value (cell.encode init))) :
    ∃ last, (Stmt.loop (slot + 1) (slot + 2) count (branchBody cell slot code)).denote arrays
        locals = some last ∧
      (cell.read slot).Holds last arrays
        (LeanExe.loop n init fun k s => value funs (.cons s (.cons k env))) := by
  let : LeanExe.Pipeline.Scalar t.denote := ⟨fun x => [cell.type.value (cell.encode x)]⟩
  have outside : ∀ j ∈ (branchBody cell slot code).writes, j = slot ∨ slot + 3 ≤ j := by
    intro j hj
    rw [branchBody_writes] at hj
    rcases hj with hj | rfl
    · exact Or.inr (code.writes j hj).1
    · exact Or.inl rfl
  have bodyBound : (Verified.WGSL.Context.cons (cell.read slot)
      (.cons (.word (.get (slot + 2))) ctx)).Bounded (slot + 3) := by
    apply ((ctxBound.mono (by omega)).cons (by exact Nat.le_refl _)).cons
    have := cell.readBound slot
    omega
  obtain ⟨last, hLoop, hHold⟩ := Stmt.denote_loop
    (α := t.denote) (vars := [slot]) (limit := slot + 1) (index := slot + 2)
    (fun k s => value funs (.cons s (.cons k env))) (by omega)
    ⟨unused _ (by omega), unused _ (by omega)⟩
    ⟨fun h => by have := outside _ h; omega, fun h => by have := outside _ h; omega⟩
    (by intro j hj; simp only [List.mem_singleton] at hj; subst j; omega)
    hCount (List.Forall₂.cons hInit .nil) (by
      intro k s current _ hFrame hIndex _ hState
      have hOuter : ctx.Agrees env current arrays := agree.frame ctxBound fun j hj => by
        apply hFrame j
        simp only [List.mem_cons, not_or]
        refine ⟨by omega, by omega, ?_⟩
        intro hw
        have := outside j hw
        omega
      have hWord : (Rep.word (.get (slot + 2))).Holds current arrays (UInt64.ofNat k) := by
        simp [Rep.Holds, LeanExe.IR.Expr.denote, hIndex]
      have hState' : current slot = some (cell.type.value (cell.encode s)) := by
        cases hState with
        | cons h _ => exact h
      have hAgree := (hOuter.cons hWord).cons (cell.readHolds current arrays slot s hState')
      obtain ⟨last, hBody, hValue⟩ := branchBody_run cell code bodyBound funs
        (.cons s (.cons (UInt64.ofNat k) env)) current arrays hAgree
        (fun j hj => unused j (by omega)) (unused slot (Nat.le_refl _))
      exact ⟨last, hBody, List.Forall₂.cons hValue .nil⟩)
  exact ⟨last, hLoop, cell.readHolds last arrays slot _ (by
    cases hHold with
    | cons h _ => exact h)⟩

end Verified.WGSL
