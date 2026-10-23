import LeanExe.Wasi.Related
import LeanExe.Wasi.PrefixProgress

namespace LeanExe.Wasi

theorem Action.Rel.resumeLoop {states : σ → τ → Prop} {relation : α → β → Prop}
    {leftTest : UInt64 → σ → Bool} {rightTest : UInt64 → τ → Bool}
    {leftStep : UInt64 → σ → Action σ} {rightStep : UInt64 → τ → Action τ}
    {leftNext : σ → Action α} {rightNext : τ → Action β}
    (tests : ∀ index left right, states left right → leftTest index left = rightTest index right)
    (steps : ∀ index left right, states left right →
      Action.Rel states (leftStep index left) (rightStep index right))
    (next : ∀ left right, states left right → Action.Rel relation (leftNext left) (rightNext right))
    (remaining : Nat) : ∀ {index left right}, states left right →
      Action.Rel relation (resumeLoop leftTest leftStep leftNext remaining index left)
        (resumeLoop rightTest rightStep rightNext remaining index right) := by
  induction remaining with
  | zero => intro index left right related; exact next left right related
  | succ remaining ih =>
      intro index left right related
      by_cases test : leftTest (UInt64.ofNat index) left = true
      · have rightRuns := (tests _ _ _ related).symm.trans test
        simpa only [LeanExe.Wasi.resumeLoop, test, rightRuns, ite_true] using
          (steps (UInt64.ofNat index) left right related).bind
            (fun a b value => ih (index := index + 1) value)
      · have rightStops : rightTest (UInt64.ofNat index) right ≠ true :=
          fun runs => test ((tests _ _ _ related).trans runs)
        simpa only [LeanExe.Wasi.resumeLoop, test, rightStops, Bool.false_eq_true, ite_false] using
          next left right related

theorem Action.Rel.advance {World : Type} {host : Host World} {relation : α → β → Prop}
    {left : Action α} {right : Action β} (related : Action.Rel relation left right)
    {world trace residual after} (advance : PrefixAdvance host left world trace residual after) :
    ∃ target, PrefixAdvance host right world trace target after ∧
      Action.Rel relation residual target := by
  cases related with
  | pure value => cases advance
  | read capacity next =>
      cases advance with
      | read_reject bound => exact ⟨_, .read_reject bound, next _⟩
      | read_return bound reply => exact ⟨_, .read_return bound reply, next _⟩
  | write output bytes next =>
      cases advance with
      | write_return reply => exact ⟨_, .write_return reply, next _⟩
  | exit code => cases advance
  | loop count initial tests steps next =>
      cases advance
      exact ⟨_, .loop, Action.Rel.resumeLoop tests steps next count.toNat initial⟩

theorem PrefixProgress.transfer {World : Type} {host : Host World}
    {relation : α → β → Prop} {left residual : Action α} {world trace after}
    (progress : PrefixProgress host left world trace residual after) :
    ∀ {right : Action β}, Action.Rel relation left right →
      ∃ target, PrefixProgress host right world trace target after ∧
        Action.Rel relation residual target := by
  induction progress with
  | refl => intro right related; exact ⟨right, .refl _ _, related⟩
  | advance step =>
      intro right related
      obtain ⟨target, step, related⟩ := related.advance step
      exact ⟨target, .advance step, related⟩
  | trans head tail ihHead ihTail =>
      intro right related
      obtain ⟨middle, head, related⟩ := ihHead related
      obtain ⟨target, tail, related⟩ := ihTail related
      exact ⟨target, .trans head tail, related⟩

theorem Action.Rel.transportPrefix {World : Type} {host : Host World} {relation : α → β → Prop}
    {left : Action α} {right : Action β} (related : Action.Rel relation left right)
    {world trace residual after} (hPrefix : Prefix host left world trace residual after) :
    ∃ target, Prefix host right world trace target after ∧ Action.Rel relation residual target := by
  obtain ⟨target, progress, related⟩ := hPrefix.progress.transfer related
  exact ⟨target, progress.toPrefix, related⟩

theorem Action.Rel.transportPrefixBack {World : Type} {host : Host World} {relation : α → β → Prop}
    {left : Action α} {right : Action β} (related : Action.Rel relation left right)
    {world trace residual after} (hPrefix : Prefix host right world trace residual after) :
    ∃ source, Prefix host left world trace source after ∧ Action.Rel relation source residual := by
  obtain ⟨source, hPrefix, related⟩ := related.symm.transportPrefix hPrefix
  exact ⟨source, hPrefix, related.symm⟩

end LeanExe.Wasi
