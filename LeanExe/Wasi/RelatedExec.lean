import LeanExe.Wasi.Related

namespace LeanExe.Wasi

theorem LoopExec.transfer {World : Type} {host : Host World}
    {states : σ → τ → Prop} {relation : α → β → Prop}
    {leftTest : UInt64 → σ → Bool} {rightTest : UInt64 → τ → Bool}
    {leftStep : UInt64 → σ → Action σ} {rightStep : UInt64 → τ → Action τ}
    {leftNext : σ → Action α} {rightNext : τ → Action β}
    (tests : ∀ index left right, states left right → leftTest index left = rightTest index right)
    (steps : ∀ index left right, states left right →
      ∀ world trace outcome final, Exec host (leftStep index left) world trace outcome final →
        ∃ result, Exec host (rightStep index right) world trace result final ∧
          Outcome.Rel states outcome result)
    (next : ∀ left right, states left right →
      ∀ world trace outcome final, Exec host (leftNext left) world trace outcome final →
        ∃ result, Exec host (rightNext right) world trace result final ∧
          Outcome.Rel relation outcome result)
    (remaining : Nat) : ∀ {index left right world trace outcome final}, states left right →
      LoopExec host remaining index left leftTest leftStep leftNext world trace outcome final →
        ∃ result, LoopExec host remaining index right rightTest rightStep rightNext
          world trace result final ∧ Outcome.Rel relation outcome result := by
  induction remaining with
  | zero =>
      intro index left right world trace outcome final related execution
      cases execution with
      | zero execution =>
          obtain ⟨result, execution, values⟩ := next left right related _ _ _ _ execution
          exact ⟨result, .zero execution, values⟩
  | succ remaining ih =>
      intro index left right world trace outcome final related execution
      cases execution with
      | stop test execution =>
          obtain ⟨result, execution, values⟩ := next left right related _ _ _ _ execution
          exact ⟨result, .stop ((tests _ _ _ related).symm.trans test) execution, values⟩
      | next test execution rest =>
          obtain ⟨middle, execution, values⟩ := steps _ left right related _ _ _ _ execution
          cases values with
          | returned values =>
              obtain ⟨result, rest, results⟩ := ih values rest
              exact ⟨result, .next ((tests _ _ _ related).symm.trans test) execution rest,
                results⟩
      | exit test execution =>
          obtain ⟨middle, execution, values⟩ := steps _ left right related _ _ _ _ execution
          cases values with
          | exited code =>
              exact ⟨_, .exit ((tests _ _ _ related).symm.trans test) execution, .exited _⟩
      | trap test execution =>
          obtain ⟨middle, execution, values⟩ := steps _ left right related _ _ _ _ execution
          cases values with
          | trapped message =>
              exact ⟨_, .trap ((tests _ _ _ related).symm.trans test) execution, .trapped _⟩

theorem Action.Rel.exec {World : Type} {host : Host World} {relation : α → β → Prop}
    {left : Action α} {right : Action β} (related : Action.Rel relation left right) :
    ∀ world trace outcome final, Exec host left world trace outcome final →
      ∃ result, Exec host right world trace result final ∧ Outcome.Rel relation outcome result := by
  induction related with
  | pure value =>
      intro world trace outcome final execution
      cases execution
      exact ⟨_, .pure _ _, .returned value⟩
  | read capacity next ih =>
      intro world trace outcome final execution
      cases execution with
      | read_reject bound execution =>
          obtain ⟨result, execution, values⟩ := ih _ _ _ _ _ execution
          exact ⟨result, .read_reject bound execution, values⟩
      | read_return bound hostReply execution =>
          obtain ⟨result, execution, values⟩ := ih _ _ _ _ _ execution
          exact ⟨result, .read_return bound hostReply execution, values⟩
      | read_trap bound hostReply => exact ⟨_, .read_trap bound hostReply, .trapped _⟩
  | write output bytes next ih =>
      intro world trace outcome final execution
      cases execution with
      | write_return hostReply execution =>
          obtain ⟨result, execution, values⟩ := ih _ _ _ _ _ execution
          exact ⟨result, .write_return hostReply execution, values⟩
      | write_trap hostReply => exact ⟨_, .write_trap hostReply, .trapped _⟩
  | exit code =>
      intro world trace outcome final execution
      cases execution with
      | exit hostReply => exact ⟨_, .exit hostReply, .exited _⟩
      | exitTrap hostReply => exact ⟨_, .exitTrap hostReply, .trapped _⟩
  | loop count initial tests steps next ihStep ihNext =>
      intro world trace outcome final execution
      cases execution with
      | loop execution =>
          obtain ⟨result, execution, values⟩ :=
            LoopExec.transfer tests ihStep ihNext count.toNat initial execution
          exact ⟨result, .loop execution, values⟩

theorem Action.Rel.exec_back {World : Type} {host : Host World} {relation : α → β → Prop}
    {left : Action α} {right : Action β} (related : Action.Rel relation left right)
    {world trace outcome final} (execution : Exec host right world trace outcome final) :
    ∃ result, Exec host left world trace result final ∧ Outcome.Rel relation result outcome := by
  obtain ⟨result, execution, values⟩ := related.symm.exec _ _ _ _ execution
  refine ⟨result, execution, ?_⟩
  cases values with
  | returned value => exact .returned value
  | exited code => exact .exited code
  | trapped message => exact .trapped message

theorem Action.Rel.exec_returned_iff {World : Type} {host : Host World}
    {flatten : α → β} {left : Action α} {right : Action β}
    (related : Action.Rel (fun native flat => flat = flatten native) left right)
    {world trace value final} :
    Exec host right world trace (.returned value) final ↔
      ∃ native, Exec host left world trace (.returned native) final ∧ value = flatten native := by
  constructor
  · intro execution
    obtain ⟨result, execution, values⟩ := related.exec_back execution
    cases values with
    | returned value => exact ⟨_, execution, value⟩
  · rintro ⟨native, execution, value⟩
    obtain ⟨result, execution, values⟩ := related.exec _ _ _ _ execution
    cases values with
    | returned same => simpa only [same, value] using execution

end LeanExe.Wasi
