import Verified.Wasi.ResourceRules
import Verified.ChargeFacts
import Verified.Wasi.Observed
import LeanExe.Wasi.PrefixProgress

/-! The premises of the resource rule of a `sys` command.  The rule bounds the command's charge on
every run and every prefix that the host permits.  A flat call's charge does not depend on the
trace, so a bound for every trace gives both premises.  A reported call's charge is the
allocation cost of the block that its reporter's reply asks for, and the first event of every run
and every nonempty prefix is that reply, so a bound on the blocks of the replies the host permits
gives both premises.  For the observed host of a run, the permitted replies are those of the base
host. -/

namespace Verified.Wasi.Resource

open LeanExe.Wasi

/-- A prefix of a call that its arguments do not reject is empty and leaves the call, or starts
with the call's event, whose reply the host permits. -/
theorem prefix_sys_first {World α : Type} {host : Host World} {call : Call} {args : List Arg}
    {next : Reply → Action α} (accepted : call.reject args = 0) {world : World}
    {trace : List Event} {residual : Action α} {after : World}
    (progress : PrefixProgress host (.sys call args next) world trace residual after) :
    (trace = [] ∧ residual = .sys call args next ∧ after = world) ∨
      ∃ reply middle rest, trace = .sys call args reply :: rest ∧
        host.sys world call args reply middle := by
  generalize hAction : (Action.sys call args next : Action α) = action at progress
  induction progress with
  | refl => exact .inl ⟨rfl, rfl, rfl⟩
  | advance step =>
    subst hAction
    cases step with
    | sys_reject fits => exact absurd accepted fits
    | sys_return _ reply => exact .inr ⟨_, _, [], rfl, reply⟩
  | trans _ _ ihHead ihTail =>
    rcases ihHead hAction with ⟨rfl, rfl, rfl⟩ | ⟨reply, middle, rest, rfl, permitted⟩
    · rcases ihTail hAction with ⟨rfl, rfl, rfl⟩ | ⟨reply, middle, rest, rfl, permitted⟩
      · exact .inl ⟨rfl, rfl, rfl⟩
      · exact .inr ⟨reply, middle, rest, rfl, permitted⟩
    · exact .inr ⟨reply, middle, _, List.cons_append .., permitted⟩

/-- A run of a call that its arguments do not reject starts with the call's event, whose reply
the host permits. -/
theorem exec_sys_first {World α : Type} {host : Host World} {call : Call} {args : List Arg}
    {next : Reply → Action α} (accepted : call.reject args = 0) {world : World}
    {trace : List Event} {outcome : Outcome α} {final : World}
    (run : Exec host (.sys call args next) world trace outcome final) :
    ∃ reply middle rest, trace = .sys call args reply :: rest ∧
      host.sys world call args reply middle := by
  cases run with
  | sys_reject fits => exact absurd accepted fits
  | sys_return _ reply => exact ⟨_, _, _, rfl, reply⟩
  | sys_trap _ reply => exact ⟨_, _, [], rfl, reply⟩

/-- The block that a successful reply of a reporter asks for: the shown size, three bytes, and
four bytes for each hidden pointer. -/
def reportedSize (outputs : List LeanExe.Bytes) : Nat :=
  ((⟨0, outputs⟩ : Reply).word 1 + 4 * (⟨0, outputs⟩ : Reply).word 0 + 3).toNat

/-- The charge of a reported call on a trace that is empty or starts with a reply of its reporter
that `host` permits in `world` is at most the allocation cost of `limit`, when every successful
reply that `host` permits there asks for a block of at most `limit` bytes. -/
theorem reported_cost_le {World : Type} {host : Host World} {call : Call} {values : List UInt64}
    {limit : Nat} {world : World} {trace : List Event}
    (bound : ∀ outputs after, host.sys world call.reporterCall [] (.returned 0 outputs) after →
      reportedSize outputs ≤ limit)
    (first : trace = [] ∨ ∃ reply middle rest, trace = .sys call.reporterCall [] reply :: rest ∧
      host.sys world call.reporterCall [] reply middle) :
    sysCost .reported call values trace ≤ Bytes.allocationCost limit := by
  rcases first with rfl | ⟨reply, middle, rest, rfl, permitted⟩
  · simp [sysCost, reportedBlock]
  · cases reply with
    | trapped message outputs => simp [sysCost, reportedBlock]
    | returned errno outputs =>
      by_cases accepted : errno = 0 ∧ (⟨errno, outputs⟩ : Reply).word 1 +
          4 * (⟨errno, outputs⟩ : Reply).word 0 + 3 < 4294967296
      · obtain ⟨rfl, small⟩ := accepted
        simp only [sysCost, reportedBlock, small, and_self, ↓reduceIte]
        exact allocationCost_mono (bound outputs middle permitted)
      · simp only [sysCost, reportedBlock, accepted, ↓reduceIte]
        exact Nat.zero_le _

/-- The premises of the rule of a `sys` command from a bound on its charge on every trace. -/
theorem sys_rule_of_bound {World : Type} {host : Host World} {form : SysForm} {call : Call}
    {values : List UInt64} {budget : Nat}
    (bound : ∀ trace, sysCost form call values trace ≤ budget) :
    (∀ world trace outcome final, Exec host (form.run call values) world trace outcome final →
      sysCost form call values trace ≤ budget) ∧
    (∀ world trace residual final, Prefix host (form.run call values) world trace residual final →
      sysCost form call values trace ≤ budget) :=
  ⟨fun _ trace _ _ _ => bound trace, fun _ trace _ _ _ => bound trace⟩

/-- The premises of the rule of a reported call, when every successful reply of its reporter that
`host` permits asks for a block of at most `limit` bytes, and the allocation cost of `limit` is
within the budget. -/
theorem reported_rule {World : Type} {host : Host World} {call : Call} {values : List UInt64}
    {limit budget : Nat}
    (bound : ∀ world outputs after, host.sys world call.reporterCall [] (.returned 0 outputs) after →
      reportedSize outputs ≤ limit)
    (enough : Bytes.allocationCost limit ≤ budget) :
    (∀ world trace outcome final, Exec host (SysForm.reported.run call values) world trace outcome
      final → sysCost .reported call values trace ≤ budget) ∧
    (∀ world trace residual final, Prefix host (SysForm.reported.run call values) world trace
      residual final → sysCost .reported call values trace ≤ budget) := by
  have accepted : call.reporterCall.reject [] = 0 := rfl
  refine ⟨fun world trace outcome final run => ?_, fun world trace residual final progress => ?_⟩
  · exact (reported_cost_le (bound world) (.inr (exec_sys_first accepted run))).trans enough
  · rcases prefix_sys_first accepted progress.progress with ⟨rfl, _, _⟩ | first
    · exact (reported_cost_le (bound world) (.inl rfl)).trans enough
    · exact (reported_cost_le (bound world) (.inr first)).trans enough

/-- `reported_rule` for the observed host of a run, from a bound on the replies of the base
host. -/
theorem reported_rule_observed {World : Type} {host : Host World} {call : Call}
    {values : List UInt64} {limit budget : Nat}
    (bound : ∀ world outputs after, host.sys world call.reporterCall [] (.returned 0 outputs) after →
      reportedSize outputs ≤ limit)
    (enough : Bytes.allocationCost limit ≤ budget) :
    (∀ world trace outcome final, Exec (observedHost host) (SysForm.reported.run call values) world
      trace outcome final → sysCost .reported call values trace ≤ budget) ∧
    (∀ world trace residual final, Prefix (observedHost host) (SysForm.reported.run call values)
      world trace residual final → sysCost .reported call values trace ≤ budget) :=
  reported_rule (fun _ outputs _ permitted => bound _ outputs _ permitted.1) enough

end Verified.Wasi.Resource
