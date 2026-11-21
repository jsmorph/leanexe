import Verified.Examples.WasiSys
import Verified.Wasi.BudgetTactics
import Verified.Wasi.SysWords
import Verified.Wasi.FunctionEntry
import Verified.FieldsArgs

/-! `_start` of `Verified.Examples.WasiSys.command` exits with an accepted status for every host
whose successful `args_sizes_get` replies ask for blocks of at most `limit` bytes, with `limit` at
most 4,294,897,328, every host environment satisfying `hostSpecWith host command.sysCalls`, and
every world, when the host does not trap along `main` and its exit (`total_of_bound`).  The
theorem discharges the heap, budget, and memory premises of the generated `command.total`.

The budget bounds the heap that `main` allocates (`body_bounded`).  The reflected body splits the
results of `args` and of `randomGet` into their components where `main` binds them, so no later
expression copies them, and the charge of `main` holds the block of `args`, which the reporter's
reply asks for, the four results of `wordBytes`, and the buffer of 16 bytes that `main` builds for
`randomGet`, which the call fills in place and charges nothing.  A returned `args` result holds at
most `limit` bytes (`args_bytes_le`).  With the literal pool's 4,096 bytes, the budget fits 65,535
pages exactly when `limit` is at most 4,294,897,328 (`initial_within`). -/

namespace Verified.Examples.WasiSys

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

/-- A bound on the heap that `main` allocates when the reporter's replies ask for blocks of at
most `limit` bytes: the block of `args`, at most `Bytes.allocationCost limit`, the four results of
`wordBytes` (56 bytes each), and the buffer of 16 bytes for `randomGet` (64 bytes). -/
def budget (limit : Nat) : Nat := Bytes.allocationCost limit + 288

private theorem wordBytes_charge (env : Env [Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get FVar.here env =
      56 := by
  cases env with
  | cons word rest =>
    cases rest
    exact (command.pureSources.wordBytes.bound_eq word).trans rfl

attribute [local charge_eqs] wordBytes_charge

private theorem exec_sys_returned {World α : Type} {host : Host World} {call : Call}
    {args : List Arg} {next : Reply → Action α} {world final : World} {trace : List Event}
    {value : α} (run : Exec host (.sys call args next) world trace (.returned value) final)
    (accepted : call.reject args = 0) :
    ∃ errno committed after rest, host.sys world call args (.returned errno committed) after ∧
      Exec host (next (sysReply errno committed)) after rest (.returned value) final := by
  cases run with
  | sys_reject fits => exact absurd accepted fits
  | sys_return _ permitted next => exact ⟨_, _, _, _, permitted, next⟩

/-- A returned `args` result holds at most `limit` bytes when every successful reply of the
reporter that `host` permits asks for a block of at most `limit` bytes: the bytes are those of
the shown region, whose size is the reporter's second word. -/
theorem args_bytes_le {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    {values : List UInt64} {world final : World} {trace : List Event}
    {value : UInt64 × UInt64 × UInt64 × LeanExe.Bytes}
    (run : Exec host (SysForm.reported.runWith Call.argsGet values [] []) world trace
      (.returned value) final) :
    value.2.2.2.data.size ≤ limit := by
  obtain ⟨errno, sizes, middle, rest, reporter, next⟩ := exec_sys_returned run rfl
  split at next
  · rw [exec_pure_value next]
    exact Nat.zero_le _
  rename_i nonzero
  have zero : errno = 0 := by simpa [sysReply] using nonzero
  subst zero
  split at next
  · rw [exec_pure_value next]
    exact Nat.zero_le _
  obtain ⟨errno, got, after, rest, getter, next⟩ := exec_sys_returned next rfl
  split at next
  · rw [exec_pure_value next]
    exact Nat.zero_le _
  rename_i _ gotNonzero
  have gotZero : errno = 0 := by simpa [sysReply] using gotNonzero
  subst gotZero
  rw [exec_pure_value next]
  have shape : sizes.map (·.data.size) = [4, 4] := (host.sys_bound reporter).1
  rcases sizes with _ | ⟨count, _ | ⟨size, _ | ⟨_, _⟩⟩⟩ <;> simp at shape
  have countSmall := littleEndian_four_lt shape.1
  have sizeSmall := littleEndian_four_lt shape.2
  have asked := bound _ _ _ reporter
  simp only [reportedSize, Reply.word, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some, UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat,
    Nat.reducePow] at asked
  have gotShape : got.map (·.data.size) = [1 * (littleEndian size).toNat] := by
    have permitted := (host.sys_bound getter).1
    rw [host.sys_reports (call := Call.argsGet) reporter rfl] at permitted
    exact permitted
  rcases got with _ | ⟨shown, _ | ⟨_, _⟩⟩ <;> simp at gotShape
  simp only [SysForm.value, wordsBytesValue, sysReply, ↓reduceIte, Reply.bytes,
    List.getElem?_cons_zero, Option.getD_some]
  omega

/-- Proves `Bounded` of the bindings of a write's window, which charge nothing, and the write. -/
local macro "window_bound" : tactic => `(tactic|
  (repeat (first
    | (apply bounded_of_rule; intro _ _ rule; refine rule 0 0 (by omega) ?_ ?_)
    | (intro _ _)
    | rule_ret
    | rule_write)))

/-- Proves `Bounded` of a flat call without an output, which charges nothing. -/
local macro "flat_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (fun _ _ _ _ _ => Nat.zero_le _) (fun _ _ _ _ _ => Nat.zero_le _)))

/-- Every run and every prefix of `main`'s body spends at most `budget limit`. -/
theorem body_bounded {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs) .nil 0 []
      (fun _ => false) command.main.func.body .nil (budget limit) := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    (inputs := []) (buffers := [])
    bound (Nat.le_refl (Bytes.allocationCost limit))
  unfold budget
  rule_bind (Bytes.allocationCost limit) 288
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments _
  obtain ⟨_, _, _, bytes⟩ := arguments
  letPair_free
  rule_ite 288
  · rule_ret
  rule_bind 0 288
  · window_bound
  intro _ _
  rule_bind 0 288
  · flat_bound
  intro _ _
  rule_ite 288
  · rule_ret
  rule_bind 56 232
  · rule_bind 56 0
    · rule_ret
    · intro _ _
      window_bound
  intro _ _
  rule_bind 56 176
  · rule_bind 56 0
    · rule_ret
    · intro _ _
      window_bound
  intro _ _
  rule_bind 0 176
  · rule_bind 0 0
    · rule_ret
    · intro _ _
      rule_bind 0 0
      · rule_ret
      · intro _ _
        flat_bound
  intro _ _
  rule_ite 176
  · rule_ret
  rule_bind 56 120
  · rule_bind 56 0
    · rule_ret
    · intro _ _
      window_bound
  intro _ _
  rule_bind 0 120
  · rule_bind 0 0
    · rule_ret
    · intro _ _
      rule_bind 0 0
      · rule_ret
      · intro _ _
        flat_bound
  intro _ _
  rule_ite 120
  · rule_ret
  rule_bind 56 64
  · rule_bind 56 0
    · rule_ret
    · intro _ _
      window_bound
  intro _ _
  rule_bind 64 0
  · rule_bind 64 0
    · rule_ret
    · intro _ _
      rule_free
  intro random _
  obtain ⟨_, _, randomBuffer⟩ := random
  letPair_free
  rule_ite 0
  · rule_ret
  rule_bind 0 0
  · window_bound
  intro _ _
  rule_ret

/-- Every prefix of a call of `main` spends at most `budget limit`. -/
theorem call_prefix_bound {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    (world : Observed World) :
    CallPrefixBound (observedHost host) (.ofProg command.pure.program command.pure.funs)
      command.program .here 0 .nil world (budget limit) := by
  intro trace residual final spent fits progress
  exact call_prefix_rule (budget limit) progress rfl ((body_bounded bound).2 world)

/-- The budget fits the heap above the literal pool's 4,096 bytes when `limit` is at most
4,294,897,328: 4,096 bytes, a block of 4,294,897,376 bytes, and 288 bytes are the 4,294,901,760
bytes of 65,535 pages, and the limit 4,294,897,329 exceeds them. -/
theorem initial_within {World : Type} (world : Observed World) {limit : Nat}
    (small : limit ≤ 4294897328) :
    (initialStaticHeap command.literalPool).Within
      (PureTransport.erase (compileInitialStoreWith command.sysCalls command.pure.module
        command.program command.entries command.mainEntry command.literalPool world))
      command.pure.module (budget limit) := by
  have cost := allocationCost_mono small
  have largest : Bytes.allocationCost 4294897328 = 4294897376 := by decide
  change 4096 + budget limit ≤ 65536 * 65535
  unfold budget
  omega

/-- `_start` exits with an accepted status for every host whose successful `args_sizes_get`
replies ask for blocks of at most `limit` bytes, with `limit` at most 4,294,897,328, every host
environment satisfying `hostSpecWith host command.sysCalls`, and every world, when the host does
not trap along `main` and its exit. -/
theorem total_of_bound {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    (small : limit ≤ 4294897328) (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies command.module (hostSpecWith host command.sysCalls))
    (safe : host.NoTrapsAlong (main.bind fun status => (Action.exit status : Action Unit))
      world.world) :
    ∃ fuelBound, ∀ fuel ≥ fuelBound,
      AcceptedExit host (main.bind fun status => (Action.exit status : Action Unit)) world
        (run fuel command.module (Wrappers.effectIndexWith command.sysCalls command.pure.module 1)
          (compileInitialStoreWith command.sysCalls command.pure.module command.program
            command.entries command.mainEntry command.literalPool world) [] targetHost) := by
  have initialized := command.initial world
  exact command.total valid initialized.1 rfl Separate.nil
    ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩ (fun _ membership => nomatch membership)
    initialized.2.1 (fun _ => ⟨initial_within world small, call_prefix_bound bound world⟩) safe

end Verified.Examples.WasiSys
