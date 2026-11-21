import Demos.RandomHistogram.CommandStart
import Demos.RandomHistogram.Compiled
import Verified.Wasi.BudgetTactics

/-! The resource model's charge of the random-residue histogram's `main`, the budget that the
generated `command.start` without guest traps and `command.total` take as a bound on every prefix
of `main`.

`body_bounded` bounds every run and every prefix of `main`'s body by `budget` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes, for every N.  The model
charges a copy of an owned value at each use after which the value stays live, and it credits no
release.  The reflector splits the result of `args`, the loop's state, and the result of
`randomGet` into their components where `main` binds them, so no use copies them.  A pass of the
draw loop charges nothing: `random_get` fills the buffer that the loop's state carries, the call
takes the buffer's variable, which dies at the call, without a copy, and `tally` reads the buffer
and updates the counts in place.  The charge of `main` holds the block of `args`, the loop's
initial counts and buffer, and the charge of `render`.  `writeAll` charges nothing
(`writeAll_bounded`): it computes the window of the output in words, and each of its passes writes
a window of the output, which it borrows, in place.  `loop_bounded` of
`Verified/Wasi/ResourceRules.lean` bounds the draw loop and the loop of `writeAll`, and the tactics
of `Verified/Wasi/BudgetTactics.lean` apply the rules of the other commands, with the charges of
`parseN`, `tally`, and `render` as the local simp set `charge_eqs`.

`budget_fits` states that the budget fits the 4,096 pages of the native executable above the
heap's start at byte 4,096.  Linux 4.13 and later limit the strings and pointers of `argv` and
`envp` together to at most 6 MiB, `argsLimit` (`get_arg_page` of `fs/exec.c` in v4.13,
`bprm_stack_limits` in v6.12). -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

/-! ## The budget -/

/-- The bytes of the arguments, with the four-byte pointer of each and three bytes of alignment,
for which the budget holds: 6 MiB, the most that Linux lets the strings and pointers of `argv` and
`envp` take together. -/
def argsLimit : Nat := 6291456

/-- A bound on the charge of `main`: the block of `args`, the loop's initial counts of 136 bytes
and buffer of 4,144 bytes, and the charge of `render`, at most 17,136 bytes. -/
def budget : Nat := Bytes.allocationCost argsLimit + 21416

theorem budget_fits : 4096 + budget ≤ 65536 * 4096 := by decide

/-! ## Facts about the reflected program -/

/-- `parseN` allocates nothing. -/
theorem parseN_charge (env : Env [Ty.bytes]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there.there.there.there env = 0 := by
  cases env with
  | cons bytes rest =>
    cases rest
    exact (command.pureSources.parseN.bound_eq bytes).trans rfl

/-- `tally` allocates nothing. -/
theorem tally_charge (env : Env [Ty.array Elem.word, Ty.bytes, Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there env = 0 := by
  cases env with
  | cons counts rest =>
    cases rest with
    | cons bytes rest =>
      cases rest with
      | cons count rest =>
        cases rest
        exact (command.pureSources.tally.bound_eq counts bytes count).trans rfl

/-- The type of the state of `main`'s loop: the counts, the buffer, the words still to draw, and
the errno of a failed call. -/
abbrev stateTy : Ty :=
  (Ty.array Elem.word).pair (Ty.bytes.pair (Ty.elem (Elem.word.prod Elem.word)))

/-- The command's `appendLine` charges what the pure core's does. -/
theorem appendLine_cost_eq (text : Array UInt64) (c : UInt64) :
    command.pureSources.appendLine.cost (⟨text⟩, c) = compiled.appendLine.cost (⟨text⟩, c) := by
  rw [command.pureSources.appendLine.cost_eq, compiled.appendLine.cost_eq]

/-- The charge of a call of `render`. -/
theorem render_charge (counts : Array UInt64) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get FVar.here
      (Env.cons counts Env.nil) = command.pureSources.render.bound counts :=
  rfl

attribute [local charge_eqs] parseN_charge tally_charge render_charge

/-- The command's `render` charges at most 17,136 bytes, as the pure core's does. -/
theorem render_bound_command (counts : Array UInt64) :
    command.pureSources.render.bound counts ≤ 17136 := by
  refine le_of_eq_of_le (command.pureSources.render.bound_eq counts) ?_
  refine le_of_eq_of_le ?_ (render_bound counts)
  rw [compiled.render.bound_eq]
  simp only [appendLine_cost_eq]

/-- The reflected `parseN` is `parseN`. -/
theorem parseN_reflected (bytes : Bytes) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get
      FVar.here.there.there.there.there.there.there.there (Env.cons bytes Env.nil) =
      parseN bytes := by
  rw [← command.pureSources.parseN.denote_eq]
  rfl

/-! ## The values that the charges read -/

/-- A returned `args` result with errno 0 holds the bytes that a successful `args_get` reply
gave. -/
theorem args_got {World : Type} {host : Host World} {values : List UInt64}
    {world final : World} {trace : List Event}
    {value : UInt64 × UInt64 × UInt64 × LeanExe.Bytes}
    (run : Exec host (SysForm.reported.runWith Call.argsGet values [] []) world trace
      (.returned value) final)
    (zero : value.1 = 0) :
    ∃ world got after, host.sys world Call.argsGet [] (.returned 0 got) after ∧
      value.2.2.2 = (sysReply 0 got).bytes 0 := by
  obtain ⟨errno, sizes, middle, rest, -, -, next⟩ := exec_sys_returned run rfl
  split at next
  · rename_i nonzero
    rw [exec_pure_value next] at zero
    simp [SysForm.value, wordsBytesValue] at zero
    simp [zero] at nonzero
  split at next
  · rw [exec_pure_value next] at zero
    simp [SysForm.value, wordsBytesValue] at zero
  obtain ⟨gotErrno, got, after, _, -, getter, next⟩ := exec_sys_returned next rfl
  split at next
  · rename_i nonzero
    rw [exec_pure_value next] at zero
    simp [SysForm.value, wordsBytesValue] at zero
    simp [zero] at nonzero
  rename_i gotZero
  have zeroErrno : gotErrno = 0 := by simpa [sysReply] using gotZero
  subst zeroErrno
  rw [exec_pure_value next]
  exact ⟨_, _, _, getter, rfl⟩

/-! ## The budget of `main` -/

/-- `writeAll` charges nothing: it computes the window of its buffer in words, and each of its
passes binds the window of the bytes that remain and writes it from the borrowed buffer. -/
theorem writeAll_bounded {World : Type} {host : Host World} {depth : UInt64}
    (env : Env [Ty.bytes, Ty.word, Ty.word]) :
    Bounded host (.ofProg command.pure.program command.pure.funs) .nil depth
      (entryModes command.writeAll.func.params command.writeAll.func.modes) (fun _ => false)
      command.writeAll.func.body env 0 := by
  rule_bind 0 0
  · rule_ret
  intro _ _
  rule_bind 0 0
  · rule_ret
  intro _ _
  apply bounded_of_rule
  intro _ _ rule
  refine rule 0 (by rule_charge) ?_ ?_
  · simp only [PureContext.loopInitFits, Bool.and_eq_true]
    exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
      Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
  refine LoopBounded.mono (loop_bounded (type := .word) (t := 0) (s := 0)
    (fun _ : UInt64 => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
  · intro index written _
    rule_charge
  · intro index written _
    exact Expr.fits_of_depthCalls _ _ _ (by decide) _
  · intro index written _
    rule_bind 0 0
    · rule_bind 0 0
      · rule_ret
      · intro _ _
        rule_bind 0 0
        · rule_ret
        · intro _ _
          rule_write
    · intro _ _
      rule_ite 0
      · rule_ret
      · rule_ret
  · intro _ _ _ _ _
    trivial
  · simp

/-- Every run and every prefix of `main`'s body charges at most `budget` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes. -/
theorem body_bounded {World : Type} {host : Host World}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ argsLimit) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs)
      (.cons command.writeAll.func .nil) 0 [] (fun _ => false) command.main.func.body .nil
      budget := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    (inputs := []) (buffers := [])
    bound (Nat.le_refl (Bytes.allocationCost argsLimit))
  unfold budget
  generalize Bytes.allocationCost argsLimit = A at reported ⊢
  rule_bind A 21416
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments returned
  obtain ⟨errno, _, _, bytes⟩ := arguments
  letPair_free
  apply bounded_of_rule
  intro _ _ rule
  refine rule 21416 21416 (ite_cost (by rule_charge)) (by rule_fits) (fun _ => ?_)
    (fun _ => ?_)
  · rule_ret
  rule_bind 0 21416
  · rule_ret
  intro n returnedN
  rule_ite 21416
  · rule_ret
  rule_bind 4280 17136
  · apply bounded_of_rule
    intro _ _ rule
    refine rule 0 (by rule_init_charge) ?_ ?_
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine LoopBounded.mono (loop_bounded (type := stateTy) (t := 0) (s := 0)
      (fun _ => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
    · intro index state _
      rule_charge
    · intro index state _
      exact Expr.fits_of_depthCalls _ _ _ (by decide) _
    · intro index state _
      obtain ⟨counts, buffer, left, errno⟩ := state
      letPair_free
      rule_free
      obtain ⟨randomErrno, randomCount, randomBuffer⟩ := ‹UInt64 × UInt64 × LeanExe.Bytes›
      letPair_free
      rule_ite 0
      · rule_ret
      · rule_ret
    · intro _ _ _ _ _
      trivial
    · simp
  intro drawn returnedLoop
  obtain ⟨counts, buffer, left, errno⟩ := drawn
  have renderBound := render_bound_command counts
  letPair_free
  rule_ite 17136
  · rule_ret
  rule_bind 17136 0
  · rule_ret
  intro output returnedOutput
  rule_bind 0 0
  · apply bounded_of_rule
    intro _ _ rule
    exact rule 0 (by rule_charge) rfl (callBounded_here (by decide) (writeAll_bounded _))
  · intro _ _
    apply bounded_of_rule
    intro _ _ rule
    exact rule (by rule_charge) (by rule_fits)

end Demos.RandomHistogram
