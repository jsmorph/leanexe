import Demos.RandomChoice.CommandStart
import Demos.RandomHistogram.Budget
import Verified.Wasi.BudgetTactics

/-! The resource model's charge of the random choice's `main`, the budget that the generated
`command.total` takes as a bound on every prefix of `main`, and the accepted exit of every run for
every N and K.

`body_bounded` bounds every run and every prefix of `main`'s body by `budget` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes, the random histogram's limit
of the arguments under Linux.  The model charges a copy of an owned value at each use after which
the value stays live, and it credits no release.  The charge of `main` holds the block of `args`
and the loop's initial draw buffer of 4,096 bytes and output buffer of 10,752 bytes, 14,944 bytes
with their headers.  A pass of the loop charges nothing: `random_get` fills the draw buffer, whose
variable dies at the call, without a copy, `putPicks` takes the output buffer, which dies at the
call, as owned and writes it in place, with a generated bound of 0 (`putPicks_charge`), and it
reads the draw buffer, which it borrows, and `writeAll` borrows the output buffer and charges
nothing (`writeAll_bounded`).  The proof of `body_bounded` applies `loop_bounded` of
`Verified/Wasi/ResourceRules.lean` with a charge of 0 for each pass to the loop of the passes and
to the loop of `writeAll`, so the bound holds for every number of passes, and the tactics of
`Verified/Wasi/BudgetTactics.lean` apply the rules of the other commands.

`initial_within` states that the budget fits the free memory of the command's initial store, and
`total_meets_every` states the accepted exit after events that meet `Meets` for every N and K,
from the generated `command.total` with these two bounds. -/

namespace Demos.RandomChoice

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

/-- A bound on the charge of `main`: the block of `args` and the loop's initial buffers of 4,144
and 10,800 bytes. -/
def budget : Nat := Bytes.allocationCost RandomHistogram.argsLimit + 14944

theorem budget_value : budget = 6306448 := by decide

/-- `parseArg` allocates nothing. -/
theorem parseArg_charge (env : Env [Ty.bytes, Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there.there.there env = 0 := by
  cases env with
  | cons bytes rest =>
    cases rest with
    | cons index rest =>
      cases rest
      exact (command.pureSources.parseArg.bound_eq bytes index).trans rfl

/-- `putPicks` allocates nothing. -/
theorem putPicks_charge (env : Env [Ty.bytes, Ty.word, Ty.bytes, Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here env = 0 := by
  cases env with
  | cons out rest =>
    cases rest with
    | cons n rest =>
      cases rest with
      | cons draw rest =>
        cases rest with
        | cons limit rest =>
          cases rest
          exact (command.pureSources.putPicks.bound_eq out n draw limit).trans rfl

attribute [local charge_eqs] parseArg_charge putPicks_charge

/-- The type of the state of `main`'s loop: the values still to choose, the status of a failed
call, the draw buffer, and the output buffer. -/
abbrev stateTy : Ty :=
  Ty.word.pair (Ty.word.pair (Ty.bytes.pair Ty.bytes))

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
        reportedSize outputs ≤ RandomHistogram.argsLimit) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs)
      (.cons command.writeAll.func .nil) 0 [] (fun _ => false) command.main.func.body .nil
      budget := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    (inputs := []) (buffers := [])
    bound (Nat.le_refl (Bytes.allocationCost RandomHistogram.argsLimit))
  unfold budget
  generalize Bytes.allocationCost RandomHistogram.argsLimit = A at reported ⊢
  rule_bind A 14944
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments returned
  obtain ⟨errno, _, _, bytes⟩ := arguments
  letPair_free
  rule_ite 14944
  · rule_ret
  rule_bind 0 14944
  · rule_ret
  intro n returnedN
  rule_bind 0 14944
  · rule_ret
  intro k returnedK
  rule_ite 14944
  · rule_ret
  rule_bind 14944 0
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
      obtain ⟨left, status, draw, out⟩ := state
      letPair_free
      rule_free
      obtain ⟨randomErrno, randomCount, randomBuffer⟩ := ‹UInt64 × UInt64 × LeanExe.Bytes›
      letPair_free
      rule_ite 0
      · rule_ret
      rule_bind 0 0
      · rule_ret
      intro put _
      obtain ⟨putBuffer, putFilled, putCount⟩ := put
      letPair_free
      rule_bind 0 0
      · apply bounded_of_rule
        intro _ _ rule
        exact rule 0 (by rule_charge) rfl (callBounded_here (by decide) (writeAll_bounded _))
      intro _ _
      rule_ite 0
      · rule_ret
      · rule_ret
    · intro _ _ _ _ _
      trivial
    · simp
  intro drawn returnedLoop
  obtain ⟨left, status, draw, out⟩ := drawn
  letPair_free
  rule_ite 0
  · rule_ret
  rule_ite 0
  · rule_ret
  · rule_ret

/-- Every prefix of a call of `main` spends at most `budget`. -/
theorem call_prefix_bound {World : Type} {host : Host World}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ RandomHistogram.argsLimit)
    (world : Observed World) :
    CallPrefixBound (observedHost host) (.ofProg command.pure.program command.pure.funs)
      command.program .here 0 .nil world budget := by
  intro trace residual final spent fits progress
  exact call_prefix_rule budget progress rfl ((body_bounded bound).2 world)

/-- The budget fits the heap of the command's initial store above its first 4,096 bytes: 4,096
bytes and the budget are at most the 4,294,901,760 bytes of 65,535 pages. -/
theorem initial_within {World : Type} (world : Observed World) :
    (initialStaticHeap command.literalPool).Within (PureTransport.erase (initialStore world))
      command.pure.module budget := by
  change 4096 + budget ≤ 65536 * 65535
  rw [budget_value]
  decide

/-- The accepted exit of every run of `_start`, for every N and K, under every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes and that traps nowhere along
`main` and its exit, and every host environment that satisfies the host's specifications: with
enough fuel the run ends with the accepted exit, with a status of at most 78, after events that
meet `Meets`. -/
theorem total_meets_every {World : Type} {host : Host World} (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies command.module (hostSpecWith host command.sysCalls))
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ RandomHistogram.argsLimit)
    (safe : host.NoTrapsAlong (main.bind fun status => Action.exit (α := Unit) status)
      world.world) :
    ∃ fuelBound, ∀ fuel ≥ fuelBound, ∃ final code events,
      run fuel command.module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        host.exited final.host.world = some code ∧ final.host.events = world.events ++ events ++
          [.exit code] ∧ code.toNat ≤ 78 ∧ Meets host world.world events code :=
  total_meets world targetHost valid (initial_within world) (call_prefix_bound bound world) safe

#print axioms body_bounded
#print axioms total_meets_every

end Demos.RandomChoice
