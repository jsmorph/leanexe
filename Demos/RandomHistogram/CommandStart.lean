import Demos.RandomHistogram.CommandProof
import Verified.Shim.Footprint

/-! The theorem of the compiled command.  For every host, every host environment that satisfies the
host's contracts for the module's imports, `hostSpecWith host command.sysCalls`, and every world,
every run of `_start` from the command's initial store with enough fuel traps (`start_ends`).  The
trap is one of three:

- the accepted exit, with a status `code` of at most 76, after the events of `Meets`
  (`exec_main`): the status is the errno of `args`, 2 for a refused argument, the errno of a
  failed `random_get`, or the errno of the one write of `renderSpec (histogramSpec w)`, with `w`
  the N words that the calls of `random_get` returned, whose counts sum to N;
- a trap of the host, or an exit that the host rejects, after the events of a run of `main` and
  its exit;
- a trap of the guest at `unreachable`, after the events of a prefix of `main` and its exit.

The generated `command.start` theorem admits the guest's trap because its resource premise, a
budget that bounds the heap that every prefix of `main` allocates, has no bound for every N: the
resource model charges each pass of the loop for its buffer and credits no release, so the charge
grows with the number of passes.  `total_meets` takes that premise, with a host that traps nowhere
along `main` and its exit, the premises of the generated `command.total`, and states that every run
then ends with the accepted exit after events that meet `Meets`. -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi

/-- The command's initial store in the observed world `world`. -/
def initialStore {World : Type} (world : Observed World) : Store (Observed World) :=
  compileInitialStoreWith command.sysCalls command.pure.module command.program command.entries
    command.mainEntry command.literalPool world

/-- The index of `_start` in the command's module. -/
def startIndex : Nat := Wrappers.effectIndexWith command.sysCalls command.pure.module 1

/-- How a run of `_start` from the observed world `initial` ends: a trap whose final world adds the
events `trace` to those of `initial`, after an accepted exit with a status `code` of at most 76
whose events meet `Meets`, after a trap of the host or a rejected exit, or, at `unreachable`, after
a prefix of `main` and its exit. -/
def Ends {World : Type} (host : Host World) (initial : Observed World) :
    Result (Observed World) → Prop
  | .Trap final message => ∃ trace, final.host.events = initial.events ++ trace ∧
      ((∃ code, message = exitTrap ∧ host.exited final.host.world = some code ∧
          ∃ events, trace = events ++ [.exit code] ∧ code.toNat ≤ 76 ∧
            Meets host initial.world events code) ∨
        (Exec host (main.bind fun status => Action.exit (α := Unit) status) initial.world trace
          (.trapped message) final.host.world) ∨
        (message = "unreachable" ∧ ∃ residual,
          Prefix host (main.bind fun status => Action.exit (α := Unit) status) initial.world trace
            residual final.host.world))
  | _ => False

/-- The command theorem's classification of a run of `_start` gives `Ends`. -/
theorem ends_of_result {World : Type} {host : Host World} {heap : Heap}
    {initial : Store (Observed World)} {aborts : Bool} {result : Result (Observed World)}
    (h : NativeFunctionResult host startSignature
      (main.bind fun status => Action.exit (α := Unit) status) (fun value : Unit => value)
      .nil [] heap initial aborts result) :
    Ends host initial.host result := by
  cases h with
  | returned value _ _ _ _ execution _ _ =>
    exact (bind_exit_not_returned (exec_observed execution).1).elim
  | terminal final trace outcome message execution terminal =>
    obtain ⟨execution, events⟩ := exec_observed execution
    refine ⟨trace, events, ?_⟩
    cases outcome with
    | returned value => exact terminal.elim
    | exited code =>
      obtain ⟨steps, htrace, small, meets⟩ := exec_main execution
      exact .inl ⟨code, terminal, execution.exited_marker, steps, htrace, small, meets⟩
    | trapped cause =>
      change message = cause at terminal
      subst terminal
      exact .inr (.inl execution)
  | resource final trace residual _ progress =>
    obtain ⟨progress, events⟩ := Verified.Shim.prefix_observed progress
    exact ⟨trace, events, .inr (.inr ⟨rfl, residual, progress⟩)⟩

/-- Every run of `_start` from the command's initial store with enough fuel ends as `Ends` states,
for every host, every host environment that satisfies the host's contracts, and every world. -/
theorem start_ends {World : Type} {host : Host World} (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies command.module (hostSpecWith host command.sysCalls)) :
    ∃ bound, ∀ fuel ≥ bound,
      Ends host world (run fuel command.module startIndex (initialStore world) [] targetHost) := by
  have initialized := command.initial world
  obtain ⟨bound, results⟩ := command.start (host := host) (aborts := true) (budget := 0) valid
    initialized.1 rfl Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) initialized.2.1 (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => ends_of_result (results fuel enough)⟩

/-- The accepted exit of every run, under the premises of the generated `command.total`: a budget
that fits the free memory of the command's initial store and bounds the heap that every prefix of
`main` allocates, and a host that traps nowhere along `main` and its exit.  Every run of `_start`
with enough fuel then ends with the accepted exit with a status of at most 76, after events that
meet `Meets`. -/
theorem total_meets {World : Type} {host : Host World} (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies command.module (hostSpecWith host command.sysCalls))
    {budget : Nat}
    (room : (Verified.initialStaticHeap command.literalPool).Within
      (PureTransport.erase (initialStore world)) command.pure.module budget)
    (bounded : Resource.CallPrefixBound (observedHost host)
      (.ofProg command.pure.program command.pure.funs) command.program .here 0 .nil world budget)
    (safe : host.NoTrapsAlong (main.bind fun status => Action.exit (α := Unit) status)
      world.world) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final code events,
      run fuel command.module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        host.exited final.host.world = some code ∧ final.host.events = world.events ++ events ++
          [.exit code] ∧ code.toNat ≤ 76 ∧ Meets host world.world events code := by
  have initialized := command.initial world
  obtain ⟨bound, exits⟩ := command.total valid initialized.1 rfl Separate.nil
    ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩ (fun _ membership => nomatch membership)
    initialized.2.1 (fun _ => ⟨room, bounded⟩) safe
  refine ⟨bound, fun fuel enough => ?_⟩
  have accepted : AcceptedExit host (main.bind fun status => Action.exit (α := Unit) status) world
      (run fuel command.module startIndex (initialStore world) [] targetHost) := exits fuel enough
  generalize run fuel command.module startIndex (initialStore world) [] targetHost = result
    at accepted ⊢
  cases result with
  | Trap final message =>
    obtain ⟨code, trace, rfl, execution, events, marker⟩ := accepted
    obtain ⟨steps, rfl, small, meets⟩ := exec_main execution
    exact ⟨final, code, steps, rfl, marker, by rw [events, List.append_assoc], small, meets⟩
  | _ => exact accepted.elim

#print axioms exec_main
#print axioms start_ends
#print axioms total_meets

end Demos.RandomHistogram
