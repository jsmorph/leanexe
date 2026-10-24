import Verified.Wasi.FunctionRun
import Verified.Wasi.LoopAfter
import Verified.Wasi.Return
import Verified.Wasi.Cleanup
import Verified.Wasi.CommandResultStore

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem ResultTy.Rep.typed {result : ResultTy} {heap : Heap} {store : Store Unit}
    {words : List Value} {value : result.denote} (rep : result.Rep heap store words value) :
    words.length = result.types.length :=
  rep.length.trans result.types_length.symm

def ItePost (targetHost : HostEnv World) (target : Module) (rest : Program)
    (Q : Assertion World) (values : List Value) : Assertion World
  | .Fallthrough final locals | .Break 0 final locals =>
      wp target rest Q final { locals with values } targetHost
  | .Break (label + 1) final locals => Q (.Break label final locals)
  | other => Q other

theorem wp_ite_bool {World : Type} {target : Module} {targetHost : HostEnv World}
    {initial : Store World} {locals : Locals} {condition : Bool}
    {yes no rest : Program} {values : List Value} {Q : Assertion World}
    (branch : wp target (if condition then yes else no)
      (ItePost targetHost target rest Q values) initial { locals with values } targetHost) :
    wp target (.eqzI64 :: .iff 0 0 no yes [] [] :: rest) Q initial
      { locals with values := .i64 (boolWord condition) :: values } targetHost := by
  cases condition <;>
    simp [boolWord, wp_eqzI64_cons] at branch ⊢
  all_goals
    refine wp_iff_cons rfl (wp.conseq (fun continuation post => ?_) branch)
    cases continuation with
    | Break label final finalLocals => cases label <;> exact post
    | _ => exact post

theorem wp_store_command_result {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool}
    {base h : Nat} {result : ResultTy} {action : Action result.denote}
    {target : Module} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {locals : Locals} {aborts : Bool}
    {code : Program} {P : Assertion (Observed World)}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (selected : ∀ i, live i = true → liveIn i = true)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + result.width ≤ h)
    (body : wp target code
      (CommandResult host env slots liveIn live (base + result.width) result action
        heap initial locals aborts) initial locals targetHost)
    (next : ∀ (finalHeap : Heap) (final : Store (Observed World)) (stored : Locals)
      (words : List Value) (value : result.denote) (trace : List Event),
      Exec (observedHost host) action initial.host trace (.returned value) final.host →
      After env slots liveIn live base heap initial locals result value
        finalHeap final stored words →
      LocalsHold stored base result.types words → P (.Fallthrough final stored))
    (terminal : ∀ (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome result.denote) (message : String),
      Exec (observedHost host) action initial.host trace outcome final.host →
      TerminalMessage message outcome → P (.Trap final message))
    (resource : ∀ (final : Store (Observed World)) (trace : List Event)
      (residual : Action result.denote), aborts = true →
      Prefix (observedHost host) action initial.host trace residual final.host →
      P (.Trap final "unreachable")) :
    wp target (code ++ storeCode h base result.types) P initial locals targetHost := by
  apply wp_append
  refine wp.conseq (fun continuation execution => ?_) body
  cases execution with
  | returned value finalHeap final finalLocals words trace execution after =>
      change wp target (storeCode h base result.types) P final
        { finalLocals with values := words.reverse ++ locals.values } targetHost
      exact wp_store_owned_result vars selected positions low room after
        (fun stored reduced held => next finalHeap final stored words value trace execution reduced held)
  | terminal final trace outcome message execution status =>
      exact terminal final trace outcome message execution status
  | resource final trace residual allowed progress =>
      exact resource final trace residual allowed progress

theorem wp_ite_branch {World : Type} {host : Host World} {source target : Module}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {all branchLive live : Nat → Bool} {base h : Nat} {result : ResultTy}
    {action : Action result.denote} {pool : Bytes.LiteralPool}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {locals : Locals} {aborts : Bool}
    {code : Program} {P : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere context slots (fun i => all i && !branchLive i)))
    (closed : Relocation.programClosed source.funcs.length
      (releaseWhere context slots (fun i => all i && !branchLive i)) = true)
    (vars : Holds env slots all base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots all (PureTransport.erase initial) locals ABI.scratch)
    (safe : pool.Safe env slots all heap (PureTransport.erase initial) locals)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (branchSelected : ∀ i, branchLive i = true → all i = true)
    (liveSelected : ∀ i, live i = true → branchLive i = true)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + result.width ≤ h)
    (body : ∀ (middleHeap : Heap) (middle : Store (Observed World)),
      Evolves env slots all branchLive (base + result.width) heap
        (PureTransport.erase initial) locals middleHeap (PureTransport.erase middle) locals →
      middleHeap.top = heap.top → middle.host = initial.host →
      middleHeap.At (PureTransport.erase middle) →
      Holds env slots branchLive (base + result.width) middleHeap
        (PureTransport.erase middle) locals →
      pool.Safe env slots branchLive middleHeap (PureTransport.erase middle) locals →
      Holds.ApartFrom env slots branchLive (PureTransport.erase middle) locals ABI.scratch →
      (PureTransport.erase middle).memoryCap source 0 ≤ 65535 →
      wp target code (CommandResult host env slots branchLive live (base + result.width)
        result action middleHeap middle locals aborts) middle locals targetHost)
    (next : ∀ (finalHeap : Heap) (final : Store (Observed World)) (stored : Locals)
      (words : List Value) (value : result.denote) (trace : List Event),
      Exec (observedHost host) action initial.host trace (.returned value) final.host →
      After env slots all live base heap initial locals result value finalHeap final stored words →
      LocalsHold stored base result.types words → P (.Fallthrough final stored))
    (terminal : ∀ (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome result.denote) (message : String),
      Exec (observedHost host) action initial.host trace outcome final.host →
      TerminalMessage message outcome → P (.Trap final message))
    (resource : ∀ (final : Store (Observed World)) (trace : List Event)
      (residual : Action result.denote), aborts = true →
      Prefix (observedHost host) action initial.host trace residual final.host →
      P (.Trap final "unreachable")) :
    wp target (Relocation.program (releaseWhere context slots (fun i => all i && !branchLive i)) ++
      code ++ storeCode h base result.types) P initial locals targetHost := by
  have liveEq : (fun i => all i && !(all i && !branchLive i)) = branchLive := by
    funext i
    exact live_released (all i) (branchLive i) (branchSelected i)
  have upperVars := vars.mono (Nat.le_add_right base result.width)
  have sequence : wp target (Relocation.program
      (releaseWhere context slots (fun i => all i && !branchLive i)) ++ code)
      (CommandResult host env slots all live (base + result.width) result action
        heap initial locals aborts) initial locals targetHost := by
    refine wp_release_context (sourceHost := sourceHost) runtime layout profile form closed
      upperVars at_ (fun _ selected => by
        simp only [Bool.and_eq_true] at selected
        exact selected.1) ?_
    intro middleHeap middle evolution top sameWorld
    have evolution' : Evolves env slots all branchLive (base + result.width) heap
        (PureTransport.erase initial) locals middleHeap (PureTransport.erase middle) locals := by
      simpa only [liveEq] using evolution
    have after := cleanup_after evolution'
    have firstExecution : Exec (observedHost host) (.pure ()) initial.host []
        (.returned ()) middle.host := by
      rw [sameWorld]
      exact .pure initial.host ()
    refine wp.conseq (fun continuation execution => ?_)
      (body middleHeap middle evolution' top sameWorld after.step.at_ after.holds
        (after.pool_safe safe upperVars apart branchSelected poolApart).1
        (after.scratch upperVars apart branchSelected)
        (by rw [after.step.cap source]; exact cap))
    simpa only [Action.bind] using CommandResult.bind_unit (next := fun _ => action)
      upperVars apart firstExecution after rfl execution branchSelected liveSelected
  simpa only [List.append_assoc] using
    wp_store_command_result vars (fun i selected => branchSelected i (liveSelected i selected))
      positions low room sequence next terminal resource

end Verified.Wasi
