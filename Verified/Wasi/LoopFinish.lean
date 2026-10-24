import Verified.Wasi.ResultRelease
import Verified.Wasi.WriteCommand

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopFinish {World : Type} {source target : Wasm.Module} {host : Host World}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {type : Ty} {state : type.denote}
    {action : Action type.denote} {liveIn live used : Nat → Bool} {base h : Nat}
    {heap currentHeap : Heap} {initial current : Store (Observed World)} {locals currentLocals : Locals}
    {words : List Value} {trace : List Event} {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere context slots (fun i => used i && !live i)))
    (closed : Relocation.programClosed source.funcs.length
      (releaseWhere context slots (fun i => used i && !live i)) = true)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (after : After env slots liveIn (fun i => live i || used i) base heap initial locals
      (.value type) state currentHeap current currentLocals words)
    (selected : ∀ i, (live i || used i) = true → liveIn i = true)
    (positions : currentLocals.positions = h)
    (held : LocalsHold currentLocals (base + 2) type.types words)
    (stack : currentLocals.values = locals.values)
    (execution : Exec (observedHost host) action initial.host trace (.returned state) current.host) :
    wp target (Relocation.program (releaseWhere context slots (fun i => used i && !live i)) ++
      loadCode h (base + 2) type.types)
      (CommandResult host env slots liveIn live base (.value type) action heap initial locals aborts)
      current currentLocals targetHost := by
  have liveEq : (fun i => (live i || used i) && !(used i && !live i)) = live := by
    funext i
    cases live i <;> cases used i <;> rfl
  refine wp_release_context (sourceHost := sourceHost) runtime layout profile form closed
    after.holds after.step.at_ (fun i chosen => by
      cases hLive : live i <;> cases hUsed : used i <;> simp_all) ?_
  intro finalHeap final evolution top sameWorld
  have evolution' : Evolves env slots (fun i => live i || used i) live base currentHeap
      (PureTransport.erase current) currentLocals finalHeap (PureTransport.erase final) currentLocals := by
    simpa only [liveEq] using evolution
  have finished := After.release vars scratch after selected
    (fun i chosen => by rw [chosen]; rfl) evolution'
  have loaded : wp target (loadCode h (base + 2) type.types ++ [])
      (CommandResult host env slots liveIn live base (.value type) action heap initial locals aborts)
      final currentLocals targetHost := by
    refine wp_loadCode words finished.rep.typed positions held ?_
    rw [wp_nil, stack]
    exact CommandResult.returned (result := .value type) state finalHeap final currentLocals words trace
      (by rw [sameWorld]; exact execution) finished
  simpa only [List.append_nil] using loaded

end Verified.Wasi
