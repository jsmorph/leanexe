import Verified.Wasi.ResultRelease
import Verified.Wasi.WriteCommand
import Verified.Wasi.CostResults

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopFinishCost {World : Type} {source target : Wasm.Module} {host : Host World}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {type : Ty} {state : type.denote}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {command : Command pureSigs effectSigs context (.value type)} {depth : UInt64}
    {liveIn live used : Nat → Bool} {base h : Nat}
    {heap currentHeap : Heap} {initial current : Store (Observed World)} {locals currentLocals : Locals}
    {words : List Value} {trace : List Event} {spent : Nat} {fits aborts : Bool}
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
    (execution : Resource.ResourceExec (observedHost host) pure program depth (slots.map Slot.mode)
      live command env initial.host trace (.returned state) current.host spent fits)
    (top : fits = true → currentHeap.top.toNat ≤ heap.top.toNat + spent) :
    wp target (Relocation.program (releaseWhere context slots (fun i => used i && !live i)) ++
      loadCode h (base + 2) type.types)
      (CostCommandResult host pure program command depth env slots liveIn live base heap initial locals aborts)
      current currentLocals targetHost := by
  have liveEq : (fun i => (live i || used i) && !(used i && !live i)) = live := by
    funext i
    cases live i <;> cases used i <;> rfl
  refine wp_release_context (sourceHost := sourceHost) runtime layout profile form closed
    after.holds after.step.at_ (fun i chosen => by
      cases hLive : live i <;> cases hUsed : used i <;> simp_all) ?_
  intro finalHeap final evolution releaseTop sameWorld
  have evolution' : Evolves env slots (fun i => live i || used i) live base currentHeap
      (PureTransport.erase current) currentLocals finalHeap (PureTransport.erase final) currentLocals := by
    simpa only [liveEq] using evolution
  have finished := After.release vars scratch after selected
    (fun i chosen => by rw [chosen]; rfl) evolution'
  have loaded : wp target (loadCode h (base + 2) type.types ++ [])
      (CostCommandResult host pure program command depth env slots liveIn live base heap initial locals aborts)
      final currentLocals targetHost := by
    refine wp_loadCode words finished.rep.typed positions held ?_
    rw [wp_nil, stack]
    exact CostCommandResult.returned (result := .value type) state finalHeap final currentLocals words trace
      spent fits (by rw [sameWorld]; exact execution) finished
      (by intro valid; rw [releaseTop]; exact top valid)
  simpa only [List.append_nil] using loaded

end Verified.Wasi
