import Verified.Wasi.WriteCommand
import Verified.Wasi.CommandValue

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cleanup_after {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {initial final : Store World} {locals finalLocals : Locals}
    (evolution : Evolves env slots liveIn live base heap (PureTransport.erase initial) locals
      finalHeap (PureTransport.erase final) finalLocals) :
    After env slots liveIn live base heap initial locals .unit ()
      finalHeap final finalLocals [] :=
  ⟨evolution.step.mono (fun _ kept => kept.1) (fun _ member => member),
    evolution.frame, evolution.holds, rfl, trivial⟩

theorem wp_cleanup {World : Type} {host : Host World} {context : List Ty}
    {env : Env context} {slots : List Slot} {live selected : Nat → Bool} {base : Nat}
    {source target : Wasm.Module} {sourceHost : HostEnv Unit}
    {targetHost : HostEnv (Observed World)} {heap : Heap} {initial : Store (Observed World)}
    {locals : Locals} {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere context slots selected))
    (closed : Relocation.programClosed source.funcs.length
      (releaseWhere context slots selected) = true)
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (selection : ∀ i, selected i = true → live i = true) :
    wp target (Relocation.program (releaseWhere context slots selected))
      (CommandResult host env slots live (fun i => live i && !selected i) base .unit (.pure ())
        heap initial locals aborts) initial locals targetHost := by
  have execution := wp_release_context (sourceHost := sourceHost) (targetHost := targetHost)
    (rest := [])
    (Q := CommandResult host env slots live (fun i => live i && !selected i) base .unit (.pure ())
      heap initial locals aborts)
    runtime layout profile form closed vars at_ selection
    (fun finalHeap final evolution _ sameWorld => by
      rw [wp_nil]
      have result : CommandResult host env slots live (fun i => live i && !selected i) base
          .unit (.pure ()) heap initial locals aborts
          (.Fallthrough final { locals with values := ([] : List Value).reverse ++ locals.values }) :=
        CommandResult.returned (result := .unit) () finalHeap final locals [] []
          (by rw [sameWorld]; exact Exec.pure (α := Unit) initial.host ())
          (cleanup_after evolution)
      cases locals
      simpa only [List.reverse_nil, List.nil_append] using result)
  simpa only [List.append_nil] using execution

end Verified.Wasi
