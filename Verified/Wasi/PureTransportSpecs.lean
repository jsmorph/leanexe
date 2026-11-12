import Verified.Wasi.PureTransportExecution
import LeanExe.Pipeline.Aborts

namespace Verified.Wasi.PureTransport

open Wasm

def KeepsWorld (world : World) : Result World → Prop
  | .Success _ store | .Trap store _ | .Thrown _ _ store => store.host = world
  | .Invalid _ | .OutOfFuel => True

theorem liftResult_keepsWorld (world : World) (result : Result Unit) :
    KeepsWorld world (liftResult world result) := by
  cases result <;> simp only [KeepsWorld, liftResult, restore_host]

theorem entry_keepsWorld_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    (fuel : Nat) (initial : Store Unit) (world : World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    KeepsWorld world (run fuel target (3 + calls.length + index) (restore world initial) args targetHost) := by
  rw [entry_transport_with layout profile hIndex fuel initial world args sourceHost targetHost]
  exact liftResult_keepsWorld world _

theorem entry_keepsWorld {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    (fuel : Nat) (initial : Store Unit) (world : World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    KeepsWorld world (run fuel target (3 + index) (restore world initial) args targetHost) := by
  layout_instance entry_keepsWorld_with

theorem runs_transport_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {aborts : Bool} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : Runs aborts sourceHost source index initial args P) (world : World) :
    Runs aborts targetHost target (3 + calls.length + index) (restore world initial) args
      (fun final values => P (erase final) values ∧ final.host = world) := by
  obtain ⟨bound, hBound⟩ := h
  refine ⟨bound, fun fuel hFuel => ?_⟩
  have hEq := entry_transport_with (calls := calls) layout profile hIndex fuel initial world args sourceHost targetHost
  rcases hBound fuel hFuel with ⟨values, final, hRun, hPost⟩ | hTrap
  · left
    refine ⟨values, restore world final, ?_, ?_⟩
    · rw [hEq, hRun]
      rfl
    · simpa only [erase_restore, restore_host, and_true] using hPost
  · right
    cases aborts with
    | false => exact hTrap.elim
    | true =>
        obtain ⟨final, hRun⟩ := hTrap
        refine ⟨restore world final, ?_⟩
        rw [hEq, hRun]
        rfl

theorem runs_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {aborts : Bool} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : Runs aborts sourceHost source index initial args P) (world : World) :
    Runs aborts targetHost target (3 + index) (restore world initial) args
      (fun final values => P (erase final) values ∧ final.host = world) := by
  layout_instance runs_transport_with

theorem terminatesWith_transport_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith sourceHost source index initial args P) (world : World) :
    TerminatesWith targetHost target (3 + calls.length + index) (restore world initial) args
      (fun final values => P (erase final) values ∧ final.host = world) :=
  (runs_transport_with (calls := calls) layout profile hIndex (h.runs (aborts := false)) world).terminatesWith

theorem terminatesWith_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith sourceHost source index initial args P) (world : World) :
    TerminatesWith targetHost target (3 + index) (restore world initial) args
      (fun final values => P (erase final) values ∧ final.host = world) := by
  layout_instance terminatesWith_transport_with

theorem entry_trap_world_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {fuel : Nat} {initial : Store Unit} {world : World} {args : List Value}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {final : Store World} {message : String}
    (hTrap : run fuel target (3 + calls.length + index) (restore world initial) args targetHost =
      .Trap final message) : final.host = world := by
  have h := entry_keepsWorld_with (calls := calls) layout profile hIndex fuel initial world args sourceHost targetHost
  rw [hTrap] at h
  exact h

theorem entry_trap_world {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {fuel : Nat} {initial : Store Unit} {world : World} {args : List Value}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {final : Store World} {message : String}
    (hTrap : run fuel target (3 + index) (restore world initial) args targetHost =
      .Trap final message) : final.host = world := by
  layout_instance entry_trap_world_with

theorem wp_transport_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    {code : Program} (hForm : Encoding.ProgramForm code)
    (hClosed : Relocation.programClosed source.funcs.length code = true)
    {initial : Store Unit} {locals : Locals} {P : Assertion Unit} {Q : Assertion World}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    (world : World) (h : wp source code P initial locals sourceHost)
    (hPost : ∀ continuation, P continuation → Q (liftContinuation world continuation)) :
    wp target (Relocation.programWith calls code) Q (restore world initial) locals targetHost := by
  unfold wp at h ⊢
  obtain ⟨bound, hBound⟩ := h
  refine ⟨bound, fun fuel hFuel => ?_⟩
  rw [code_transport_with layout profile hForm hClosed fuel initial world locals sourceHost targetHost]
  exact hPost _ (hBound fuel hFuel)

theorem wp_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {code : Program} (hForm : Encoding.ProgramForm code)
    (hClosed : Relocation.programClosed source.funcs.length code = true)
    {initial : Store Unit} {locals : Locals} {P : Assertion Unit} {Q : Assertion World}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    (world : World) (h : wp source code P initial locals sourceHost)
    (hPost : ∀ continuation, P continuation → Q (liftContinuation world continuation)) :
    wp target (Relocation.program code) Q (restore world initial) locals targetHost := by
  layout_instance wp_transport_with

end Verified.Wasi.PureTransport
