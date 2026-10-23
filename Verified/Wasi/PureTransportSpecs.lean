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

theorem entry_keepsWorld {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    (fuel : Nat) (initial : Store Unit) (world : World) (args : List Value)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    KeepsWorld world (run fuel target (3 + index) (restore world initial) args targetHost) := by
  rw [entry_transport layout profile hIndex fuel initial world args sourceHost targetHost]
  exact liftResult_keepsWorld world _

theorem runs_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {aborts : Bool} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : Runs aborts sourceHost source index initial args P) (world : World) :
    Runs aborts targetHost target (3 + index) (restore world initial) args
      (fun final values => P (erase final) values ∧ final.host = world) := by
  obtain ⟨bound, hBound⟩ := h
  refine ⟨bound, fun fuel hFuel => ?_⟩
  have hEq := entry_transport layout profile hIndex fuel initial world args sourceHost targetHost
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

theorem terminatesWith_transport {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith sourceHost source index initial args P) (world : World) :
    TerminatesWith targetHost target (3 + index) (restore world initial) args
      (fun final values => P (erase final) values ∧ final.host = world) :=
  (runs_transport layout profile hIndex (h.runs (aborts := false)) world).terminatesWith

theorem entry_trap_world {World : Type} {source target : Module}
    (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    {index : Nat} (hIndex : index < source.funcs.length)
    {fuel : Nat} {initial : Store Unit} {world : World} {args : List Value}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {final : Store World} {message : String}
    (hTrap : run fuel target (3 + index) (restore world initial) args targetHost =
      .Trap final message) : final.host = world := by
  have h := entry_keepsWorld layout profile hIndex fuel initial world args sourceHost targetHost
  rw [hTrap] at h
  exact h

end Verified.Wasi.PureTransport
