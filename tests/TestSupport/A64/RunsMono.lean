module

public import LeanExe.A64.Proof.BytesRuns
public import TestSupport.A64.Uart

@[expose] public section

/-!
Tests of `LeanExe.A64.BytesRuns.mono` and `LeanExe.A64.InputRuns.mono`, which weaken the predicate
of the statuses with which a program that reads its input from the UART reaches the exit word.  A
program of `bytes_runs` whose function may reach `unreachable` and whose stack bound lies within
the room has the theorem with the status 1 of the trap alone.  GCD's loop of
`TestSupport.A64.Uart`, whose theorem `input_runs` states with the statuses 1 and 4, has the
theorem without a status, the form that `input_runs_bounded` gives, from `input_runs` and the
bound of its stack.
-/

namespace TestSupport.A64.RunsMono

open Wasm LeanExe.A64 TestSupport.A64.Uart TestSupport.Native.Gcd

/-- The statuses of `bytes_runs` with the stack bound within the room: the trap at `unreachable`
alone. -/
example {aborts : Bool} {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {Out : List UInt8 → List UInt8}
    (h : BytesRuns m k inMax room cap Out fun _ c =>
      aborts = true ∧ c = 1 ∨ room.toNat < stackBound m k ∧ c = 4)
    (hs : stackBound m k ≤ room.toNat) :
    BytesRuns m k inMax room cap Out fun _ c => c = 1 :=
  h.mono fun _ _ hc => hc.elim (fun h => h.2) fun h => absurd h.1 (Nat.not_lt.2 hs)

/-- GCD's loop on two words read from the UART, from `input_runs`: with a room at or above the
stack bound, the program reaches the exit word with no status. -/
theorem uart_runs_mono (room : UInt64) (cap : Nat)
    (hroom : stackBound loopCompiled.module 2 ≤ room.toNat) :
    InputRuns loopCompiled.module 2 2 room cap .word
      (fun ws => LeanExe.Native.encodeWord (gcd (ws.getD 0 0) (ws.getD 1 0))) fun _ _ => False :=
  (input_runs loopCompiled.gcd.implements args loopCompiled.initial.1 (fun _ _ _ => trivial)
    writes_word (hargs := fun ws hws => by
      match ws, hws with
      | [_, _], _ => rfl)).mono
    fun _ _ hc => hc.elim (fun h => Bool.false_ne_true h.1) fun h => absurd h.2.1 (Nat.not_lt.2 hroom)

#print axioms LeanExe.A64.BytesRuns.mono
#print axioms LeanExe.A64.InputRuns.mono
#print axioms uart_runs_mono

end TestSupport.A64.RunsMono
