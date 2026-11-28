module

public import Verified.Reflect.Command
public import LeanExe.A64.Proof.BytesRuns
public import TestSupport.A64.Programs

@[expose] public section

/-!
Tests of `LeanExe.A64.bytes_runs_on` and `LeanExe.A64.bytes_runs_at` (leanexe#30) on a function
over bytes whose theorem without the trap, `compiled.twice.trapFree`, holds only under room for
its generated bound after the message's block.  `twice` writes each byte of its message twice,
and `verified_compile` compiles it.  `twice_runs` states its program in the form `BytesRuns` with
the status 1 of the trap only for a message without that room, `RoomFor`, from `trapFree` for the
messages with room and `compiled.twice.implements` for the others, and `twice_runs_room` drops the
status 4, since the stack that the program uses fits the room of `TestSupport.A64.Programs`.
-/

namespace TestSupport.A64.Twice

open LeanExe LeanExe.A64 LeanExe.Pipeline TestSupport.A64

/-- Each byte of the message, twice. -/
def twice (b : Bytes) : Bytes := Bytes.build (2 * b.size) fun i => b.get (i / 2)

verified_compile compiled := [twice]

/-- The index of `twice` among the functions of `compiled.module`, after the allocator and the
release. -/
def entry : Nat := 2

/-- The largest length of a message. -/
def inMax : UInt64 := 4096

/-- The memory's cap in pages. -/
def cap : Nat := 16

/-- The payload of an allocation of `L` bytes exceeds `L` by at most 8 bytes. -/
theorem allocSize_le_add {L : Nat} (h : L ≤ 4294967296) :
    (allocSize (UInt64.ofNat L)).toNat ≤ L + 8 := by
  have hL : (UInt64.ofNat L).toNat = L := by
    rw [UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have hRound : ((UInt64.ofNat L + 7) / 8 * 8).toNat = (L + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat, hL]
    omega
  unfold allocSize
  split
  · simp only [UInt64.reduceToNat]
    omega
  · rw [hRound]
    omega

/-- The heap's `top` at the module's start. -/
theorem top_eq : (Verified.initialHeap compiled.tables).top.toNat = 4096 := by decide +kernel

/-- The message `b` leaves room for the generated bound of `twice` after its block. -/
def RoomFor (b : Bytes) : Prop :=
  ((Verified.initialHeap compiled.tables).allocate
      (allocSize (UInt64.ofNat b.data.size))).top.toNat + compiled.twice.bound b ≤ 65536 * cap

/-- The program of `twice` writes each byte of a message of at most `inMax` bytes twice and
returns 0, or reaches the exit word with the status 1 of the trap only for a message without
room for the bound, or with the status 4 when the room lies below the stack's bound. -/
theorem twice_runs :
    BytesRuns compiled.module entry inMax room cap
      (fun msg => (twice ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun msg c => (¬ RoomFor ⟨⟨msg.toArray⟩⟩ ∧ c = 1) ∨
        (room.toNat < stackBound compiled.module entry ∧ c = 4) := by
  have hAt := compiled.initial.1
  refine bytes_runs_on (G := RoomFor) compiled.twice.trapFree compiled.twice.implements
    (typeIdx := 0) rfl hAt (by decide) (fun L hL => Heap.Within.room ?_ (by decide))
    (fun b st _ hcap hG => ?_) (fun _ _ _ _ => trivial) (by decide +kernel) (by decide +kernel)
  · show _ + _ ≤ 65536 * cap
    have := allocSize_le_add (L := L) (by simp only [inMax, UInt64.reduceToNat] at hL; omega)
    simp only [inMax, UInt64.reduceToNat, cap] at hL ⊢
    rw [top_eq]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
    rw [hcap]
    exact hG

/-- The stack that `twice` uses fits the room. -/
theorem stack_twice : stackBound compiled.module entry ≤ room.toNat := by decide +kernel

/-- `twice_runs` with the status 1 alone, for a message without room for the bound. -/
theorem twice_runs_room :
    BytesRuns compiled.module entry inMax room cap
      (fun msg => (twice ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun msg c => ¬ RoomFor ⟨⟨msg.toArray⟩⟩ ∧ c = 1 :=
  twice_runs.mono fun _ _ hc => hc.elim id fun h => absurd h.1 (Nat.not_lt.2 stack_twice)

#print axioms LeanExe.A64.bytes_runs_at
#print axioms LeanExe.A64.bytes_runs_on
#print axioms LeanExe.A64.bytes_runs
#print axioms twice_runs
#print axioms twice_runs_room

end TestSupport.A64.Twice
