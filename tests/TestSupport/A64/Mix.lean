module

public import Verified.Reflect.Command
public import Verified.BytesRuns
public import Verified.Call
public import TestSupport.A64.Twice

@[expose] public section

/-!
Tests of the theorems of `Verified/BytesRuns.lean` (leanexe#20) on a wrapper over a table as the
entry of a program over bytes.  `mix` applies `mixWith` to the table `tbl`, so its generated
theorems `compiled.mix.trapFree` and `compiled.mix.implements` are `Verified.ImplementsTables`
theorems, which ask for the table borrowed in the store of the call.  `mix_runs_bounded` states
its program without a status from `trapFree`, with the table borrowed at the module's initial
store (`tables_borrowed`) and room for the bound `mix_bound` of every message of at most `inMax`
bytes.  `mix_runs` states it with the status 1 only for a message without room for the generated
bound, from `trapFree` and `implements` (leanexe#30), and `mix_runs_room` drops the status 4.
-/

namespace TestSupport.A64.Mix

open LeanExe LeanExe.A64 LeanExe.Pipeline TestSupport.A64

/-- The table of `mix`. -/
def tbl : Array UInt64 := #[0x20, 0x01, 0x40]

/-- The bytes of `b`, each XORed with the word of `t` that its position modulo 3 chooses. -/
def mixWith (t : Array UInt64) (b : Bytes) : Bytes :=
  Bytes.build b.size fun i => b.get i ^^^ t[(i % 3).toNat]!

/-- `mixWith` on the table `tbl`, which `verified_compile` compiles to a wrapper that reads the
table from the store. -/
def mix (b : Bytes) : Bytes := mixWith tbl b

verified_compile compiled := [mixWith, mix]

/-- The index of the wrapper `mix` among the functions of `compiled.module`, after the allocator,
the release, and `mixWith`. -/
def entry : Nat := 3

/-- The largest length of a message. -/
def inMax : UInt64 := 4096

/-- The memory's cap in pages. -/
def cap : Nat := 16

/-- The heap's `top` at the module's start lies above the table. -/
theorem top_le : (Verified.initialHeap compiled.tables).top.toNat ≤ 8192 := by decide +kernel

/-- The table of the wrapper's theorems is a borrowed array of the module's initial store. -/
theorem tables_borrowed : ∀ t ∈ [((4096 : UInt64), tbl)],
    (Verified.initialHeap compiled.tables).Borrowed
      (compiled.module.initialStore : Wasm.Store Unit) t.1 t.2 := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  exact (Verified.Ready.initial rfl compiled.initial).2.2 0 (by decide)

/-- The result's block takes at most 56 bytes more than the message. -/
theorem mix_bound (b : Bytes) : compiled.mix.bound b ≤ b.data.size + 56 := by
  rw [compiled.mix.bound_eq, compiled.mixWith.bound_eq]
  have h : b.size.toNat ≤ b.data.size := by
    simp only [Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  unfold Verified.Bytes.allocationCost
  split
  · omega
  · rcases Nat.le_total 1 ((b.size.toNat + 7) / 8) with h1 | h1
    · rw [Nat.max_eq_right h1]
      omega
    · rw [Nat.max_eq_left h1]
      omega

/-- The stack that `mix` uses fits the room. -/
theorem stack_mix : stackBound compiled.module entry ≤ room.toNat := by decide +kernel

/-- The allocator has room for the block of every message of at most `inMax` bytes. -/
theorem room_alloc (L : Nat) (hL : L ≤ inMax.toNat) :
    (Verified.initialHeap compiled.tables).Room (initStore compiled.module cap) compiled.module
      (allocSize (UInt64.ofNat L)) := by
  refine Heap.Within.room ?_ (by decide)
  show _ + _ ≤ 65536 * cap
  have := Twice.allocSize_le_add (L := L) (by simp only [inMax, UInt64.reduceToNat] at hL; omega)
  have := top_le
  simp only [inMax, UInt64.reduceToNat, cap] at hL ⊢
  omega

/-- The program of `mix` writes the bytes of `mix` of a message of at most `inMax` bytes and
returns 0: the cap holds the message's block and the bound of the wrapper. -/
theorem mix_runs_bounded :
    BytesRuns compiled.module entry inMax room cap
      (fun msg => (mix ⟨⟨msg.toArray⟩⟩).data.data.toList) fun _ _ => False := by
  refine Verified.ImplementsTables.bytes_runs_bounded compiled.mix.trapFree (typeIdx := 0) rfl
    compiled.initial.1 tables_borrowed (by decide) room_alloc (fun b st hb hcap => ?_)
    (by decide +kernel) stack_mix
  show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
  rw [hcap]
  simp only [inMax, UInt64.reduceToNat] at hb
  have hfit : (Verified.initialHeap compiled.tables).Fits
      (allocSize (UInt64.ofNat b.data.size)) := by
    intro _
    have := Twice.allocSize_le_add (L := b.data.size) (by omega)
    have := top_le
    omega
  have htop := Heap.allocate_top hfit
  have := Twice.allocSize_le_add (L := b.data.size) (by omega)
  have := mix_bound b
  have := top_le
  simp only [Verified.allocCost, cap] at htop ⊢
  omega

/-- The message `b` leaves room for the generated bound of `mix` after its block. -/
def RoomFor (b : Bytes) : Prop :=
  ((Verified.initialHeap compiled.tables).allocate
      (allocSize (UInt64.ofNat b.data.size))).top.toNat + compiled.mix.bound b ≤ 65536 * cap

/-- The program of `mix` traps only on a message without room for the generated bound, from the
wrapper's theorems without and with the trap. -/
theorem mix_runs :
    BytesRuns compiled.module entry inMax room cap
      (fun msg => (mix ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun msg c => (¬ RoomFor ⟨⟨msg.toArray⟩⟩ ∧ c = 1) ∨
        (room.toNat < stackBound compiled.module entry ∧ c = 4) := by
  refine Verified.ImplementsTables.bytes_runs_on (G := RoomFor) compiled.mix.trapFree
    compiled.mix.implements (typeIdx := 0) rfl compiled.initial.1 tables_borrowed (by decide)
    room_alloc (fun b st _ hcap hG => ?_) (fun _ _ _ _ => trivial) (by decide +kernel)
    (by decide +kernel)
  show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
  rw [hcap]
  exact hG

/-- `mix_runs` with the status 1 alone, for a message without room for the bound. -/
theorem mix_runs_room :
    BytesRuns compiled.module entry inMax room cap
      (fun msg => (mix ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun msg c => ¬ RoomFor ⟨⟨msg.toArray⟩⟩ ∧ c = 1 :=
  mix_runs.mono fun _ _ hc => hc.elim id fun h => absurd h.1 (Nat.not_lt.2 stack_mix)

#print axioms LeanExe.A64.callStore_writesWithin
#print axioms LeanExe.A64.borrowed_callStore
#print axioms Verified.ImplementsTables.implementsA_bytes
#print axioms Verified.ImplementsTables.bytes_runs_on
#print axioms Verified.ImplementsTables.bytes_runs_bounded
#print axioms mix_runs_bounded
#print axioms mix_runs
#print axioms mix_runs_room

end TestSupport.A64.Mix
