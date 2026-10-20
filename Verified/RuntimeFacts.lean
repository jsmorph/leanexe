import Verified.AllocCost
import LeanExe.Pipeline.RuntimeSpec

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- A module with the runtime's `alloc` and `release` at functions 0 and 1, no imports, and a
32-bit memory, as `compile` builds it. -/
structure Runtime (m : Module) : Prop where
  imports : m.imports = []
  memory32 : m.memIs64 = false
  alloc : m.funcs[0]? = some (allocFunction 0)
  release : m.funcs[1]? = some (releaseFunction 1)

/-- Whether `top` can rise by `n` bytes within the memory cap of `m`. -/
def _root_.LeanExe.Pipeline.Heap.Within (heap : Heap) (store : Store Unit) (m : Module)
    (n : Nat) : Prop :=
  heap.top.toNat + n ≤ 65536 * store.memoryCap m 0

instance {heap : Heap} {store : Store Unit} {m : Module} {n : Nat} :
    Decidable (heap.Within store m n) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem _root_.LeanExe.Pipeline.Heap.Within.mono {heap : Heap} {store : Store Unit}
    {m : Module} {n n' : Nat}
    (h : heap.Within store m n) (hle : n' ≤ n) : heap.Within store m n' := by
  unfold Heap.Within at *; omega

theorem _root_.Wasm.TrapOK.within {P P' : Prop} [Decidable P] [Decidable P'] {Q : Assertion Unit}
    (h : TrapOK (!decide P) Q) (hP : P → P') : TrapOK (!decide P') Q := by
  by_cases hp' : P'
  · simp [hp', TrapOK]
  · have hp : ¬P := fun hp => hp' (hP hp)
    simpa [hp, hp'] using h

theorem _root_.LeanExe.Pipeline.Heap.Within.after {heap heap1 : Heap} {store store1 : Store Unit}
    {m : Module} {c1 c2 : Nat} (h : heap.Within store m (c1 + c2))
    (hTop : heap1.top.toNat ≤ heap.top.toNat + c1)
    (hCaps : store1.memoryCap m 0 = store.memoryCap m 0) : heap1.Within store1 m c2 := by
  unfold Heap.Within at *; rw [hCaps]; omega

/-- An allocation of `need` bytes for which `top` can rise by `48 + need` within the cap has the
room that `alloc` needs. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.room {heap : Heap} {store : Store Unit}
    {m : Module} {need : UInt64}
    (h : heap.Within store m (48 + need.toNat)) (hCap : store.memoryCap m 0 ≤ 65535) :
    heap.Room store m need := by
  unfold Heap.Within at h
  intro _
  unfold FixedArrayBump.requiredPages
  constructor
  · omega
  · intro _; omega

/-- An allocation that fits raises `top` by at most `48 + need`. -/
theorem _root_.LeanExe.Pipeline.Heap.allocate_top {heap : Heap} {need : UInt64}
    (h : heap.Fits need) :
    (heap.allocate need).top.toNat ≤ heap.top.toNat + allocCost need.toNat := by
  have hTop := allocatedTop_toNat heap.top need heap.free h.fit32
  simp only [Heap.allocate, allocCost]
  rw [hTop]
  split <;> omega

/-- How an allocation of `bytes` changed `top`: it reused free memory, which leaves `top` unchanged
and gives a block of at least `bytes`, or it raised `top` by `48 + allocSize bytes` for a block of
exactly that capacity. -/
def AllocShape (heap heap' : Heap) (bytes : UInt64) (cap : Nat) : Prop :=
  (heap'.top.toNat = heap.top.toNat ∧ bytes.toNat ≤ cap) ∨
    (heap'.top.toNat = heap.top.toNat + 48 + (allocSize bytes).toNat ∧
      cap = (allocSize bytes).toNat)

theorem AllocShape.le {heap heap' : Heap} {bytes : UInt64} {cap : Nat}
    (h : AllocShape heap heap' bytes cap) (hb : bytes.toNat ≤ 4294967296) : bytes.toNat ≤ cap := by
  rcases h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact h
  · exact le_allocSize hb

theorem _root_.LeanExe.Pipeline.Heap.allocate_shape {heap : Heap} {bytes : UInt64}
    (hb : bytes.toNat ≤ 4294967296) (h : heap.Fits (allocSize bytes)) :
    AllocShape heap (heap.allocate (allocSize bytes)) bytes
      (allocatedCapacity (allocSize bytes) heap.free).toNat := by
  have hTop := allocatedTop_toNat heap.top (allocSize bytes) heap.free h.fit32
  have hCap := allocated_capacity (allocSize bytes) heap.free
  have hRound := le_allocSize hb
  simp only [AllocShape, Heap.allocate]
  rw [hTop]
  cases hTake : takeFirstFitFrom 0 (allocSize bytes) heap.free with
  | some choice =>
    left
    exact ⟨by simp, by omega⟩
  | none =>
    right
    simp [allocatedCapacity, hTake]

/-- A call of `alloc` on the byte count on top of the stack: the allocation, which raises `top`
by at most `c`, or a trap at `unreachable`, which happens only when `top` cannot rise by `c`
within the cap. -/
theorem wp_alloc {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {bytes : UInt64} {vs : List Value} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (hBytes : bytes.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535) (hc : allocCost (allocSize bytes).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hNext : heap.Fits (allocSize bytes) →
      (heap.allocate (allocSize bytes)).top.toNat ≤ heap.top.toNat + c →
      wp m rest Q (heap.allocateStore store (allocSize bytes) 1)
        { s with values := .i64 (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free) ::
          vs } host) :
    wp m (.call 0 :: rest) Q store { s with values := .i64 bytes :: vs } host := by
  have hRun := (alloc_spec_runs (!decide (heap.Within store m c)) hm.memory32 hm.imports hm.alloc
    host heap store bytes hAt hBytes hCap fun hw => by
      simp only [Bool.not_eq_false'] at hw
      exact ((of_decide_eq_true hw).mono hc).room hCap).append_args (by simp [hm.imports])
    (by simpa [hm.imports] using hm.alloc) (by rfl) vs
  refine wp_call_runs hRun hTrap fun st' out hPost => ?_
  obtain ⟨out', rfl, hFits, rfl, rfl⟩ := hPost
  simpa using hNext hFits ((Heap.allocate_top hFits).trans (by omega))

/-- The byte count of an array of `size` words is a multiple of 8, which `alloc` keeps. -/
theorem allocSize_words {size : Nat} (h : size < 536870912) :
    ((UInt64.ofNat size + 1) * 8).toNat = 8 * (size + 1) ∧
      allocSize ((UInt64.ofNat size + 1) * 8) = (UInt64.ofNat size + 1) * 8 := by
  have hN : (UInt64.ofNat size).toNat = size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hBytes : ((UInt64.ofNat size + 1) * 8).toNat = 8 * (size + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, hN, UInt64.reduceToNat]
    omega
  refine ⟨hBytes, ?_⟩
  have hRound : (((UInt64.ofNat size + 1) * 8 + 7) / 8 * 8).toNat = 8 * (size + 1) := by
    rw [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, hBytes]
    simp only [UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · rename_i hLt
    rw [UInt64.lt_iff_toNat_lt, hRound] at hLt
    simp at hLt
  · apply UInt64.toNat_inj.mp
    rw [hRound, hBytes]

end Verified
