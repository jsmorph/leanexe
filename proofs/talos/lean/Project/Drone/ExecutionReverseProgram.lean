import Project.Drone.ExecutionPushAllocation
import Project.ProofKit.WordArrayReverseCopy
import Project.ProofKit.WordArrayPushCapacity

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def reverseProgram (base : Nat) : Wasm.Program :=
  FixedArrayCapacity.localProgram (base + 4) 1 (base + 9) ++ FixedArrayAllocate.program (base + 9) 1 ++
  [.localGet (base + 14), .localSet (base + 5), .localGet (base + 5), .wrapI64,
    .localGet (base + 4), .store64 0] ++
  WordArrayReverse.copyProgram (base + 3) (base + 4) (base + 5) (base + 6) ++ [.localGet (base + 5)]

theorem reverse_capacity_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Value) (s : Scratch) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (frame params saved tail { s with need := FixedArrayCapacity.normalizedCapacity s.target 1 }) env) :
    wp Project.Drone.«module» (FixedArrayCapacity.localProgram (params.length + saved.length + 4) 1
      (params.length + saved.length + 9) ++ rest) Q store (frame params saved tail s) env := by
  refine FixedArrayCapacity.localProgram_spec _ s.target 1 _ Project.Drone.«module» env store
    (frame params saved tail s) ?_ rfl (by simp [frame]; omega) (frame_valid _ _ _ _ 9 (by decide)) Q rest ?_
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ] using
      frame_get params saved tail s 4 (by decide)
  · simpa only [capacityFrame_eq] using hNext

theorem reverse_install_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Value) (s : Scratch) (hBound : s.root.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q (FixedArrayResult.writeLength store s.root s.target)
      (frame params saved tail { s with counter := s.root }) env) :
    wp Project.Drone.«module» ([.localGet (params.length + saved.length + 14),
      .localSet (params.length + saved.length + 5), .localGet (params.length + saved.length + 5), .wrapI64,
      .localGet (params.length + saved.length + 4), .store64 0] ++ rest) Q store (frame params saved tail s) env := by
  wp_push_frame [List.cons_append, List.nil_append, show 2^32 = 4294967296 by decide,
    ← Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero, Nat.not_lt.mpr hBound]
  exact hNext

theorem reverse_counter_frame (params saved tail : List Value) (s : Scratch) (count : Nat)
    (hCounter : (frame params saved tail s).validIndex (params.length + saved.length + 6)) :
    FixedArrayCopy.counterFrame (frame params saved tail s) (params.length + saved.length + 6) count hCounter =
      frame params saved tail { s with value := UInt64.ofNat count } := by
  simp [FixedArrayCopy.counterFrame, Locals.set, frame, Scratch.words, Nat.add_assoc]

theorem reverse_copy_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Value) (s : Scratch) (input : Array UInt64)
    (hLength : s.target = UInt64.ofNat input.size) (hSource : UInt64Array.At store s.nextLength input)
    (hFit : s.counter.toNat + 8 * (input.size + 1) ≤ 4294967296)
    (hMemory : s.counter.toNat + 8 * (input.size + 1) ≤ store.mem.pages * 65536)
    (hHeader : store.mem.read64 s.counter.toUInt32 = UInt64.ofNat input.size)
    (hSeparate : s.nextLength.toNat + 8 * (input.size + 1) ≤ s.counter.toNat ∨
      s.counter.toNat + 8 * (input.size + 1) ≤ s.nextLength.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit, UInt64Array.At final s.counter input.reverse →
      Memory.WritesRange store final s.counter.toNat (s.counter.toNat + 8 * (input.size + 1)) →
      wp Project.Drone.«module» rest Q final
        { frame params saved tail { s with value := UInt64.ofNat input.size } with values := [.i64 s.counter] } env) :
    wp Project.Drone.«module» (WordArrayReverse.copyProgram (params.length + saved.length + 3)
      (params.length + saved.length + 4) (params.length + saved.length + 5) (params.length + saved.length + 6) ++
      [.localGet (params.length + saved.length + 5)] ++ rest) Q store (frame params saved tail s) env := by
  rw [List.append_assoc]
  apply WordArrayReverse.copy_spec _ _ _ _ Project.Drone.«module» env store (frame params saved tail s)
    s.nextLength s.counter input (frame_valid _ _ _ _ 6 (by decide)) (by omega) (by omega) (by omega) rfl
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ] using
      frame_get params saved tail s 3 (by decide)
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ, hLength] using
      frame_get params saved tail s 4 (by decide)
  · simpa only [Scratch.words, List.getElem?_cons_zero, List.getElem?_cons_succ] using
      frame_get params saved tail s 5 (by decide)
  · exact hSource
  · exact hFit
  · exact hMemory
  · exact hHeader
  · exact hSeparate
  · intro final _ hOutput hWrites
    rw [reverse_counter_frame]
    wp_push_frame [List.cons_append, List.nil_append]
    exact hNext final hOutput hWrites

#print axioms reverse_capacity_spec
#print axioms reverse_install_spec
#print axioms reverse_copy_spec
end Project.Drone.Execution
