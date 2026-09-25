import Project.LebU32.BranchBounds
import Project.LebU32.FinalByte

namespace Project.LebU32.Spec
open Wasm Project.ProofKit Project.EulerRiemann.Execution

theorem finalStep_spec (env : HostEnv Unit) (seed : Heap) (initial current : Store Unit)
    (input value : UInt64) (base frame : Locals) (count : Nat) (bytes : ByteArray)
    (facts : RunningFacts seed initial input current base count value bytes)
    (hFrame : BranchFrame frame (UInt64.ofNat (10 - count)) value (bytePointer seed count) (UInt64.ofNat count))
    (hLength : (lebList 10 input).length ≤ 5) (hRest : value / 128 = 0)
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, FinishedState seed initial input final result →
      encodingMeasure final result < encodingMeasure current base → wp «module» rest Q final result env) :
    wp «module» (finalByteCode ++ rest) Q current frame env := by
  have hCount : count ≤ 4 := by have := facts.bound; omega
  have hFuel : 10 - count = (9 - count) + 1 := by omega
  have hSplit : lebList 10 input = (bytes.push (value % 128).toUInt8).data.toList := by
    rw [facts.split, hFuel, lebList_final _ _ hRest]
    simp [ByteArray.data_push]
  have hCountResult : (lebList 10 input).length = count + 1 := by
    rw [hSplit, Array.length_toList]
    change (bytes.push (value % 128).toUInt8).size = count + 1
    rw [ByteArray.size_push, facts.storage.size]
  apply finalByte_spec env current (runningHeap seed count) frame (UInt64.ofNat (10 - count)) value
    (bytePointer seed count) bytes (by simpa only [facts.storage.size] using hFrame)
    facts.storage.heap facts.storage.values facts.storage.protected (by rw [facts.storage.size]; omega)
    (facts.storage.bump_bounds hCount hFit hMemory hCap) (by rw [facts.storage.pages]; exact hPages)
  intro final result hFinished hOutput hFinalPages
  have hStorage := facts.storage.pushed (value % 128) hCount hFit hMemory hOutput hFinalPages
  have hResultFrame : FinishedFrame result (UInt64.ofNat (11 - (lebList 10 input).length))
      (bytePointer seed (lebList 10 input).length) (UInt64.ofNat (lebList 10 input).length) := by
    simpa only [running_allocation_root seed count bytes hCount facts.storage.size, facts.storage.size,
      hCountResult, show 11 - (count + 1) = 10 - count by omega,
      bytePointer, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel] using hFinished
  apply hNext final result
  · refine ⟨bytes.push (value % 128).toUInt8, hSplit.symm, hResultFrame, ?_⟩
    simpa only [hCountResult] using hStorage.finished
  · rw [measure_running current base count value (bytePointer seed count) facts.frame,
      measure_finished final result (lebList 10 input).length _ hResultFrame, hCountResult]
    omega

#print axioms finalStep_spec
end Project.LebU32.Spec
