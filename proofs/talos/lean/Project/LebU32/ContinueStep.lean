import Project.LebU32.BranchBounds
import Project.LebU32.ContinuePush
import Project.LebU32.ContinueRelease

namespace Project.LebU32.Spec
open Wasm Project.Common Project.ProofKit Project.EulerRiemann.Execution

theorem continueStep_spec (env : HostEnv Unit) (seed : Heap) (initial current : Store Unit)
    (input value : UInt64) (base frame : Locals) (count : Nat) (bytes : ByteArray)
    (facts : RunningFacts seed initial input current base count value bytes)
    (hFrame : BranchFrame frame (UInt64.ofNat (10 - count)) value (bytePointer seed count) (UInt64.ofNat count))
    (hLength : (lebList 10 input).length ≤ 5) (hRest : value / 128 ≠ 0)
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, RunningState seed initial input final result →
      encodingMeasure final result < encodingMeasure current base → wp «module» rest Q final result env) :
    wp «module» (continueByteCode ++ rest) Q current frame env := by
  have hCount : count ≤ 4 := by have := facts.bound; omega
  have hFuel : 10 - count = (10 - (count + 1)) + 1 := by omega
  have hSplit : lebList 10 input = (bytes.push (value % 128 + 128).toUInt8).data.toList ++
      lebList (10 - (count + 1)) (value / 128) := by
    rw [facts.split, hFuel, lebList_cont _ _ hRest]
    simp [ByteArray.data_push, List.append_assoc]
  have hBound : count + 1 < (lebList 10 input).length := by
    have hPositive := lebList_length_pos (10 - (count + 1)) (value / 128) (by omega)
    have hSizes : (lebList 10 input).length = bytes.size + 1 +
        (lebList (10 - (count + 1)) (value / 128)).length := by
      simpa only [List.length_append, Array.length_toList, ByteArray.data_push, Array.size_push, ByteArray.size]
        using congrArg List.length hSplit
    rw [facts.storage.size] at hSizes
    omega
  have hFuelWord : UInt64.ofNat (10 - count) - 1 = UInt64.ofNat (10 - (count + 1)) := by
    u64_omega
  rw [← List.take_append_drop 69 continueByteCode, List.append_assoc]
  apply continuePush_spec env current (runningHeap seed count) frame (UInt64.ofNat (10 - count)) value
    (bytePointer seed count) bytes (by simpa only [facts.storage.size] using hFrame)
    facts.storage.heap facts.storage.values facts.storage.protected (by rw [facts.storage.size]; omega)
    (facts.storage.bump_bounds hCount hFit hMemory hCap) (by rw [facts.storage.pages]; exact hPages)
  intro pushed pushFrame hAdvance hOutput hPushPages
  have hStorage := facts.storage.pushed (value % 128 + 128) hCount hFit hMemory hOutput hPushPages
  apply continueRelease_spec env seed initial pushed pushFrame (UInt64.ofNat (10 - count)) value count bytes
    (by simpa only [facts.storage.size, running_allocation_root seed count bytes hCount facts.storage.size] using hAdvance)
    hStorage hCount hFit
  intro final result hRunning hFinalStorage
  have hResultFrame : RunningFrame result (UInt64.ofNat (10 - (count + 1))) (value / 128)
      (bytePointer seed (count + 1)) (UInt64.ofNat (count + 1)) := by
    simpa only [hFuelWord] using hRunning
  apply hNext final result
  · exact ⟨count + 1, value / 128, bytes.push (value % 128 + 128).toUInt8,
      hSplit, hBound, hResultFrame, hFinalStorage⟩
  · rw [measure_running current base count value (bytePointer seed count) facts.frame,
      measure_running final result (count + 1) (value / 128) (bytePointer seed (count + 1)) hResultFrame]
    omega

#print axioms continueStep_spec
end Project.LebU32.Spec
