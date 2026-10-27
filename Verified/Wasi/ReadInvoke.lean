import Verified.Wasi.ReadReady
import Verified.Wasi.ReadResult
import Verified.Wasi.ReadCall

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem read_narrow64 (word : UInt64) (h : word.toNat < 4294967296) :
    word.toUInt32.toUInt64 = word := by
  rw [UInt64.toUInt64_toUInt32]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mod, UInt64.reduceToNat, Nat.mod_eq_of_lt h]

theorem wp_read_invoke {World : Type} {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial before : Store (Observed World)} {heap0 heap : Heap}
    {capacity root oldErrno oldLength : UInt64} {values : List Value}
    {rest : Program} {Q : Assertion (Observed World)} {budget : Nat}
    (hHost : env.Satisfies target (hostSpec host))
    (hCapacity : capacity.toNat < 4294967296)
    (hReady : ReadReady heap (PureTransport.erase before) root capacity)
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hWorld : before.host = initial.host)
    (hTop : heap.top.toNat ≤ heap0.top.toNat + budget)
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (root' length : UInt64)
      (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readSome capacity) initial.host trace (.returned result) final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root') →
      Bytes.Rep heap' (PureTransport.erase final) root' length result.bytes →
      heap'.top.toNat ≤ heap0.top.toNat + budget →
      wp target rest Q final (readLocals capacity root' result.errno length values) env)
    (hTrap : ∀ (final : Store (Observed World)) (heap' : Heap)
      (message : String) (trace : List Event),
      Exec (observedHost host) (readSome capacity) initial.host trace (.trapped message) final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      heap'.top.toNat ≤ heap0.top.toNat + budget → Q (.Trap final message)) :
    wp target (readCallCode 1 0 ++ readResultCode ++ rest) Q before
      (readLocals capacity root oldErrno oldLength values) env := by
  have hAddress := hReady.address
  have hRoot : root.toNat < 4294967296 := by omega
  have hRootNat : root.toUInt32.toNat = root.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt hRoot]
  have hCapacityNat : capacity.toUInt32.toNat = capacity.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt hCapacity]
  have hRootCast := read_narrow64 root hRoot
  have hCapacityCast := read_narrow64 capacity hCapacity
  have hMemory : 16 ≤ before.mem.pages * 65536 := by
    have hBase := hBefore.at_.base
    have hBound := hBefore.at_.top
    change 16 ≤ (PureTransport.erase before).mem.pages * 65536
    omega
  have hSeparate : capacity.toUInt32 = 0 ∨ 16 ≤ root.toUInt32.toNat := by
    rcases hReady with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hBufferCapacity⟩
    · left; rfl
    · right
      rw [hRootNat]
      have := hBuffer.object.base
      omega
  rw [List.append_assoc]
  refine wp_read_call (pointer := root.toUInt32) (capacity := capacity.toUInt32)
    hImports hHost hMemory
    (by rw [hRootNat, hCapacityNat]; exact hReady.memory hBefore.at_)
    (by rw [hRootNat, hCapacityNat]; omega) hSeparate
    (by simpa only [hRootCast] using readLocals_root capacity root oldErrno oldLength values)
    (by simpa only [hCapacityCast] using readLocals_capacity capacity root oldErrno oldLength values)
    ?_ ?_
  · intro after errno committed hRead hFrame hData
    rw [hCapacityCast] at hRead
    rw [hRootNat, hCapacityNat] at hFrame
    have hPayload : errno = 0 → Bytes.At after.mem root committed := by
      intro hZero
      simpa only [hRootCast] using (hData hZero).1
    have hStep := hReady.frame_step hBefore hFrame
    have hRep := hReady.reply_rep hBefore.at_ hRead hFrame hPayload
    have hErrnoBound := ((observedHost host).read_bound hRead).2
    have hExec : Exec (observedHost host) (readSome capacity) initial.host
        [.read capacity (.returned errno committed)] (.returned (readResult errno committed))
        after.host :=
      .read_return hCapacity (by simpa only [hWorld] using hRead) (.pure after.host _)
    simp only [readLocals_values, readLocals_stack]
    refine wp_read_result runtime layout profile hImports sourceHost hStep.at_ hRep
      (by change errno.toNat < 4294967296; change errno.toNat ≤ 76 at hErrnoBound; omega)
      (by rw [hFrame.pages]; exact hMemory)
      (fun hZero => by simpa only [readResult, hZero, ite_true] using (hData hZero).2)
      (fun hNonzero => by simp only [readResult, ite_eq_right hNonzero]) ?_ ?_
    · intro hZero hNonempty
      exact hNext heap after root (readResult errno committed).bytes.size
        (readResult errno committed) [.read capacity (.returned errno committed)] hExec hStep hRep hTop
    · intro hEmpty final hStore hFinalWorld
      have hFinalStep := read_discard_step hStep hRep hStore
      have hFinalTop := read_discard_top hStep.at_ hRep
      refine hNext _ final 0 0 (readResult errno committed)
        [.read capacity (.returned errno committed)] ?_ hFinalStep ?_ ?_
      · simpa only [hFinalWorld] using hExec
      · simpa only [hEmpty] using Bytes.Rep.empty
          (Bytes.releasedHeap heap (PureTransport.erase after) root) (PureTransport.erase final)
      · rw [hFinalTop]
        exact hTop
  · intro after message committed hRead hFrame
    rw [hCapacityCast] at hRead
    rw [hRootNat, hCapacityNat] at hFrame
    exact hTrap after heap message [.read capacity (.trapped message committed)]
      (.read_trap hCapacity (by simpa only [hWorld] using hRead))
      (hReady.frame_step hBefore hFrame) hTop

end Verified.Wasi
