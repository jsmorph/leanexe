import Verified.Wasi.Scratch
import Verified.Wasi.GuestFrame
import Verified.Wasi.ReadCode
import Interpreter.Wasm.Wp.Call

namespace Verified.Wasi

open Wasm LeanExe.Wasi

theorem wp_read_call {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {store : Store (Observed World)} {s : Locals}
    {pointer capacity : UInt32} {pointerSlot capacitySlot : Nat}
    {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.imports) (hHost : env.Satisfies m (hostSpec host))
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hBuffer : pointer.toNat + capacity.toNat ≤ store.mem.pages * 65536)
    (hAddress : pointer.toNat + capacity.toNat ≤ 2 ^ 32)
    (hSeparate : capacity = 0 ∨ 16 ≤ pointer.toNat)
    (hPointerLocal : s.get pointerSlot = some (.i64 pointer.toUInt64))
    (hCapacityLocal : s.get capacitySlot = some (.i64 capacity.toUInt64))
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (committed : LeanExe.Bytes),
      (observedHost host).read store.host capacity.toUInt64
        (.returned errno committed) final.host →
      GuestFrame store final [ABI.scratch, (pointer.toNat, capacity.toNat)] →
      (errno = 0 → Bytes.At final.mem pointer.toUInt64 committed ∧
        final.mem.read32 8 = UInt32.ofNat committed.data.size) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (committed : LeanExe.Bytes),
      (observedHost host).read store.host capacity.toUInt64
        (.trapped message committed) final.host →
      GuestFrame store final [ABI.scratch, (pointer.toNat, capacity.toNat)] →
      Q (.Trap final message)) :
    wp m (readCallCode pointerSlot capacitySlot ++ rest) Q store s env := by
  let initial := initializeScratch store pointer capacity
  have hFrame : GuestFrame store initial [ABI.scratch, (pointer.toNat, capacity.toNat)] :=
    (GuestFrame.ofScratchWrites (initializeScratch_range store pointer capacity)).weaken
      (by simp)
  have hRequest : ReadRequest initial [.i32 0, .i32 0, .i32 1, .i32 8]
      pointer capacity := by
    have hReads := initializeScratch_reads store pointer capacity
    exact ⟨rfl, hMemory, hReads.1, hReads.2.1, hBuffer, hAddress, hSeparate⟩
  simp only [readCallCode, List.append_assoc]
  refine wp_metadata hPointerLocal hCapacityLocal hMemory ?_
  simp only [UInt32.toUInt32_toUInt64, List.cons_append, List.nil_append, wp_const_cons]
  refine wp_call_host_contract (id := 0) (imp := ABI.imports[0]!) (c := readContract host)
    (by simp [hImports, ABI.imports]) hHost
    (by simp [hImports, ABI.imports]) (hostSpec_read host) ?_ ?_ ?_
  · intro values final hContract
    obtain ⟨errno, committed, rfl, hRead, hGuest, hData⟩ :=
      hContract pointer capacity (by simpa [ABI.imports, ABI.transferType] using hRequest)
    exact hNext final errno committed hRead (hFrame.trans hGuest) hData
  · intro final message hContract
    obtain ⟨committed, hRead, hGuest⟩ :=
      hContract pointer capacity (by simpa [ABI.imports, ABI.transferType] using hRequest)
    exact hTrap final message committed hRead (hFrame.trans hGuest)
  · intro final tag arguments hContract
    exact False.elim (hContract pointer capacity (by
      simpa [ABI.imports, ABI.transferType] using hRequest))

end Verified.Wasi
