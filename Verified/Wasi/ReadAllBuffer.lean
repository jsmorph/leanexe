import Verified.Wasi.ReadSteps
import LeanExe.Wasi.ReadAll

/-! The buffer of `readAll` across one read into its tail.  The host writes only the scratch
bytes and the 4,096 bytes after the bytes held, which lie inside the buffer's payload, so the
buffer keeps its header and the bytes held, and a successful read appends its bytes. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem GuestFrame.widen {World : Type} {before after : Store World}
    {first inner outer : Nat × Nat} (h : GuestFrame before after [first, inner])
    (hLow : outer.1 ≤ inner.1) (hHigh : inner.1 + inner.2 ≤ outer.1 + outer.2) :
    GuestFrame before after [first, outer] := by
  refine ⟨h.resources, h.pages, fun address hOutside => h.bytes address ?_⟩
  intro region hRegion
  rcases List.mem_cons.mp hRegion with rfl | hRegion
  · exact hOutside _ (List.mem_cons_self ..)
  · obtain rfl := List.mem_singleton.mp hRegion
    intro hIn
    apply hOutside outer (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    dsimp only [InRange] at hIn ⊢
    omega

/-- A buffer holds the empty string under its header. -/
theorem _root_.LeanExe.Pipeline.Heap.Buffer.toEmpty {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) :
    Heap.Buffer heap store root LeanExe.Bytes.empty :=
  ⟨h.object, h.magic, h.count, h.minimum, Nat.zero_le _, h.kind, h.width, h.childMask,
    fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem readAll_tail_address {root : UInt64} {length : Nat}
    (h : root.toNat + length < 4294967296) :
    (root + UInt64.ofNat length).toNat = root.toNat + length := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
  omega

/-- After a read into the tail that returned `committed` at the address after the bytes `held`,
the buffer holds `held` followed by `committed`. -/
theorem readAll_buffer_append {World : Type} {before after : Store World} {heap : Heap}
    {root : UInt64} {held committed : LeanExe.Bytes}
    (h : Heap.Buffer heap (PureTransport.erase before) root held)
    (hHeap : heap.At (PureTransport.erase before))
    (hRoom : held.data.size + 4096 ≤ capacityAt (PureTransport.erase before) root)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat + held.data.size, 4096)])
    (hSize : committed.data.size ≤ 4096)
    (hData : Bytes.At after.mem (root + UInt64.ofNat held.data.size) committed) :
    Heap.Buffer heap (PureTransport.erase after) root (appendBytes held committed) := by
  have hBase := h.object.base
  have hFit := h.object.address
  have hBelow := h.object.below
  have hTop := hHeap.top
  have wide := hFrame.widen (outer := (root.toNat, capacityAt (PureTransport.erase before) root))
    (by dsimp only; omega) (by dsimp only; omega)
  have hTail := readAll_tail_address (root := root) (length := held.data.size) (by omega)
  refine allocated_afterRead h wide (by simp only [appendBytes_size]; omega) ⟨?_, ?_, ?_⟩
  · simp only [appendBytes_size]
    omega
  · simp only [appendBytes_size]
    rw [hFrame.pages]
    change root.toNat + _ ≤ (PureTransport.erase before).mem.pages * 65536
    omega
  · intro i hi
    have hSize : i < held.data.size + committed.data.size := by
      simpa only [appendBytes_size] using hi
    by_cases hLeft : i < held.data.size
    · rw [appendBytes_get_left hi hLeft]
      have hSame : after.mem.bytes (root.toNat + i) = before.mem.bytes (root.toNat + i) := by
        apply hFrame.bytes
        intro region hRegion
        rcases List.mem_cons.mp hRegion with rfl | hRegion
        · dsimp only [InRange, ABI.scratch]
          omega
        · obtain rfl := List.mem_singleton.mp hRegion
          dsimp only [InRange]
          omega
      rw [hSame]
      exact h.contents i hLeft
    · rw [appendBytes_get_right hi (by omega)]
      have hContents := hData.contents (i - held.data.size) (by omega)
      rw [hTail, show root.toNat + held.data.size + (i - held.data.size) = root.toNat + i by
        omega] at hContents
      exact hContents

/-- After a read into the tail, the buffer keeps the bytes `held`. -/
theorem readAll_buffer_keep {World : Type} {before after : Store World} {heap : Heap}
    {root : UInt64} {held : LeanExe.Bytes}
    (h : Heap.Buffer heap (PureTransport.erase before) root held)
    (hHeap : heap.At (PureTransport.erase before))
    (hRoom : held.data.size + 4096 ≤ capacityAt (PureTransport.erase before) root)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat + held.data.size, 4096)]) :
    Heap.Buffer heap (PureTransport.erase after) root held := by
  have hFit := h.object.address
  have hBelow := h.object.below
  have hTop := hHeap.top
  have hTail := readAll_tail_address (root := root) (length := held.data.size) (by omega)
  have hEmpty : Bytes.At after.mem (root + UInt64.ofNat held.data.size) LeanExe.Bytes.empty := by
    refine ⟨?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · change (root + UInt64.ofNat held.data.size).toNat + 0 ≤ 4294967296
      omega
    · change (root + UInt64.ofNat held.data.size).toNat + 0 ≤ after.mem.pages * 65536
      rw [hFrame.pages]
      change _ ≤ (PureTransport.erase before).mem.pages * 65536
      omega
  have hAppend := readAll_buffer_append h hHeap hRoom hFrame (by decide) hEmpty
  have hSame : appendBytes held LeanExe.Bytes.empty = held := by
    cases held
    simp only [appendBytes, LeanExe.Bytes.empty, ByteArray.append_empty]
  rwa [hSame] at hAppend

/-- A read into the tail keeps the step from the start of `readAll`, with the buffer as its fresh
block. -/
theorem readAll_tail_step {World : Type} {initial before after : Store World}
    {heap0 heap : Heap} {root : UInt64} {held : LeanExe.Bytes}
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) [block (PureTransport.erase before) root])
    (h : Heap.Buffer heap (PureTransport.erase before) root held)
    (hRoom : held.data.size + 4096 ≤ capacityAt (PureTransport.erase before) root)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat + held.data.size, 4096)]) :
    Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase after) [block (PureTransport.erase after) root] := by
  have wide := hFrame.widen (outer := (root.toNat, capacityAt (PureTransport.erase before) root))
    (by dsimp only; omega) (by dsimp only; omega)
  have hStep := read_fresh_step hBefore h le_rfl wide
  simpa only [Bytes.regions, ite_eq_right h.nonzero] using hStep

theorem readAll_capacity {World : Type} {before after : Store World} {heap : Heap}
    {root : UInt64} {held : LeanExe.Bytes}
    (h : Heap.Buffer heap (PureTransport.erase before) root held)
    (hRoom : held.data.size + 4096 ≤ capacityAt (PureTransport.erase before) root)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat + held.data.size, 4096)]) :
    capacityAt (PureTransport.erase after) root = capacityAt (PureTransport.erase before) root :=
  read_capacity h (hFrame.widen
    (outer := (root.toNat, capacityAt (PureTransport.erase before) root))
    (by dsimp only; omega) (by dsimp only; omega))

end Verified.Wasi
