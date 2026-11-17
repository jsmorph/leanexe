import LeanExe.Linux.CallTable
import Verified.Wasi.HostMemory

/-!
The guest's linear memory as the Linux call layer sees it.  `ShimLayout` holds the address of the
guest's byte 0 in the process, and `shimMemory` reads and writes the byte at `base + g` as the
guest's byte `g`, with a region accessible when it lies below the memory's size.  `shimMemory`
meets the layer's laws, its byte strings are the Talos memory's, and `step_read` and `step_write`
evaluate the layer's rule for the requests of `fd_read` and `fd_write` on a guest buffer.
-/

namespace Verified.Shim

open Wasm LeanExe

/-- The addresses that the shim's requests carry: `base`, the address of the guest's byte 0. -/
structure ShimLayout where
  base : UInt64

/-- The guest's address of the process address `a`: `a - base`, modulo 2^64. -/
def ShimLayout.offset (L : ShimLayout) (a : UInt64) : Nat := (a - L.base).toNat

/-- The guest's linear memory as process memory: the byte at `base + g` is the guest's byte `g`,
and the `n` bytes from an address are accessible when they lie below the memory's size. -/
def shimMemory (L : ShimLayout) : Linux.Memory Mem where
  read m a := m.bytes (L.offset a)
  write m a v := { m with bytes := fun i => if i = L.offset a then v else m.bytes i }
  mapped m a n := decide (L.offset a + n ≤ m.pages * 65536)

/-- The request of `fd_read`: a `read` of descriptor 0 into the guest's buffer. -/
def readRequest (L : ShimLayout) (pointer capacity : UInt32) : Linux.Request :=
  ⟨Linux.readCall, [0, L.base + pointer.toUInt64, capacity.toUInt64]⟩

/-- The request of `fd_write`: a `write` to `fd` from the guest's buffer. -/
def writeRequest (L : ShimLayout) (fd : UInt64) (pointer length : UInt32) : Linux.Request :=
  ⟨Linux.writeCall, [fd, L.base + pointer.toUInt64, length.toUInt64]⟩

theorem offset_base (L : ShimLayout) (o : UInt64) : L.offset (L.base + o) = o.toNat := by
  rw [ShimLayout.offset, UInt64.add_comm, UInt64.add_sub_cancel]

theorem offset_add (L : ShimLayout) (a : UInt64) (i : Nat) :
    L.offset (a + UInt64.ofNat i) = (L.offset a + i) % 2 ^ 64 := by
  simp only [ShimLayout.offset, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat',
    Nat.reducePow]
  have := a.toNat_lt
  have := L.base.toNat_lt
  omega

theorem shimMemory_lawful (L : ShimLayout) : (shimMemory L).Lawful where
  read_write_same m a v _ := by simp [shimMemory]
  read_write_other m a b v _ hne := by
    change (if L.offset b = L.offset a then v else m.bytes (L.offset b)) = m.bytes (L.offset b)
    have apart : L.offset b ≠ L.offset a := by
      intro same
      apply hne
      apply UInt64.toNat_inj.mp
      simp only [ShimLayout.offset, UInt64.toNat_sub, Nat.reducePow] at same
      have := a.toNat_lt
      have := b.toNat_lt
      have := L.base.toNat_lt
      omega
    simp only [apart, ↓reduceIte]
  mapped_bytes m a n h i hi := by
    simp only [shimMemory, decide_eq_true_eq, offset_add] at h ⊢
    have := Nat.mod_le (L.offset a + i) (2 ^ 64)
    omega
  mapped_write m a v b k _ := rfl

theorem readBytes_eq_map {M : Type} (I : Linux.Memory M) (m : M) :
    ∀ (n : Nat) (a : UInt64),
      I.readBytes m a n = (List.range n).map fun i => I.read m (a + UInt64.ofNat i)
  | 0, _ => rfl
  | n + 1, a => by
    show I.read m a :: I.readBytes m (a + 1) n = _
    rw [readBytes_eq_map I m n (a + 1), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Linux.succ_ofNat]
    simp

/-- The `n` bytes from `base + o` are the Talos memory's bytes from `o`. -/
theorem shim_readBytes (L : ShimLayout) (m : Mem) (o : UInt64) (n : Nat)
    (h : o.toNat + n ≤ 2 ^ 64) :
    (shimMemory L).readBytes m (L.base + o) n = m.readBytes o.toNat n := by
  rw [readBytes_eq_map, Mem.readBytes]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  change m.bytes (L.offset (L.base + o + UInt64.ofNat i)) = m.bytes (o.toNat + i)
  rw [UInt64.add_assoc, offset_base]
  congr 1
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
  omega

theorem Mem.writeBytes_cons' (m : Mem) (offset : Nat) (b : UInt8) (bs : List UInt8) :
    m.writeBytes offset (b :: bs) =
      ({ m with bytes := fun i => if i = offset then b else m.bytes i } : Mem).writeBytes
        (offset + 1) bs := by
  rw [show b :: bs = [b] ++ bs by rfl, Mem.writeBytes_append]
  congr 1
  cases m with
  | mk pages bytes =>
    simp only [Mem.writeBytes, List.length_cons, List.length_nil]
    congr
    funext i
    by_cases hi : i = offset
    · subst i
      simp
    · simp only [hi, ↓reduceIte]
      split
      · omega
      · rfl

/-- The bytes `bs` written from `base + o` are the Talos memory's write from `o`. -/
theorem shim_writeBytes (L : ShimLayout) :
    ∀ (bs : List UInt8) (m : Mem) (o : UInt64), o.toNat + bs.length < 2 ^ 64 →
      (shimMemory L).writeBytes m (L.base + o) bs = m.writeBytes o.toNat bs
  | [], m, o, _ => by simp [Linux.Memory.writeBytes]
  | b :: bs, m, o, h => by
    simp only [List.length_cons] at h
    have next : (o + 1).toNat = o.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow]
      omega
    have written : (shimMemory L).write m (L.base + o) b =
        ({ m with bytes := fun i => if i = o.toNat then b else m.bytes i } : Mem) := by
      change ({ m with bytes := fun i => if i = L.offset (L.base + o) then b else m.bytes i } :
        Mem) = _
      rw [offset_base]
    show (shimMemory L).writeBytes ((shimMemory L).write m (L.base + o) b) (L.base + o + 1) bs = _
    rw [UInt64.add_assoc, shim_writeBytes L bs _ (o + 1) (by rw [next]; omega), next,
      Mem.writeBytes_cons', written]

/-- The event of `fd_read`'s `read` with the reply `r`, from the memory `m`. -/
def readEvent (L : ShimLayout) (m : Mem) (pointer capacity : UInt32) (r : Linux.Reply) :
    Linux.Event :=
  ⟨Linux.readCall, [0, L.base + pointer.toUInt64, capacity.toUInt64], [],
    m.readBytes pointer.toNat capacity.toNat, r.ret, (List.range capacity.toNat).map r.bytes⟩

/-- The event of `fd_write`'s `write` to `fd` with the reply `r`, from the memory `m`. -/
def writeEvent (L : ShimLayout) (m : Mem) (fd : UInt64) (pointer length : UInt32)
    (r : Linux.Reply) : Linux.Event :=
  ⟨Linux.writeCall, [fd, L.base + pointer.toUInt64, length.toUInt64],
    [m.readBytes pointer.toNat length.toNat], [], r.ret, []⟩

theorem step_read (L : ShimLayout) (m : Mem) (pointer capacity : UInt32) (r : Linux.Reply)
    (fits : pointer.toNat + capacity.toNat ≤ m.pages * 65536) :
    Linux.step (shimMemory L) m (readRequest L pointer capacity) r =
      some (m.writeBytes pointer.toNat ((List.range capacity.toNat).map r.bytes),
        readEvent L m pointer capacity r) := by
  have hp := pointer.toNat_lt
  have hc := capacity.toNat_lt
  have regions := Linux.regions_read (shimMemory L) m 0 (L.base + pointer.toUInt64)
    capacity.toUInt64
  have hmap : (shimMemory L).mapped m (L.base + pointer.toUInt64) capacity.toNat = true := by
    simp only [shimMemory, offset_base, UInt32.toNat_toUInt64, decide_eq_true_eq]
    exact fits
  have hw := shim_writeBytes L ((List.range capacity.toNat).map r.bytes) m pointer.toUInt64
    (by simp only [UInt32.toNat_toUInt64, List.length_map, List.length_range]; omega)
  have hr := shim_readBytes L m pointer.toUInt64 capacity.toNat
    (by simp only [UInt32.toNat_toUInt64]; omega)
  simp only [UInt32.toNat_toUInt64] at hw hr
  simp only [Linux.step, readRequest, regions.1, regions.2, List.all_nil, List.all_cons,
    UInt32.toNat_toUInt64, hmap, Bool.and_true, ↓reduceIte, List.map_nil, hw, readEvent,
    hr]

theorem step_write (L : ShimLayout) (m : Mem) (fd : UInt64) (pointer length : UInt32)
    (r : Linux.Reply) (fits : pointer.toNat + length.toNat ≤ m.pages * 65536) :
    Linux.step (shimMemory L) m (writeRequest L fd pointer length) r =
      some (m, writeEvent L m fd pointer length r) := by
  have hp := pointer.toNat_lt
  have hc := length.toNat_lt
  have regions := Linux.regions_write (shimMemory L) m fd (L.base + pointer.toUInt64)
    length.toUInt64
  have hmap : (shimMemory L).mapped m (L.base + pointer.toUInt64) length.toNat = true := by
    simp only [shimMemory, offset_base, UInt32.toNat_toUInt64, decide_eq_true_eq]
    exact fits
  have hr := shim_readBytes L m pointer.toUInt64 length.toNat
    (by simp only [UInt32.toNat_toUInt64]; omega)
  simp only [UInt32.toNat_toUInt64] at hr
  simp only [Linux.step, writeRequest, regions.1, regions.2, List.all_nil, List.all_cons,
    UInt32.toNat_toUInt64, hmap, Bool.and_true, ↓reduceIte, List.map_cons,
    List.map_nil, hr, writeEvent]

end Verified.Shim
