module

public import LeanExe.Linux.CallTable
public import Verified.Wasi.HostMemory

@[expose] public section

/-!
The guest's linear memory and the shim's scratch as the Linux call layer sees them.  `ShimLayout`
holds the address of the guest's byte 0 in the process and the addresses of the scratch's
timespec, `open_how` record, path buffer, and `statx` record.  `shimMemory` reads and writes the
byte at `base + g` as the guest's byte `g`, with a region accessible when it lies below the
memory's size.  `shimMemory` meets the layer's laws, its byte strings are the Talos memory's, and
`step_read`, `step_write`, and `step_random` evaluate the layer's rule for the requests of `read`,
`write`, and `getrandom` on a guest buffer.  The requests of `clock_gettime`, `openat2`, and
`statx` name only the scratch, which lies outside the Talos store: `step_clock`, `step_openat2`,
and `step_statx` state that every memory that holds the bytes that the stub writes there before
the call, zeros in the timespec, the path with its terminating zero and the record, and the empty
path and zeros in the `statx` record, gives the events `clockEvent`, `openEvent`, and
`statxEvent`, and `step_close` gives `closeEvent` for every memory.
-/

namespace Verified.Shim

open Wasm LeanExe

/-- The addresses that the shim's requests carry: `base`, the address of the guest's byte 0, and
the addresses of the scratch's 16-byte timespec, its 24-byte `open_how` record, its path buffer
of 4,096 bytes, and its 256-byte record of `statx`. -/
structure ShimLayout where
  base : UInt64
  timespec : UInt64
  openHow : UInt64
  path : UInt64
  statx : UInt64

/-- The guest's address of the process address `a`: `a - base`, modulo 2^64. -/
def ShimLayout.offset (L : ShimLayout) (a : UInt64) : Nat := (a - L.base).toNat

/-- The guest's linear memory as process memory: the byte at `base + g` is the guest's byte `g`,
and the `n` bytes from an address are accessible when they lie below the memory's size. -/
def shimMemory (L : ShimLayout) : Linux.Memory Mem where
  read m a := m.bytes (L.offset a)
  write m a v := { m with bytes := fun i => if i = L.offset a then v else m.bytes i }
  mapped m a n := decide (L.offset a + n ≤ m.pages * 65536)

/-- The request of `fd_read`: a `read` of `fd` into the guest's buffer. -/
def readRequest (L : ShimLayout) (fd : UInt64) (pointer capacity : UInt32) : Linux.Request :=
  ⟨Linux.readCall, [fd, L.base + pointer.toUInt64, capacity.toUInt64]⟩

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

/-- The event of `fd_read`'s `read` of `fd` with the reply `r`, from the memory `m`. -/
def readEvent (L : ShimLayout) (m : Mem) (fd : UInt64) (pointer capacity : UInt32)
    (r : Linux.Reply) : Linux.Event :=
  ⟨Linux.readCall, [fd, L.base + pointer.toUInt64, capacity.toUInt64], [],
    m.readBytes pointer.toNat capacity.toNat, r.ret, (List.range capacity.toNat).map r.bytes⟩

/-- The event of `fd_write`'s `write` to `fd` with the reply `r`, from the memory `m`. -/
def writeEvent (L : ShimLayout) (m : Mem) (fd : UInt64) (pointer length : UInt32)
    (r : Linux.Reply) : Linux.Event :=
  ⟨Linux.writeCall, [fd, L.base + pointer.toUInt64, length.toUInt64],
    [m.readBytes pointer.toNat length.toNat], [], r.ret, []⟩

theorem step_read (L : ShimLayout) (m : Mem) (fd : UInt64) (pointer capacity : UInt32)
    (r : Linux.Reply) (fits : pointer.toNat + capacity.toNat ≤ m.pages * 65536) :
    Linux.step (shimMemory L) m (readRequest L fd pointer capacity) r =
      some (m.writeBytes pointer.toNat ((List.range capacity.toNat).map r.bytes),
        readEvent L m fd pointer capacity r) := by
  have hp := pointer.toNat_lt
  have hc := capacity.toNat_lt
  have regions := Linux.regions_read (shimMemory L) m fd (L.base + pointer.toUInt64)
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

/-- The request of one `getrandom` of `random_get`'s loop: `n` bytes into the guest's memory from
its byte `o`, with no flags. -/
def randomRequest (L : ShimLayout) (o : UInt64) (n : Nat) : Linux.Request :=
  ⟨Linux.getrandomCall, [L.base + o, UInt64.ofNat n, 0]⟩

/-- The event of `randomRequest L o n` with the reply `r`, from the memory `m`. -/
def randomEvent (L : ShimLayout) (m : Mem) (o : UInt64) (n : Nat) (r : Linux.Reply) :
    Linux.Event :=
  ⟨Linux.getrandomCall, [L.base + o, UInt64.ofNat n, 0], [], m.readBytes o.toNat n, r.ret,
    (List.range n).map r.bytes⟩

theorem step_random (L : ShimLayout) (m : Mem) (o : UInt64) (n : Nat) (r : Linux.Reply)
    (fits : o.toNat + n ≤ m.pages * 65536) (address : o.toNat + n ≤ 2 ^ 32) :
    Linux.step (shimMemory L) m (randomRequest L o n) r =
      some (m.writeBytes o.toNat ((List.range n).map r.bytes), randomEvent L m o n r) := by
  have small : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (show n < 2 ^ 64 by omega)
  have regions := Linux.regions_getrandom (shimMemory L) m (L.base + o) (UInt64.ofNat n) 0
  have hmap : (shimMemory L).mapped m (L.base + o) n = true := by
    simp only [shimMemory, offset_base, decide_eq_true_eq]
    exact fits
  have hw := shim_writeBytes L ((List.range n).map r.bytes) m o
    (by simp only [List.length_map, List.length_range]; omega)
  have hr := shim_readBytes L m o n (by omega)
  simp only [Linux.step, randomRequest, regions.1, regions.2, List.all_nil, List.all_cons,
    small, hmap, Bool.and_true, ↓reduceIte, List.map_nil, hw, randomEvent, hr]

/-- The event of `clock_gettime` of the clock `id` into the scratch's timespec, which the stub
clears before the call, with the reply `r`. -/
def clockEvent (L : ShimLayout) (id : UInt64) (r : Linux.Reply) : Linux.Event :=
  ⟨Linux.clockGettimeCall, [id, L.timespec], [], List.replicate 16 0, r.ret,
    (List.range 16).map r.bytes⟩

/-- Every memory whose timespec is accessible and holds zeros gives `clockEvent`. -/
theorem step_clock {M : Type} (I : Linux.Memory M) (m : M) (L : ShimLayout) (id : UInt64)
    (r : Linux.Reply) (mapped : I.mapped m L.timespec 16 = true)
    (cleared : I.readBytes m L.timespec 16 = List.replicate 16 0) :
    Linux.step I m ⟨Linux.clockGettimeCall, [id, L.timespec]⟩ r =
      some (I.writeBytes m L.timespec ((List.range 16).map r.bytes), clockEvent L id r) := by
  have regions := Linux.regions_clockGettime I m id L.timespec
  simp only [Linux.step, regions.1, regions.2, List.all_nil, List.all_cons, mapped,
    Bool.and_true, ↓reduceIte, List.map_nil, cleared, clockEvent]

/-- The event of `openat2` under the directory `dir` of the path `path`, which the scratch's path
buffer holds with its terminating zero, with the record `how` in the scratch's `open_how`, and
the reply `r`. -/
def openEvent (L : ShimLayout) (dir : UInt64) (path how : List UInt8) (r : Linux.Reply) :
    Linux.Event :=
  ⟨Linux.openat2Call, [dir, L.path, L.openHow, 24], [path ++ [0], how], [], r.ret, []⟩

/-- Every memory that holds a path of fewer than 4,096 bytes, none of them zero, with its
terminating zero at the path buffer and the record `how` at `open_how`, both accessible, gives
`openEvent` and keeps its bytes. -/
theorem step_openat2 {M : Type} (I : Linux.Memory M) (m : M) (L : ShimLayout) (dir : UInt64)
    (path how : List UInt8) (r : Linux.Reply) (short : path.length < 4096) (nonzero : 0 ∉ path)
    (named : I.readBytes m L.path (path.length + 1) = path ++ [0])
    (record : I.readBytes m L.openHow 24 = how)
    (mappedPath : I.mapped m L.path (path.length + 1) = true)
    (mappedHow : I.mapped m L.openHow 24 = true) :
    Linux.step I m ⟨Linux.openat2Call, [dir, L.path, L.openHow, 24]⟩ r =
      some (m, openEvent L dir path how r) := by
  have byte : ∀ i < path.length + 1,
      some (I.read m (L.path + UInt64.ofNat i)) = (path ++ [0])[i]? := by
    intro i hi
    rw [← named, readBytes_eq_map, List.getElem?_map, List.getElem?_range hi]
    rfl
  have length : I.pathLength m L.path = path.length + 1 := by
    refine Linux.Memory.pathLength_eq I m L.path short ?_ ?_
    · have last := byte path.length (by omega)
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at last
      simpa using last
    · intro i hi same
      have inner := byte i (by omega)
      rw [List.getElem?_append_left hi, same, List.getElem?_eq_getElem hi] at inner
      exact nonzero (by rw [Option.some.inj inner]; exact List.getElem_mem hi)
  have regions := Linux.regions_openat2 I m dir L.path L.openHow 24
  simp only [Linux.step, regions.1, regions.2, length, List.all_nil, List.all_cons, mappedPath,
    mappedHow, UInt64.reduceToNat, Bool.and_true, ↓reduceIte, List.map_cons,
    List.map_nil, named, record, openEvent]

/-- The flags of the `statx` of `fd_filestat_get`, `AT_EMPTY_PATH` (`0x1000`), with which the
empty path names the descriptor itself. -/
def statxFlags : UInt64 := 0x1000

/-- The mask of the `statx` of `fd_filestat_get`, `STATX_BASIC_STATS | STATX_BTIME` (`0xFFF`), the
mask of Rust's `File::metadata`, through which Wasmtime 44 reads a file's metadata. -/
def statxMask : UInt64 := 0xFFF

/-- The event of `statx` of the descriptor `fd` with the empty path, which the scratch's path
buffer holds as its terminating zero, into the scratch's `statx` record, which the stub clears
before the call, with the reply `r`. -/
def statxEvent (L : ShimLayout) (fd : UInt64) (r : Linux.Reply) : Linux.Event :=
  ⟨Linux.statxCall, [fd, L.path, statxFlags, statxMask, L.statx], [[0]], List.replicate 256 0,
    r.ret, (List.range 256).map r.bytes⟩

/-- Every memory whose path buffer starts with a zero byte and whose `statx` record is accessible
and holds zeros gives `statxEvent`. -/
theorem step_statx {M : Type} (I : Linux.Memory M) (m : M) (L : ShimLayout) (fd : UInt64)
    (r : Linux.Reply) (empty : I.read m L.path = 0) (mappedPath : I.mapped m L.path 1 = true)
    (mapped : I.mapped m L.statx 256 = true)
    (cleared : I.readBytes m L.statx 256 = List.replicate 256 0) :
    Linux.step I m ⟨Linux.statxCall, [fd, L.path, statxFlags, statxMask, L.statx]⟩ r =
      some (I.writeBytes m L.statx ((List.range 256).map r.bytes), statxEvent L fd r) := by
  have length : I.pathLength m L.path = 1 :=
    Linux.Memory.pathLength_eq I m L.path (n := 0) (by decide)
      (by rw [show L.path + UInt64.ofNat 0 = L.path by simp]; exact empty)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
  have named : I.readBytes m L.path 1 = [0] := by
    show [I.read m L.path] = [0]
    rw [empty]
  have regions := Linux.regions_statx I m fd L.path statxFlags statxMask L.statx
  simp only [Linux.step, regions.1, regions.2, length, List.all_nil, List.all_cons, mappedPath,
    mapped, Bool.and_true, ↓reduceIte, List.map_cons, List.map_nil, named, cleared, statxEvent]

/-- The event of `close` of `fd` with the reply `r`. -/
def closeEvent (fd : UInt64) (r : Linux.Reply) : Linux.Event :=
  ⟨Linux.closeCall, [fd], [], [], r.ret, []⟩

theorem step_close {M : Type} (I : Linux.Memory M) (m : M) (fd : UInt64) (r : Linux.Reply) :
    Linux.step I m ⟨Linux.closeCall, [fd]⟩ r = some (m, closeEvent fd r) := by
  have regions := Linux.regions_close I m fd
  simp only [Linux.step, regions.1, regions.2, List.all_nil, Bool.and_self, ↓reduceIte,
    List.map_nil, closeEvent]

end Verified.Shim
