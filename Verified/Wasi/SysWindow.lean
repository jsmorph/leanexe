import Verified.Wasi.SysIovecCall
import Verified.AlignedTailLoop
import Verified.Wasi.ReadAllBuffer
import LeanExe.Wasi.Window

/-! The window of a buffer that a `sys` command fills or writes.  The code computes the window's
first position and length in words, which agree with `Bytes.window` for a buffer whose size lies
below `2^64`, and its address, the root plus the first position, which lies below `2^32` since the
buffer does.  A fill leaves the buffer's block in place: the host writes only the scratch bytes and
the window, so the buffer keeps its header and the bytes outside the window, and the window holds
the bytes that the host wrote, or after an errno the zeros that the code stores. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## The window in words -/

/-- The count, or the capacity when the count is at least the capacity. -/
def readLength (count capacity : UInt64) : UInt64 := if capacity ≤ count then capacity else count

theorem readLength_toNat (count capacity : UInt64) :
    (readLength count capacity).toNat = min count.toNat capacity.toNat := by
  unfold readLength
  split
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    omega
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    omega

theorem readLength_eq_min (count capacity : UInt64) : readLength count capacity = min count capacity :=
  UInt64.toNat_inj.mp (by
    rw [readLength_toNat, UInt64.toNat_min])

/-- The code of the minimum leaves `readLength` of the count and the capacity. -/
theorem wp_min_code {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {countLocal capacityLocal : Nat} {count capacity : UInt64} {rest : Program}
    {Q : Assertion α}
    (hCount : s.get countLocal = some (.i64 count))
    (hCapacity : s.get capacityLocal = some (.i64 capacity))
    (h : wp m rest Q st { s with values := .i64 (readLength count capacity) :: s.values } env) :
    wp m (minCode countLocal capacityLocal ++ rest) Q st s env := by
  simp only [minCode, List.cons_append, List.nil_append, wp_localGet_cons, hCount,
    Locals.get_values, hCapacity, wp_geUI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hLarge : capacity ≤ count
  · rw [ite_eq_left (by simp [hLarge])]
    simp only [wp_localGet_cons, hCapacity, wp_nil, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append, List.drop_zero]
    simpa only [readLength, hLarge, ite_true] using h
  · rw [ite_eq_right (by simp [hLarge])]
    simp only [wp_localGet_cons, hCount, wp_nil, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append, List.drop_zero]
    simpa only [readLength, hLarge, ite_false] using h

/-- The first position of a window as the code computes it: the start, or the size when that is
smaller. -/
def windowFirstWord (size start : UInt64) : UInt64 := readLength start size

/-- The length of a window as the code computes it: the count, or the bytes from the first
position on when they are fewer. -/
def windowLengthWord (size start count : UInt64) : UInt64 :=
  readLength count (size - windowFirstWord size start)

theorem window_words {bytes : LeanExe.Bytes} {size : UInt64}
    (hSize : size.toNat = bytes.data.size) (start count : UInt64) :
    (windowFirstWord size start).toNat = (bytes.window start count).1 ∧
      (windowLengthWord size start count).toNat = (bytes.window start count).2 ∧
      windowLengthWord size start count = bytes.windowLength start count := by
  have hFirst : (windowFirstWord size start).toNat = min start.toNat size.toNat :=
    readLength_toNat start size
  have hLe : windowFirstWord size start ≤ size := by
    rw [UInt64.le_iff_toNat_le]
    omega
  have hRest : (size - windowFirstWord size start).toNat =
      size.toNat - (windowFirstWord size start).toNat := UInt64.toNat_sub_of_le _ _ hLe
  have hLength : (windowLengthWord size start count).toNat =
      min count.toNat (size - windowFirstWord size start).toNat :=
    readLength_toNat count _
  have hFirst' : (windowFirstWord size start).toNat = (bytes.window start count).1 := by
    rw [hFirst, LeanExe.Bytes.window_fst, hSize]
  have hLength' : (windowLengthWord size start count).toNat = (bytes.window start count).2 := by
    rw [hLength, LeanExe.Bytes.window_snd, hRest, hFirst, hSize]
  refine ⟨hFirst', hLength', ?_⟩
  apply UInt64.toNat_inj.mp
  rw [hLength', LeanExe.Bytes.windowLength_toNat]

/-- Leaves in `target` the window's address and in `target + 1` its length. -/
theorem wp_window_code {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {root start count target : Nat} {rootWord size startWord countWord : UInt64}
    {rest : Program} {Q : Assertion α}
    (hRoot : s.get root = some (.i64 rootWord)) (hSize : s.get (root + 1) = some (.i64 size))
    (hStart : s.get start = some (.i64 startWord)) (hCount : s.get count = some (.i64 countWord))
    (hRootBelow : root + 1 < target) (hCountBelow : count < target)
    (hLow : s.params.length ≤ target) (hHigh : target + 1 < s.params.length + s.locals.length)
    (h : ∀ s' : Locals, LocalsOutside s s' target 2 → s'.values = s.values →
      s'.get target = some (.i64 (rootWord + windowFirstWord size startWord)) →
      s'.get (target + 1) = some (.i64 (windowLengthWord size startWord countWord)) →
      wp m rest Q st s' env) :
    wp m (windowCode root start count target ++ rest) Q st s env := by
  simp only [windowCode, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_min_code hStart hSize ?_
  refine wp_localSet_local hLow (by omega) ?_
  let s1 := setLocal { s with values := s.values } target (.i64 (windowFirstWord size startWord))
  have outside1 : LocalsOutside s s1 target 2 :=
    ((LocalsOutside.refl s target 2).values s.values).set hLow le_rfl (by omega)
  have get1 : s1.get target = some (.i64 (windowFirstWord size startWord)) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) hLow (by omega)
  have size1 : s1.get (root + 1) = some (.i64 size) := by
    rw [outside1.others _ (by omega)]
    exact hSize
  change wp m (.localGet (root + 1) :: .localGet target :: .subI64 :: .localSet (target + 1) ::
    _) Q st s1 env
  refine wp_localGet_get size1 ?_
  refine wp_localGet_get (by rw [Locals.get_values]; exact get1) ?_
  simp only [wp_subI64_cons]
  refine wp_localSet_local (by rw [outside1.params]; omega)
    (by rw [outside1.params, outside1.length]; omega) ?_
  let s2 := setLocal { s1 with values := s.values } (target + 1)
    (.i64 (size - windowFirstWord size startWord))
  have outside2 : LocalsOutside s s2 target 2 :=
    (outside1.values s.values).set hLow (by omega) (by omega)
  have get2 : s2.get (target + 1) = some (.i64 (size - windowFirstWord size startWord)) :=
    Locals.get_setLocal_same (s := { s1 with values := s.values })
      (by rw [outside1.params]; omega) (by rw [outside1.params, outside1.length]; omega)
  have count2 : s2.get count = some (.i64 countWord) := by
    rw [outside2.others _ (by omega)]
    exact hCount
  change wp m (minCode count (target + 1) ++ .localSet (target + 1) :: .localGet root ::
    .localGet target :: .addI64 :: .localSet target :: rest) Q st s2 env
  refine wp_min_code count2 get2 ?_
  refine wp_localSet_local (by rw [outside2.params]; omega)
    (by rw [outside2.params, outside2.length]; omega) ?_
  let s3 := setLocal { s2 with values := s.values } (target + 1)
    (.i64 (windowLengthWord size startWord countWord))
  have outside3 : LocalsOutside s s3 target 2 :=
    (outside2.values s.values).set hLow (by omega) (by omega)
  have get3 : s3.get (target + 1) = some (.i64 (windowLengthWord size startWord countWord)) :=
    Locals.get_setLocal_same (s := { s2 with values := s.values })
      (by rw [outside2.params]; omega) (by rw [outside2.params, outside2.length]; omega)
  have first3 : s3.get target = some (.i64 (windowFirstWord size startWord)) := by
    rw [Locals.get_setLocal_ne (s := { s2 with values := s.values })
      (by rw [outside2.params]; omega) (by omega), Locals.get_values,
      Locals.get_setLocal_ne (s := { s1 with values := s.values })
      (by rw [outside1.params]; omega) (by omega), Locals.get_values]
    exact get1
  have root3 : s3.get root = some (.i64 rootWord) := by
    rw [outside3.others _ (by omega)]
    exact hRoot
  refine wp_localGet_get root3 ?_
  refine wp_localGet_get (by rw [Locals.get_values]; exact first3) ?_
  simp only [wp_addI64_cons]
  have b3 := outside3.bounds hLow (by omega) (show target ≤ target by omega) (by omega)
  refine wp_localSet_local b3.1 b3.2 ?_
  let s4 := setLocal { s3 with values := s.values } target
    (.i64 (rootWord + windowFirstWord size startWord))
  refine h s4 ((outside3.values s.values).set hLow le_rfl (by omega)) rfl
    (Locals.get_setLocal_same (s := { s3 with values := s.values })
      b3.1 b3.2) ?_
  rw [Locals.get_setLocal_ne (s := { s3 with values := s.values })
    b3.1 (by omega), Locals.get_values]
  exact get3

/-! ## The window of a represented buffer -/

/-- The window of a buffer that its representation places at `root`: its address and length in
words, their sum below `2^32` and within memory, and an address of at least 16 for a nonempty
window. -/
structure WindowAt (heap : Heap) (store : Store Unit) (root size : UInt64)
    (buffer : LeanExe.Bytes) (start count : UInt64) (address length : UInt64) : Prop where
  address_eq : address = root + windowFirstWord size start
  length_eq : length = buffer.windowLength start count
  address_toNat : address.toNat = root.toNat + (buffer.window start count).1
  length_toNat : length.toNat = (buffer.window start count).2
  fits : address.toNat + length.toNat < 4294967296
  memory : address.toNat + length.toNat ≤ store.mem.pages * 65536
  separate : 16 ≤ address.toNat ∨ (length = 0 ∧ address = 0)

theorem window_at {heap : Heap} {store : Store Unit} {root size : UInt64} {buffer : LeanExe.Bytes}
    (rep : Bytes.Rep heap store root size buffer) (hHeap : heap.At store) (start count : UInt64) :
    WindowAt heap store root size buffer start count (root + windowFirstWord size start)
      (windowLengthWord size start count) := by
  obtain ⟨hFirst, hLength, hEq⟩ := window_words rep.length_eq start count
  have hWindow := buffer.window_le start count
  have hAt := rep.toAt hHeap
  have hAddress : (root + windowFirstWord size start).toNat =
      root.toNat + (buffer.window start count).1 := by
    rw [UInt64.toNat_add, hFirst]
    exact Nat.mod_eq_of_lt (by have := hAt.address; omega)
  refine ⟨rfl, hEq, hAddress, hLength, ?_, ?_, ?_⟩
  · rcases rep.buffer with ⟨hRoot0, hEmpty⟩ | hBuffer
    · rw [hAddress, hLength, hRoot0]
      simp only [UInt64.toNat_zero]
      omega
    · have := hBuffer.object.address
      have := hBuffer.capacity
      rw [hAddress, hLength]
      omega
  · rw [hAddress, hLength]
    have := hAt.memory
    omega
  · rcases rep.buffer with ⟨hRoot0, hEmpty⟩ | hBuffer
    · right
      have hZero : (buffer.window start count).1 = 0 ∧ (buffer.window start count).2 = 0 := by
        omega
      refine ⟨UInt64.toNat_inj.mp (by rw [hLength, hZero.2]; rfl), ?_⟩
      exact UInt64.toNat_inj.mp (by rw [hAddress, hZero.1, hRoot0]; rfl)
    · left
      have := hBuffer.object.base
      rw [hAddress]
      omega

/-- The bytes of a window of a buffer in memory lie at the window's address. -/
theorem bytes_at_window {mem : Mem} {root address : UInt64} {buffer : LeanExe.Bytes}
    {start count : UInt64} (h : Bytes.At mem root buffer)
    (hAddress : address.toNat = root.toNat + (buffer.window start count).1) :
    Bytes.At mem address (buffer.range start count) := by
  have hWindow := buffer.window_le start count
  have hAddress' := h.address
  have hMemory := h.memory
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [LeanExe.Bytes.range_size, hAddress]
    omega
  · rw [LeanExe.Bytes.range_size, hAddress]
    omega
  · rw [LeanExe.Bytes.range_get, hAddress, Nat.add_assoc]
    exact h.contents _ _

/-! ## The buffer after a fill -/

/-- A buffer holds `buffer` with the bytes from `first` replaced by `out` after a frame that
writes only the scratch bytes and those positions, which then hold `out`. -/
theorem window_splice_buffer {World : Type} {before after : Store World} {heap : Heap}
    {root : UInt64} {buffer out : LeanExe.Bytes} {first : Nat}
    (h : Heap.Buffer heap (PureTransport.erase before) root buffer)
    (hHeap : heap.At (PureTransport.erase before))
    (hWindow : first + out.data.size ≤ buffer.data.size)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat + first, out.data.size)])
    (hData : ∀ (i : Nat) (hi : i < out.data.size),
      after.mem.bytes (root.toNat + first + i) = out.data[i]) :
    Heap.Buffer heap (PureTransport.erase after) root (buffer.splice first out) := by
  have hBase := h.object.base
  have hFit := h.object.address
  have hCapacity := h.capacity
  have hSize := LeanExe.Bytes.splice_size hWindow
  have wide := hFrame.widen (outer := (root.toNat, capacityAt (PureTransport.erase before) root))
    (by dsimp only; omega) (by dsimp only; omega)
  refine allocated_afterRead h wide (by rw [hSize]; exact hCapacity) ⟨?_, ?_, ?_⟩
  · rw [hSize]
    omega
  · rw [hSize, hFrame.pages]
    exact (h.toAt hHeap).memory
  · intro i hi
    rw [hSize] at hi
    by_cases hLeft : i < first
    · rw [LeanExe.Bytes.splice_get_before hWindow hLeft]
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
      exact h.contents i _
    · by_cases hInside : i < first + out.data.size
      · rw [LeanExe.Bytes.splice_get_inside hWindow (by omega) hInside]
        have := hData (i - first) (by omega)
        rw [show root.toNat + first + (i - first) = root.toNat + i by omega] at this
        exact this
      · rw [LeanExe.Bytes.splice_get_after hWindow (by omega) hi]
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
        exact h.contents i hi

/-- A step whose kept regions lie apart from the blocks `fresh` names them fresh. -/
theorem step_withFresh {heap heap' : Heap} {store store' : Store Unit} {keep : Nat × Nat → Prop}
    {fresh : List (Nat × Nat)} (h : Step heap store keep heap' store' [])
    (hApart : ∀ r, keep r → ∀ b ∈ fresh, regionsDisjoint r b) :
    Step heap store keep heap' store' fresh :=
  ⟨h.at_, h.caps, fun r hr hpos hk => by
    obtain ⟨hBytes, hRegion, _⟩ := h.keeps r hr hpos hk
    exact ⟨hBytes, hRegion, hApart r hk⟩⟩

/-- A frame that writes the scratch bytes and a window of a buffer is a step that keeps the
regions apart from the low memory and from the buffer's block, and whose fresh block is the
buffer's. -/
theorem window_step {World : Type} {before after : Store World} {heap : Heap}
    {root size : UInt64} {buffer : LeanExe.Bytes} {first length : Nat}
    (rep : Bytes.Rep heap (PureTransport.erase before) root size buffer)
    (hHeap : heap.At (PureTransport.erase before))
    (hWindow : first + length ≤ buffer.data.size)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat + first, length)]) :
    Step heap (PureTransport.erase before)
      (fun r => regionsDisjoint r ABI.low ∧
        ∀ b ∈ Bytes.regions (PureTransport.erase before) root, regionsDisjoint r b)
      heap (PureTransport.erase after) (Bytes.regions (PureTransport.erase after) root) := by
  rcases rep.buffer with ⟨rfl, hEmpty⟩ | hBuffer
  · have hZero : GuestFrame before after [ABI.scratch, (0, 0)] := by
      have h0 : first = 0 ∧ length = 0 := by omega
      obtain ⟨rfl, rfl⟩ := h0
      simpa using hFrame
    simpa only [Bytes.regions, ite_true] using
      ((read_zero_frame hZero).scratchStep hHeap).mono (fun _ kept => kept.1) (fun _ h => h)
  · have hCapacity := hBuffer.capacity
    have wide := hFrame.widen
      (outer := (root.toNat, capacityAt (PureTransport.erase before) root))
      (by dsimp only; omega) (by dsimp only; omega)
    have hRead := wide.readStep hHeap (read_payload_region hBuffer le_rfl)
    have hSame := read_capacity hBuffer wide
    have hNonzero := hBuffer.nonzero
    simp only [Bytes.regions, ite_eq_right hNonzero, List.mem_singleton, forall_eq,
      block_eq hSame]
    refine step_withFresh (hRead.mono (fun r kept => ⟨kept.1, ?_⟩) (fun _ h => h)) ?_
    · have hBlock := kept.2
      have hBase := hBuffer.object.base
      simp only [block, LeanExe.Runtime.regionsDisjoint] at hBlock ⊢
      omega
    · intro r kept b member
      rw [List.mem_singleton] at member
      subst member
      exact kept.2

/-- Stores 0 into the `count` bytes from `address`, with the index in local `index`. -/
theorem wp_zero_code {World : Type} {m : Module} {env : HostEnv World} {st : Store World}
    {s : Locals} {pointer length index : Nat} {address count : UInt64} {rest : Program}
    {Q : Assertion World}
    (hPointer : s.get pointer = some (.i64 address)) (hLength : s.get length = some (.i64 count))
    (hPointerIndex : pointer ≠ index) (hLengthIndex : length ≠ index)
    (hLow : s.params.length ≤ index) (hHigh : index < s.params.length + s.locals.length)
    (hFit : address.toNat + count.toNat < 4294967296)
    (hMemory : address.toNat + count.toNat ≤ st.mem.pages * 65536)
    (h : ∀ final : Store World, ∀ s' : Locals,
      Memory.WritesRange st final address.toNat (address.toNat + count.toNat) →
      (∀ i, i < count.toNat → final.mem.bytes (address.toNat + i) = 0) →
      LocalsOutside s s' index 1 → s'.values = s.values →
      wp m rest Q final s' env) :
    wp m (zeroCode pointer length index ++ rest) Q st s env := by
  let Inv : Nat → AssertionF World := fun k store frame =>
    k ≤ count.toNat ∧ LocalsOutside s frame index 1 ∧ frame.values = s.values ∧
      frame.get index = some (.i64 (UInt64.ofNat k)) ∧
      Memory.WritesRange st store address.toNat (address.toNat + count.toNat) ∧
      ∀ i, i < k → store.mem.bytes (address.toNat + i) = 0
  simp only [zeroCode, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_localSet_local hLow hHigh ?_
  let s0 := setLocal { s with values := s.values } index (.i64 0)
  have outside0 : LocalsOutside s s0 index 1 :=
    ((LocalsOutside.refl s index 1).values s.values).set hLow le_rfl (by omega)
  have init : Inv 0 st s0 :=
    ⟨Nat.zero_le _, outside0, rfl,
      Locals.get_setLocal_same (s := { s with values := s.values }) hLow hHigh,
      Memory.WritesRange.refl st _ _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  apply wp_block_cons
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  refine Tail.wp_loop_indexed (Inv := Inv) (rank := fun k => count.toNat - k) init ?_
  intro k store frame inv
  obtain ⟨hk, outside, values, hIndex, writes, zeros⟩ := inv
  have pointerF : frame.get pointer = some (.i64 address) := by
    rw [outside.others _ (by omega)]
    exact hPointer
  have lengthF : frame.get length = some (.i64 count) := by
    rw [outside.others _ (by omega)]
    exact hLength
  have hk64 : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, hIndex, Locals.get_values, lengthF, wp_geUI64_cons,
    wp_br_if_cons]
  by_cases hDone : k = count.toNat
  · have hGe : UInt64.ofNat k ≥ count := by
      rw [GE.ge, UInt64.le_iff_toNat_le, hk64]
      omega
    simp only [hGe, ite_true]
    simp only [List.take_zero, List.nil_append, List.drop_zero, wp_nil]
    refine h store { frame with values := s.values } writes (fun i hi => zeros i (by omega))
      (outside.values s.values) rfl
  · have hLt : ¬ (UInt64.ofNat k ≥ count) := by
      rw [GE.ge, UInt64.le_iff_toNat_le, hk64]
      omega
    simp only [hLt, ite_false]
    simp only [wp_localGet_cons, Locals.get_values, pointerF, hIndex, wp_addI64_cons,
      wp_wrapI64_cons, wp_const_cons, wp_store8_cons]
    have hAddress : (address + UInt64.ofNat k).toNat = address.toNat + k := by
      rw [UInt64.toNat_add, hk64]
      exact Nat.mod_eq_of_lt (by omega)
    have hWrap : (UInt32.ofNat ((address + UInt64.ofNat k).toNat % 2 ^ 32)).toNat =
        address.toNat + k := by
      rw [hAddress, Nat.mod_eq_of_lt (by omega)]
      exact UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega)
    have hPages : store.mem.pages = st.mem.pages := writes.2.1
    rw [ite_eq_right (by
      simp only [UInt32.toNat_zero, Nat.add_zero, gt_iff_lt, not_lt, hWrap, hPages]
      omega)]
    simp only [wp_localGet_cons, Locals.get_values, hIndex, wp_constI64_cons, wp_addI64_cons]
    have hLowF : frame.params.length ≤ index := by rw [outside.params]; exact hLow
    have hHighF : index < frame.params.length + frame.locals.length := by
      rw [outside.params, outside.length]; exact hHigh
    refine wp_localSet_local (s := frame) (vs := frame.values) hLowF hHighF ?_
    rw [wp_br_cons]
    have hSlot : (UInt32.ofNat ((address + UInt64.ofNat k).toNat % 2 ^ 32) + 0).toNat =
        address.toNat + k := by
      rw [UInt32.add_zero, hWrap]
    refine ⟨k + 1, ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
    · exact ((outside.values frame.values).set hLow le_rfl (by omega)).values _
    · simp only [List.take_zero, List.nil_append, List.drop_zero]
      exact values
    · rw [Locals.get_values, Locals.get_setLocal_same (s := { frame with values := frame.values })
        hLowF hHighF]
      congr 2
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, hk64,
        UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
      simp only [UInt64.reduceToNat]
      omega
    · exact writes.trans (Memory.WritesRange.write8 store _ _ _ _ (by rw [hSlot]; omega)
        (by rw [hSlot]; omega))
    · intro i hi
      by_cases hLast : i = k
      · subst hLast
        simp only [Mem.write8, hSlot, ite_true]
        rfl
      · have hOther : address.toNat + i ≠
            (UInt32.ofNat ((address + UInt64.ofNat k).toNat % 2 ^ 32) + 0).toNat := by
          rw [hSlot]
          omega
        simp only [Mem.write8, hOther, ite_false]
        exact zeros i (by omega)

/-- The end of a fill: after an errno the zero fill of the window, and the pushes of the errno,
the count, and the buffer's root and size. -/
theorem wp_fill_tail {World : Type} {m : Module} {env : HostEnv World} {st : Store World}
    {s : Locals} {root base : Nat} {errno address length count rootWord size : UInt64}
    {rest : Program} {Q : Assertion World}
    (hErrno : s.get base = some (.i64 errno)) (hAddress : s.get (base + 1) = some (.i64 address))
    (hLength : s.get (base + 2) = some (.i64 length))
    (hCount : s.get (base + 3) = some (.i64 count))
    (hRoot : s.get root = some (.i64 rootWord)) (hSize : s.get (root + 1) = some (.i64 size))
    (hRootBelow : root + 1 < base + 4)
    (hLow : s.params.length ≤ base + 4) (hHigh : base + 4 < s.params.length + s.locals.length)
    (hFit : address.toNat + length.toNat < 4294967296)
    (hMemory : address.toNat + length.toNat ≤ st.mem.pages * 65536)
    (h : ∀ final : Store World, ∀ s' : Locals,
      (errno = 0 → final = st) →
      (errno ≠ 0 → Memory.WritesRange st final address.toNat (address.toNat + length.toNat) ∧
        ∀ i, i < length.toNat → final.mem.bytes (address.toNat + i) = 0) →
      LocalsOutside s s' (base + 4) 1 → s'.values = s.values →
      wp m rest Q final { s' with values :=
        [Value.i64 size, .i64 rootWord, .i64 count, .i64 errno] ++ s.values } env) :
    wp m (fillTailCode root base ++ rest) Q st s env := by
  have finish : ∀ (final : Store World) (s' : Locals), LocalsOutside s s' (base + 4) 1 →
      s'.values = s.values → (errno = 0 → final = st) →
      (errno ≠ 0 → Memory.WritesRange st final address.toNat (address.toNat + length.toNat) ∧
        ∀ i, i < length.toNat → final.mem.bytes (address.toNat + i) = 0) →
      wp m ([.localGet base, .localGet (base + 3), .localGet root, .localGet (root + 1)] ++ rest)
        Q final s' env := by
    intro final s' outside values zero nonzero
    have get : ∀ j, (j < base + 4 ∨ base + 4 + 1 ≤ j) → s'.get j = s.get j := fun j hj =>
      outside.others j hj
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get_values,
      get base (by omega), hErrno, get (base + 3) (by omega), hCount, get root (by omega), hRoot,
      get (root + 1) (by omega), hSize]
    have next := h final s' zero nonzero outside values
    rw [values]
    simpa only [List.cons_append, List.nil_append] using next
  simp only [fillTailCode, List.cons_append, List.nil_append, wp_localGet_cons, hErrno,
    wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hZero : errno = 0
  · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
    exact finish st { s with values := s.values } (LocalsOutside.refl s (base + 4) 1) rfl
      (fun _ => rfl) (fun nonzero => absurd hZero nonzero)
  · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
    rw [← List.append_nil (zeroCode (base + 1) (base + 2) (base + 4))]
    refine wp_zero_code (s := { s with values := s.values }) hAddress hLength (by omega)
      (by omega) hLow hHigh hFit hMemory ?_
    intro final s' writes zeros outside values
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
    exact finish final { s' with values := s.values } (outside.values s.values) rfl
      (fun zero => absurd zero hZero) (fun _ => ⟨writes, zeros⟩)

end Verified.Wasi
