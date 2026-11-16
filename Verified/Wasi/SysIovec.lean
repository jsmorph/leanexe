import Verified.Wasi.SysIovecCall
import Verified.Wasi.SysFlat

/-! The code of an iovec call, from the argument test to the result on the stack.  A read tests
the handle and the capacity, allocates the buffer, writes the element, runs the call, and on errno
0 keeps the count, at most the capacity, as the buffer's length, or otherwise releases the buffer;
its result holds the errno and the prefix of the buffer of that length.  A write tests the handle
and the input's length, writes the element of the input, runs the call, and on errno 0 loads the
count; its result holds the errno and the count. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## The prefix of a buffer -/

theorem prefixBytes_empty (errno count : UInt64) :
    (⟨errno, []⟩ : Reply).prefixBytes 0 count = LeanExe.Bytes.empty := by
  have hEmpty : ((⟨errno, []⟩ : Reply).bytes 0).data.extract 0 count.toNat = ByteArray.empty := by
    apply ByteArray.size_eq_zero_iff.mp
    simp [Reply.bytes, LeanExe.Bytes.empty, ByteArray.size_extract]
  simp only [Reply.prefixBytes, hEmpty, LeanExe.Bytes.empty]

theorem prefixBytes_size (buffer count : LeanExe.Bytes) (errno : UInt64) :
    ((⟨errno, [buffer, count]⟩ : Reply).prefixBytes 0 ((⟨errno, [buffer, count]⟩ : Reply).word 1))
      = ⟨buffer.data.extract 0 (littleEndian count).toNat⟩ := rfl

/-- The first `count` bytes of bytes in memory lie at the same root. -/
theorem bytes_at_prefix {mem : Mem} {root : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem root bytes) (count : Nat) :
    Bytes.At mem root ⟨bytes.data.extract 0 count⟩ := by
  have hSize : (bytes.data.extract 0 count).size = min count bytes.data.size := by
    rw [ByteArray.size_extract]; omega
  have hAddress := h.address
  have hMemory := h.memory
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · change root.toNat + (bytes.data.extract 0 count).size ≤ 4294967296
    rw [hSize]; omega
  · change root.toNat + (bytes.data.extract 0 count).size ≤ mem.pages * 65536
    rw [hSize]; omega
  · change i < (bytes.data.extract 0 count).size at hi
    change mem.bytes (root.toNat + i) = (bytes.data.extract 0 count)[i]
    rw [ByteArray.getElem_extract, h.contents i (by rw [hSize] at hi; omega)]
    simp

/-- The number of bytes of a read: the count, or the capacity when the count is at least the
capacity. -/
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

/-- A buffer of `capacity` bytes that holds `buffer` after a frame that writes it holds the prefix
of `count` bytes, with the length `readLength count capacity`. -/
theorem ReadReady.prefix_rep {World : Type} {before after : Store World} {heap : Heap}
    {root capacity count : UInt64} {buffer : LeanExe.Bytes}
    (h : ReadReady heap (PureTransport.erase before) root capacity)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)])
    (hData : Bytes.At after.mem root buffer) (hSize : buffer.data.size = capacity.toNat) :
    Bytes.Rep heap (PureTransport.erase after) root (readLength count capacity)
      ⟨buffer.data.extract 0 count.toNat⟩ := by
  have hPrefixSize : (buffer.data.extract 0 count.toNat).size = min count.toNat capacity.toNat := by
    rw [ByteArray.size_extract]; omega
  have hLength : (readLength count capacity).toNat =
      (⟨buffer.data.extract 0 count.toNat⟩ : LeanExe.Bytes).data.size := by
    rw [readLength_toNat]
    exact hPrefixSize.symm
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · refine ⟨hLength, .inl ⟨rfl, ?_⟩⟩
    change (buffer.data.extract 0 count.toNat).size = 0
    rw [hPrefixSize]
    simp
  · refine ⟨hLength, .inr ?_⟩
    exact allocated_afterRead hBuffer hFrame (by rw [hPrefixSize]; omega)
      (bytes_at_prefix hData count.toNat)

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

theorem head_toList_of_length {places : List Nat} (h : places.length ≤ 1) :
    places.head?.toList = places := by
  match places, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- The words of an iovec call: its handle and second word, and the others in their locals. -/
theorem iovec_held {s : Locals} {locs : List Nat} {values : List UInt64} {count : Nat}
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hLength : values.length = 1 + count) :
    ∃ handleLocal rest handle extra, locs = handleLocal :: rest ∧ values = handle :: extra ∧
      s.get handleLocal = some (.i64 handle) ∧
      List.Forall₂ (fun place value => s.get place = some (.i64 value)) rest extra ∧
      extra.length = count := by
  cases hHeld with
  | nil => exact absurd hLength (by simp only [List.length_nil]; omega)
  | cons head tail =>
    exact ⟨_, _, _, _, rfl, rfl, head, tail, by simp at hLength; omega⟩

/-! ## Reads -/

/-- An accepted read: the allocation of the buffer, the element, the call, and on errno 0 the
length of the prefix, or otherwise the release of the buffer, with the continuation `K` of the
enclosing `iff`. -/
theorem wp_sys_iovec_read_accept_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {offset : Bool} {handleLocal capacityLocal : Nat}
    {extraLocs : List Nat} {handle capacity : UInt64} {extra : List UInt64}
    {s0 s : Locals} {base : Nat} {aborts : Bool} {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams false offset)
    (hExtra : extra.length = if offset then 1 else 0)
    (hHandleSmall : handle.toNat < 4294967296) (hCapacitySmall : capacity.toNat < 4294967296)
    (hHandle : s.get handleLocal = some (.i64 handle))
    (hCapacity : s.get capacityLocal = some (.i64 capacity))
    (hExtraHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) extraLocs
      extra)
    (hLocs : ∀ place ∈ handleLocal :: capacityLocal :: extraLocs, place < base)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hOutside : LocalsOutside s0 s base 4)
    (e2 : s.get (base + 2) = some (.i64 0))
    (hRoom : aborts = false → capacity ≠ 0 →
      heap.Room (PureTransport.erase initial) source (allocSize capacity))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → K (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno root length : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        ([.word handle, .space capacity] ++ extra.map .word) (.returned errno outputs)
        final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length
        ((sysReply errno outputs).prefixBytes 0 ((sysReply errno outputs).word 1)) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      LocalsOutside s0 sF base 4 → sF.values = s.values →
      sF.get base = some (.i64 errno) → sF.get (base + 1) = some (.i64 root) →
      sF.get (base + 2) = some (.i64 length) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        ([.word handle, .space capacity] ++ extra.map .word) (.trapped message outputs)
        final.host → K (.Trap final message)) :
    wp target (sysAllocateCodeWith calls capacityLocal (base + 1) ++
      metadataCode (base + 1) capacityLocal ++ iovecLowerCode handleLocal extraLocs.head? ++
      [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
       .iff 0 0 (readCountCode capacityLocal base) (discardReadCodeWith calls (base + 1)) [] []])
      K initial s env := by
  have hPositions : base + 6 ≤ s0.params.length + s0.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have bound := fun (t : Locals) (outside : LocalsOutside s0 t base 4) i
    (hi : base ≤ i) (hi' : i < base + 4) => outside.bounds hLow (by omega) hi hi'
  have hExtraLength : extraLocs.length ≤ 1 := by
    rw [hExtraHeld.length_eq, hExtra]; split <;> omega
  have hOffsetHeld : ∀ t : Locals, (∀ place ∈ extraLocs, t.get place = s.get place) →
      List.Forall₂ (fun place value => t.get place = some (.i64 value))
        extraLocs.head?.toList extra := by
    intro t same
    rw [head_toList_of_length hExtraLength]
    exact held_transfer hExtraHeld same
  -- The invocation from the state after the allocation.
  have invoke : ∀ (before : Store (Observed World)) (heapA : Heap) (sA : Locals) (root : UInt64),
      ReadReady heapA (PureTransport.erase before) root capacity →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heapA (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root) →
      before.host = initial.host →
      heapA.top.toNat ≤ heap.top.toNat + readCost capacity →
      LocalsOutside s0 sA base 4 → sA.values = s.values →
      sA.get (base + 1) = some (.i64 root) → sA.get (base + 2) = some (.i64 0) →
      (∀ place ∈ handleLocal :: capacityLocal :: extraLocs, sA.get place = s.get place) →
      wp target (metadataCode (base + 1) capacityLocal ++ (iovecLowerCode handleLocal
        extraLocs.head? ++
        [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
         .iff 0 0 (readCountCode capacityLocal base) (discardReadCodeWith calls (base + 1))
           [] []])) K before sA env := by
    intro before heapA sA root hReady hBefore hWorld hTop outsideA valuesA rootA lengthA same
    have hAddress := hReady.address
    have hRootSmall : root.toNat < 4294967296 := by omega
    have hRoot32 : root.toUInt32.toNat = root.toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRootSmall]
    have hCapacity32 : capacity.toUInt32.toNat = capacity.toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hCapacitySmall]
    have hMemory : 16 ≤ before.mem.pages * 65536 := by
      have hBase := hBefore.at_.base
      have hBound := hBefore.at_.top
      change 16 ≤ (PureTransport.erase before).mem.pages * 65536
      omega
    have hSeparate : 16 ≤ root.toNat ∨ (capacity = 0 ∧ root = 0) := by
      rcases hReady with ⟨rfl, rfl⟩ | ⟨previous, hBuf, _⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl (by have := hBuf.object.base; omega)
    have hCapacityA : sA.get capacityLocal = some (.i64 capacity) :=
      (same capacityLocal (by simp)).trans hCapacity
    have hHandleA : sA.get handleLocal = some (.i64 handle) :=
      (same handleLocal (by simp)).trans hHandle
    refine wp_metadata rootA hCapacityA hMemory ?_
    let middle := initializeScratch before root.toUInt32 capacity.toUInt32
    have hScratch : GuestFrame before middle [ABI.scratch] :=
      GuestFrame.ofScratchWrites (initializeScratch_range before _ _)
    have hPagesMiddle : middle.mem.pages = before.mem.pages := hScratch.pages
    have hElement := element_written before root.toUInt32 capacity.toUInt32 hMemory
    rw [hCapacity32] at hElement
    refine wp_iovec_read_call_with (root := root) hImports hHost hCall hParams hExtra
      hHandleSmall hCapacitySmall hHandleA
      (hOffsetHeld sA fun place member => same place (by simp [member])) hElement
      (by rw [hPagesMiddle]; exact hMemory)
      (by rw [hPagesMiddle]; exact hReady.memory hBefore.at_) (by omega) hSeparate ?_ ?_
    · intro after errno outputs hSys hFrame hShown
      have hFrame' : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)] := by
        refine (hScratch.weaken fun region member => ?_).trans (hFrame.cover fun region member => ?_)
        · rw [List.mem_singleton] at member
          subst member
          exact List.mem_cons_self ..
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), le_rfl, le_rfl⟩
          · exact ⟨ABI.scratch, List.mem_cons_self .., by decide, by decide⟩
      have hStep := hReady.frame_step hBefore hFrame'
      have hBound := (observedHost host).sys_bound hSys
      have hErrno : errno.toNat ≤ 76 := hBound.2
      have hSizes : outputs.map (fun output => output.data.size) = [capacity.toNat, 4] := by
        have h : outputs.map (fun output => output.data.size) =
            outputSizesOf call.params (host.reported middle.host.world call)
              ([.word handle, .space capacity] ++ extra.map .word) := hBound.1
        rw [h, hParams, iovec_read_sizes offset handle capacity hExtra]
      have hSys' : (observedHost host).sys initial.host call
          ([.word handle, .space capacity] ++ extra.map .word) (.returned errno outputs)
          after.host := by
        rw [← hWorld]; exact hSys
      simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
      have b0 := bound sA outsideA base le_rfl (by omega)
      refine wp_localSet_local b0.1 b0.2 ?_
      let sE := setLocal { sA with values := sA.values } base (.i64 errno)
      have hGetE : sE.get base = some (.i64 errno) :=
        Locals.get_setLocal_same (s := { sA with values := sA.values }) b0.1 b0.2
      have hOtherE : ∀ j, j ≠ base → sE.get j = sA.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { sA with values := sA.values }) b0.1 hj
      have outsideE : LocalsOutside s0 sE base 4 :=
        (outsideA.values sA.values).set hLow le_rfl (by omega)
      have hRootE : sE.get (base + 1) = some (.i64 root) := (hOtherE (base + 1) (by omega)).trans rootA
      have hLengthE : sE.get (base + 2) = some (.i64 0) :=
        (hOtherE (base + 2) (by omega)).trans lengthA
      change wp target (.localGet base :: _) K after sE env
      refine wp_localGet_get hGetE ?_
      simp only [wp_eqzI64_cons]
      refine wp_iff_cons rfl ?_
      by_cases hZero : errno = 0
      · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
        obtain ⟨buffer, count, rfl, hBufferAt, hCountAt⟩ := hShown hZero
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hSizes
        obtain ⟨hBufferSize, hCountSize⟩ := hSizes
        have hReply : sysReply errno [buffer, count] = ⟨errno, [buffer, count]⟩ := by
          simp [sysReply, hZero]
        have hCountWord := littleEndian_read32 hCountAt hCountSize
        have h8 : (8 : UInt64).toUInt32 = 8 := rfl
        rw [h8] at hCountWord
        have hCapacityE : sE.get capacityLocal = some (.i64 capacity) :=
          (hOtherE capacityLocal (by have := hLocs capacityLocal (by simp); omega)).trans
            hCapacityA
        have b3 := bound sE outsideE (base + 3) (by omega) (by omega)
        have b2 := bound sE outsideE (base + 2) (by omega) (by omega)
        simp only [readCountCode, List.cons_append, List.nil_append, wp_const_cons, wp_load32_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
        rw [ite_eq_right (by
          have hp := hFrame'.pages
          simp only [UInt32.reduceToNat, gt_iff_lt, not_lt]
          omega)]
        simp only [wp_extendUI32_cons]
        rw [hCountWord]
        refine wp_localSet_local b3.1 b3.2 ?_
        let sC := setLocal { sE with values := sE.values } (base + 3) (.i64 (littleEndian count))
        have hGetC : sC.get (base + 3) = some (.i64 (littleEndian count)) :=
          Locals.get_setLocal_same (s := { sE with values := sE.values }) b3.1 b3.2
        have hOtherC : ∀ j, j ≠ base + 3 → sC.get j = sE.get j := fun j hj =>
          Locals.get_setLocal_ne (s := { sE with values := sE.values }) b3.1 hj
        have outsideC : LocalsOutside s0 sC base 4 :=
          (outsideE.values sE.values).set hLow (by omega) (by omega)
        have hCapacityC : sC.get capacityLocal = some (.i64 capacity) :=
          (hOtherC capacityLocal (by have := hLocs capacityLocal (by simp); omega)).trans
            hCapacityE
        have hRepPrefix := hReady.prefix_rep (count := littleEndian count) hFrame' hBufferAt
          hBufferSize
        refine wp_min_code hGetC hCapacityC ?_
        have b2C := bound sC outsideC (base + 2) (by omega) (by omega)
        refine wp_localSet_local b2C.1 b2C.2 ?_
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hOther2 : ∀ j, j ≠ base + 2 → (setLocal { sC with values := sC.values } (base + 2)
            (.i64 (readLength (littleEndian count) capacity))).get j = sC.get j :=
          fun j hj => Locals.get_setLocal_ne (s := { sC with values := sC.values }) b2C.1 hj
        refine hNext heapA after _ errno root (readLength (littleEndian count) capacity)
          [buffer, count] hSys' hStep (by rw [hReply]; exact hRepPrefix) hTop ?_ ?_ ?_ ?_ ?_
        · exact (((outsideC.values sC.values).set hLow (by omega) (by omega)).values _)
        · exact valuesA
        · rw [Locals.get_values, hOther2 base (by omega), hOtherC base (by omega)]
          exact hGetE
        · rw [Locals.get_values, hOther2 (base + 1) (by omega), hOtherC (base + 1) (by omega)]
          exact hRootE
        · rw [Locals.get_values]
          exact Locals.get_setLocal_same (s := { sC with values := sC.values }) b2C.1 b2C.2
      · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
        have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, hZero]
        have hEmpty := hReady.empty_rep hBefore.at_ hFrame'
        have b1 := bound sE outsideE (base + 1) (by omega) (by omega)
        rw [← List.append_nil (discardReadCodeWith calls (base + 1))]
        refine wp_discard_read_with runtime layout profile hImports sourceHost hStep.at_ hEmpty
          hRootE b1.1 b1.2 ?_
        intro final hStore hFinalWorld
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hFinalStep := read_discard_step hStep hEmpty hStore
        have hFinalTop := read_discard_top hStep.at_ hEmpty
        have hOtherD : ∀ j, j ≠ base + 1 → (setLocal sE (base + 1) (.i64 0)).get j = sE.get j :=
          fun j hj => Locals.get_setLocal_ne b1.1 hj
        refine hNext _ final _ errno 0 0 outputs (by rw [hFinalWorld]; exact hSys')
          (by simpa only [Bytes.regions, ite_true] using hFinalStep) ?_
          (by rw [hFinalTop]; exact hTop) ((outsideE.set hLow (by omega) (by omega)).values _) ?_
          ?_ ?_ ?_
        · rw [hReply, prefixBytes_empty]
          exact Bytes.Rep.empty _ _
        · exact valuesA
        · rw [Locals.get_values, hOtherD base (by omega)]
          exact hGetE
        · rw [Locals.get_values]
          exact Locals.get_setLocal_same b1.1 b1.2
        · rw [Locals.get_values, hOtherD (base + 2) (by omega)]
          exact hLengthE
    · intro after message outputs hSys
      exact hTrap after message outputs (by rw [← hWorld]; exact hSys)
  -- The allocation of the buffer.
  have hLowA := (bound s hOutside (base + 1) (by omega) (by omega)).1
  have hHighA := (bound s hOutside (base + 1) (by omega) (by omega)).2
  have afterAllocation : ∀ root : UInt64,
      LocalsOutside s0 (setLocal s (base + 1) (.i64 root)) base 4 ∧
      (setLocal s (base + 1) (.i64 root)).get (base + 1) = some (.i64 root) ∧
      (∀ j, j ≠ base + 1 → (setLocal s (base + 1) (.i64 root)).get j = s.get j) :=
    fun root => ⟨hOutside.set hLow (by omega) (by omega),
      Locals.get_setLocal_same hLowA hHighA, fun j hj => Locals.get_setLocal_ne hLowA hj⟩
  have sameAfter : ∀ root : UInt64, ∀ place ∈ handleLocal :: capacityLocal :: extraLocs,
      (setLocal s (base + 1) (.i64 root)).get place = s.get place := by
    intro root place member
    exact (afterAllocation root).2.2 place (by have := hLocs place member; omega)
  simp only [List.append_assoc]
  refine wp_sys_allocate_with (capacityLocal := capacityLocal) (rootLocal := base + 1) runtime
    layout profile hImports sourceHost hHeap (by omega) hCap hCapacity hLowA hHighA
    (fun hNonzero hAbort => hRoom hAbort hNonzero) hResource ?_ ?_
  · intro hZero
    subst hZero
    obtain ⟨outsideA, rootA, otherA⟩ := afterAllocation 0
    exact invoke initial heap _ 0 (Or.inl ⟨rfl, rfl⟩)
      (by simpa only [Bytes.regions, ite_true] using
        Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch))
      rfl (by simp) outsideA rfl rootA ((otherA (base + 2) (by omega)).trans e2) (sameAfter 0)
  · intro hNonzero before hFits hStore hWorld
    obtain ⟨hAllocate, hBuffer, hCapacityAt, hTopAlloc⟩ :=
      read_allocation_buffer hHeap (by omega) hFits hStore
    let root := FixedArrayAllocate.root heap.top (allocSize capacity) heap.free
    obtain ⟨outsideA, rootA, otherA⟩ := afterAllocation root
    have hBefore : Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.scratch)
        (heap.allocate (allocSize capacity)) (PureTransport.erase before)
        (Bytes.regions (PureTransport.erase before) root) := by
      have hRoot : root ≠ 0 := hBuffer.nonzero
      rw [Bytes.regions, ite_eq_right hRoot]
      exact hAllocate.mono
        (keep' := fun region => regionsDisjoint region ABI.scratch)
        (fresh' := [block (PureTransport.erase before) root])
        (fun _ _ => True.intro) (fun _ h => h)
    exact invoke before (heap.allocate (allocSize capacity)) _ root
      (Or.inr ⟨_, hBuffer, hCapacityAt⟩) hBefore hWorld
      (by rw [readCost_positive hCapacitySmall hNonzero]; exact hTopAlloc)
      outsideA rfl rootA ((otherA (base + 2) (by omega)).trans e2) (sameAfter root)

/-- The code of a read, from the words in their locals to the errno and the buffer's root and
length on the stack.  A rejected request returns its errno without a call; an accepted request
allocates the buffer, runs the call, keeps the prefix of the count, at most the capacity, on
errno 0, and otherwise releases the buffer. -/
theorem wp_sys_iovec_read_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {offset : Bool} {locs : List Nat} {values : List UInt64}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)} {aborts : Bool}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams false offset)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hLocs : ∀ place ∈ locs, place < base)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hRoom : aborts = false → (values.getD 1 0).toNat < 4294967296 → values.getD 1 0 ≠ 0 →
      heap.Room (PureTransport.erase initial) source (allocSize (values.getD 1 0)))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (trace : List Event) (reply : Reply) (root length : UInt64),
      Exec (observedHost host) (.sys call (flatArgsWith call.params values []) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length (reply.prefixBytes 0 (reply.word 1)) →
      heap'.top.toNat ≤ heap.top.toNat + readCost (values.getD 1 0) →
      LocalsOutside s finalLocals base 4 →
      wp target rest Q final { finalLocals with values :=
        ([Value.i64 reply.errno] ++ [Value.i64 root, Value.i64 length]).reverse ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.sys call (flatArgsWith call.params values []) Action.pure)
        initial.host trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysIovecReadCodeWith calls call locs base ++ rest) Q initial s env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hLength : values.length = 1 + (1 + if offset then 1 else 0) := by
    rw [hCount, iovec_wordCount hParams]; simp only [Bool.false_eq_true, ite_false]; omega
  obtain ⟨handleLocal, rest1, handle, rest2, rfl, rfl, hHandle, held1, length1⟩ :=
    iovec_held hHeld hLength
  obtain ⟨capacityLocal, extraLocs, capacity, extra, rfl, rfl, hCapacity, hExtraHeld, hExtra⟩ :=
    iovec_held held1 length1
  have hArgs : flatArgsWith call.params (handle :: capacity :: extra) [] =
      [.word handle, .space capacity] ++ extra.map .word := by
    rw [hParams, iovec_read_args offset _ (by simp; omega)]
    rfl
  have hReject : call.reject ([.word handle, .space capacity] ++ extra.map .word) =
      if handle.toNat < 2 ^ 32 then (if capacity.toNat < 2 ^ 32 then 0 else 61) else 61 := by
    change rejectArgs call.params _ = _
    rw [hParams, iovec_reject false offset handle _ hExtra]
    rfl
  simp only [sysIovecReadCodeWith, List.getD_cons_zero, List.getD_cons_succ, List.append_assoc,
    List.cons_append]
  refine wp_iovec_reject hHandle hCapacity ?_
  generalize hRejectEq : (if handle.toNat < 2 ^ 32 then (if capacity.toNat < 2 ^ 32 then 0 else 61)
    else 61 : UInt64) = reject
  rw [hRejectEq] at hReject
  refine wp_localSet_local hLow (by omega) ?_
  let s1 := setLocal { s with values := s.values } base (.i64 reject)
  have outside1 : LocalsOutside s s1 base 4 :=
    ((LocalsOutside.refl s base 4).values s.values).set hLow le_rfl (by omega)
  have hGet1 : s1.get base = some (.i64 reject) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) hLow (by omega)
  change wp target (zeroLocalsCode (base + 1) 3 ++ _) Q initial s1 env
  refine wp_zero_locals 3 (base + 1) s1 (by rw [outside1.params]; omega)
    (by rw [outside1.params, outside1.length]; omega) ?_
  intro s2 outside2 values2 zeros2
  have outside2' : LocalsOutside s s2 base 4 := outside1.trans (outside2.widen (by omega) (by omega))
  have hGet2 : s2.get base = some (.i64 reject) := (outside2.others base (by omega)).trans hGet1
  have hLocs' : ∀ place ∈ handleLocal :: capacityLocal :: extraLocs, s2.get place = s.get place :=
    fun place member => outside2'.others place (by have := hLocs place member; omega)
  have hRoot2 : s2.get (base + 1) = some (.i64 0) := by simpa using zeros2 0 (by omega)
  have hLength2 : s2.get (base + 2) = some (.i64 0) := by simpa using zeros2 1 (by omega)
  simp only [wp_localGet_cons, hGet2, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have finish : ∀ (final : Store (Observed World)) (sF : Locals) (heap' : Heap)
      (trace : List Event) (reply : Reply) (root length : UInt64),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (handle :: capacity :: extra) []) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length
        (reply.prefixBytes 0 (reply.word 1)) →
      heap'.top.toNat ≤ heap.top.toNat + readCost capacity →
      LocalsOutside s sF base 4 → sF.get base = some (.i64 reply.errno) →
      sF.get (base + 1) = some (.i64 root) → sF.get (base + 2) = some (.i64 length) →
      wp target (.localGet base :: .localGet (base + 1) :: .localGet (base + 2) :: rest) Q final
        { sF with values := s.values } env := by
    intro final sF heap' trace reply root length execution step rep top outsideF errnoF rootF
      lengthF
    simp only [wp_localGet_cons, Locals.get_values, errnoF, rootF, lengthF]
    simpa only [List.singleton_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      hNext heap' final { sF with values := s.values } trace reply root length execution step rep
        top (outsideF.values s.values)
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hSmall : handle.toNat < 4294967296 ∧ capacity.toNat < 4294967296 := by
      rw [← hRejectEq] at hAccepted
      by_cases h1 : handle.toNat < 2 ^ 32
      · by_cases h2 : capacity.toNat < 2 ^ 32
        · exact ⟨h1, h2⟩
        · rw [ite_eq_left h1, ite_eq_right h2] at hAccepted
          exact absurd hAccepted (by decide)
      · rw [ite_eq_right h1] at hAccepted
        exact absurd hAccepted (by decide)
    have hRejectZero : call.reject ([.word handle, .space capacity] ++ extra.map .word) = 0 := by
      rw [hReject, hAccepted]
    change wp target (sysIovecReadCallCodeWith calls call
      (handleLocal :: capacityLocal :: extraLocs) base) _ initial s2 env
    simp only [sysIovecReadCallCodeWith, List.getD_cons_zero, List.getD_cons_succ,
      List.getElem?_cons_succ]
    rw [show extraLocs[0]? = extraLocs.head? by cases extraLocs <;> rfl]
    refine wp_sys_iovec_read_accept_with (s0 := s) runtime layout profile hImports sourceHost
      hHost hCall hParams hExtra hSmall.1 hSmall.2 ((hLocs' handleLocal (by simp)).trans hHandle)
      ((hLocs' capacityLocal (by simp)).trans hCapacity)
      (held_transfer hExtraHeld fun place member => hLocs' place (by simp [member]))
      hLocs hHeap hCap hLow hHigh outside2' hLength2
      (fun hAbort hNonzero => hRoom hAbort hSmall.2 hNonzero) hResource ?_ ?_
    · intro heap' final sF errno root length outputs hSys hStep hRep hTop outsideF valuesF
        errnoF rootF lengthF
      simp only [List.take_zero, List.nil_append, List.drop_zero, values2]
      refine finish final sF heap'
        [.sys call (flatArgsWith call.params (handle :: capacity :: extra) [])
          (.returned errno outputs)]
        (sysReply errno outputs) root length ?_ hStep hRep hTop outsideF errnoF rootF lengthF
      rw [hArgs]
      exact .sys_return hRejectZero hSys (.pure final.host _)
    · intro final message outputs hSys
      exact hTrap final message _ (by rw [hArgs]; exact .sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] :
      ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, values2]
    have hRejectNe : call.reject ([.word handle, .space capacity] ++ extra.map .word) ≠ 0 := by
      rw [hReject]; exact hAccepted
    refine finish initial s2 heap [] ⟨reject, []⟩ 0 0 ?_ ?_ ?_ (by omega) outside2' hGet2 hRoot2
      hLength2
    · rw [hArgs, ← hReject]
      exact .sys_reject hRejectNe (.pure initial.host _)
    · simpa only [Bytes.regions, ite_true] using
        Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch)
    · rw [prefixBytes_empty]
      exact Bytes.Rep.empty _ _

/-! ## Writes -/

/-- The code of a write, from the handle and the offset in their locals and the input in its two
locals to the errno and the count on the stack.  A rejected request returns its errno without a
call; an accepted request writes the element of the input, runs the call, and loads the count on
errno 0. -/
theorem wp_sys_iovec_write_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World}
    (hImports : target.imports = ABI.importsWith calls) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {offset : Bool} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams true offset)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hLocs : ∀ place ∈ locs, place < base)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hInputLocs : ∀ place ∈ inputLocs, place + 2 ≤ base)
    (hInputReps : ∀ input ∈ inputs, ∃ length,
      Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
        ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.scratch)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap (PureTransport.erase final) [] →
      LocalsOutside s finalLocals base 2 →
      wp target rest Q final { finalLocals with values :=
        ([Value.i64 reply.errno, Value.i64 (reply.word 0)]).reverse ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysIovecWriteCodeWith calls call locs inputLocs base ++ rest) Q initial s env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hLength : values.length = 1 + if offset then 1 else 0 := by
    rw [hCount, iovec_wordCount hParams]; simp only [ite_true]
  obtain ⟨handleLocal, extraLocs, handle, extra, rfl, rfl, hHandle, hExtraHeld, hExtra⟩ :=
    iovec_held hHeld hLength
  have hOneInput : inputs.length = 0 + 1 := by rw [hInputCount, iovec_inputCount hParams]; rfl
  obtain ⟨inputLocal, input, inputLocs', inputs', hInputHeld, hInputsRest, rfl, rfl⟩ :=
    forall₂_head hInputs hOneInput
  have hNoMore : inputs' = [] := List.eq_nil_of_length_eq_zero (by simpa using hOneInput)
  subst hNoMore
  cases hInputsRest
  obtain ⟨hRootLocal, hSizeLocal, hSize⟩ := hInputHeld
  have hArgs : flatArgsWith call.params (handle :: extra) ([input].map Prod.snd) =
      [.word handle, .bytes input.2] ++ extra.map .word := by
    rw [hParams, List.map_singleton, iovec_write_args offset _ input.2 (by simp; omega)]
    rfl
  have hReject : call.reject ([.word handle, .bytes input.2] ++ extra.map .word) =
      if handle.toNat < 2 ^ 32 then
        (if (LeanExe.Bytes.size input.2).toNat < 2 ^ 32 then 0 else 61) else 61 := by
    change rejectArgs call.params _ = _
    rw [hParams, iovec_reject true offset handle _ hExtra,
      LeanExe.Bytes.size_toNat input.2 (by omega)]
    rfl
  simp only [sysIovecWriteCodeWith, List.getD_cons_zero, List.append_assoc, List.cons_append]
  refine wp_iovec_reject hHandle hSizeLocal ?_
  generalize hRejectEq : (if handle.toNat < 2 ^ 32 then
    (if (LeanExe.Bytes.size input.2).toNat < 2 ^ 32 then 0 else 61) else 61 : UInt64) = reject
  rw [hRejectEq] at hReject
  refine wp_localSet_local hLow (by omega) ?_
  let s1 := setLocal { s with values := s.values } base (.i64 reject)
  have outside1 : LocalsOutside s s1 base 2 :=
    ((LocalsOutside.refl s base 2).values s.values).set hLow le_rfl (by omega)
  have hGet1 : s1.get base = some (.i64 reject) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) hLow (by omega)
  change wp target (zeroLocalsCode (base + 1) 1 ++ _) Q initial s1 env
  refine wp_zero_locals 1 (base + 1) s1 (by rw [outside1.params]; omega)
    (by rw [outside1.params, outside1.length]; omega) ?_
  intro s2 outside2 values2 zeros2
  have outside2' : LocalsOutside s s2 base 2 := outside1.trans (outside2.widen (by omega) (by omega))
  have hGet2 : s2.get base = some (.i64 reject) := (outside2.others base (by omega)).trans hGet1
  have hCount2 : s2.get (base + 1) = some (.i64 0) := by simpa using zeros2 0 (by omega)
  have same2 : ∀ place, place < base → s2.get place = s.get place :=
    fun place below => outside2'.others place (.inl below)
  simp only [wp_localGet_cons, hGet2, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have finish : ∀ (final : Store (Observed World)) (sF : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (handle :: extra) ([input].map Prod.snd))
          Action.pure) initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap (PureTransport.erase final) [] →
      LocalsOutside s sF base 2 → sF.get base = some (.i64 reply.errno) →
      sF.get (base + 1) = some (.i64 (reply.word 0)) →
      wp target (.localGet base :: .localGet (base + 1) :: rest) Q final
        { sF with values := s.values } env := by
    intro final sF trace reply execution step outsideF errnoF countF
    simp only [wp_localGet_cons, Locals.get_values, errnoF, countF]
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.singleton_append] using
      hNext final { sF with values := s.values } trace reply execution step
        (outsideF.values s.values)
  have hRefl : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch) heap (PureTransport.erase initial)
      (Bytes.regions (PureTransport.erase initial) 0) := by
    simpa only [Bytes.regions, ite_true] using
      Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch)
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hSmall : handle.toNat < 4294967296 ∧ input.2.data.size < 4294967296 := by
      rw [← hRejectEq, LeanExe.Bytes.size_toNat input.2 (by omega)] at hAccepted
      by_cases h1 : handle.toNat < 2 ^ 32
      · by_cases h2 : input.2.data.size < 2 ^ 32
        · exact ⟨h1, h2⟩
        · rw [ite_eq_left h1, ite_eq_right h2] at hAccepted
          exact absurd hAccepted (by decide)
      · rw [ite_eq_right h1] at hAccepted
        exact absurd hAccepted (by decide)
    have hRejectZero : call.reject ([.word handle, .bytes input.2] ++ extra.map .word) = 0 := by
      rw [hReject, hAccepted]
    change wp target (sysIovecWriteCallCodeWith calls call (handleLocal :: extraLocs)
      [inputLocal] base) _ initial s2 env
    simp only [sysIovecWriteCallCodeWith, List.getD_cons_zero, List.getElem?_cons_succ]
    rw [show extraLocs[0]? = extraLocs.head? by cases extraLocs <;> rfl]
    obtain ⟨⟨hInputAt, hRootSmall⟩, hApart, _⟩ :=
      input_at_call (root := 0) (capacity := 0) (hInputReps input (List.mem_singleton_self _))
        hRefl (Or.inl ⟨rfl, rfl⟩)
    have hRootLocal2 : s2.get inputLocal = some (.i64 input.1) :=
      (same2 inputLocal (by have := hInputLocs inputLocal (by simp); omega)).trans hRootLocal
    have hSizeLocal2 : s2.get (inputLocal + 1) = some (.i64 (LeanExe.Bytes.size input.2)) :=
      (same2 (inputLocal + 1) (by have := hInputLocs inputLocal (by simp); omega)).trans
        hSizeLocal
    have hMemory : 16 ≤ initial.mem.pages * 65536 := by
      have hBase := hHeap.base
      have hBound := hHeap.top
      change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
      omega
    simp only [List.append_assoc]
    refine wp_metadata hRootLocal2 hSizeLocal2 hMemory ?_
    let middle := initializeScratch initial input.1.toUInt32 (LeanExe.Bytes.size input.2).toUInt32
    have hScratch : GuestFrame initial middle [ABI.scratch] :=
      GuestFrame.ofScratchWrites (initializeScratch_range initial _ _)
    have hElement := element_written initial input.1.toUInt32
      (LeanExe.Bytes.size input.2).toUInt32 hMemory
    have hLengthNat : (LeanExe.Bytes.size input.2).toUInt32.toNat = input.2.data.size := by
      rw [bytes_size_toUInt32 hSmall.2, UInt32.toNat_ofNat_of_lt' hSmall.2]
    rw [hLengthNat] at hElement
    have hBytesMiddle : Bytes.At middle.mem input.1 input.2 :=
      hInputAt.writesRange (initializeScratch_range initial _ _) (by
        simp only [regionsDisjoint, ABI.scratch] at hApart
        omega)
    have hExtraHeld2 := held_transfer hExtraHeld fun place member =>
      same2 place (hLocs place (List.mem_cons_of_mem _ member))
    refine wp_iovec_write_call_with (root := input.1) (bytes := input.2) hImports hHost hCall
      hParams hExtra hSmall.1 hSmall.2
      ((same2 handleLocal (hLocs handleLocal (by simp))).trans hHandle)
      (by
        rw [head_toList_of_length (by rw [hExtraHeld2.length_eq, hExtra]; split <;> omega)]
        exact hExtraHeld2)
      hElement hBytesMiddle hRootSmall hApart (by rw [hScratch.pages]; exact hMemory) ?_ ?_
    · intro after errno outputs hSys hFrame hShown
      have hFrame' : GuestFrame initial after [ABI.scratch, (0, 0)] := by
        refine (hScratch.weaken fun region member => ?_).trans (hFrame.cover fun region member => ?_)
        · rw [List.mem_singleton] at member
          subst member
          exact List.mem_cons_self ..
        · rw [List.mem_singleton] at member
          subst member
          exact ⟨ABI.scratch, List.mem_cons_self .., by decide, by decide⟩
      have hStep : Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch) heap (PureTransport.erase after)
          [] := by
        simpa only [Bytes.regions, ite_true] using
          ReadReady.frame_step (Or.inl ⟨rfl, rfl⟩) hRefl (by simpa using hFrame')
      have hErrno : errno.toNat ≤ 76 := ((observedHost host).sys_bound hSys).2
      have hSys' : (observedHost host).sys initial.host call
          ([.word handle, .bytes input.2] ++ extra.map .word) (.returned errno outputs)
          after.host := hSys
      simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
      have b0 := outside2'.bounds hLow (by omega) (le_refl base) (by omega)
      refine wp_localSet_local b0.1 b0.2 ?_
      let sE := setLocal { s2 with values := s2.values } base (.i64 errno)
      have hGetE : sE.get base = some (.i64 errno) :=
        Locals.get_setLocal_same (s := { s2 with values := s2.values }) b0.1 b0.2
      have hOtherE : ∀ j, j ≠ base → sE.get j = s2.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { s2 with values := s2.values }) b0.1 hj
      have outsideE : LocalsOutside s sE base 2 :=
        (outside2'.values s2.values).set hLow le_rfl (by omega)
      change wp target (.localGet base :: _) _ after sE env
      refine wp_localGet_get hGetE ?_
      simp only [wp_eqzI64_cons]
      refine wp_iff_cons rfl ?_
      by_cases hZero : errno = 0
      · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
        obtain ⟨count, rfl, hCountAt⟩ := hShown hZero
        have hCountSize : count.data.size = 4 := by
          have hSizes : [count].map (fun output => output.data.size) =
              outputSizesOf call.params (host.reported initial.host.world call)
                ([.word handle, .bytes input.2] ++ extra.map .word) :=
            ((observedHost host).sys_bound hSys).1
          rw [hParams, iovec_write_sizes offset handle input.2 hExtra] at hSizes
          simpa using hSizes
        have hCountWord := littleEndian_read32 hCountAt hCountSize
        have h8 : (8 : UInt64).toUInt32 = 8 := rfl
        rw [h8] at hCountWord
        have b1 := outsideE.bounds hLow (by omega) (show base ≤ base + 1 by omega) (by omega)
        simp only [List.nil_append, wp_const_cons, wp_load32_cons,
          UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
        rw [ite_eq_right (by
          have hp := hFrame'.pages
          simp only [UInt32.reduceToNat, gt_iff_lt, not_lt]
          omega)]
        simp only [wp_extendUI32_cons]
        rw [hCountWord]
        refine wp_localSet_local b1.1 b1.2 ?_
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hOther1 : ∀ j, j ≠ base + 1 → (setLocal { sE with values := sE.values } (base + 1)
            (.i64 (littleEndian count))).get j = sE.get j :=
          fun j hj => Locals.get_setLocal_ne (s := { sE with values := sE.values }) b1.1 hj
        simp only [values2]
        refine finish after _
          [.sys call (flatArgsWith call.params (handle :: extra) ([input].map Prod.snd))
            (.returned errno [count])] (sysReply errno [count]) ?_ hStep ?_ ?_ ?_
        · rw [hArgs]
          exact .sys_return hRejectZero hSys' (.pure after.host _)
        · exact (outsideE.values _).set hLow (by omega) (by omega)
        · rw [hOther1 base (by omega)]
          simpa [sysReply, hZero] using hGetE
        · rw [Locals.get_setLocal_same (s := { sE with values := sE.values }) b1.1 b1.2]
          simp [sysReply, hZero, Reply.word]
      · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, values2]
        refine finish after sE
          [.sys call (flatArgsWith call.params (handle :: extra) ([input].map Prod.snd))
            (.returned errno outputs)] (sysReply errno outputs) ?_ hStep outsideE ?_ ?_
        · rw [hArgs]
          exact .sys_return hRejectZero hSys' (.pure after.host _)
        · simpa [sysReply, hZero] using hGetE
        · rw [hOtherE (base + 1) (by omega), hCount2]
          simp [sysReply, hZero, Reply.word]
    · intro final message outputs hSys
      exact hTrap final message _ (by rw [hArgs]; exact .sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] :
      ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, values2]
    have hRejectNe : call.reject ([.word handle, .bytes input.2] ++ extra.map .word) ≠ 0 := by
      rw [hReject]; exact hAccepted
    refine finish initial s2 [] ⟨reject, []⟩ ?_ (by simpa only [Bytes.regions, ite_true] using hRefl)
      outside2' hGet2 (by rw [hCount2]; simp [Reply.word])
    rw [hArgs, ← hReject]
    exact .sys_reject hRejectNe (.pure initial.host _)

end Verified.Wasi
