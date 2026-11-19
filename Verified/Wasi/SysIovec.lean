import Verified.Wasi.SysFill

/-! The code of an iovec call, from the argument test to the result on the stack.  A read computes
the window of its buffer, tests the handle and the window's length, writes the element of the
window, runs the call, and on errno 0 clamps the count to the window's length; after an errno it
stores 0 into the window, and its result holds the errno, the count, and the buffer.  A write
computes the window of its input, tests the handle and the window's length, writes the element of
the window, runs the call, and on errno 0 loads the count; its result holds the errno and the
count. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

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

theorem iovec_read_lower (offset : Bool) (handle start count : UInt64) (extra : List UInt64)
    (buffer : LeanExe.Bytes) (hExtra : extra.length = if offset then 1 else 0) :
    lowerWords (iovecParams false offset) (handle :: start :: count :: extra) [buffer] =
        [handle, buffer.windowLength start count] ++ extra ∧
      windowWords (iovecParams false offset) (handle :: start :: count :: extra) =
        (start, count) := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- The code of a read that fills the window of the buffer whose root and size lie in the two
locals from `rootLocal`, from the handle, the window's start and count, and the offset of
`fd_pread` in their locals to the errno, the count, and the buffer's root and size on the stack.
A rejected request and an errno of the host leave the window's bytes 0. -/
theorem wp_sys_iovec_fill_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {offset : Bool} {locs : List Nat} {values : List UInt64}
    {rootLocal : Nat} {root size : UInt64} {buffer : LeanExe.Bytes}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams false offset)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argWords)
    (hLocs : ∀ place ∈ locs, place < base)
    (hRoot : s.get rootLocal = some (.i64 root))
    (hSize : s.get (rootLocal + 1) = some (.i64 size)) (hRootBelow : rootLocal + 2 ≤ base)
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer]) [])
          Action.pure) initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial)
        (fun r => regionsDisjoint r ABI.low ∧
          ∀ b ∈ Bytes.regions (PureTransport.erase initial) root, regionsDisjoint r b)
        heap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap (PureTransport.erase final) root size
        (readFill call.params values buffer reply).buffer →
      LocalsOutside s finalLocals base 6 →
      wp target rest Q final { finalLocals with values :=
        [Value.i64 size, .i64 root, .i64 (readFill call.params values buffer reply).count,
          .i64 reply.errno] ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer]) [])
          Action.pure) initial.host trace (.trapped message) final.host →
      Q (.Trap final message)) :
    wp target (sysIovecReadCodeWith calls call locs rootLocal base ++ rest) Q initial s env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hLength3 : values.length = 1 + (2 + if offset then 1 else 0) := by
    rw [hCount, Call.argWords, hParams]
    cases offset <;> rfl
  obtain ⟨handleLocal, rest1, handle, rest2, rfl, rfl, hHandle, held1, length1⟩ :=
    iovec_held hHeld hLength3
  obtain ⟨startLocal, rest3, start, rest4, rfl, rfl, hStartLocal, held2, length2⟩ :=
    iovec_held (count := 1 + if offset then 1 else 0) held1 (by rw [length1]; omega)
  obtain ⟨countLocal, extraLocs, count, extra, rfl, rfl, hCountLocal, hExtraHeld, hExtra⟩ :=
    iovec_held (count := if offset then 1 else 0) held2 (by omega)
  obtain ⟨hLowerEq, hWindowWords⟩ := iovec_read_lower offset handle start count extra buffer hExtra
  have hArgs : flatArgsWith call.params (lowerWords call.params
      (handle :: start :: count :: extra) [buffer]) [] =
      [.word handle, .space (buffer.windowLength start count)] ++ extra.map .word := by
    rw [hParams, hLowerEq, iovec_read_args offset _ (by simp; omega)]
    rfl
  have hReadFill : ∀ reply, readFill call.params (handle :: start :: count :: extra) buffer reply =
      FillResult.of buffer start count reply.errno
        (min (reply.word 1) (buffer.windowLength start count)) (reply.bytes 0) := by
    intro reply
    simp only [readFill, hParams, hWindowWords]
  obtain ⟨hFirst, hLength, hLengthEq⟩ := window_words hRep.length_eq start count
  obtain ⟨_, _, hAddrNat, _, hFits, hMem, hSep⟩ := window_at hRep hHeap start count
  have hWindowLe := buffer.window_le start count
  generalize hP : root + windowFirstWord size start = P at hAddrNat hFits hMem hSep
  generalize hLw : windowLengthWord size start count = Lw at hFits hMem hSep hLength hLengthEq
  generalize hFirstNat : (buffer.window start count).1 = first at hFirst hAddrNat hWindowLe
  generalize hLengthNat : (buffer.window start count).2 = length at hLength hWindowLe
  have hPsmall : P.toNat < 4294967296 := by have := hFits; omega
  have hLwSmall : Lw.toNat < 4294967296 := by have := hFits; omega
  have hMemory : 16 ≤ initial.mem.pages * 65536 := by
    have hBase := hHeap.base
    have hBound := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega
  have hStartBelow := hLocs startLocal (by simp)
  have hCountBelow := hLocs countLocal (by simp)
  have hHandleBelow := hLocs handleLocal (by simp)
  have afterCall : ∀ (final : Store (Observed World)) (sF : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params
          (handle :: start :: count :: extra) [buffer]) []) Action.pure)
        initial.host trace (.returned reply) final.host →
      GuestFrame initial final [ABI.scratch, (root.toNat + first, length)] →
      (reply.errno = 0 → (reply.bytes 0).data.size = length ∧
        ∀ (i : Nat) (hi : i < (reply.bytes 0).data.size),
          final.mem.bytes (root.toNat + first + i) = (reply.bytes 0).data[i]) →
      LocalsOutside s sF base 6 → sF.values = s.values →
      sF.get base = some (.i64 reply.errno) → sF.get (base + 1) = some (.i64 P) →
      sF.get (base + 2) = some (.i64 Lw) →
      sF.get (base + 3) = some (.i64
        (readFill call.params (handle :: start :: count :: extra) buffer reply).count) →
      wp target (fillTailCode rootLocal base ++ rest) Q final sF env := by
    intro final sF trace reply execution frame output outsideF valuesF errnoF addressF lengthF
      countF
    have pagesF : final.mem.pages = initial.mem.pages := frame.pages
    refine wp_fill_tail errnoF addressF lengthF countF
      (by rw [outsideF.others _ (by omega)]; exact hRoot)
      (by rw [outsideF.others _ (by omega)]; exact hSize) (by omega)
      (by rw [outsideF.params]; omega) (by rw [outsideF.params, outsideF.length]; omega)
      hFits (by rw [pagesF]; exact hMem) ?_
    intro final' s' same zeros outside' values'
    have hHost' : final'.host = final.host := by
      by_cases hZero : reply.errno = 0
      · rw [same hZero]
      · have writes := (zeros hZero).1
        rw [writes.1]
    obtain ⟨hRep', hStep'⟩ := fill_after
        (used := min (reply.word 1) (buffer.windowLength start count))
      hRep hHeap (by rw [hFirstNat, hLengthNat]; exact frame)
      (fun zero => by rw [hFirstNat, hLengthNat]; exact output zero) same
      (fun nonzero => by
        obtain ⟨writes, zeroBytes⟩ := zeros nonzero
        rw [hFirstNat, hLengthNat]
        rw [hAddrNat, hLength] at writes
        refine ⟨writes, fun i hi => ?_⟩
        have := zeroBytes i (by rw [hLength]; exact hi)
        rwa [hAddrNat] at this)
    rw [valuesF]
    refine hNext final' s' trace reply (by rw [hHost']; exact execution) hStep' ?_
      (outsideF.trans (outside'.widen (by omega) (by omega)))
    rw [hReadFill]
    exact hRep'
  simp only [sysIovecReadCodeWith, List.getD_cons_zero, List.getD_cons_succ, List.append_assoc]
  refine wp_window_code hRoot hSize hStartLocal hCountLocal (by omega) (by omega) (by omega)
    (by omega) ?_
  intro s1 outside1 values1 getP getL
  rw [hP] at getP
  rw [hLw] at getL
  have handle1 : s1.get handleLocal = some (.i64 handle) := by
    rw [outside1.others _ (by omega)]; exact hHandle
  refine wp_iovec_reject handle1 getL ?_
  generalize hRejectEq : (if handle.toNat < 2 ^ 32 then (if Lw.toNat < 2 ^ 32 then 0 else 61)
    else 61 : UInt64) = reject
  have hReject : call.reject ([.word handle, .space (buffer.windowLength start count)] ++
      extra.map .word) = reject := by
    change rejectArgs call.params _ = _
    rw [hParams, iovec_reject false offset handle _ hExtra, ← hRejectEq, ← hLengthEq]
    rfl
  simp only [List.cons_append, List.nil_append]
  have hLow1 : s1.params.length ≤ base := by rw [outside1.params]; exact hLow
  refine wp_localSet_local hLow1 (by rw [outside1.params, outside1.length]; omega) ?_
  let s2 := setLocal { s1 with values := s1.values } base (.i64 reject)
  have hLow2 : s2.params.length ≤ base + 3 := by simp only [s2, setLocal]; omega
  have hHigh2 : base + 3 < s2.params.length + s2.locals.length := by
    simp only [s2, setLocal, List.length_set]; rw [outside1.params, outside1.length]; omega
  refine wp_set_word hLow2 hHigh2 ?_
  let s3 := setLocal s2 (base + 3) (.i64 0)
  have get3 : ∀ j, s3.get j = if j = base + 3 then some (.i64 0)
      else if j = base then some (.i64 reject) else s1.get j := by
    intro j
    by_cases h3 : j = base + 3
    · subst h3
      simp only [ite_true]
      exact Locals.get_setLocal_same hLow2 hHigh2
    · rw [ite_eq_right h3, Locals.get_setLocal_ne hLow2 h3]
      by_cases h0 : j = base
      · subst h0
        simp only [ite_true]
        exact Locals.get_setLocal_same (s := { s1 with values := s1.values }) hLow1
          (by rw [outside1.params, outside1.length]; omega)
      · rw [ite_eq_right h0]
        exact Locals.get_setLocal_ne (s := { s1 with values := s1.values }) hLow1 h0
  have outside3 : LocalsOutside s s3 base 6 := by
    refine ⟨outside1.params, by simp only [s3, s2, setLocal, List.length_set]; exact outside1.length,
      fun j hj => ?_⟩
    rw [get3, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact outside1.others j (by omega)
  have values3 : s3.values = s.values := values1
  have errno3 : s3.get base = some (.i64 reject) := by rw [get3]; simp
  have address3 : s3.get (base + 1) = some (.i64 P) := by rw [get3]; simpa using getP
  have length3 : s3.get (base + 2) = some (.i64 Lw) := by rw [get3]; simpa using getL
  have count3 : s3.get (base + 3) = some (.i64 0) := by rw [get3]; simp
  have below3 : ∀ j, j < base → s3.get j = s.get j := fun j hj =>
    outside3.others j (Or.inl hj)
  change wp _ _ _ _ s3 _
  simp only [wp_localGet_cons, errno3, wp_eqzI64_cons]
  refine wp_iff_cons rfl ?_
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hHandleSmall : handle.toNat < 4294967296 := by
      rw [← hRejectEq] at hAccepted
      by_contra large
      simp [large] at hAccepted
    have hRejectZero : call.reject ([.word handle, .space (buffer.windowLength start count)] ++
        extra.map .word) = 0 := by
      rw [hReject, hAccepted]
    simp only [sysIovecReadCallCodeWith, List.getD_cons_zero, List.getElem?_cons_succ,
      List.append_assoc]
    rw [show extraLocs[0]? = extraLocs.head? by cases extraLocs <;> rfl]
    refine wp_metadata address3 length3 hMemory ?_
    let middle := initializeScratch initial P.toUInt32 Lw.toUInt32
    have hScratch : GuestFrame initial middle [ABI.scratch] :=
      GuestFrame.ofScratchWrites (initializeScratch_range initial _ _)
    have hPagesMiddle : middle.mem.pages = initial.mem.pages := hScratch.pages
    have hElement := element_written initial P.toUInt32 Lw.toUInt32 hMemory
    have hLw32 : Lw.toUInt32.toNat = Lw.toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hLwSmall]
    rw [hLw32] at hElement
    have hExtraHeld3 := held_transfer hExtraHeld fun place member =>
      below3 place (hLocs place (by simp [member]))
    refine wp_iovec_read_call_with (root := P) (capacity := Lw) hImports hHost hCall hParams
      hExtra hHandleSmall hLwSmall ((below3 handleLocal hHandleBelow).trans hHandle)
      (by
        rw [head_toList_of_length (by rw [hExtraHeld3.length_eq, hExtra]; split <;> omega)]
        exact hExtraHeld3)
      hElement (by rw [hPagesMiddle]; exact hMemory)
      (by rw [hPagesMiddle]; exact hMem) hFits hSep ?_ ?_
    · intro after errno outputs hSys hFrame hShown
      have hFrame' : GuestFrame initial after [ABI.scratch, (P.toNat, Lw.toNat)] := by
        refine (hScratch.weaken fun region member => ?_).trans (hFrame.cover fun region member => ?_)
        · rw [List.mem_singleton] at member
          subst member
          exact List.mem_cons_self ..
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), le_rfl, le_rfl⟩
          · exact ⟨ABI.scratch, List.mem_cons_self .., by decide, by decide⟩
      have hFrameWindow : GuestFrame initial after [ABI.scratch, (root.toNat + first, length)] := by
        rw [hAddrNat, hLength] at hFrame'
        exact hFrame'
      have hBound := (observedHost host).sys_bound hSys
      have hErrno : errno.toNat ≤ 76 := hBound.2
      have hSizes : outputs.map (fun output => output.data.size) = [Lw.toNat, 4] := by
        have h : outputs.map (fun output => output.data.size) =
            outputSizesOf call.params (host.reported middle.host.world call)
              ([.word handle, .space Lw] ++ extra.map .word) := hBound.1
        rw [h, hParams, iovec_read_sizes offset handle Lw hExtra]
      have hSys' : (observedHost host).sys initial.host call
          ([.word handle, .space (buffer.windowLength start count)] ++ extra.map .word)
          (.returned errno outputs) after.host := by
        rw [← hLengthEq]; exact hSys
      have hExec : Exec (observedHost host)
          (.sys call (flatArgsWith call.params (lowerWords call.params
            (handle :: start :: count :: extra) [buffer]) []) Action.pure) initial.host
          [.sys call ([.word handle, .space (buffer.windowLength start count)] ++
            extra.map .word) (.returned errno outputs)]
          (.returned (sysReply errno outputs)) after.host := by
        rw [hArgs]
        exact .sys_return hRejectZero hSys' (.pure after.host _)
      simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
      have hLow3 : s3.params.length ≤ base := by rw [outside3.params]; exact hLow
      have hHigh3 : base + 5 < s3.params.length + s3.locals.length := by
        rw [outside3.params, outside3.length]; omega
      refine wp_localSet_local hLow3 (by omega) ?_
      let s4 := setLocal { s3 with values := s3.values } base (.i64 errno)
      have get4 : ∀ j, j ≠ base → s4.get j = s3.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { s3 with values := s3.values }) hLow3 hj
      have errno4 : s4.get base = some (.i64 errno) :=
        Locals.get_setLocal_same (s := { s3 with values := s3.values }) hLow3 (by omega)
      have outside4 : LocalsOutside s s4 base 6 :=
        (outside3.values s3.values).set hLow le_rfl (by omega)
      have hHigh4 : base + 3 < s4.params.length + s4.locals.length := by
        rw [outside4.params, outside4.length]; omega
      have hLow4 : s4.params.length ≤ base + 3 := by rw [outside4.params]; omega
      change wp _ _ _ _ s4 _
      simp only [wp_localGet_cons, errno4, wp_eqzI64_cons]
      refine wp_iff_cons rfl ?_
      by_cases hZero : errno = 0
      · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
        obtain ⟨bytes, countBytes, rfl, hBytesAt, hCountAt⟩ := hShown hZero
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hSizes
        obtain ⟨hBufferSize, hCountSize⟩ := hSizes
        have hReply : sysReply errno [bytes, countBytes] = ⟨errno, [bytes, countBytes]⟩ := by
          simp [sysReply, hZero]
        have hCountWord := littleEndian_read32 hCountAt hCountSize
        have h8 : (8 : UInt64).toUInt32 = 8 := rfl
        rw [h8] at hCountWord
        simp only [readCountCode, List.cons_append, List.nil_append, List.append_assoc,
          wp_const_cons, wp_load32_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
        rw [ite_eq_right (by
          have hp := hFrameWindow.pages
          simp only [UInt32.reduceToNat, gt_iff_lt, not_lt]
          omega)]
        simp only [wp_extendUI32_cons]
        rw [hCountWord]
        refine wp_localSet_local hLow4 hHigh4 ?_
        let s5 := setLocal { s4 with values := s4.values } (base + 3)
          (.i64 (littleEndian countBytes))
        have word5 : s5.get (base + 3) = some (.i64 (littleEndian countBytes)) :=
          Locals.get_setLocal_same (s := { s4 with values := s4.values }) hLow4 hHigh4
        have get5 : ∀ j, j ≠ base + 3 → s5.get j = s4.get j := fun j hj =>
          Locals.get_setLocal_ne (s := { s4 with values := s4.values }) hLow4 hj
        have length5 : s5.get (base + 2) = some (.i64 Lw) := by
          rw [get5 _ (by omega), get4 _ (by omega)]; exact length3
        have outside5 : LocalsOutside s s5 base 6 :=
          (outside4.values s4.values).set hLow (by omega) (by omega)
        refine wp_min_code word5 length5 ?_
        have hLow5 : s5.params.length ≤ base + 3 := by rw [outside5.params]; omega
        have hHigh5 : base + 3 < s5.params.length + s5.locals.length := by
          rw [outside5.params, outside5.length]; omega
        refine wp_localSet_local hLow5 hHigh5 ?_
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        refine afterCall after _ _ (sysReply errno [bytes, countBytes]) hExec hFrameWindow
          (fun _ => ?_) (((outside5.values _).set hLow (by omega) (by omega)).values _)
          (by simp only [List.take_zero, List.nil_append, List.drop_zero]; exact values1)
          ?_ ?_ ?_ ?_
        · rw [hReply]
          refine ⟨by
            simp only [Reply.bytes, List.getElem?_cons_zero, Option.getD_some]
            rw [hBufferSize, hLength], fun i hi => ?_⟩
          have := hBytesAt.contents i hi
          rw [hAddrNat] at this
          exact this
        · rw [Locals.get_values, Locals.get_setLocal_ne (s := { s5 with values := s5.values })
            hLow5 (by omega), get5 _ (by omega)]
          simpa [sysReply, hZero] using errno4
        · rw [Locals.get_values, Locals.get_setLocal_ne (s := { s5 with values := s5.values })
            hLow5 (by omega), get5 _ (by omega), get4 _ (by omega)]
          exact address3
        · rw [Locals.get_values, Locals.get_setLocal_ne (s := { s5 with values := s5.values })
            hLow5 (by omega), length5]
        · rw [Locals.get_values, Locals.get_setLocal_same (s := { s5 with values := s5.values })
            hLow5 hHigh5, hReadFill, hReply]
          simp only [FillResult.of, hZero, ite_true, readLength_eq_min, Reply.word, ← hLengthEq]
          rfl
      · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, hZero]
        refine afterCall after _ _ (sysReply errno outputs) hExec hFrameWindow
          (fun zero => absurd (by simpa [hReply] using zero) hZero) (outside4.values _)
          (by simp only [List.take_zero, List.nil_append, List.drop_zero]; exact values1)
          (by rw [Locals.get_values, hReply]; exact errno4) ?_ ?_ ?_
        · rw [Locals.get_values, get4 _ (by omega)]
          exact address3
        · rw [Locals.get_values, get4 _ (by omega)]
          exact length3
        · rw [Locals.get_values, get4 _ (by omega), count3, hReadFill]
          simp [FillResult.of, hReply, hZero]
    · intro final message outputs hSys
      exact hTrap final message _ (by
        rw [hArgs]
        exact .sys_trap hRejectZero (by rw [← hLengthEq]; exact hSys))
  · rw [ite_eq_right (by simp [hAccepted] : ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
    have hRejectNe : call.reject ([.word handle, .space (buffer.windowLength start count)] ++
        extra.map .word) ≠ 0 := by
      rw [hReject]; exact hAccepted
    refine afterCall initial _ [] ⟨reject, []⟩ (by
        rw [hArgs, ← hReject]
        exact .sys_reject hRejectNe (.pure initial.host _))
      (GuestFrame.refl _ _) (fun zero => absurd zero hAccepted)
      (outside3.values _) values3 errno3 address3 length3 ?_
    rw [count3, hReadFill]
    simp [FillResult.of, hAccepted]

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
    (hInputAt : ∀ input ∈ inputs,
      (Bytes.At initial.mem input.1 input.2 ∧ input.1.toNat < 4294967296) ∧
        regionsDisjoint (input.1.toNat, input.2.data.size) ABI.scratch)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
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
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
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
      (fun region => regionsDisjoint region ABI.low) heap (PureTransport.erase initial)
      (Bytes.regions (PureTransport.erase initial) 0) := by
    simpa only [Bytes.regions, ite_true] using
      Step.refl hHeap (fun region => regionsDisjoint region ABI.low)
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
    obtain ⟨⟨hInputAt, hRootSmall⟩, hApart⟩ := hInputAt input (List.mem_singleton_self _)
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
          (fun region => regionsDisjoint region ABI.low) heap (PureTransport.erase after)
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

theorem iovec_write_lower (offset : Bool) (handle start count : UInt64) (extra : List UInt64)
    (input : LeanExe.Bytes) (hExtra : extra.length = if offset then 1 else 0) :
    lowerWords (iovecParams true offset) (handle :: start :: count :: extra) [] = handle :: extra ∧
      lowerInputs (iovecParams true offset) (handle :: start :: count :: extra) [input] =
        [input.range start count] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- The code of a write of the window of the input whose root and length lie in the two locals
from `inputLocal`, from the handle, the window's start and count, and the offset of `fd_pwrite` in
their locals to the errno and the count on the stack. -/
theorem wp_sys_iovec_window_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World}
    (hImports : target.imports = ABI.importsWith calls) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {offset : Bool} {locs : List Nat} {values : List UInt64}
    {inputLocal : Nat} {root size : UInt64} {input : LeanExe.Bytes}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams true offset)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argWords)
    (hLocs : ∀ place ∈ locs, place < base)
    (hRoot : s.get inputLocal = some (.i64 root))
    (hSize : s.get (inputLocal + 1) = some (.i64 size)) (hInputBelow : inputLocal + 2 ≤ base)
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size input)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 8 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host) (.sys call (sysArgs call.params values [input] []) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      LocalsOutside s finalLocals base 8 →
      wp target rest Q final { finalLocals with values :=
        [Value.i64 (reply.word 0), Value.i64 reply.errno] ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.sys call (sysArgs call.params values [input] []) Action.pure)
        initial.host trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysIovecWindowCodeWith calls call locs inputLocal base ++ rest) Q initial s env := by
  have hPositions : base + 8 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hLength3 : values.length = 1 + (2 + if offset then 1 else 0) := by
    rw [hCount, Call.argWords, hParams]
    cases offset <;> rfl
  obtain ⟨handleLocal, rest1, handle, rest2, rfl, rfl, hHandle, held1, length1⟩ :=
    iovec_held hHeld hLength3
  obtain ⟨startLocal, rest3, start, rest4, rfl, rfl, hStartLocal, held2, length2⟩ :=
    iovec_held (count := 1 + if offset then 1 else 0) held1 (by rw [length1]; omega)
  obtain ⟨countLocal, extraLocs, count, extra, rfl, rfl, hCountLocal, hExtraHeld, hExtra⟩ :=
    iovec_held (count := if offset then 1 else 0) held2 (by omega)
  obtain ⟨hLowerWords, hLowerInputs⟩ := iovec_write_lower offset handle start count extra input
    hExtra
  have hArgs : sysArgs call.params (handle :: start :: count :: extra) [input] [] =
      flatArgsWith call.params (handle :: extra)
        ([((root + windowFirstWord size start), input.range start count)].map Prod.snd) := by
    simp only [sysArgs, hParams, hLowerWords, hLowerInputs, List.map_cons, List.map_nil]
  obtain ⟨hFirst, hLength, hLengthEq⟩ := window_words hRep.length_eq start count
  obtain ⟨_, _, hAddrNat, _, hFits, _, hSep⟩ := window_at hRep hHeap start count
  have hStartBelow := hLocs startLocal (by simp)
  have hCountBelow := hLocs countLocal (by simp)
  simp only [sysIovecWindowCodeWith, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
    List.drop_zero, List.append_assoc]
  refine wp_window_code hRoot hSize hStartLocal hCountLocal (by omega) (by omega) hLow
    (by omega) ?_
  intro s1 outside1 values1 getP getL
  have hRangeSize : (input.range start count).data.size = (input.window start count).2 :=
    LeanExe.Bytes.range_size input start count
  have hSizeWord : windowLengthWord size start count =
      LeanExe.Bytes.size (input.range start count) := by
    rw [hLengthEq]
    simp only [LeanExe.Bytes.windowLength, LeanExe.Bytes.size, hRangeSize]
  have hRangeSmall : (input.range start count).data.size < 2 ^ 32 := by
    rw [hRangeSize, ← hLength]
    have := hFits
    omega
  have below1 : ∀ j, j < base → s1.get j = s.get j := fun j hj => outside1.others j (Or.inl hj)
  have hAt := bytes_at_window (start := start) (count := count) (hRep.toAt hHeap)
    hAddrNat
  rw [show (PureTransport.erase initial).mem = initial.mem from rfl] at hAt
  refine wp_sys_iovec_write_with (base := base + 2) (locs := handleLocal :: extraLocs)
    (values := handle :: extra) (inputLocs := [base])
    (inputs := [(root + windowFirstWord size start, input.range start count)]) hImports hHost
    hCall hParams (.cons ((below1 _ (hLocs handleLocal (by simp))).trans hHandle)
      (held_transfer hExtraHeld fun place member =>
        below1 place (hLocs place (by simp [member]))))
    (by rw [iovec_wordCount hParams]; simp [hExtra]; omega)
    (fun place member => by
      rcases List.mem_cons.mp member with same | member
      · have := hLocs handleLocal (by simp)
        omega
      · have := hLocs place (by simp [member]); omega)
    (.cons ⟨getP, by rw [getL, hSizeWord], hRangeSmall⟩ .nil)
    (by rw [iovec_inputCount hParams]; rfl) (fun place member => by
      rw [List.mem_singleton] at member
      omega)
    (fun item member => by
      rw [List.mem_singleton] at member
      subst member
      dsimp only
      refine ⟨⟨hAt, by have := hFits; omega⟩, ?_⟩
      simp only [LeanExe.Runtime.regionsDisjoint, ABI.scratch, hRangeSize, ← hLength]
      rcases hSep with high | ⟨zero, address⟩
      · omega
      · rw [address, zero]
        simp)
    hHeap (by rw [outside1.params]; omega)
    (by
      have := hHigh
      simp only [Locals.positions] at this ⊢
      rw [outside1.params, outside1.length]
      omega) ?_ ?_
  · intro final finalLocals trace reply execution step outsideF
    rw [values1]
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append] using
      hNext final finalLocals trace reply (by rw [hArgs]; exact execution) step
        ((outside1.widen (by omega) (by omega)).trans (outsideF.widen (by omega) (by omega)))
  · intro final message trace execution
    exact hTrap final message trace (by rw [hArgs]; exact execution)

end Verified.Wasi
