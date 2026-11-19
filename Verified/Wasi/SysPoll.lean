import Verified.Wasi.SysPollParts

/-! The code of a `poll` call, from the argument test to the errno, the number of events, and the
fields of the first event on the stack: the test of the fields' words, the locals of the result
set to 0, the accepted call with its block, and the pushes.  The block is released after the call
whatever the errno, so the result holds no heap value. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## The test of the fields -/

/-- The test of the fields leaves the errno that `rejectFields` gives. -/
theorem wp_fields_reject {α : Type} {m : Module} {st : Store α} {env : HostEnv α} :
    ∀ (fields : List Field) (locs : List Nat) (values : List UInt64) (s : Locals)
      (rest : Program) (Q : Assertion α),
      List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
      values.length = fields.length →
      wp m rest Q st
        { s with values := .i64 (rejectFields fields (values.map .word)) :: s.values } env →
      wp m (fieldsRejectCode fields locs ++ rest) Q st s env
  | [], locs, values, s, rest, Q, held, length, h => by
    have hNil : values = [] := List.eq_nil_of_length_eq_zero length
    subst hNil
    cases held
    simpa only [fieldsRejectCode, rejectFields, List.map_nil, List.cons_append, List.nil_append,
      wp_constI64_cons] using h
  | field :: fields, locs, values, s, rest, Q, held, length, h => by
    cases held with
    | nil => simp at length
    | @cons place value locs values hPlace held =>
    have hRest : values.length = fields.length := by simpa using length
    by_cases hWide : field.width < 8
    · have hPower : (UInt64.ofNat (2 ^ (8 * field.width))).toNat = 2 ^ (8 * field.width) :=
        UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 2 ^ 64 from rfl]
          exact Nat.pow_lt_pow_right (by decide) (by omega))
      simp only [fieldsRejectCode, hWide, ite_true, List.cons_append, wp_localGet_cons, hPlace,
        wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      by_cases hSmall : value.toNat < 2 ^ (8 * field.width)
      · have hNot : ¬UInt64.ofNat (2 ^ (8 * field.width)) ≤ value := by
          rw [UInt64.le_iff_toNat_le, hPower]; omega
        rw [ite_eq_right (by simp [hNot])]
        rw [← List.append_nil (fieldsRejectCode fields locs)]
        refine wp_fields_reject fields locs values _ [] _
          (by simpa only [Locals.get_values] using held) hRest ?_
        simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
          List.drop_zero]
        simpa [rejectFields, Arg.value, hSmall] using h
      · have hYes : UInt64.ofNat (2 ^ (8 * field.width)) ≤ value := by
          rw [UInt64.le_iff_toNat_le, hPower]; omega
        rw [ite_eq_left (by simp [hYes])]
        simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
          List.cons_append, List.nil_append, List.drop_zero]
        simpa [rejectFields, Arg.value, hSmall] using h
    · have hSmall : value.toNat < 2 ^ (8 * field.width) :=
        Nat.lt_of_lt_of_le value.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
      simp only [fieldsRejectCode, hWide, ite_false]
      refine wp_fields_reject fields locs values s rest Q held hRest ?_
      simpa [rejectFields, Arg.value, hSmall] using h

/-! ## The host call -/

/-- The host call of a `poll` request whose subscriptions lie at `pointer` and whose events follow
them: the code pushes the core arguments and calls the import, and the call's specification
gives the errno, the frame of the events and the result word, and on errno 0 the events and the
count. -/
theorem wp_poll_call_with {calls : List LeanExe.Wasi.Call} {World : Type} {m : Module}
    {host : Host World} {env : HostEnv (Observed World)} {store : Store (Observed World)}
    {s : Locals} {call : LeanExe.Wasi.Call} {records : List (List Field)} {values : List UInt64}
    {pointerLocal : Nat} {pointer : UInt64} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = [.subscriptions records, .result32])
    (hFits : recordsFit records = true)
    (hLength : values.length = (argFields records).length)
    (hAccepted : rejectFields (argFields records) (values.map .word) = 0)
    (hPointer : s.get pointerLocal = some (.i64 pointer))
    (hSubscriptions : Bytes.At store.mem pointer (subscriptionBytes records (values.map .word)))
    (hBlock : pointer.toNat + 80 * records.length ≤ store.mem.pages * 65536)
    (hAddress : pointer.toNat + 80 * records.length < 4294967296)
    (hAligned : pointer.toNat % 8 = 0) (hLow : 16 ≤ pointer.toNat)
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call (values.map .word) (.returned errno outputs)
        final.host →
      GuestFrame store final
        [(pointer.toNat + 48 * records.length, 32 * records.length), (0, 4)] →
      (errno = 0 → ∃ events count, outputs = [events, count] ∧
        Bytes.At final.mem (pointer + UInt64.ofNat (48 * records.length)) events ∧
        Bytes.At final.mem 0 count) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call (values.map .word) (.trapped message outputs)
        final.host → Q (.Trap final message)) :
    wp m ([.localGet pointerLocal, .wrapI64, .localGet pointerLocal,
      .constI64 (UInt64.ofNat (48 * records.length)), .addI64, .wrapI64,
      .const (UInt32.ofNat records.length), .const 0, .call (3 + calls.idxOf call)] ++ rest) Q
      store s env := by
  have hPointer32 : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hFortyEight : (UInt64.ofNat (48 * records.length)).toNat = 48 * records.length :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hEvents : (pointer + UInt64.ofNat (48 * records.length)).toNat =
      pointer.toNat + 48 * records.length := by
    rw [UInt64.toNat_add, hFortyEight]
    exact Nat.mod_eq_of_lt (by omega)
  have hEvents32 : (pointer + UInt64.ofNat (48 * records.length)).toUInt32.toNat =
      pointer.toNat + 48 * records.length := by
    rw [UInt64.toNat_toUInt32, hEvents, Nat.mod_eq_of_lt (by omega)]
  let events32 := (pointer + UInt64.ofNat (48 * records.length)).toUInt32
  let args : List Arg := values.map .word
  have hRequest : ∀ sizes, SysRequest store
      (lowerArgs call.params args [pointer.toUInt32, events32, 0]) call args
      [pointer.toUInt32, events32, 0] sizes := by
    intro sizes
    have hRegions := poll_regions records sizes args pointer.toUInt32 events32
    have hPlaces := poll_places records args pointer.toUInt32 events32
    rw [← hParams] at hRegions hPlaces
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hParams]
      simp only [argsFit, Param.takesArg, Bool.false_eq_true, ite_false, Bool.and_eq_true, hFits,
        true_and]
      refine ⟨argFieldsFit_of_reject _ values hLength hAccepted, ?_⟩
      simp [args, ← hLength]
    · change rejectArgs call.params args = 0
      rw [hParams, poll_reject]
      exact hAccepted
    · rw [hPlaces]
      intro place member
      rw [List.mem_singleton] at member
      subst member
      simpa only [read_narrow64 pointer (by omega)] using hSubscriptions
    · rw [hRegions]
      intro region member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [events32, hEvents32]
        refine ⟨by omega, by omega, ?_⟩
        omega
      · simp only [UInt32.reduceToNat]
        exact ⟨by omega, by decide, by decide⟩
    · rw [hRegions]
      simp only [List.map_cons, List.map_nil, Region.span, events32, hEvents32, UInt32.reduceToNat,
        List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true, regionsDisjoint]
      omega
    · rw [hRegions, hPlaces]
      intro region member place placeMember
      rw [List.mem_singleton] at placeMember
      subst placeMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [subscriptionBytes_size]
      rcases member with rfl | rfl
      · simp only [Region.span, events32, hEvents32, hPointer32, regionsDisjoint]
        omega
      · simp only [Region.span, hPointer32, UInt32.reduceToNat, regionsDisjoint]
        omega
  have hLower := poll_lower records args pointer.toUInt32 events32
  rw [← hParams] at hLower
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, hPointer, Locals.get_values,
    wp_wrapI64_cons, wrap_toUInt32, wp_constI64_cons, wp_addI64_cons, wp_const_cons]
  obtain ⟨hTake, hDrop⟩ := call_stack_take (call := call) s.values
    (lowerArgs_length call.params args [pointer.toUInt32, events32, 0])
  have hStack : Value.i32 0 :: Value.i32 (UInt32.ofNat records.length) :: Value.i32 events32 ::
      Value.i32 pointer.toUInt32 :: s.values =
      (lowerArgs call.params args [pointer.toUInt32, events32, 0]).reverse ++ s.values := by
    rw [hLower]
    rfl
  rw [hStack]
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  refine wp_call_host_contract (id := 3 + calls.idxOf call) (imp := ABI.callImport call)
    (c := sysContract host call) (by rw [hImports]; exact ABI.importsWith_call hCall) hHost
    (by rw [hImports, ABI.importsWith_length]; omega) (hostSpecWith_sys host hCall) ?_ ?_ ?_
  · intro returned final contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨errno, outputs, rfl, hSys, hFrame, hShown⟩ := contract _ _ (hRequest _)
    have hRegions := poll_regions records (host.reported store.host.world call) args
      pointer.toUInt32 events32
    rw [← hParams] at hRegions
    have hFrame' : GuestFrame store final
        [(pointer.toNat + 48 * records.length, 32 * records.length), (0, 4)] := by
      have h := hFrame
      simp only [hRegions, List.map_cons, List.map_nil, Region.span, events32, hEvents32,
        UInt32.reduceToNat] at h
      exact h
    have hShown' : errno = 0 → ∃ events count, outputs = [events, count] ∧
        Bytes.At final.mem (pointer + UInt64.ofNat (48 * records.length)) events ∧
        Bytes.At final.mem 0 count := by
      intro hZero
      have h := hShown hZero
      simp only [hRegions] at h
      match outputs, h with
      | [events, count], h =>
        simp only [ShownAt, ite_true] at h
        obtain ⟨atEvents, atCount, _⟩ := h
        refine ⟨events, count, rfl, ?_, atCount⟩
        rwa [read_narrow64 _ (by rw [hEvents]; omega)] at atEvents
      | [], h => simp [ShownAt] at h
      | [_], h => simp [ShownAt] at h
      | _ :: _ :: _ :: _, h => simp [ShownAt] at h
    rw [hDrop]
    simpa only [ABI.callImport, ABI.callType, List.length_cons, List.length_nil, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
      hNext final errno outputs hSys hFrame' hShown'
  · intro final message contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨outputs, hSys, _⟩ := contract _ _ (hRequest _)
    exact hTrap final message outputs hSys
  · intro final tag arguments contract
    rw [hTake, List.reverse_reverse] at contract
    exact (contract _ _ (hRequest _)).elim

/-! ## The accepted call -/

theorem pollWords_length (reply : Reply) : (pollWords reply).length = 6 := rfl

theorem pollWords_reply (errno : UInt64) (events count : LeanExe.Bytes) :
    pollWords ⟨errno, [events, count]⟩ = littleEndian count :: fieldWords events eventFields :=
  rfl

theorem pollWords_empty (errno : UInt64) (i : Nat) : (pollWords ⟨errno, []⟩).getD i 0 = 0 := by
  have hField : ∀ field : Nat × Nat, (⟨errno, []⟩ : Reply).field 0 field.1 field.2 = 0 :=
    fun field => field_empty errno field.1 field.2
  simp only [pollWords, eventFields, List.map_cons, List.map_nil, hField]
  have hWord : (⟨errno, []⟩ : Reply).word 1 = 0 := rfl
  rw [hWord]
  rcases (show i < 6 ∨ 6 ≤ i by omega) with small | large
  · interval_cases i <;> rfl
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
    rfl

theorem eventFields_fit {size : Nat} (hSize : 32 ≤ size) : fieldsFit size eventFields := by
  intro field member
  simp only [eventFields, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- An accepted `poll` request: the allocation of the block, the subscriptions' pointer, the
subscriptions, the call, the loads of the number of events and of the first event's fields on
errno 0, and the release of the block, with the continuation `K` of the enclosing `iff`. -/
theorem wp_sys_poll_accept_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {records : List (List Field)} {locs : List Nat}
    {values : List UInt64} {s0 s : Locals} {base : Nat} {aborts : Bool}
    {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = [.subscriptions records, .result32])
    (hFit : subscriptionsFit records = true)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hLength : values.length = (argFields records).length)
    (hAccepted : rejectFields (argFields records) (values.map .word) = 0)
    (hLocs : ∀ place ∈ locs, place < base)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s0.params.length ≤ base) (hHigh : base + 9 ≤ s0.positions)
    (hOutside : LocalsOutside s0 s base 9)
    (hZero : ∀ i, i < 6 → s.get (base + 3 + i) = some (.i64 0))
    (hRoom : aborts = false → heap.Room (PureTransport.erase initial) source
      (allocSize (UInt64.ofNat (80 * records.length + 7))))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → K (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call (values.map .word) (.returned errno outputs)
        final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap' (PureTransport.erase final) [] →
      heap'.top.toNat ≤ heap.top.toNat + Bytes.allocationCost (80 * records.length + 7) →
      LocalsOutside s0 sF base 9 → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      (∀ i, i < 6 → sF.get (base + 3 + i) =
        some (.i64 ((pollWords (sysReply errno outputs)).getD i 0))) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call (values.map .word) (.trapped message outputs)
        final.host → K (.Trap final message)) :
    wp target (sysPollCallCodeWith calls call records locs base) K initial s env := by
  obtain ⟨hNonempty, hFits, hWidths, hBlock⟩ := subscriptionsFit_facts hFit
  have hBlockNat : (UInt64.ofNat (80 * records.length + 7)).toNat = 80 * records.length + 7 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hCostEq := Verified.Bytes.allocationCost_eq
    (count := UInt64.ofNat (80 * records.length + 7)) (by rw [hBlockNat]; omega)
    (by rw [hBlockNat]; omega)
  rw [hBlockNat] at hCostEq
  have hPositions : base + 9 ≤ s0.params.length + s0.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have bound := fun (t : Locals) (outside : LocalsOutside s0 t base 9) i
    (hi : base ≤ i) (hi' : i < base + 9) =>
    outside.bounds hLow (by omega) hi hi'
  -- The allocation of the block.
  simp only [sysPollCallCodeWith, List.append_assoc, List.cons_append, List.nil_append,
    wp_constI64_cons]
  refine wp_alloc_frame_with (s := s) (values := s.values) runtime layout profile hImports
    sourceHost hHeap (by rw [hBlockNat]; omega) hCap hRoom hResource ?_
  intro allocated hHeapFits hStore hWorld
  obtain ⟨hAllocate, hBuffer, hCapacity, hTopAlloc⟩ :=
    read_allocation_buffer hHeap (by rw [hBlockNat]; omega) hHeapFits hStore
  let root := FixedArrayAllocate.root heap.top
    (allocSize (UInt64.ofNat (80 * records.length + 7))) heap.free
  have hBefore : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.low)
      (heap.allocate (allocSize (UInt64.ofNat (80 * records.length + 7))))
      (PureTransport.erase allocated) (Bytes.regions (PureTransport.erase allocated) root) := by
    have hRoot : root ≠ 0 := hBuffer.nonzero
    rw [Bytes.regions, ite_eq_right hRoot]
    exact hAllocate.mono
      (keep' := fun region => regionsDisjoint region ABI.low)
      (fresh' := [block (PureTransport.erase allocated) root])
      (fun _ _ => True.intro) (fun _ h => h)
  have hReady : ReadReady (heap.allocate (allocSize (UInt64.ofNat (80 * records.length + 7))))
      (PureTransport.erase allocated) root (UInt64.ofNat (80 * records.length + 7)) :=
    Or.inr ⟨_, hBuffer, hCapacity⟩
  have hRootAddress := hReady.address
  have hRootMemory := hReady.memory hBefore.at_
  rw [hBlockNat] at hRootAddress hRootMemory
  have hRootBase : 16 ≤ root.toNat := by
    have h : 4096 + 48 ≤ root.toNat := hBuffer.object.base
    omega
  have b1 := bound s hOutside (base + 1) (by omega) (by omega)
  refine wp_localSet_local b1.1 b1.2 ?_
  let sA := setLocal { s with values := s.values } (base + 1) (.i64 root)
  have outsideA : LocalsOutside s0 sA base 9 :=
    (hOutside.values s.values).set hLow (by omega) (by omega)
  have hRootA : sA.get (base + 1) = some (.i64 root) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) b1.1 b1.2
  have hOtherA : ∀ j, j ≠ base + 1 → sA.get j = s.get j := fun j hj =>
    Locals.get_setLocal_ne (s := { s with values := s.values }) b1.1 hj
  change wp target (recordAddressCode base 8 ++ _) K allocated sA env
  -- The subscriptions' pointer.
  simp only [recordAddressCode, List.cons_append, List.nil_append, wp_localGet_cons, hRootA,
    wp_constI64_cons, wp_addI64_cons]
  have b2 := bound sA outsideA (base + 2) (by omega) (by omega)
  refine wp_localSet_local b2.1 b2.2 ?_
  let sB := setLocal { sA with values := sA.values } (base + 2)
    (.i64 (root + UInt64.ofNat (8 - 1)))
  have hGetB : sB.get (base + 2) = some (.i64 (root + UInt64.ofNat (8 - 1))) :=
    Locals.get_setLocal_same (s := { sA with values := sA.values }) b2.1 b2.2
  have outsideB : LocalsOutside s0 sB base 9 :=
    (outsideA.values sA.values).set hLow (by omega) (by omega)
  change wp target (.localGet (base + 2) :: _) K allocated sB env
  simp only [wp_localGet_cons, hGetB, Locals.get_values, wp_constI64_cons, wp_remUI64_cons,
    show UInt64.ofNat 8 ≠ 0 by decide, ite_false, wp_subI64_cons]
  have b2B := bound sB outsideB (base + 2) (by omega) (by omega)
  refine wp_localSet_local b2B.1 b2B.2 ?_
  let pointer := recordAddress root 8
  let sC := setLocal { sB with values := sB.values } (base + 2) (.i64 pointer)
  have hPointerC : sC.get (base + 2) = some (.i64 pointer) :=
    Locals.get_setLocal_same (s := { sB with values := sB.values }) b2B.1 b2B.2
  have hOtherC : ∀ j, j ≠ base + 2 → sC.get j = sA.get j := fun j hj =>
    (Locals.get_setLocal_ne (s := { sB with values := sB.values }) b2B.1 hj).trans
      (Locals.get_setLocal_ne (s := { sA with values := sA.values }) b2.1 hj)
  have outsideC : LocalsOutside s0 sC base 9 :=
    (outsideB.values sB.values).set hLow (by omega) (by omega)
  have hOtherCs : ∀ j, j ≠ base + 1 → j ≠ base + 2 → sC.get j = s.get j := fun j h1 h2 =>
    (hOtherC j h2).trans (hOtherA j h1)
  have hRootC : sC.get (base + 1) = some (.i64 root) := (hOtherC (base + 1) (by omega)).trans hRootA
  obtain ⟨hPointerLow, hPointerHigh, hAligned⟩ : root.toNat ≤ pointer.toNat ∧
      pointer.toNat + 1 ≤ root.toNat + 8 ∧ pointer.toNat % 8 = 0 :=
    recordAddress_spec (root := root) (align := 8) (by decide) (by omega)
  have hHeldC := held_transfer hHeld fun place member =>
    hOtherCs place (by have := hLocs place member; omega) (by have := hLocs place member; omega)
  -- The subscriptions.
  have hBlockFit : pointer.toNat + 80 * records.length ≤ allocated.mem.pages * 65536 := by
    change _ ≤ (PureTransport.erase allocated).mem.pages * 65536
    omega
  change wp target (zeroWordsCode (base + 2) 0 (6 * records.length) ++ _) K allocated sC env
  refine wp_zero_words (before := allocated.mem) (size := 48 * records.length) hPointerC
    (by omega) (by omega) (6 * records.length) 0 allocated _ (BlockAt.refl allocated.mem _ _)
    (by omega) ?_
  intro zeroed hZeroed
  refine wp_field_stores (before := allocated.mem) (size := 48 * records.length) hPointerC
    (by omega) (by omega) (placedFields 0 records) locs values { allocated with mem := zeroed } []
    hHeldC (by rw [hLength]; rfl) hWidths (hZeroed.congr fun i hi => ?_) ?_
  · simp only [blockFold, List.foldl_nil]
    exact ite_eq_left (by omega)
  intro stored hStored
  have hSubscriptions : Bytes.At stored pointer (subscriptionBytes records (values.map .word)) := by
    have h := hStored.at_ (bytes := subscriptionBytes records (values.map .word))
      (subscriptionBytes_size _ _) (fun i hi => by
        rw [subscriptionBytes_get, List.nil_append]
        rfl) (by omega) (by omega)
    rwa [UInt64.ofNat_toNat] at h
  have hStoresFrame : GuestFrame allocated { allocated with mem := stored }
      [(pointer.toNat, 48 * records.length)] := hStored.frame
  let middle : Store (Observed World) := { allocated with mem := stored }
  change wp target _ K middle sC env
  -- The host call.
  refine wp_poll_call_with (pointer := pointer) hImports hHost hCall hParams hFits hLength
    hAccepted hPointerC hSubscriptions (by rw [hStoresFrame.pages]; exact hBlockFit) (by omega)
    hAligned (by omega) ?_ ?_
  · intro after errno outputs hSys hFrame hShown
    have hFrame' : GuestFrame allocated after
        [ABI.scratch, (root.toNat, (UInt64.ofNat (80 * records.length + 7)).toNat)] := by
      refine (hStoresFrame.cover fun region member => ?_).trans
        (hFrame.cover fun region member => ?_)
      · rw [List.mem_singleton] at member
        subst member
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by simp only; omega,
          by simp only; rw [hBlockNat]; omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by simp only; omega,
            by simp only; rw [hBlockNat]; omega⟩
        · exact ⟨ABI.scratch, List.mem_cons_self .., by decide, by decide⟩
    have hStep := hReady.frame_step hBefore hFrame'
    have hEmpty := hReady.empty_rep hBefore.at_ hFrame'
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hOutputSizes : outputs.map (fun output => output.data.size) =
        [32 * records.length, 4] := by
      have h : outputs.map (fun output => output.data.size) =
          outputSizesOf call.params (host.reported middle.host.world call) (values.map .word) :=
        hBound.1
      rw [h, hParams, poll_sizes]
    have hSys' : (observedHost host).sys initial.host call (values.map .word)
        (.returned errno outputs) after.host := by
      rw [← hWorld]; exact hSys
    simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
    have bE := bound sC outsideC base le_rfl (by omega)
    refine wp_localSet_local bE.1 bE.2 ?_
    let sE := setLocal { sC with values := sC.values } base (.i64 errno)
    have hGetE : sE.get base = some (.i64 errno) :=
      Locals.get_setLocal_same (s := { sC with values := sC.values }) bE.1 bE.2
    have hOtherE : ∀ j, j ≠ base → sE.get j = sC.get j := fun j hj =>
      Locals.get_setLocal_ne (s := { sC with values := sC.values }) bE.1 hj
    have outsideE : LocalsOutside s0 sE base 9 :=
      (outsideC.values sC.values).set hLow le_rfl (by omega)
    have hRootE : sE.get (base + 1) = some (.i64 root) :=
      (hOtherE (base + 1) (by omega)).trans hRootC
    -- The release of the block and the end of the accepted branch.
    have release : ∀ sL : Locals, LocalsOutside s0 sL base 9 →
        sL.values = s.values → sL.get base = some (.i64 errno) →
        sL.get (base + 1) = some (.i64 root) →
        (∀ i, i < 6 → sL.get (base + 3 + i) =
          some (.i64 ((pollWords (sysReply errno outputs)).getD i 0))) →
        wp target (discardReadCodeWith calls (base + 1)) K after sL env := by
      intro sL outsideL valuesL errnoL rootL wordsL
      have b1L := bound sL outsideL (base + 1) (by omega) (by omega)
      rw [← List.append_nil (discardReadCodeWith calls (base + 1))]
      refine wp_discard_read_with runtime layout profile hImports sourceHost hStep.at_ hEmpty rootL
        b1L.1 b1L.2 ?_
      intro released hReleased hReleasedWorld
      rw [wp_nil]
      refine hNext _ released (setLocal sL (base + 1) (.i64 0)) errno outputs
        (by rw [hReleasedWorld]; exact hSys')
        (read_discard_step hStep hEmpty hReleased)
        (by rw [read_discard_top hStep.at_ hEmpty, hCostEq]; exact hTopAlloc)
        (outsideL.set hLow (by omega) (by omega)) valuesL
        ((Locals.get_setLocal_ne b1L.1 (by omega)).trans errnoL) ?_
      intro i hi
      exact (Locals.get_setLocal_ne b1L.1 (by omega)).trans (wordsL i hi)
    change wp target (.localGet base :: _) K after sE env
    refine wp_localGet_get hGetE ?_
    simp only [wp_eqzI64_cons]
    refine wp_iff_cons rfl ?_
    by_cases hZeroErrno : errno = 0
    · rw [ite_eq_left (by simp [hZeroErrno] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
      obtain ⟨events, count, rfl, hEventsAt, hCountAt⟩ := hShown hZeroErrno
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hOutputSizes
      obtain ⟨hEventsSize, hCountSize⟩ := hOutputSizes
      have hCountWord := littleEndian_read32 hCountAt hCountSize
      have h0 : (0 : UInt64).toUInt32 = 0 := rfl
      rw [h0] at hCountWord
      simp only [wp_const_cons, wp_load32_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
      rw [ite_eq_right (by
        have hp := hFrame'.pages
        change ¬(0 + 0 + 4 > after.mem.pages * 65536)
        omega)]
      simp only [wp_extendUI32_cons]
      rw [hCountWord]
      have b3 := bound sE outsideE (base + 3) (by omega) (by omega)
      refine wp_localSet_local b3.1 b3.2 ?_
      let sF := setLocal { sE with values := sE.values } (base + 3) (.i64 (littleEndian count))
      have hGetF : sF.get (base + 3) = some (.i64 (littleEndian count)) :=
        Locals.get_setLocal_same (s := { sE with values := sE.values }) b3.1 b3.2
      have hOtherF : ∀ j, j ≠ base + 3 → sF.get j = sE.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { sE with values := sE.values }) b3.1 hj
      have outsideF : LocalsOutside s0 sF base 9 :=
        (outsideE.values sE.values).set hLow (by omega) (by omega)
      have hPointerF : sF.get (base + 2) = some (.i64 pointer) :=
        (hOtherF (base + 2) (by omega)).trans ((hOtherE (base + 2) (by omega)).trans hPointerC)
      change wp target (.localGet (base + 2) :: _) _ after sF env
      simp only [wp_localGet_cons, hPointerF, wp_constI64_cons, wp_addI64_cons]
      have b2F := bound sF outsideF (base + 2) (by omega) (by omega)
      refine wp_localSet_local b2F.1 b2F.2 ?_
      let sG := setLocal { sF with values := sF.values } (base + 2)
        (.i64 (pointer + UInt64.ofNat (48 * records.length)))
      have hPointerG : sG.get (base + 2) =
          some (.i64 (pointer + UInt64.ofNat (48 * records.length))) :=
        Locals.get_setLocal_same (s := { sF with values := sF.values }) b2F.1 b2F.2
      have hOtherG : ∀ j, j ≠ base + 2 → sG.get j = sF.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { sF with values := sF.values }) b2F.1 hj
      have outsideG : LocalsOutside s0 sG base 9 :=
        (outsideF.values sF.values).set hLow (by omega) (by omega)
      change wp target (recordLoadCode (base + 2) eventFields (base + 4)) _ after sG env
      have hEventsLength : eventFields.length = 5 := rfl
      rw [← List.append_nil (recordLoadCode (base + 2) eventFields (base + 4))]
      refine wp_record_loads eventFields (base + 4) sG [] _ hPointerG hEventsAt
        (eventFields_fit (by rw [hEventsSize]; omega)) (by left; omega)
        (by rw [outsideG.params]; omega)
        (by rw [outsideG.params, outsideG.length, hEventsLength]; omega) ?_
      intro sL outsideL heldL
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      refine release _ ?_ rfl ?_ ?_ ?_
      · exact outsideG.trans ((outsideL.widen (by omega) (by rw [hEventsLength])).values _)
      · rw [Locals.get_values, outsideL.others base (by omega), hOtherG base (by omega),
          hOtherF base (by omega)]
        exact hGetE
      · rw [Locals.get_values, outsideL.others (base + 1) (by omega),
          hOtherG (base + 1) (by omega), hOtherF (base + 1) (by omega)]
        exact hRootE
      · intro i hi
        rw [Locals.get_values,
          show sysReply errno [events, count] = ⟨errno, [events, count]⟩ by
            simp [sysReply, hZeroErrno], pollWords_reply]
        cases i with
        | zero =>
          rw [Nat.add_zero, outsideL.others (base + 3) (by omega),
            hOtherG (base + 3) (by omega)]
          exact hGetF
        | succ i =>
          rw [show base + 3 + (i + 1) = base + 4 + i by omega,
            heldL i (by rw [hEventsLength]; omega), List.getD_cons_succ]
    · rw [ite_eq_right (by simp [hZeroErrno] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      refine release _ outsideE rfl hGetE hRootE ?_
      intro i hi
      rw [show sysReply errno outputs = ⟨errno, []⟩ by simp [sysReply, hZeroErrno],
        pollWords_empty]
      exact (hOtherE (base + 3 + i) (by omega)).trans
        ((hOtherCs (base + 3 + i) (by omega) (by omega)).trans (hZero i hi))
  · intro after message outputs hSys
    exact hTrap after message outputs (by rw [← hWorld]; exact hSys)

/-- The code of a `poll` call, from the words of its fields in their locals to the errno, the
number of events, and the fields of the first event on the stack.  A rejected request returns its
errno without a call; an accepted request allocates the block, writes the subscriptions, runs the
call, loads the results on errno 0, and releases the block. -/
theorem wp_sys_poll_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {records : List (List Field)} {locs : List Nat}
    {values : List UInt64} {s : Locals} {base : Nat} {rest : Program}
    {Q : Assertion (Observed World)} {aborts : Bool}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = [.subscriptions records, .result32])
    (hFit : subscriptionsFit records = true)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hLocs : ∀ place ∈ locs, place < base)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + 9 ≤ s.positions)
    (hRoom : aborts = false → heap.Room (PureTransport.erase initial) source
      (allocSize (UInt64.ofNat (80 * records.length + 7))))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (trace : List Event) (reply : Reply),
      Exec (observedHost host) (.sys call (flatArgsWith call.params values []) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap' (PureTransport.erase final) [] →
      heap'.top.toNat ≤ heap.top.toNat + Bytes.allocationCost (80 * records.length + 7) →
      LocalsOutside s finalLocals base 9 →
      wp target rest Q final { finalLocals with values :=
        ((reply.errno :: pollWords reply).map Value.i64).reverse ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.sys call (flatArgsWith call.params values []) Action.pure)
        initial.host trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysPollCodeWith calls call locs base ++ rest) Q initial s env := by
  have hPositions : base + 9 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hLength : values.length = (argFields records).length := by
    rw [hCount, poll_wordCount hParams]
  have hArgs : flatArgsWith call.params values [] = values.map .word := by
    rw [hParams, poll_args records values hLength]
  have hRecords : subscriptionsOf call.params = some records := by rw [hParams]; rfl
  simp only [sysPollCodeWith, hRecords, List.append_assoc, List.cons_append]
  refine wp_fields_reject (argFields records) locs values s _ Q hHeld
    (by rw [hLength]) ?_
  generalize hRejectEq : rejectFields (argFields records) (values.map .word) = reject
  have hReject : call.reject (flatArgsWith call.params values []) = reject := by
    change rejectArgs call.params _ = _
    rw [hArgs, hParams, poll_reject, hRejectEq]
  refine wp_localSet_local hLow (by omega) ?_
  let s1 := setLocal { s with values := s.values } base (.i64 reject)
  have outside1 : LocalsOutside s s1 base 9 :=
    ((LocalsOutside.refl s base 9).values s.values).set hLow le_rfl (by omega)
  have hGet1 : s1.get base = some (.i64 reject) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) hLow (by omega)
  change wp target (zeroLocalsCode (base + 3) 6 ++ _) Q initial s1 env
  refine wp_zero_locals 6 (base + 3) s1 (by rw [outside1.params]; omega)
    (by rw [outside1.params, outside1.length]; omega) ?_
  intro s2 outside2 values2 zeros2
  have outside2' : LocalsOutside s s2 base 9 :=
    outside1.trans (outside2.widen (by omega) (by omega))
  have hGet2 : s2.get base = some (.i64 reject) := (outside2.others base (by omega)).trans hGet1
  have held2 := held_transfer hHeld fun place member =>
    outside2'.others place (.inl (hLocs place member))
  simp only [wp_localGet_cons, hGet2, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have finish : ∀ (final : Store (Observed World)) (sF : Locals) (heap' : Heap)
      (trace : List Event) (reply : Reply),
      Exec (observedHost host) (.sys call (flatArgsWith call.params values []) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap' (PureTransport.erase final) [] →
      heap'.top.toNat ≤ heap.top.toNat + Bytes.allocationCost (80 * records.length + 7) →
      LocalsOutside s sF base 9 →
      sF.get base = some (.i64 reply.errno) →
      (∀ i, i < 6 → sF.get (base + 3 + i) = some (.i64 ((pollWords reply).getD i 0))) →
      wp target (.localGet base :: ((List.range 6).map
        (fun index => .localGet (base + 3 + index)) ++ rest)) Q final
        { sF with values := s.values } env := by
    intro final sF heap' trace reply execution step top outsideF errnoF wordsF
    simp only [wp_localGet_cons, Locals.get_values, errnoF]
    rw [show (6 : Nat) = (pollWords reply).length from rfl]
    refine wp_push_words (pollWords reply) (base + 3) _ (fun i hi => wordsF i hi) ?_
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using
      hNext heap' final { sF with values := s.values } trace reply execution step top
        (outsideF.values s.values)
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hRejectZero : call.reject (values.map .word) = 0 := by
      rw [← hArgs, hReject, hAccepted]
    change wp target (sysPollCallCodeWith calls call records locs base) _ initial s2 env
    refine wp_sys_poll_accept_with (s0 := s) runtime layout profile hImports sourceHost hHost
      hCall hParams hFit held2 hLength (by rw [hRejectEq, hAccepted]) hLocs hHeap hCap hLow
      hHigh outside2' zeros2 hRoom hResource ?_ ?_
    · intro heap' final sF errno outputs hSys hStep hTop outsideF valuesF errnoF wordsF
      simp only [List.take_zero, List.nil_append, List.drop_zero, values2]
      have execution : Exec (observedHost host)
          (.sys call (flatArgsWith call.params values []) Action.pure) initial.host
          [.sys call (values.map .word) (.returned errno outputs)]
          (.returned (sysReply errno outputs)) final.host := by
        rw [hArgs]
        exact .sys_return hRejectZero hSys (.pure final.host _)
      exact finish final sF heap' _ (sysReply errno outputs) execution hStep hTop outsideF errnoF
        wordsF
    · intro final message outputs hSys
      exact hTrap final message _ (by rw [hArgs]; exact .sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] :
      ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, values2]
    have hRejectNe : call.reject (flatArgsWith call.params values []) ≠ 0 := by
      rw [hReject]; exact hAccepted
    have hReply : (⟨call.reject (flatArgsWith call.params values []), []⟩ : Reply) =
        ⟨reject, []⟩ := by rw [hReject]
    refine finish initial s2 heap [] ⟨reject, []⟩ ?_ (Step.refl hHeap _) (by omega) outside2'
      hGet2 ?_
    · rw [← hReply]
      exact .sys_reject hRejectNe (.pure initial.host _)
    · intro i hi
      rw [pollWords_empty]
      exact zeros2 i hi

end Verified.Wasi
