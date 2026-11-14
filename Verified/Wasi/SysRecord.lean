import Verified.Wasi.SysRecordCall

/-! The code of a record call, from the argument test to the errno and the field words on the
stack: the test of the arguments, the field locals set to 0, the accepted call with its block,
and the pushes of the errno and the fields.  The block is released after the call whatever the
errno, so the result holds no heap value. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

namespace LocalsOutside

theorem refl (s : Locals) (target count : Nat) : LocalsOutside s s target count :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem trans {s s' s'' : Locals} {target count : Nat} (first : LocalsOutside s s' target count)
    (second : LocalsOutside s' s'' target count) : LocalsOutside s s'' target count :=
  ⟨second.params.trans first.params, second.length.trans first.length,
    fun j hj => (second.others j hj).trans (first.others j hj)⟩

theorem widen {s s' : Locals} {target count target' count' : Nat}
    (h : LocalsOutside s s' target count) (hTarget : target' ≤ target)
    (hCount : target + count ≤ target' + count') : LocalsOutside s s' target' count' :=
  ⟨h.params, h.length, fun j hj => h.others j (by omega)⟩

theorem values {s s' : Locals} {target count : Nat} (h : LocalsOutside s s' target count)
    (values : List Value) : LocalsOutside s { s' with values } target count :=
  ⟨h.params, h.length, h.others⟩

theorem set {s s' : Locals} {target count i : Nat} {v : Value}
    (h : LocalsOutside s s' target count) (hLow : s.params.length ≤ target) (hi : target ≤ i)
    (hi' : i < target + count) : LocalsOutside s (setLocal s' i v) target count := by
  have hParams : s'.params.length ≤ i := by rw [h.params]; omega
  refine ⟨h.params, by simp only [setLocal, List.length_set, h.length], fun j hj => ?_⟩
  rw [Locals.get_setLocal_ne hParams (by omega)]
  exact h.others j hj

theorem bounds {s s' : Locals} {target count i : Nat} (h : LocalsOutside s s' target count)
    (hLow : s.params.length ≤ target)
    (hHigh : target + count ≤ s.params.length + s.locals.length) (hi : target ≤ i)
    (hi' : i < target + count) :
    s'.params.length ≤ i ∧ i < s'.params.length + s'.locals.length := by
  rw [h.params, h.length]
  omega

theorem frame {base count : Nat} {s s' : Locals} (h : LocalsOutside s s' base count)
    (hHigh : base + count ≤ s.positions) : Frame base s s' :=
  ⟨h.params, h.length, fun j hj => ⟨h.others j (Or.inl hj), h.others _ (Or.inr (by omega))⟩,
    fun j _ => h.others _ (Or.inr (by omega))⟩

end LocalsOutside

theorem recordFits_bounds {size align : Nat} {fields : List (Nat × Nat)}
    (h : recordFits size align fields = true) :
    0 < size ∧ 0 < align ∧ size + align ≤ 4294967296 := by
  simp only [recordFits, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem recordWords_length {params : List Param} {size align : Nat} {fields : List (Nat × Nat)}
    (hRecord : recordOf params = some (size, align, fields)) (reply : Reply) :
    (recordWords params reply).length = fields.length := by
  simp [recordWords, hRecord]

theorem recordWords_record {params : List Param} {size align : Nat} {fields : List (Nat × Nat)}
    (hRecord : recordOf params = some (size, align, fields)) (errno : UInt64)
    (record : LeanExe.Bytes) :
    recordWords params ⟨errno, [record]⟩ = fieldWords record fields := by
  simp only [recordWords, hRecord, fieldWords, Reply.field, Reply.bytes, List.getElem?_cons_zero,
    Option.getD_some]

theorem field_empty (errno : UInt64) (offset width : Nat) :
    (⟨errno, []⟩ : Reply).field 0 offset width = 0 := by
  have hSize : (((⟨errno, []⟩ : Reply).bytes 0).data.extract offset (offset + width)).size = 0 := by
    simp [Reply.bytes, LeanExe.Bytes.empty, ByteArray.size_empty]
  simp only [Reply.field, littleEndian, hSize, List.range_zero, List.foldr_nil]

theorem getD_map_zero {β : Type} (f : β → UInt64) (hf : ∀ x, f x = 0) :
    ∀ (items : List β) (i : Nat), (items.map f).getD i 0 = 0
  | [], _ => by simp
  | item :: _, 0 => by rw [List.map_cons, List.getD_cons_zero]; exact hf item
  | _ :: items, i + 1 => by
    rw [List.map_cons, List.getD_cons_succ]; exact getD_map_zero f hf items i

theorem recordWords_empty (params : List Param) (errno : UInt64) (i : Nat) :
    (recordWords params ⟨errno, []⟩).getD i 0 = 0 := by
  cases hRecord : recordOf params with
  | none => simp [recordWords, hRecord]
  | some record =>
    obtain ⟨_, _, fields⟩ := record
    simp only [recordWords, hRecord, field_empty]
    exact getD_map_zero (fun _ : Nat × Nat => (0 : UInt64)) (fun _ => rfl) fields i

/-- Sets `count` locals from `first` to 0. -/
theorem wp_zero_locals {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {rest : Program} {Q : Assertion α} :
    ∀ (count first : Nat) (s : Locals), s.params.length ≤ first →
    first + count ≤ s.params.length + s.locals.length →
    (∀ s' : Locals, LocalsOutside s s' first count → s'.values = s.values →
      (∀ i, i < count → s'.get (first + i) = some (.i64 0)) → wp m rest Q st s' env) →
    wp m (zeroLocalsCode first count ++ rest) Q st s env
  | 0, first, s, _, _, h => by
    simpa [zeroLocalsCode] using
      h s (LocalsOutside.refl s first 0) rfl (fun i hi => absurd hi (Nat.not_lt_zero i))
  | count + 1, first, s, hLow, hHigh, h => by
    simp only [zeroLocalsCode, List.cons_append]
    refine wp_set_word hLow (by omega) ?_
    refine wp_zero_locals count (first + 1) (setLocal s first (.i64 0))
      (by simp only [setLocal]; omega) (by simp only [setLocal, List.length_set]; omega) ?_
    intro s' outside values zeros
    refine h s' ⟨outside.params, ?_, ?_⟩ values ?_
    · rw [outside.length]
      simp [setLocal, List.length_set]
    · intro j hj
      rw [outside.others j (by omega), Locals.get_setLocal_ne hLow (by omega)]
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, outside.others first (by omega)]
        exact Locals.get_setLocal_same hLow (by omega)
      | succ i =>
        rw [show first + (i + 1) = first + 1 + i by omega]
        exact zeros i (by omega)

/-- An accepted record request: the allocation of the block, the record pointer, the host call,
the loads of the fields on errno 0, and the release of the block, with the continuation `K` of the
enclosing `iff`. -/
theorem wp_sys_record_accept_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {params : List Param} {size align : Nat}
    {fields : List (Nat × Nat)} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {s0 s : Locals} {base : Nat} {aborts : Bool} {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = params ++ [.record size align fields])
    (hKinds : params.all Param.argKind = true) (hFits : recordFits size align fields = true)
    (hAccepted : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hLocs : ∀ place ∈ locs, place < base ∨ base + fields.length + 3 ≤ place)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hInputLocs : ∀ place ∈ inputLocs, place + 2 ≤ base ∨ base + fields.length + 3 ≤ place)
    (hInputReps : ∀ input ∈ inputs, ∃ length,
      Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
        ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.scratch)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s0.params.length ≤ base) (hHigh : base + fields.length + 3 ≤ s0.positions)
    (hOutside : LocalsOutside s0 s base (fields.length + 3))
    (hZero : ∀ i, i < fields.length → s.get (base + 3 + i) = some (.i64 0))
    (hRoom : aborts = false → heap.Room (PureTransport.erase initial) source
      (allocSize (UInt64.ofNat (size + align - 1))))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → K (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.returned errno outputs)
        final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) [] →
      heap'.top.toNat ≤ heap.top.toNat + Bytes.allocationCost (size + align - 1) →
      LocalsOutside s0 sF base (fields.length + 3) → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      (∀ i, i < fields.length → sF.get (base + 3 + i) =
        some (.i64 ((recordWords call.params (sysReply errno outputs)).getD i 0))) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.trapped message outputs)
        final.host → K (.Trap final message)) :
    wp target (sysRecordCallCodeWith calls call locs inputLocs base size align fields) K
      initial s env := by
  have hRecord : recordOf call.params = some (size, align, fields) := by
    rw [hParams]; exact recordOf_record size align fields hKinds
  have hFieldsFit := recordFits_fields hFits
  obtain ⟨hSize, hAlign, hBlock⟩ := recordFits_bounds hFits
  have hBlockNat : (UInt64.ofNat (size + align - 1)).toNat = size + align - 1 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hAlignNe : UInt64.ofNat align ≠ 0 := by
    intro hZeroAlign
    have := congrArg UInt64.toNat hZeroAlign
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
      at this
    simp at this
    omega
  have hCostEq := Verified.Bytes.allocationCost_eq (count := UInt64.ofNat (size + align - 1))
    (by rw [hBlockNat]; omega) (by rw [hBlockNat]; omega)
  rw [hBlockNat] at hCostEq
  have hPositions : base + fields.length + 3 ≤ s0.params.length + s0.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have bound := fun (t : Locals) (outside : LocalsOutside s0 t base (fields.length + 3)) i
    (hi : base ≤ i) (hi' : i < base + (fields.length + 3)) =>
    outside.bounds hLow (by omega) hi hi'
  -- The allocation of the block.
  simp only [sysRecordCallCodeWith, List.append_assoc, List.cons_append, List.nil_append,
    wp_constI64_cons]
  refine wp_alloc_frame_with (s := s) (values := s.values) runtime layout profile hImports
    sourceHost hHeap (by rw [hBlockNat]; omega) hCap hRoom hResource ?_
  intro allocated hHeapFits hStore hWorld
  obtain ⟨hAllocate, hBuffer, hCapacity, hTopAlloc⟩ :=
    read_allocation_buffer hHeap (by rw [hBlockNat]; omega) hHeapFits hStore
  let root := FixedArrayAllocate.root heap.top (allocSize (UInt64.ofNat (size + align - 1)))
    heap.free
  have hBefore : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      (heap.allocate (allocSize (UInt64.ofNat (size + align - 1))))
      (PureTransport.erase allocated) (Bytes.regions (PureTransport.erase allocated) root) := by
    have hRoot : root ≠ 0 := hBuffer.nonzero
    rw [Bytes.regions, ite_eq_right hRoot]
    exact hAllocate.mono
      (keep' := fun region => regionsDisjoint region ABI.scratch)
      (fresh' := [block (PureTransport.erase allocated) root])
      (fun _ _ => True.intro) (fun _ h => h)
  have hReady : ReadReady (heap.allocate (allocSize (UInt64.ofNat (size + align - 1))))
      (PureTransport.erase allocated) root (UInt64.ofNat (size + align - 1)) :=
    Or.inr ⟨_, hBuffer, hCapacity⟩
  have hRootAddress := hReady.address
  have hRootMemory := hReady.memory hBefore.at_
  rw [hBlockNat] at hRootAddress hRootMemory
  have b1 := bound s hOutside (base + 1) (by omega) (by omega)
  refine wp_localSet_local b1.1 b1.2 ?_
  let sA := setLocal { s with values := s.values } (base + 1) (.i64 root)
  have outsideA : LocalsOutside s0 sA base (fields.length + 3) :=
    (hOutside.values s.values).set hLow (by omega) (by omega)
  have hRootA : sA.get (base + 1) = some (.i64 root) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) b1.1 b1.2
  have hOtherA : ∀ j, j ≠ base + 1 → sA.get j = s.get j := fun j hj =>
    Locals.get_setLocal_ne (s := { s with values := s.values }) b1.1 hj
  change wp target (recordAddressCode base align ++ _) K allocated sA env
  -- The record pointer.
  simp only [recordAddressCode, List.cons_append, List.nil_append, wp_localGet_cons, hRootA,
    wp_constI64_cons, wp_addI64_cons]
  have b2 := bound sA outsideA (base + 2) (by omega) (by omega)
  refine wp_localSet_local b2.1 b2.2 ?_
  let sB := setLocal { sA with values := sA.values } (base + 2)
    (.i64 (root + UInt64.ofNat (align - 1)))
  have hGetB : sB.get (base + 2) = some (.i64 (root + UInt64.ofNat (align - 1))) :=
    Locals.get_setLocal_same (s := { sA with values := sA.values }) b2.1 b2.2
  have outsideB : LocalsOutside s0 sB base (fields.length + 3) :=
    (outsideA.values sA.values).set hLow (by omega) (by omega)
  change wp target (.localGet (base + 2) :: _) K allocated sB env
  simp only [wp_localGet_cons, hGetB, Locals.get_values, wp_constI64_cons, wp_remUI64_cons,
    hAlignNe, ite_false, wp_subI64_cons]
  have b2B := bound sB outsideB (base + 2) (by omega) (by omega)
  refine wp_localSet_local b2B.1 b2B.2 ?_
  let pointer := recordAddress root align
  let sC := setLocal { sB with values := sB.values } (base + 2) (.i64 pointer)
  have hPointerC : sC.get (base + 2) = some (.i64 pointer) :=
    Locals.get_setLocal_same (s := { sB with values := sB.values }) b2B.1 b2B.2
  have hOtherC : ∀ j, j ≠ base + 2 → sC.get j = sA.get j := fun j hj =>
    (Locals.get_setLocal_ne (s := { sB with values := sB.values }) b2B.1 hj).trans
      (Locals.get_setLocal_ne (s := { sA with values := sA.values }) b2.1 hj)
  have outsideC : LocalsOutside s0 sC base (fields.length + 3) :=
    (outsideB.values sB.values).set hLow (by omega) (by omega)
  have hOtherCs : ∀ j, j ≠ base + 1 → j ≠ base + 2 → sC.get j = s.get j := fun j h1 h2 =>
    (hOtherC j h2).trans (hOtherA j h1)
  have hRootC : sC.get (base + 1) = some (.i64 root) := (hOtherC (base + 1) (by omega)).trans hRootA
  change wp target (sysLowerInputsCode call.params locs inputLocs (base + 1) 0 ++ _) K allocated
    sC env
  obtain ⟨hPointerLow, hPointerHigh, hAligned⟩ : root.toNat ≤ pointer.toNat ∧
      pointer.toNat + 1 ≤ root.toNat + align ∧ pointer.toNat % align = 0 :=
    recordAddress_spec (root := root) (align := align) hAlign (by omega)
  have hHeldC := held_transfer hHeld fun place member =>
    hOtherCs place (by rcases hLocs place member with h | h <;> omega)
      (by rcases hLocs place member with h | h <;> omega)
  have hInputsC := inputsHeld_transfer hInputs fun place member => by
    rcases hInputLocs place member with h | h
    · exact ⟨hOtherCs place (by omega) (by omega), hOtherCs (place + 1) (by omega) (by omega)⟩
    · exact ⟨hOtherCs place (by omega) (by omega), hOtherCs (place + 1) (by omega) (by omega)⟩
  have facts := fun input (member : input ∈ inputs) =>
    input_at_call (hInputReps input member) hBefore hReady
  -- The host call.
  refine wp_sys_record_call_with (root := root) (pointer := pointer) hImports hHost hCall hParams
    hKinds hAccepted hHeldC hCount hInputsC hInputCount hRootC hPointerC
    (by change pointer.toNat + size ≤ (PureTransport.erase allocated).mem.pages * 65536; omega)
    (by omega) hAligned (fun input member => (facts input member).1)
    (fun input member => by
      have apart := (facts input member).2.2
      rw [hBlockNat] at apart
      simp only [regionsDisjoint] at apart ⊢
      omega) ?_ ?_
  · intro after errno outputs hSys hFrame hShown
    have hFrame' : GuestFrame allocated after
        [ABI.scratch, (root.toNat, (UInt64.ofNat (size + align - 1)).toNat)] :=
      hFrame.cover fun region member => by
        rw [List.mem_singleton] at member
        subst member
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
          (show root.toNat ≤ pointer.toNat by omega),
          (show pointer.toNat + size ≤ root.toNat + (UInt64.ofNat (size + align - 1)).toNat by
            rw [hBlockNat]; omega)⟩
    have hStep := hReady.frame_step hBefore hFrame'
    have hEmpty := hReady.empty_rep hBefore.at_ hFrame'
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hOutputSizes : outputs.map (fun output => output.data.size) = [size] := by
      have h : outputs.map (fun output => output.data.size) =
          outputSizesOf call.params (host.reported allocated.host.world call)
            (flatArgsWith call.params values (inputs.map Prod.snd)) := hBound.1
      rw [h, hParams, outputSizesOf_record size align fields params _ _ hKinds]
    simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
    have bE := bound sC outsideC base le_rfl (by omega)
    refine wp_localSet_local bE.1 bE.2 ?_
    let sE := setLocal { sC with values := sC.values } base (.i64 errno)
    have hGetE : sE.get base = some (.i64 errno) :=
      Locals.get_setLocal_same (s := { sC with values := sC.values }) bE.1 bE.2
    have hOtherE : ∀ j, j ≠ base → sE.get j = sC.get j := fun j hj =>
      Locals.get_setLocal_ne (s := { sC with values := sC.values }) bE.1 hj
    have outsideE : LocalsOutside s0 sE base (fields.length + 3) :=
      (outsideC.values sC.values).set hLow le_rfl (by omega)
    have hRootE : sE.get (base + 1) = some (.i64 root) :=
      (hOtherE (base + 1) (by omega)).trans hRootC
    -- The release of the block and the end of the accepted branch.
    have release : ∀ sL : Locals, LocalsOutside s0 sL base (fields.length + 3) →
        sL.values = s.values → sL.get base = some (.i64 errno) →
        sL.get (base + 1) = some (.i64 root) →
        (∀ i, i < fields.length → sL.get (base + 3 + i) =
          some (.i64 ((recordWords call.params (sysReply errno outputs)).getD i 0))) →
        wp target (discardReadCodeWith calls (base + 1)) K after sL env := by
      intro sL outsideL valuesL errnoL rootL fieldsL
      have b1L := bound sL outsideL (base + 1) (by omega) (by omega)
      rw [← List.append_nil (discardReadCodeWith calls (base + 1))]
      refine wp_discard_read_with runtime layout profile hImports sourceHost hStep.at_ hEmpty rootL
        b1L.1 b1L.2 ?_
      intro released hReleased hReleasedWorld
      rw [wp_nil]
      refine hNext _ released (setLocal sL (base + 1) (.i64 0)) errno outputs
        (by rw [hReleasedWorld, ← hWorld]; exact hSys)
        (read_discard_step hStep hEmpty hReleased)
        (by rw [read_discard_top hStep.at_ hEmpty, hCostEq]; exact hTopAlloc)
        (outsideL.set hLow (by omega) (by omega)) valuesL
        ((Locals.get_setLocal_ne b1L.1 (by omega)).trans errnoL) ?_
      intro i hi
      exact (Locals.get_setLocal_ne b1L.1 (by omega)).trans (fieldsL i hi)
    change wp target (.localGet base :: _) K after sE env
    refine wp_localGet_get hGetE ?_
    simp only [wp_eqzI64_cons]
    refine wp_iff_cons rfl ?_
    by_cases hZeroErrno : errno = 0
    · rw [ite_eq_left (by simp [hZeroErrno] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
      obtain ⟨record, rfl, hAt⟩ := hShown hZeroErrno
      have hRecordSize : record.data.size = size := by simpa using hOutputSizes
      have hPointerE : sE.get (base + 2) = some (.i64 pointer) :=
        (hOtherE (base + 2) (by omega)).trans hPointerC
      change wp target (recordLoadCode (base + 2) fields (base + 3)) _ after sE env
      rw [← List.append_nil (recordLoadCode (base + 2) fields (base + 3))]
      refine wp_record_loads fields (base + 3) sE [] _ hPointerE hAt
        (by rw [hRecordSize]; exact hFieldsFit) (by omega) (by rw [outsideE.params]; omega)
        (by rw [outsideE.params, outsideE.length]; omega) ?_
      intro sL outsideL heldL
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      refine release _ ?_ rfl ?_ ?_ ?_
      · exact outsideE.trans ((outsideL.widen (by omega) (by omega)).values _)
      · exact (outsideL.others base (by omega)).trans hGetE
      · exact (outsideL.others (base + 1) (by omega)).trans hRootE
      · intro i hi
        rw [show sysReply errno [record] = ⟨errno, [record]⟩ by simp [sysReply, hZeroErrno],
          recordWords_record hRecord]
        exact heldL i hi
    · rw [ite_eq_right (by simp [hZeroErrno] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      refine release _ outsideE rfl hGetE hRootE ?_
      intro i hi
      rw [show sysReply errno outputs = ⟨errno, []⟩ by simp [sysReply, hZeroErrno],
        recordWords_empty]
      exact (hOtherE (base + 3 + i) (by omega)).trans
        ((hOtherCs (base + 3 + i) (by omega) (by omega)).trans (hZero i hi))
  · intro after message outputs hSys
    exact hTrap after message outputs (by rw [← hWorld]; exact hSys)

/-- The code of a record call, from the argument words and the inputs in their locals to the
errno and the field words on the stack.  A rejected request returns its errno without a call; an
accepted request allocates the block, runs the call, loads the fields on errno 0, and releases the
block. -/
theorem wp_sys_record_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {params : List Param} {size align : Nat}
    {fields : List (Nat × Nat)} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)} {aborts : Bool}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = params ++ [.record size align fields])
    (hKinds : params.all Param.argKind = true) (hFits : recordFits size align fields = true)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hLocs : ∀ place ∈ locs, place < base ∨ base + fields.length + 3 ≤ place)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hInputLocs : ∀ place ∈ inputLocs, place + 2 ≤ base ∨ base + fields.length + 3 ≤ place)
    (hInputReps : ∀ input ∈ inputs, ∃ length,
      Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
        ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.scratch)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + fields.length + 3 ≤ s.positions)
    (hRoom : aborts = false → heap.Room (PureTransport.erase initial) source
      (allocSize (UInt64.ofNat (size + align - 1))))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (trace : List Event) (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) [] →
      heap'.top.toNat ≤ heap.top.toNat + Bytes.allocationCost (size + align - 1) →
      LocalsOutside s finalLocals base (fields.length + 3) →
      wp target rest Q final { finalLocals with values :=
        ((reply.errno :: recordWords call.params reply).map Value.i64).reverse ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysRecordCodeWith calls call locs inputLocs base ++ rest) Q initial s env := by
  have hRecord : recordOf call.params = some (size, align, fields) := by
    rw [hParams]; exact recordOf_record size align fields hKinds
  have hPositions : base + fields.length + 3 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hInputCount' : inputs.length = params.count .input := by
    rw [hInputCount, Call.inputCount, hParams, count_input_record]
  have hCount' : values.length = params.countP Param.takesWord := by
    rw [hCount, Call.wordCount, hParams, countP_takesWord_record]
  have hArgs : flatArgsWith call.params values (inputs.map Prod.snd) =
      flatArgsWith params values (inputs.map Prod.snd) := by
    rw [hParams, flatArgsWith_record]
  simp only [sysRecordCodeWith, hRecord, List.append_assoc, List.cons_append]
  rw [show sysRejectInputsCode call.params locs inputLocs =
      sysRejectInputsCode params locs inputLocs by rw [hParams, sysRejectInputsCode_record]]
  refine wp_sys_reject_inputs params locs values inputLocs inputs s _ Q (argKind_inputKind hKinds)
    hHeld hCount' hInputs hInputCount' ?_
  generalize hRejectEq : rejectArgs params (flatArgsWith params values (inputs.map Prod.snd)) =
    reject
  have hReject : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = reject := by
    change rejectArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd)) = reject
    rw [hArgs, hParams, rejectArgs_record, hRejectEq]
  refine wp_localSet_local hLow (by omega) ?_
  let s1 := setLocal { s with values := s.values } base (.i64 reject)
  have outside1 : LocalsOutside s s1 base (fields.length + 3) :=
    ((LocalsOutside.refl s base (fields.length + 3)).values s.values).set hLow le_rfl (by omega)
  have hGet1 : s1.get base = some (.i64 reject) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) hLow (by omega)
  change wp target (zeroLocalsCode (base + 3) fields.length ++ _) Q initial s1 env
  refine wp_zero_locals fields.length (base + 3) s1 (by rw [outside1.params]; omega)
    (by rw [outside1.params, outside1.length]; omega) ?_
  intro s2 outside2 values2 zeros2
  have outside2' : LocalsOutside s s2 base (fields.length + 3) :=
    outside1.trans (outside2.widen (by omega) (by omega))
  have hGet2 : s2.get base = some (.i64 reject) := (outside2.others base (by omega)).trans hGet1
  have hValues2 : s2.values = s.values := values2
  have held2 := held_transfer hHeld fun place member =>
    outside2'.others place (by rcases hLocs place member with h | h <;> omega)
  have inputs2 := inputsHeld_transfer hInputs fun place member => by
    rcases hInputLocs place member with h | h
    · exact ⟨outside2'.others place (by omega), outside2'.others (place + 1) (by omega)⟩
    · exact ⟨outside2'.others place (by omega), outside2'.others (place + 1) (by omega)⟩
  simp only [wp_localGet_cons, hGet2, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hWordsLength := recordWords_length hRecord
  have finish : ∀ (final : Store (Observed World)) (sF : Locals) (heap' : Heap)
      (trace : List Event) (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) [] →
      heap'.top.toNat ≤ heap.top.toNat + Bytes.allocationCost (size + align - 1) →
      LocalsOutside s sF base (fields.length + 3) →
      sF.get base = some (.i64 reply.errno) →
      (∀ i, i < fields.length → sF.get (base + 3 + i) =
        some (.i64 ((recordWords call.params reply).getD i 0))) →
      wp target (.localGet base :: ((List.range fields.length).map
        (fun index => .localGet (base + 3 + index)) ++ rest)) Q final
        { sF with values := s.values } env := by
    intro final sF heap' trace reply execution step top outsideF errnoF fieldsF
    simp only [wp_localGet_cons, Locals.get_values, errnoF]
    rw [← hWordsLength reply]
    refine wp_push_words (recordWords call.params reply) (base + 3) _
      (fun i hi => fieldsF i (by rw [← hWordsLength reply]; exact hi)) ?_
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using
      hNext heap' final { sF with values := s.values } trace reply execution step top
        (outsideF.values s.values)
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hRejectZero : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0 := by
      rw [hReject, hAccepted]
    change wp target (sysRecordCallCodeWith calls call locs inputLocs base size align fields) _
      initial s2 env
    refine wp_sys_record_accept_with (s0 := s) runtime layout profile hImports sourceHost hHost
      hCall hParams hKinds hFits hRejectZero held2 hCount hLocs inputs2 hInputCount hInputLocs
      hInputReps hHeap hCap hLow hHigh outside2' zeros2 hRoom ?_ ?_ ?_
    · intro hAbort final hWorld
      exact hResource hAbort final hWorld
    · intro heap' final sF errno outputs hSys hStep hTop outsideF valuesF errnoF fieldsF
      simp only [List.take_zero, List.nil_append, List.drop_zero, hValues2]
      exact finish final sF heap'
        [.sys call (flatArgsWith call.params values (inputs.map Prod.snd))
          (.returned errno outputs)]
        (sysReply errno outputs) (.sys_return hRejectZero hSys (.pure final.host _)) hStep hTop
        outsideF errnoF fieldsF
    · intro final message outputs hSys
      exact hTrap final message _ (.sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] :
      ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, hValues2]
    have hRejectNe : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) ≠ 0 := by
      rw [hReject]; exact hAccepted
    have hReply : (⟨call.reject (flatArgsWith call.params values (inputs.map Prod.snd)), []⟩ :
        Reply) = ⟨reject, []⟩ := by rw [hReject]
    refine finish initial s2 heap [] ⟨reject, []⟩ ?_ (Step.refl hHeap _) (by omega) outside2'
      hGet2 ?_
    · rw [← hReply]
      exact .sys_reject hRejectNe (.pure initial.host _)
    · intro i hi
      rw [recordWords_empty]
      exact zeros2 i hi

end Verified.Wasi
