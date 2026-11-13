import Verified.Wasi.SysFlatParts
import Verified.Wasi.ReadAllLoop

/-! The host call of a flat command and the code after it: from the state after the allocation of
the output buffer, the code calls the import, sets the errno, and on errno 0 loads the result
words and keeps the buffer, or otherwise releases it. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- A buffer of `capacity` bytes holds `output` after a frame that writes it. -/
theorem ReadReady.output_rep {World : Type} {before after : Store World} {heap : Heap}
    {root capacity : UInt64} {output : LeanExe.Bytes}
    (h : ReadReady heap (PureTransport.erase before) root capacity)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)])
    (hData : Bytes.At after.mem root output) (hSize : output.data.size = capacity.toNat) :
    Bytes.Rep heap (PureTransport.erase after) root capacity output := by
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · have hEmpty : output = LeanExe.Bytes.empty := by
      cases output with
      | mk data =>
        have : data.size = 0 := by simpa using hSize
        have := ByteArray.size_eq_zero_iff.mp this
        subst this
        rfl
    subst hEmpty
    exact Bytes.Rep.empty heap (PureTransport.erase after)
  · have hBuffer' := allocated_afterRead hBuffer hFrame (by omega) hData
    have hRep := hBuffer'.rep
    have hLength : output.size = capacity := by
      apply UInt64.toNat_inj.mp
      rw [LeanExe.Bytes.size_toNat output (by have := hBuffer'.size_lt; omega), hSize]
    rwa [hLength] at hRep

/-- A buffer holds the empty string after a frame that leaves its header. -/
theorem ReadReady.empty_rep {World : Type} {before after : Store World} {heap : Heap}
    {root capacity : UInt64} (h : ReadReady heap (PureTransport.erase before) root capacity)
    (hHeap : heap.At (PureTransport.erase before))
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)]) :
    Bytes.Rep heap (PureTransport.erase after) root 0 LeanExe.Bytes.empty := by
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · exact Bytes.Rep.empty heap (PureTransport.erase after)
  · exact (allocated_afterRead hBuffer hFrame (by change 0 ≤ _; omega)
      (read_empty_at hBuffer hHeap hFrame)).rep


theorem resultBytes_none :
    ∀ (params : List Param) (values : List UInt64) (reply : Reply) (index : Nat),
    params.all Param.flatKind = true → flatCapacity params values = none →
    resultBytes params reply index = LeanExe.Bytes.empty
  | [], _, _, _, _, _ => rfl
  | param :: params, values, reply, index, kinds, none' => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input => simp [Param.flatKind] at kinds
    | reported | record => simp [Param.flatKind] at kinds
    | output => simp [flatCapacity] at none'
    | word32 | word64 | enum32 | flags32 | flags64 =>
      exact resultBytes_none params values.tail reply index kinds.2
        (by simpa [flatCapacity, Param.takesArg] using none')
    | result32 | result64 =>
      exact resultBytes_none params values reply (index + 1) kinds.2
        (by simpa [flatCapacity, Param.takesArg] using none')

theorem sys_extend_errno {errno : UInt64} (h : errno.toNat ≤ 76) :
    UInt64.ofNat errno.toUInt32.toNat = errno := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]
      have := errno.toUInt32.toNat_lt
      omega),
    UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]

/-- The host call of an accepted flat request and the code after it, from the state after the
allocation, with `root` and `capacity` the buffer's, or 0 and 0 for a call without an output. -/
theorem wp_sys_flat_invoke_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial before : Store (Observed World)} {heap0 heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64} {buffer : Option Nat}
    {s0 s : Locals} {base : Nat} {root capacity : UInt64} {budget : Nat}
    {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.flatKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hAccepted : call.reject (flatArgs call.params values) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argCount)
    (hBuffer : (buffer = none ∧ flatCapacity call.params values = none ∧ root = 0 ∧
        capacity = 0) ∨
      ∃ place, buffer = some place ∧ flatCapacity call.params values = some capacity ∧
        s.get place = some (.i64 capacity) ∧ (place < base ∨ base + 6 ≤ place))
    (hReady : ReadReady heap (PureTransport.erase before) root capacity)
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hWorld : before.host = initial.host)
    (hTop : heap.top.toNat ≤ heap0.top.toNat + budget)
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hOutside : ReadAllOutside base s0 s)
    (hRootLocal : s.get (base + 1) = some (.i64 root))
    (hLengthLocal : s.get (base + 2) = some (.i64 0))
    (hThree : s.get (base + 3) = some (.i64 0)) (hFour : s.get (base + 4) = some (.i64 0))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno root' length : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call (flatArgs call.params values)
        (.returned errno outputs) final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root') →
      Bytes.Rep heap' (PureTransport.erase final) root' length
        (resultBytes call.params (sysReply errno outputs) 0) →
      heap'.top.toNat ≤ heap0.top.toNat + budget →
      ReadAllOutside base s0 sF → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      (∀ i, i < call.params.countP Param.isResult → sF.get (base + 3 + i) =
        some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0))) →
      sF.get (base + 1) = some (.i64 root') → sF.get (base + 2) = some (.i64 length) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call (flatArgs call.params values)
        (.trapped message outputs) final.host → K (.Trap final message)) :
    wp target (sysLowerCode call.params locs (base + 1) 0 ++
      [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
       .iff 0 0 (sysLoadCode call.params 0 (base + 3) ++ sysKeepCode buffer base)
         (sysDiscardCodeWith calls buffer base) [] []]) K before s env := by
  have hAddress := hReady.address
  have hRootSmall : root.toNat < 4294967296 := by omega
  have hMemory : 16 ≤ before.mem.pages * 65536 := by
    have hBase := hBefore.at_.base
    have hBound := hBefore.at_.top
    change 16 ≤ (PureTransport.erase before).mem.pages * 65536
    omega
  have hCapacityEq : ∀ value, flatCapacity call.params values = some value →
      value.toNat = capacity.toNat := by
    intro value found
    rcases hBuffer with ⟨_, none', _, _⟩ | ⟨place, _, found', _, _⟩
    · simp [none'] at found
    · rw [found'] at found
      cases found
      rfl
  have hBufferCall : ∀ value, flatCapacity call.params values = some value →
      root.toNat + value.toNat ≤ before.mem.pages * 65536 ∧
        root.toNat + value.toNat ≤ 2 ^ 32 ∧
        (16 ≤ root.toNat ∨ (value.toNat = 0 ∧ root = 0)) := by
    intro value found
    rw [hCapacityEq value found]
    refine ⟨hReady.memory hBefore.at_, by omega, ?_⟩
    rcases hReady with ⟨rfl, rfl⟩ | ⟨previous, hBuf, _⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl (by have := hBuf.object.base; omega)
  have hBaseLow : s.params.length ≤ base := by rw [hOutside.params]; exact hLow
  have hBaseHigh : base < s.params.length + s.locals.length := by
    rw [hOutside.params, hOutside.length]; exact Locals.lt_total (by omega)
  refine wp_sys_flat_call_with (rootLocal := base + 1) hImports hHost hCall hKinds hOutputs
    hResults hAccepted hHeld hCount hRootLocal hRootSmall hMemory hBufferCall ?_ ?_
  · intro after errno outputs hSys hFrame hShown
    have hFrame' := flat_frame_cover (capacity := capacity.toNat) hKinds hOutputs hResults
      hRootSmall hCapacityEq hFrame
    have hStep := hReady.frame_step hBefore hFrame'
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hSizes : outputs.map (fun output => output.data.size) =
        outputSizesOf call.params (host.reported before.host.world call)
          (flatArgs call.params values) := hBound.1
    have hSys' : (observedHost host).sys initial.host call (flatArgs call.params values)
        (.returned errno outputs) after.host := by rw [← hWorld]; exact hSys
    have hPages : after.mem.pages = before.mem.pages := hFrame.pages
    have hMemoryAfter : 16 ≤ after.mem.pages * 65536 := by rw [hPages]; exact hMemory
    simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
    refine wp_localSet_local hBaseLow hBaseHigh ?_
    -- The locals after the errno is set.
    have hGet1 : (setLocal { s with values := s.values } base (.i64 errno)).get base =
        some (.i64 errno) := Locals.get_setLocal_same hBaseLow hBaseHigh
    have hOther1 : ∀ j, j ≠ base →
        (setLocal { s with values := s.values } base (.i64 errno)).get j = s.get j :=
      fun j hj => Locals.get_setLocal_ne (s := { s with values := s.values }) hBaseLow hj
    have hOutside1 : ReadAllOutside base s0 (setLocal { s with values := s.values } base
        (.i64 errno)) := (hOutside.values s.values).set hLow le_rfl (by omega)
    have hParams1 : (setLocal { s with values := s.values } base (.i64 errno)).params.length =
        s0.params.length := by rw [hOutside1.params]
    have hLocals1 : (setLocal { s with values := s.values } base (.i64 errno)).locals.length =
        s0.locals.length := by rw [hOutside1.length]
    have hPositions : base + 6 ≤ s0.params.length + s0.locals.length := by
      have := hHigh
      simp only [Locals.positions] at this
      omega
    have hS6 : base + 6 ≤ s.params.length + s.locals.length := by
      rw [hOutside.params, hOutside.length]; exact hPositions
    simp only [wp_localGet_cons, hGet1, wp_eqzI64_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : errno = 0
    · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
      have hReply : sysReply errno outputs = ⟨errno, outputs⟩ := by simp [sysReply, hZero]
      refine wp_sys_loads (errno := errno) hMemoryAfter call.params values 0 (base + 3) outputs
        _ _ _ hKinds hOutputs (by omega) (hShown hZero) hSizes (by simp only [setLocal]; omega)
        (by simp only [setLocal, List.length_set]; omega) ?_
      intro sL outsideL heldL
      have hKeepL : ∀ j, (j < base + 3 ∨ base + 3 + call.params.countP Param.isResult ≤ j) →
          sL.get j = (setLocal { s with values := s.values } base (.i64 errno)).get j :=
        fun j hj => (outsideL.others j hj).trans rfl
      have hOutsideL : ReadAllOutside base s0 sL := by
        refine ⟨outsideL.params.trans hOutside1.params, outsideL.length.trans hOutside1.length,
          fun j hj => ?_⟩
        rw [hKeepL j (by omega)]
        exact hOutside1.others j hj
      have hWordsL : ∀ i, i < call.params.countP Param.isResult → sL.get (base + 3 + i) =
          some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0)) := by
        intro i hi
        rw [hReply]
        exact heldL i hi
      have hErrnoL : sL.get base = some (.i64 errno) := (hKeepL base (by omega)).trans hGet1
      have hRootL : sL.get (base + 1) = some (.i64 root) :=
        ((hKeepL (base + 1) (by omega)).trans (hOther1 (base + 1) (by omega))).trans hRootLocal
      have hLengthL : sL.get (base + 2) = some (.i64 0) :=
        ((hKeepL (base + 2) (by omega)).trans (hOther1 (base + 2) (by omega))).trans hLengthLocal
      rcases hBuffer with ⟨rfl, none', rfl, rfl⟩ | ⟨place, rfl, found, hPlace, placeOut⟩
      · simp only [sysKeepCode, wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        refine hNext heap after { sL with values := s.values } errno 0 0 outputs hSys' hStep ?_
          hTop (hOutsideL.values s.values) rfl hErrnoL hWordsL hRootL hLengthL
        rw [resultBytes_none call.params values _ 0 hKinds none']
        exact Bytes.Rep.empty heap (PureTransport.erase after)
      · have hOutputAt := flat_output_at (errno := errno) call.params values outputs 0 capacity
          hKinds hOutputs (hShown hZero) hSizes found
        have hRoot64 : root.toUInt32.toUInt64 = root := read_narrow64 root hRootSmall
        rw [hRoot64] at hOutputAt
        have hRep := hReady.output_rep hFrame' hOutputAt.1 hOutputAt.2
        have hPlaceL : sL.get place = some (.i64 capacity) :=
          ((hKeepL place (by omega)).trans (hOther1 place (by omega))).trans hPlace
        have hLow2 : sL.params.length ≤ base + 2 := by rw [hOutsideL.params]; omega
        have hHigh2 : base + 2 < sL.params.length + sL.locals.length := by
          rw [hOutsideL.params, hOutsideL.length]; omega
        simp only [sysKeepCode, List.cons_append, List.nil_append, wp_localGet_cons,
          Locals.get_values, hPlaceL]
        refine wp_localSet_local hLow2 hHigh2 ?_
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hOther2 : ∀ j, j ≠ base + 2 →
            (setLocal { sL with values := s.values } (base + 2) (.i64 capacity)).get j =
              sL.get j :=
          fun j hj => Locals.get_setLocal_ne (s := { sL with values := s.values }) hLow2 hj
        refine hNext heap after
          { setLocal { sL with values := s.values } (base + 2) (.i64 capacity) with
            values := s.values } errno root capacity outputs hSys' hStep (by rwa [hReply]) hTop
          (((hOutsideL.values s.values).set hLow (by omega) (by omega)).values s.values) rfl
          ((hOther2 base (by omega)).trans hErrnoL)
          (fun i hi => (hOther2 (base + 3 + i) (by omega)).trans (hWordsL i hi))
          ((hOther2 (base + 1) (by omega)).trans hRootL)
          (Locals.get_setLocal_same (s := { sL with values := s.values }) hLow2 hHigh2)
    · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, hZero]
      have hWordsZero : ∀ i, i < call.params.countP Param.isResult →
          (setLocal { s with values := s.values } base (.i64 errno)).get (base + 3 + i) =
            some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0)) := by
        intro i hi
        rw [hReply, resultWords_empty, hOther1 _ (by omega)]
        have hZeroLocal : s.get (base + 3 + i) = some (.i64 0) := by
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · exact hThree
          · exact hFour
        rw [hZeroLocal]
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]
      have hRoot1 : (setLocal { s with values := s.values } base (.i64 errno)).get (base + 1) =
          some (.i64 root) := (hOther1 (base + 1) (by omega)).trans hRootLocal
      have hLength1 : (setLocal { s with values := s.values } base (.i64 errno)).get (base + 2) =
          some (.i64 0) := (hOther1 (base + 2) (by omega)).trans hLengthLocal
      rcases hBuffer with ⟨rfl, none', rfl, rfl⟩ | ⟨place, rfl, found, hPlace, placeOut⟩
      · simp only [sysDiscardCodeWith, wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        refine hNext heap after
          { setLocal { s with values := s.values } base (.i64 errno) with values := s.values }
          errno 0 0 outputs hSys' hStep ?_ hTop (hOutside1.values s.values) rfl hGet1 hWordsZero
          hRoot1 hLength1
        rw [hReply, resultBytes_empty]
        exact Bytes.Rep.empty heap (PureTransport.erase after)
      · have hEmpty := hReady.empty_rep hBefore.at_ hFrame'
        have hLow1 : (setLocal { s with values := s.values } base (.i64 errno)).params.length ≤
            base + 1 := by simp only [setLocal]; omega
        have hHigh1 : base + 1 < (setLocal { s with values := s.values } base (.i64 errno)).params.length +
            (setLocal { s with values := s.values } base (.i64 errno)).locals.length := by
          simp only [setLocal, List.length_set]; omega
        simp only [sysDiscardCodeWith]
        rw [← List.append_nil (discardReadCodeWith calls (base + 1))]
        refine wp_discard_read_with runtime layout profile hImports sourceHost hStep.at_ hEmpty
          hRoot1 hLow1 hHigh1 ?_
        intro final hStore hFinalWorld
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hFinalStep := read_discard_step hStep hEmpty hStore
        have hFinalTop := read_discard_top hStep.at_ hEmpty
        have hOtherD : ∀ j, j ≠ base + 1 →
            (setLocal (setLocal { s with values := s.values } base (.i64 errno)) (base + 1)
              (.i64 0)).get j = (setLocal { s with values := s.values } base (.i64 errno)).get j :=
          fun j hj => Locals.get_setLocal_ne hLow1 hj
        refine hNext _ final
          { setLocal (setLocal { s with values := s.values } base (.i64 errno)) (base + 1)
            (.i64 0) with values := s.values } errno 0 0 outputs
          (by rw [hFinalWorld]; exact hSys')
          (by simpa only [Bytes.regions, ite_true] using hFinalStep) ?_
          (by rw [hFinalTop]; exact hTop)
          ((hOutside1.set hLow (by omega) (by omega)).values s.values) rfl
          ((hOtherD base (by omega)).trans hGet1)
          (fun i hi => (hOtherD (base + 3 + i) (by omega)).trans (hWordsZero i hi))
          (Locals.get_setLocal_same hLow1 hHigh1)
          ((hOtherD (base + 2) (by omega)).trans hLength1)
        rw [hReply, resultBytes_empty]
        exact Bytes.Rep.empty _ _
  · intro after message outputs hSys hFrame
    exact hTrap after message outputs (by rw [← hWorld]; exact hSys)

/-! ## Calls with inputs -/

theorem resultBytes_none_inputs :
    ∀ (params : List Param) (values : List UInt64) (inputs : List LeanExe.Bytes) (reply : Reply)
      (index : Nat),
    params.all Param.inputKind = true → inputs.length = params.count .input →
    flatCapacityWith params values inputs = none →
    resultBytes params reply index = LeanExe.Bytes.empty
  | [], _, _, _, _, _, _, _ => rfl
  | param :: params, values, inputs, reply, index, kinds, count, none' => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record => simp [Param.inputKind, Param.flatKind] at kinds
    | output => simp [flatCapacityWith] at none'
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        exact resultBytes_none_inputs params values inputs reply index kinds.2
          (by simpa [List.count_cons] using count) (by simpa [flatCapacityWith] using none')
    | word32 | word64 | enum32 | flags32 | flags64 =>
      exact resultBytes_none_inputs params values.tail inputs reply index kinds.2
        (by simpa [List.count_cons] using count)
        (by simpa [flatCapacityWith, Param.takesArg] using none')
    | result32 | result64 =>
      exact resultBytes_none_inputs params values inputs reply (index + 1) kinds.2
        (by simpa [List.count_cons] using count)
        (by simpa [flatCapacityWith, Param.takesArg] using none')

/-- The host call of an accepted flat request with inputs and the code after it, from the state
after the allocation, with `root` and `capacity` the buffer's, or 0 and 0 for a call without an
output. -/
theorem wp_sys_flat_invoke_inputs_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial before : Store (Observed World)} {heap0 heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)} {buffer : Option Nat}
    {s0 s : Locals} {base : Nat} {root capacity : UInt64} {budget : Nat}
    {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.inputKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hAccepted : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hBuffer : (buffer = none ∧ flatCapacityWith call.params values (inputs.map Prod.snd) = none ∧
        root = 0 ∧ capacity = 0) ∨
      ∃ place, buffer = some place ∧
        flatCapacityWith call.params values (inputs.map Prod.snd) = some capacity ∧
        s.get place = some (.i64 capacity) ∧ (place < base ∨ base + 6 ≤ place))
    (hReady : ReadReady heap (PureTransport.erase before) root capacity)
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hWorld : before.host = initial.host)
    (hTop : heap.top.toNat ≤ heap0.top.toNat + budget)
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hOutside : ReadAllOutside base s0 s)
    (hRootLocal : s.get (base + 1) = some (.i64 root))
    (hLengthLocal : s.get (base + 2) = some (.i64 0))
    (hThree : s.get (base + 3) = some (.i64 0)) (hFour : s.get (base + 4) = some (.i64 0))
    (hInputAt : ∀ input ∈ inputs,
      Bytes.At before.mem input.1 input.2 ∧ input.1.toNat < 4294967296)
    (hInputApart : ∀ input ∈ inputs,
      regionsDisjoint (input.1.toNat, input.2.data.size) ABI.scratch ∧
        regionsDisjoint (input.1.toNat, input.2.data.size) (root.toNat, capacity.toNat))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno root' length : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.returned errno outputs)
        final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root') →
      Bytes.Rep heap' (PureTransport.erase final) root' length
        (resultBytes call.params (sysReply errno outputs) 0) →
      heap'.top.toNat ≤ heap0.top.toNat + budget →
      ReadAllOutside base s0 sF → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      (∀ i, i < call.params.countP Param.isResult → sF.get (base + 3 + i) =
        some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0))) →
      sF.get (base + 1) = some (.i64 root') → sF.get (base + 2) = some (.i64 length) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.trapped message outputs)
        final.host → K (.Trap final message)) :
    wp target (sysLowerInputsCode call.params locs inputLocs (base + 1) 0 ++
      [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
       .iff 0 0 (sysLoadCode call.params 0 (base + 3) ++ sysKeepCode buffer base)
         (sysDiscardCodeWith calls buffer base) [] []]) K before s env := by
  have hAddress := hReady.address
  have hRootSmall : root.toNat < 4294967296 := by omega
  have hInputCount' : inputs.length = call.params.count .input := hInputCount
  have hMemory : 16 ≤ before.mem.pages * 65536 := by
    have hBase := hBefore.at_.base
    have hBound := hBefore.at_.top
    change 16 ≤ (PureTransport.erase before).mem.pages * 65536
    omega
  have hCapacityEq : ∀ value,
      flatCapacityWith call.params values (inputs.map Prod.snd) = some value →
      value.toNat = capacity.toNat := by
    intro value found
    rcases hBuffer with ⟨_, none', _, _⟩ | ⟨place, _, found', _, _⟩
    · simp [none'] at found
    · rw [found'] at found
      cases found
      rfl
  have hBufferCall : ∀ value,
      flatCapacityWith call.params values (inputs.map Prod.snd) = some value →
      root.toNat + value.toNat ≤ before.mem.pages * 65536 ∧
        root.toNat + value.toNat < 2 ^ 32 ∧
        (16 ≤ root.toNat ∨ (value.toNat = 0 ∧ root = 0)) := by
    intro value found
    rw [hCapacityEq value found]
    refine ⟨hReady.memory hBefore.at_, by omega, ?_⟩
    rcases hReady with ⟨rfl, rfl⟩ | ⟨previous, hBuf, _⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl (by have := hBuf.object.base; omega)
  have hInputApartCall : ∀ input ∈ inputs,
      regionsDisjoint (input.1.toNat, input.2.data.size) ABI.scratch ∧
        ∀ value, flatCapacityWith call.params values (inputs.map Prod.snd) = some value →
          regionsDisjoint (input.1.toNat, input.2.data.size) (root.toNat, value.toNat) := by
    intro input member
    refine ⟨(hInputApart input member).1, fun value found => ?_⟩
    rw [hCapacityEq value found]
    exact (hInputApart input member).2
  have hBaseLow : s.params.length ≤ base := by rw [hOutside.params]; exact hLow
  have hBaseHigh : base < s.params.length + s.locals.length := by
    rw [hOutside.params, hOutside.length]; exact Locals.lt_total (by omega)
  refine wp_sys_flat_call_inputs_with (rootLocal := base + 1) hImports hHost hCall hKinds hOutputs
    hResults hAccepted hHeld hCount hInputs hInputCount hRootLocal hRootSmall hMemory hBufferCall
    hInputAt hInputApartCall ?_ ?_
  · intro after errno outputs hSys hFrame hShown
    have hFrame' := flat_frame_cover_inputs (capacity := capacity.toNat) hKinds hOutputs hResults
      hInputCount' hRootSmall hCapacityEq hFrame
    have hStep := hReady.frame_step hBefore hFrame'
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hSizes : outputs.map (fun output => output.data.size) =
        outputSizesOf call.params (host.reported before.host.world call)
          (flatArgsWith call.params values (inputs.map Prod.snd)) := hBound.1
    have hSys' : (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd))
        (.returned errno outputs) after.host := by rw [← hWorld]; exact hSys
    have hPages : after.mem.pages = before.mem.pages := hFrame.pages
    have hMemoryAfter : 16 ≤ after.mem.pages * 65536 := by rw [hPages]; exact hMemory
    simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
    refine wp_localSet_local hBaseLow hBaseHigh ?_
    have hGet1 : (setLocal { s with values := s.values } base (.i64 errno)).get base =
        some (.i64 errno) := Locals.get_setLocal_same hBaseLow hBaseHigh
    have hOther1 : ∀ j, j ≠ base →
        (setLocal { s with values := s.values } base (.i64 errno)).get j = s.get j :=
      fun j hj => Locals.get_setLocal_ne (s := { s with values := s.values }) hBaseLow hj
    have hOutside1 : ReadAllOutside base s0 (setLocal { s with values := s.values } base
        (.i64 errno)) := (hOutside.values s.values).set hLow le_rfl (by omega)
    have hPositions : base + 6 ≤ s0.params.length + s0.locals.length := by
      have := hHigh
      simp only [Locals.positions] at this
      omega
    have hS6 : base + 6 ≤ s.params.length + s.locals.length := by
      rw [hOutside.params, hOutside.length]; exact hPositions
    simp only [wp_localGet_cons, hGet1, wp_eqzI64_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : errno = 0
    · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
      have hReply : sysReply errno outputs = ⟨errno, outputs⟩ := by simp [sysReply, hZero]
      refine wp_sys_loads_inputs (errno := errno) hMemoryAfter call.params values inputs 0
        (base + 3) outputs _ _ _ hKinds hOutputs (by omega) hInputCount' (hShown hZero) hSizes
        (by simp only [setLocal]; omega) (by simp only [setLocal, List.length_set]; omega) ?_
      intro sL outsideL heldL
      have hKeepL : ∀ j, (j < base + 3 ∨ base + 3 + call.params.countP Param.isResult ≤ j) →
          sL.get j = (setLocal { s with values := s.values } base (.i64 errno)).get j :=
        fun j hj => (outsideL.others j hj).trans rfl
      have hOutsideL : ReadAllOutside base s0 sL := by
        refine ⟨outsideL.params.trans hOutside1.params, outsideL.length.trans hOutside1.length,
          fun j hj => ?_⟩
        rw [hKeepL j (by omega)]
        exact hOutside1.others j hj
      have hWordsL : ∀ i, i < call.params.countP Param.isResult → sL.get (base + 3 + i) =
          some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0)) := by
        intro i hi
        rw [hReply]
        exact heldL i hi
      have hErrnoL : sL.get base = some (.i64 errno) := (hKeepL base (by omega)).trans hGet1
      have hRootL : sL.get (base + 1) = some (.i64 root) :=
        ((hKeepL (base + 1) (by omega)).trans (hOther1 (base + 1) (by omega))).trans hRootLocal
      have hLengthL : sL.get (base + 2) = some (.i64 0) :=
        ((hKeepL (base + 2) (by omega)).trans (hOther1 (base + 2) (by omega))).trans hLengthLocal
      rcases hBuffer with ⟨rfl, none', rfl, rfl⟩ | ⟨place, rfl, found, hPlace, placeOut⟩
      · simp only [sysKeepCode, wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        refine hNext heap after { sL with values := s.values } errno 0 0 outputs hSys' hStep ?_
          hTop (hOutsideL.values s.values) rfl hErrnoL hWordsL hRootL hLengthL
        rw [resultBytes_none_inputs call.params values _ _ 0 hKinds (by simpa using hInputCount')
          none']
        exact Bytes.Rep.empty heap (PureTransport.erase after)
      · have hOutputAt := flat_output_at_inputs (errno := errno) call.params values inputs outputs
          0 capacity hKinds hOutputs hInputCount' (hShown hZero) hSizes found
        have hRoot64 : root.toUInt32.toUInt64 = root := read_narrow64 root hRootSmall
        rw [hRoot64] at hOutputAt
        have hRep := hReady.output_rep hFrame' hOutputAt.1 hOutputAt.2
        have hPlaceL : sL.get place = some (.i64 capacity) :=
          ((hKeepL place (by omega)).trans (hOther1 place (by omega))).trans hPlace
        have hLow2 : sL.params.length ≤ base + 2 := by rw [hOutsideL.params]; omega
        have hHigh2 : base + 2 < sL.params.length + sL.locals.length := by
          rw [hOutsideL.params, hOutsideL.length]; omega
        simp only [sysKeepCode, List.cons_append, List.nil_append, wp_localGet_cons,
          Locals.get_values, hPlaceL]
        refine wp_localSet_local hLow2 hHigh2 ?_
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hOther2 : ∀ j, j ≠ base + 2 →
            (setLocal { sL with values := s.values } (base + 2) (.i64 capacity)).get j =
              sL.get j :=
          fun j hj => Locals.get_setLocal_ne (s := { sL with values := s.values }) hLow2 hj
        refine hNext heap after
          { setLocal { sL with values := s.values } (base + 2) (.i64 capacity) with
            values := s.values } errno root capacity outputs hSys' hStep (by rwa [hReply]) hTop
          (((hOutsideL.values s.values).set hLow (by omega) (by omega)).values s.values) rfl
          ((hOther2 base (by omega)).trans hErrnoL)
          (fun i hi => (hOther2 (base + 3 + i) (by omega)).trans (hWordsL i hi))
          ((hOther2 (base + 1) (by omega)).trans hRootL)
          (Locals.get_setLocal_same (s := { sL with values := s.values }) hLow2 hHigh2)
    · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, hZero]
      have hWordsZero : ∀ i, i < call.params.countP Param.isResult →
          (setLocal { s with values := s.values } base (.i64 errno)).get (base + 3 + i) =
            some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0)) := by
        intro i hi
        rw [hReply, resultWords_empty, hOther1 _ (by omega)]
        have hZeroLocal : s.get (base + 3 + i) = some (.i64 0) := by
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · exact hThree
          · exact hFour
        rw [hZeroLocal]
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]
      have hRoot1 : (setLocal { s with values := s.values } base (.i64 errno)).get (base + 1) =
          some (.i64 root) := (hOther1 (base + 1) (by omega)).trans hRootLocal
      have hLength1 : (setLocal { s with values := s.values } base (.i64 errno)).get (base + 2) =
          some (.i64 0) := (hOther1 (base + 2) (by omega)).trans hLengthLocal
      rcases hBuffer with ⟨rfl, none', rfl, rfl⟩ | ⟨place, rfl, found, hPlace, placeOut⟩
      · simp only [sysDiscardCodeWith, wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        refine hNext heap after
          { setLocal { s with values := s.values } base (.i64 errno) with values := s.values }
          errno 0 0 outputs hSys' hStep ?_ hTop (hOutside1.values s.values) rfl hGet1 hWordsZero
          hRoot1 hLength1
        rw [hReply, resultBytes_empty]
        exact Bytes.Rep.empty heap (PureTransport.erase after)
      · have hEmpty := hReady.empty_rep hBefore.at_ hFrame'
        have hLow1 : (setLocal { s with values := s.values } base (.i64 errno)).params.length ≤
            base + 1 := by simp only [setLocal]; omega
        have hHigh1 : base + 1 < (setLocal { s with values := s.values } base (.i64 errno)).params.length +
            (setLocal { s with values := s.values } base (.i64 errno)).locals.length := by
          simp only [setLocal, List.length_set]; omega
        simp only [sysDiscardCodeWith]
        rw [← List.append_nil (discardReadCodeWith calls (base + 1))]
        refine wp_discard_read_with runtime layout profile hImports sourceHost hStep.at_ hEmpty
          hRoot1 hLow1 hHigh1 ?_
        intro final hStore hFinalWorld
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hFinalStep := read_discard_step hStep hEmpty hStore
        have hFinalTop := read_discard_top hStep.at_ hEmpty
        have hOtherD : ∀ j, j ≠ base + 1 →
            (setLocal (setLocal { s with values := s.values } base (.i64 errno)) (base + 1)
              (.i64 0)).get j = (setLocal { s with values := s.values } base (.i64 errno)).get j :=
          fun j hj => Locals.get_setLocal_ne hLow1 hj
        refine hNext _ final
          { setLocal (setLocal { s with values := s.values } base (.i64 errno)) (base + 1)
            (.i64 0) with values := s.values } errno 0 0 outputs
          (by rw [hFinalWorld]; exact hSys')
          (by simpa only [Bytes.regions, ite_true] using hFinalStep) ?_
          (by rw [hFinalTop]; exact hTop)
          ((hOutside1.set hLow (by omega) (by omega)).values s.values) rfl
          ((hOtherD base (by omega)).trans hGet1)
          (fun i hi => (hOtherD (base + 3 + i) (by omega)).trans (hWordsZero i hi))
          (Locals.get_setLocal_same hLow1 hHigh1)
          ((hOtherD (base + 2) (by omega)).trans hLength1)
        rw [hReply, resultBytes_empty]
        exact Bytes.Rep.empty _ _
  · intro after message outputs hSys hFrame
    exact hTrap after message outputs (by rw [← hWorld]; exact hSys)

end Verified.Wasi
