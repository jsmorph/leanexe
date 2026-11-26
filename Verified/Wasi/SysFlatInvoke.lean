module

public import Verified.Wasi.SysFlatParts
public import Verified.Wasi.ReadAllLoop

@[expose] public section

/-! The host call of a flat command without an output and the code after it: the code calls the
import, sets the errno, and on errno 0 loads the result words. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

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

theorem sys_extend_errno {errno : UInt64} (h : errno.toNat ≤ 76) :
    UInt64.ofNat errno.toUInt32.toNat = errno := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]
      have := errno.toUInt32.toNat_lt
      omega),
    UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]


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
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | output => simp [flatCapacityWith] at none'
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        exact resultBytes_none_inputs params values inputs reply index kinds.2
          (by simpa [List.count_cons] using count) (by simpa [flatCapacityWith] using none')
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      exact resultBytes_none_inputs params values.tail inputs reply index kinds.2
        (by simpa [List.count_cons] using count)
        (by simpa [flatCapacityWith, Param.takesArg] using none')
    | result32 | result64 =>
      exact resultBytes_none_inputs params values inputs reply (index + 1) kinds.2
        (by simpa [List.count_cons] using count)
        (by simpa [flatCapacityWith, Param.takesArg] using none')

/-- The host call of an accepted flat request with inputs and without an output, and the code
after it. -/
theorem wp_sys_flat_invoke_inputs_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {s0 s : Locals} {base : Nat} {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.inputKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hNone : flatCapacityWith call.params values (inputs.map Prod.snd) = none)
    (hAccepted : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hOutside : ReadAllOutside base s0 s)
    (hRootLocal : s.get (base + 1) = some (.i64 0))
    (hThree : s.get (base + 3) = some (.i64 0)) (hFour : s.get (base + 4) = some (.i64 0))
    (hInputAt : ∀ input ∈ inputs,
      Bytes.At initial.mem input.1 input.2 ∧ input.1.toNat < 4294967296)
    (hInputApart : ∀ input ∈ inputs,
      regionsDisjoint (input.1.toNat, input.2.data.size) ABI.low)
    (hNext : ∀ (final : Store (Observed World)) (sF : Locals) (errno : UInt64)
      (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.returned errno outputs)
        final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      ReadAllOutside base s0 sF → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      (∀ i, i < call.params.countP Param.isResult → sF.get (base + 3 + i) =
        some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0))) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.trapped message outputs)
        final.host → K (.Trap final message)) :
    wp target (sysFlatCallInputsCodeWith calls call locs inputLocs base) K initial s env := by
  have hInputCount' : inputs.length = call.params.count .input := by
    rw [hInputCount, Call.inputCount_of_inputKind hKinds]
  have hMemory : 16 ≤ initial.mem.pages * 65536 := by
    have hBase := hHeap.base
    have hBound := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega
  have hBaseLow : s.params.length ≤ base := by rw [hOutside.params]; exact hLow
  have hBaseHigh : base < s.params.length + s.locals.length := by
    rw [hOutside.params, hOutside.length]; exact Locals.lt_total (by omega)
  simp only [sysFlatCallInputsCodeWith]
  refine wp_sys_flat_call_inputs_with (rootLocal := base + 1) (root := 0) hImports hHost hCall
    hKinds hOutputs hResults hAccepted hHeld hCount hInputs hInputCount hRootLocal (by decide)
    hMemory (fun value found => by simp [hNone] at found)
    hInputAt (fun input member => ⟨hInputApart input member, fun value found => by
      simp [hNone] at found⟩) ?_ ?_
  · intro after errno outputs hSys hFrame hShown
    have hFrame' := flat_frame_cover_inputs (capacity := 0) hKinds hOutputs hResults
      hInputCount' (by decide) (fun value found => by
        simp [hNone] at found) hFrame
    have hStep : Step heap (PureTransport.erase initial)
        (fun region => regionsDisjoint region ABI.low) heap (PureTransport.erase after) [] :=
      (read_zero_frame hFrame').scratchStep hHeap
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hSizes : outputs.map (fun output => output.data.size) =
        outputSizesOf call.params (host.reported initial.host.world call)
          (flatArgsWith call.params values (inputs.map Prod.snd)) := hBound.1
    have hMemoryAfter : 16 ≤ after.mem.pages * 65536 := by rw [hFrame.pages]; exact hMemory
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
      rw [← List.append_nil (sysLoadCode call.params 0 (base + 3))]
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
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      refine hNext after { sL with values := s.values } errno outputs
        hSys hStep
        (hOutsideL.values s.values) rfl ((hKeepL base (by omega)).trans hGet1) ?_
      intro i hi
      rw [hReply]
      exact heldL i hi
    · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, hZero]
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      refine hNext after
        { setLocal { s with values := s.values } base (.i64 errno) with values := s.values }
        errno outputs hSys hStep (hOutside1.values s.values) rfl hGet1 ?_
      intro i hi
      rw [hReply, resultWords_empty, Locals.get_values, hOther1 _ (by omega)]
      have hZeroLocal : s.get (base + 3 + i) = some (.i64 0) := by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · exact hThree
        · exact hFour
      rw [hZeroLocal]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]
  · intro after message outputs hSys _
    exact hTrap after message outputs hSys

end Verified.Wasi
