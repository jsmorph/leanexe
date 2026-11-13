import Verified.Wasi.SysFlat

/-! The call of a reported request into its block: the hidden region's address, the call with
the hidden region and the shown region at the block's root, and the code after the call, which
keeps the shown region's size as the length on errno 0 and releases the block otherwise. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_localGet_get {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {i : Nat} {v : Value} {rest : Program} {Q : Assertion α} (h : s.get i = some v)
    (next : wp m rest Q st { s with values := v :: s.values } env) :
    wp m (.localGet i :: rest) Q st s env := by
  rw [wp_localGet_cons, h]
  exact next

/-- The hidden region's address: the end of the shown region rounded up to a multiple of 4. -/
def hiddenAddress (root size : UInt64) : UInt64 :=
  (root + size + 3) - (root + size + 3) % 4

theorem hiddenAddress_toNat {root size : UInt64} (h : root.toNat + size.toNat + 3 < 4294967296) :
    (hiddenAddress root size).toNat =
      (root.toNat + size.toNat + 3) - (root.toNat + size.toNat + 3) % 4 := by
  have hSum : (root + size + 3).toNat = root.toNat + size.toNat + 3 := by
    rw [UInt64.toNat_add, UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (a := root.toNat + size.toNat) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hRem : ((root + size + 3) % 4).toNat = (root.toNat + size.toNat + 3) % 4 := by
    rw [UInt64.toNat_mod, hSum]
    rfl
  rw [hiddenAddress, UInt64.toNat_sub_of_le _ _ (by
    rw [UInt64.le_iff_toNat_le, hRem, hSum]; omega), hSum, hRem]

/-- A reported request with its hidden region at `hidden` and its shown region at `root`. -/
theorem reported_request {World : Type} {before : Store (Observed World)} {call : Call}
    {hidden root : UInt32} {count size : Nat}
    (hParams : call.params = [.reported 4 4 false, .reported 1 1 true])
    (hHidden : hidden.toNat % 4 = 0) (hApart : root.toNat + size ≤ hidden.toNat)
    (hMemory : hidden.toNat + 4 * count ≤ before.mem.pages * 65536)
    (hAddress : hidden.toNat + 4 * count < 2 ^ 32) :
    SysRequest before [.i32 hidden, .i32 root] call [] [hidden, root] [4 * count, size] := by
  refine ⟨by simp [hParams, argsFit, Param.takesArg],
    by simp [Call.reject, hParams, rejectArgs, Param.takesArg],
    by simp [hParams, lowerArgs], by simp [hParams, inputPlaces], ?_, ?_,
    by simp [hParams, inputPlaces]⟩
  · intro region member
    simp only [hParams, outputRegions, List.headD_cons, List.tail_cons, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨by simpa using hMemory, by simpa using hAddress, by simpa using hHidden⟩
    · exact ⟨by simp only; omega, by simp only; omega, Nat.mod_one _⟩
  · simp only [hParams, outputRegions, List.headD_cons, List.tail_cons,
      List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
      forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
      and_true, Region.span, regionsDisjoint]
    omega


/-- The hidden address, the call of a reported request into its block, and the code after the
call: errno 0 keeps the shown region's size as the length, and an errno releases the block and
clears the sizes and the length. -/
theorem wp_sys_reported_call_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial before : Store (Observed World)} {heap0 heap : Heap} {call : LeanExe.Wasi.Call}
    {s0 s : Locals} {base : Nat} {root count size : UInt64} {previous : LeanExe.Bytes}
    {budget : Nat} {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = [.reported 4 4 false, .reported 1 1 true])
    (hSizes : host.reported before.host.world call = [4 * count.toNat, size.toNat])
    (hBlock : size.toNat + 4 * count.toNat + 3 < 4294967296)
    (hBuffer : Heap.Buffer heap (PureTransport.erase before) root previous)
    (hCapacity : size.toNat + 4 * count.toNat + 3 ≤ capacityAt (PureTransport.erase before) root)
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hTop : heap.top.toNat ≤ heap0.top.toNat + budget)
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hOutside : ReadAllOutside base s0 s)
    (hCountLocal : s.get (base + 1) = some (.i64 count))
    (hSizeLocal : s.get (base + 2) = some (.i64 size))
    (hRootLocal : s.get (base + 3) = some (.i64 root))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno root' length : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys before.host call [] (.returned errno outputs) final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root') →
      Bytes.Rep heap' (PureTransport.erase final) root' length
        ((sysReply errno outputs).bytes 0) →
      heap'.top.toNat ≤ heap0.top.toNat + budget →
      ReadAllOutside base s0 sF → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      sF.get (base + 1) = some (.i64 (if errno = 0 then count else 0)) →
      sF.get (base + 2) = some (.i64 (if errno = 0 then size else 0)) →
      sF.get (base + 3) = some (.i64 root') → sF.get (base + 4) = some (.i64 length) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys before.host call [] (.trapped message outputs) final.host →
      K (.Trap final message)) :
    wp target (hiddenAddressCode base ++
      [.localGet (base + 3), .wrapI64, .call (3 + calls.idxOf call), .extendUI32,
       .localSet base, .localGet base, .eqzI64,
       .iff 0 0 [.localGet (base + 2), .localSet (base + 4)]
         (discardReadCodeWith calls (base + 3) ++
           [.constI64 0, .localSet (base + 1), .constI64 0, .localSet (base + 2),
            .constI64 0, .localSet (base + 4)])
         [] []]) K before s env := by
  have hBase := hBuffer.object.base
  have hAddress := hBuffer.object.address
  have hBelow := hBuffer.object.below
  have hHeapTop := hBefore.at_.top
  have hRootSmall : root.toNat + size.toNat + 4 * count.toNat + 3 < 4294967296 := by omega
  have hMemoryRoom : root.toNat + size.toNat + 4 * count.toNat + 3 ≤
      before.mem.pages * 65536 := by
    change _ ≤ (PureTransport.erase before).mem.pages * 65536
    omega
  have hPositions : base + 6 ≤ s0.params.length + s0.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have bound := fun i (hi : base ≤ i) (hi' : i < base + 6) => hOutside.bounds hLow hHigh hi hi'
  have hsLow : s.params.length ≤ base := by rw [hOutside.params]; exact hLow
  have hsHigh : base + 6 ≤ s.params.length + s.locals.length := by
    rw [hOutside.params, hOutside.length]; exact hPositions
  have hHiddenNat := hiddenAddress_toNat (root := root) (size := size) (by omega)
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hHidden32 : (hiddenAddress root size).toUInt32.toNat = (hiddenAddress root size).toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  -- The hidden address.
  simp only [hiddenAddressCode, List.cons_append, List.nil_append, wp_localGet_cons,
    hRootLocal, hSizeLocal, Locals.get_values, wp_addI64_cons, wp_constI64_cons]
  refine wp_localSet_local (bound (base + 4) (by omega) (by omega)).1
    (bound (base + 4) (by omega) (by omega)).2 ?_
  have hLowT := (bound (base + 4) (by omega) (by omega)).1
  have hOtherT : ∀ j, j ≠ base + 4 →
      (setLocal { s with values := s.values } (base + 4) (.i64 (root + size + 3))).get j =
        s.get j :=
    fun j hj => Locals.get_setLocal_ne (s := { s with values := s.values }) hLowT hj
  have hT : (setLocal { s with values := s.values } (base + 4) (.i64 (root + size + 3))).get
      (base + 4) = some (.i64 (root + size + 3)) :=
    Locals.get_setLocal_same (s := { s with values := s.values }) hLowT
      (bound (base + 4) (by omega) (by omega)).2
  simp only [wp_localGet_cons, hT, Locals.get_values, wp_constI64_cons,
    wp_remUI64_cons, show (4 : UInt64) ≠ 0 by decide, ite_false, wp_subI64_cons,
    wp_wrapI64_cons, wrap_toUInt32, hOtherT (base + 3) (by omega), hRootLocal]
  have hBlockU : (size + 4 * count + 3).toNat = size.toNat + 4 * count.toNat + 3 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (a := 4 * count.toNat) (by omega),
      Nat.mod_eq_of_lt (a := size.toNat + 4 * count.toNat) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hRequest : SysRequest before
      [.i32 (hiddenAddress root size).toUInt32, .i32 root.toUInt32] call []
      [(hiddenAddress root size).toUInt32, root.toUInt32]
      (host.reported before.host.world call) := by
    rw [hSizes]
    exact reported_request hParams (by rw [hHidden32, hHiddenNat]; omega)
      (by rw [hRoot32, hHidden32, hHiddenNat]; omega) (by rw [hHidden32, hHiddenNat]; omega)
      (by rw [hHidden32, hHiddenNat]; omega)
  have hImpLength : (ABI.callImport call).params.length = 2 := by
    simp [ABI.callImport, ABI.callType, hParams, ABI.paramTypes]
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  refine wp_call_host_contract (id := 3 + calls.idxOf call) (imp := ABI.callImport call)
    (c := sysContract host call) (by rw [hImports]; exact ABI.importsWith_call hCall) hHost
    (by rw [hImports, ABI.importsWith_length]; omega) (hostSpecWith_sys host hCall) ?_ ?_ ?_
  · intro returned after contract
    simp only [hImpLength, List.take_succ_cons, List.take_zero, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append] at contract
    obtain ⟨errno, outputs, rfl, hSys, hFrame, hShown⟩ := contract [] _ hRequest
    have hFrame' : GuestFrame before after
        [ABI.scratch, (root.toNat, (size + 4 * count + 3).toNat)] := by
      refine hFrame.cover fun span member => ?_
      simp only [hSizes, hParams, outputRegions, List.headD_cons, List.tail_cons, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Region.span] at member
      rcases member with rfl | rfl
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_, ?_⟩ <;>
          simp only [hHidden32, hHiddenNat, hBlockU] <;> omega
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_, ?_⟩ <;>
          simp only [hRoot32, hBlockU] <;> omega
    have hReady : ReadReady heap (PureTransport.erase before) root (size + 4 * count + 3) :=
      Or.inr ⟨previous, hBuffer, by rw [hBlockU]; exact hCapacity⟩
    have hStep := hReady.frame_step hBefore hFrame'
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hOutputSizes : outputs.map (fun output => output.data.size) = [size.toNat] := by
      have := hBound.1
      simp only [Transfer.committed] at this
      rw [this]
      simp [Call.outputSizes, hParams, outputSizesOf, observedHost, hSizes]
    simp only [hParams, ABI.paramTypes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append, ABI.callImport, ABI.callType, List.length_cons,
      List.length_nil, Nat.zero_add]
    simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
    let sT := setLocal { s with values := s.values } (base + 4) (.i64 (root + size + 3))
    have outsideT : ReadAllOutside base s0 sT := (hOutside.values s.values).set hLow (by omega)
      (by omega)
    have hLowE := (outsideT.bounds hLow hHigh (i := base) le_rfl (by omega))
    refine wp_localSet_local (s := sT) hLowE.1 hLowE.2 ?_
    let sE := setLocal { sT with values := sT.values } base (.i64 errno)
    have outsideE : ReadAllOutside base s0 sE := (outsideT.values sT.values).set hLow le_rfl
      (by omega)
    change wp target _ K after sE env
    have hGetE : sE.get base = some (.i64 errno) := Locals.get_setLocal_same hLowE.1 hLowE.2
    have hOtherE : ∀ j, j ≠ base → j ≠ base + 4 → sE.get j = s.get j := fun j hj hj' =>
      (Locals.get_setLocal_ne (s := { sT with values := sT.values }) hLowE.1 hj).trans
        (hOtherT j hj')
    refine wp_localGet_get hGetE ?_
    simp only [wp_eqzI64_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : errno = 0
    · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
      have hSizeE : sE.get (base + 2) = some (.i64 size) :=
        (hOtherE (base + 2) (by omega) (by omega)).trans hSizeLocal
      simp only [List.cons_append, List.nil_append]
      refine wp_localGet_get hSizeE ?_
      have hB4 := outsideE.bounds hLow hHigh (i := base + 4) (by omega) (by omega)
      refine wp_localSet_local (s := sE) hB4.1 hB4.2 ?_
      let sK := setLocal { sE with values := sE.values } (base + 4) (.i64 size)
      have outsideK : ReadAllOutside base s0 sK := (outsideE.values sE.values).set hLow
        (by omega) (by omega)
      have hOtherK : ∀ j, j ≠ base + 4 → sK.get j = sE.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { sE with values := sE.values }) hB4.1 hj
      have hGetK : sK.get (base + 4) = some (.i64 size) := Locals.get_setLocal_same hB4.1 hB4.2
      change wp target [] _ after sK env
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      -- The shown output and its representation.
      cases outputs with
      | nil => simp at hOutputSizes
      | cons output rest =>
        cases rest with
        | cons _ _ => simp at hOutputSizes
        | nil =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hOutputSizes
          have hData := (hShown hZero)
          simp only [hSizes, hParams, outputRegions, List.headD_cons, List.tail_cons, ShownAt,
            Bool.false_eq_true, ite_false, ite_true, read_narrow64 root (by omega)] at hData
          have hBuffer' := allocated_afterRead hBuffer hFrame' (by omega) hData.1
          have hRep := hBuffer'.rep
          have hSizeEq : output.size = size := by
            apply UInt64.toNat_inj.mp
            rw [LeanExe.Bytes.size_toNat output (by omega), hOutputSizes]
          rw [hSizeEq] at hRep
          refine hNext heap after { sK with values := s.values } errno root size [output] hSys
            hStep (by simpa [sysReply, hZero, Reply.bytes] using hRep) hTop
            (outsideK.values s.values) rfl ((hOtherK base (by omega)).trans hGetE) ?_ ?_ ?_
            hGetK
          · rw [ite_eq_left hZero]
            exact (hOtherK (base + 1) (by omega)).trans
              ((hOtherE (base + 1) (by omega) (by omega)).trans hCountLocal)
          · rw [ite_eq_left hZero]
            exact (hOtherK (base + 2) (by omega)).trans hSizeE
          · exact (hOtherK (base + 3) (by omega)).trans
              ((hOtherE (base + 3) (by omega) (by omega)).trans hRootLocal)
    · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      have hEmpty := hReady.empty_rep hBefore.at_ hFrame'
      have hRootE : sE.get (base + 3) = some (.i64 root) :=
        (hOtherE (base + 3) (by omega) (by omega)).trans hRootLocal
      have hB3 := outsideE.bounds hLow hHigh (i := base + 3) (by omega) (by omega)
      refine wp_discard_read_with (s := { sE with values := sE.values }) runtime layout profile
        hImports sourceHost hStep.at_ hEmpty hRootE hB3.1 hB3.2 ?_
      intro final hStore hFinalWorld
      have hFinalStep := read_discard_step hStep hEmpty hStore
      have hFinalTop := read_discard_top hStep.at_ hEmpty
      let sD := setLocal { sE with values := sE.values } (base + 3) (.i64 0)
      have outsideD : ReadAllOutside base s0 sD := (outsideE.values sE.values).set hLow
        (by omega) (by omega)
      change wp target _ _ final sD env
      have hB1 := outsideD.bounds hLow hHigh (i := base + 1) (by omega) (by omega)
      refine wp_set_word hB1.1 hB1.2 ?_
      let s1 := setLocal sD (base + 1) (.i64 0)
      have outside1 : ReadAllOutside base s0 s1 := outsideD.set hLow (by omega) (by omega)
      change wp target _ _ final s1 env
      have hB2 := outside1.bounds hLow hHigh (i := base + 2) (by omega) (by omega)
      refine wp_set_word hB2.1 hB2.2 ?_
      let s2 := setLocal s1 (base + 2) (.i64 0)
      have outside2 : ReadAllOutside base s0 s2 := outside1.set hLow (by omega) (by omega)
      change wp target _ _ final s2 env
      have hB4 := outside2.bounds hLow hHigh (i := base + 4) (by omega) (by omega)
      refine wp_set_word hB4.1 hB4.2 ?_
      let s3 := setLocal s2 (base + 4) (.i64 0)
      have outside3 : ReadAllOutside base s0 s3 := outside2.set hLow (by omega) (by omega)
      change wp target [] _ final s3 env
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      have g3 : ∀ j, j ≠ base + 4 → s3.get j = s2.get j := fun j hj =>
        Locals.get_setLocal_ne hB4.1 hj
      have g2 : ∀ j, j ≠ base + 2 → s2.get j = s1.get j := fun j hj =>
        Locals.get_setLocal_ne hB2.1 hj
      have g1 : ∀ j, j ≠ base + 1 → s1.get j = sD.get j := fun j hj =>
        Locals.get_setLocal_ne hB1.1 hj
      have gD : ∀ j, j ≠ base + 3 → sD.get j = sE.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { sE with values := sE.values }) hB3.1 hj
      refine hNext _ final { s3 with values := s.values } errno 0 0 outputs
        (by rw [hFinalWorld]; exact hSys)
        (by simpa only [Bytes.regions, ite_true] using hFinalStep) ?_
        (by rw [hFinalTop]; exact hTop) (outside3.values s.values) rfl ?_ ?_ ?_ ?_ ?_
      · simp only [sysReply, hZero, ite_false, Reply.bytes, List.getElem?_nil, Option.getD_none]
        exact Bytes.Rep.empty _ _
      · exact (g3 base (by omega)).trans ((g2 base (by omega)).trans ((g1 base (by omega)).trans
          ((gD base (by omega)).trans hGetE)))
      · rw [ite_eq_right hZero]
        exact (g3 (base + 1) (by omega)).trans ((g2 (base + 1) (by omega)).trans
          (Locals.get_setLocal_same hB1.1 hB1.2))
      · rw [ite_eq_right hZero]
        exact (g3 (base + 2) (by omega)).trans (Locals.get_setLocal_same hB2.1 hB2.2)
      · exact (g3 (base + 3) (by omega)).trans ((g2 (base + 3) (by omega)).trans
          ((g1 (base + 3) (by omega)).trans
            (Locals.get_setLocal_same (s := { sE with values := sE.values }) hB3.1 hB3.2)))
      · exact Locals.get_setLocal_same hB4.1 hB4.2

  · intro final message contract
    simp only [hImpLength, List.take_succ_cons, List.take_zero, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append] at contract
    obtain ⟨outputs, hSys, _⟩ := contract [] _ hRequest
    exact hTrap final message outputs hSys
  · intro final tag arguments contract
    simp only [hImpLength, List.take_succ_cons, List.take_zero, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append] at contract
    exact (contract [] _ hRequest).elim

end Verified.Wasi
