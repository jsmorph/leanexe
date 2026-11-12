import Verified.Wasi.SysReportedCall

/-! The code of a reported call, from the locals set to 0 to the errno, the reporter's words, and
the block's root and length on the stack: the reporter's call with its words at the scratch
addresses 0 and 8, the size test, the allocation of the block, and the call into it. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem reporterCall_params (call : LeanExe.Wasi.Call) :
    call.reporterCall.params = [.result32, .result32] := rfl

/-- The pushes of the five result locals. -/
theorem wp_push_five {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {base : Nat} {a b c d e : UInt64} {rest : Program} {Q : Assertion α}
    (ha : s.get base = some (.i64 a)) (hb : s.get (base + 1) = some (.i64 b))
    (hc : s.get (base + 2) = some (.i64 c)) (hd : s.get (base + 3) = some (.i64 d))
    (he : s.get (base + 4) = some (.i64 e))
    (h : wp m rest Q st { s with values :=
      ([a, b, c].map Value.i64 ++ [Value.i64 d, Value.i64 e]).reverse ++ s.values } env) :
    wp m (.localGet base :: .localGet (base + 1) :: .localGet (base + 2) :: .localGet (base + 3) ::
      .localGet (base + 4) :: rest) Q st s env := by
  simp only [wp_localGet_cons, Locals.get_values, ha, hb, hc, hd, he]
  simpa using h


/-- The code of a reported call.  The reporter's errno ends the call with that errno; sizes whose
block would reach `2 ^ 32` bytes give errno 61; otherwise the code allocates the block, calls the
import, and leaves the errno, the reporter's words, and the block's root and length. -/
theorem wp_sys_reported_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {call : LeanExe.Wasi.Call}
    {values : List UInt64} {s : Locals} {base : Nat} {rest : Program}
    {Q : Assertion (Observed World)} {aborts : Bool}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hReporter : calls[calls.idxOf call.reporterCall]? = some call.reporterCall)
    (hParams : call.params = [.reported 4 4 false, .reported 1 1 true])
    (hName : call.reporter = some call.reporterCall.name)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hRoom : aborts = false → ∀ (after : Store (Observed World)) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call.reporterCall [] (.returned 0 outputs)
        after.host →
      ∀ block, reportedBlock [.sys call.reporterCall [] (.returned 0 outputs)] = some block →
      heap.Within (PureTransport.erase initial) source (Bytes.allocationCost block.toNat))
    (hResource : aborts = true → ∀ (after : Store (Observed World))
      (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call.reporterCall [] (.returned 0 outputs)
        after.host →
      ∀ final : Store (Observed World), final.host = after.host →
        Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (errno count size root length : UInt64) (output : LeanExe.Bytes) (trace : List Event),
      Exec (observedHost host) (SysForm.reported.run call values) initial.host trace
        (.returned (wordsBytesValue 3 [errno, count, size] output)) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length output →
      heap'.top.toNat ≤ heap.top.toNat + sysCost .reported call values trace →
      ReadAllOutside base s finalLocals →
      wp target rest Q final { finalLocals with values :=
        ([errno, count, size].map Value.i64 ++ [Value.i64 root, Value.i64 length]).reverse ++
          s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (SysForm.reported.run call values) initial.host trace
        (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysReportedCodeWith calls call base ++ rest) Q initial s env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have outside0 := ReadAllOutside.refl base s
  simp only [sysReportedCodeWith, List.append_assoc, List.cons_append]
  -- The locals set to 0.
  have b0 := outside0.bounds hLow hHigh (i := base) le_rfl (by omega)
  refine wp_set_word b0.1 b0.2 ?_
  let s1 := setLocal s base (.i64 0)
  have outside1 : ReadAllOutside base s s1 := outside0.set hLow le_rfl (by omega)
  change wp target _ Q initial s1 env
  have b1 := outside1.bounds hLow hHigh (i := base + 1) (by omega) (by omega)
  refine wp_set_word b1.1 b1.2 ?_
  let s2 := setLocal s1 (base + 1) (.i64 0)
  have outside2 : ReadAllOutside base s s2 := outside1.set hLow (by omega) (by omega)
  change wp target _ Q initial s2 env
  have b2 := outside2.bounds hLow hHigh (i := base + 2) (by omega) (by omega)
  refine wp_set_word b2.1 b2.2 ?_
  let s3 := setLocal s2 (base + 2) (.i64 0)
  have outside3 : ReadAllOutside base s s3 := outside2.set hLow (by omega) (by omega)
  change wp target _ Q initial s3 env
  have b3 := outside3.bounds hLow hHigh (i := base + 3) (by omega) (by omega)
  refine wp_set_word b3.1 b3.2 ?_
  let s4 := setLocal s3 (base + 3) (.i64 0)
  have outside4 : ReadAllOutside base s s4 := outside3.set hLow (by omega) (by omega)
  change wp target _ Q initial s4 env
  have b4 := outside4.bounds hLow hHigh (i := base + 4) (by omega) (by omega)
  refine wp_set_word b4.1 b4.2 ?_
  let s5 := setLocal s4 (base + 4) (.i64 0)
  have outside5 : ReadAllOutside base s s5 := outside4.set hLow (by omega) (by omega)
  change wp target _ Q initial s5 env
  have z4 : s5.get (base + 4) = some (.i64 0) := Locals.get_setLocal_same b4.1 b4.2
  have z3 : s5.get (base + 3) = some (.i64 0) :=
    (Locals.get_setLocal_ne b4.1 (by omega)).trans (Locals.get_setLocal_same b3.1 b3.2)
  have z2 : s5.get (base + 2) = some (.i64 0) :=
    (Locals.get_setLocal_ne b4.1 (by omega)).trans ((Locals.get_setLocal_ne b3.1 (by omega)).trans
      (Locals.get_setLocal_same b2.1 b2.2))
  have z1 : s5.get (base + 1) = some (.i64 0) :=
    (Locals.get_setLocal_ne b4.1 (by omega)).trans ((Locals.get_setLocal_ne b3.1 (by omega)).trans
      ((Locals.get_setLocal_ne b2.1 (by omega)).trans (Locals.get_setLocal_same b1.1 b1.2)))
  have hMemory : 16 ≤ initial.mem.pages * 65536 := by
    have hBase := hHeap.base
    have hBound := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega
  -- The reporter's call.
  have hReporterKinds : call.reporterCall.params.all Param.flatKind = true := by
    rw [reporterCall_params]; rfl
  refine wp_sys_flat_call_with (call := call.reporterCall) (locs := []) (values := [])
    (rootLocal := base + 3) (root := 0) hImports hHost hReporter hReporterKinds
    (by rw [reporterCall_params]; decide) (by rw [reporterCall_params]; decide)
    rfl .nil rfl z3 (by decide)
    hMemory (by intro capacity found; rw [reporterCall_params] at found; simp [flatCapacity] at found)
    ?_ ?_
  · intro after errno outputs hSys hFrame hShown
    have hReporterOutputs : call.reporterCall.params.count .output ≤ 1 := by
      rw [reporterCall_params]; decide
    have hReporterResults : call.reporterCall.params.countP Param.isResult ≤ 2 := by
      rw [reporterCall_params]; decide
    have hFrame0 := flat_frame_cover (capacity := 0) hReporterKinds hReporterOutputs
      hReporterResults (by decide)
      (by intro v found; rw [reporterCall_params] at found; simp [flatCapacity] at found) hFrame
    have hScratch := read_zero_frame (by simpa using hFrame0)
    have hStep0 := hScratch.scratchStep hHeap
    have hBound := (observedHost host).sys_bound hSys
    have hErrno : errno.toNat ≤ 76 := hBound.2
    have hFits : call.reporterCall.reject [] = 0 := rfl
    simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
    have bE := outside5.bounds hLow hHigh (i := base) le_rfl (by omega)
    refine wp_localSet_local (s := s5) bE.1 bE.2 ?_
    let sE := setLocal { s5 with values := s5.values } base (.i64 errno)
    have outsideE : ReadAllOutside base s sE := (outside5.values s5.values).set hLow le_rfl
      (by omega)
    change wp target _ Q after sE env
    have hGetE : sE.get base = some (.i64 errno) := Locals.get_setLocal_same bE.1 bE.2
    have hOtherE : ∀ j, j ≠ base → sE.get j = s5.get j := fun j hj =>
      Locals.get_setLocal_ne (s := { s5 with values := s5.values }) bE.1 hj
    refine wp_localGet_get hGetE ?_
    simp only [wp_eqzI64_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    -- The pushes after the outer `iff`.
    have finish : ∀ (final : Store (Observed World)) (sF : Locals) (heap' : Heap)
        (e c z root length : UInt64) (output : LeanExe.Bytes) (trace : List Event),
        Exec (observedHost host) (SysForm.reported.run call values) initial.host trace
          (.returned (wordsBytesValue 3 [e, c, z] output)) final.host →
        Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch)
          heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
        Bytes.Rep heap' (PureTransport.erase final) root length output →
        heap'.top.toNat ≤ heap.top.toNat + sysCost .reported call values trace →
        ReadAllOutside base s sF →
        sF.get base = some (.i64 e) → sF.get (base + 1) = some (.i64 c) →
        sF.get (base + 2) = some (.i64 z) → sF.get (base + 3) = some (.i64 root) →
        sF.get (base + 4) = some (.i64 length) →
        wp target (.localGet base :: .localGet (base + 1) :: .localGet (base + 2) ::
          .localGet (base + 3) :: .localGet (base + 4) :: ([] ++ rest)) Q final
          { sF with values := s.values } env := by
      intro final sF heap' e c z root length output trace execution step rep top outsideF g0 g1 g2
        g3 g4
      refine wp_push_five g0 g1 g2 g3 g4 ?_
      simpa only [List.nil_append] using
        hNext heap' final { sF with values := s.values } e c z root length output trace
          execution step rep top (outsideF.values s.values)
    have zE1 : sE.get (base + 1) = some (.i64 0) := (hOtherE (base + 1) (by omega)).trans z1
    have zE2 : sE.get (base + 2) = some (.i64 0) := (hOtherE (base + 2) (by omega)).trans z2
    have zE3 : sE.get (base + 3) = some (.i64 0) := (hOtherE (base + 3) (by omega)).trans z3
    have zE4 : sE.get (base + 4) = some (.i64 0) := (hOtherE (base + 4) (by omega)).trans z4
    by_cases hZero : errno = 0
    · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
      have hSizesL : outputs.map (fun output => output.data.size) = [4, 4] := by
        have := hBound.1
        simp only [Transfer.committed] at this
        rw [this]
        simp [Call.outputSizes, reporterCall_params, outputSizesOf]
      have hLength : outputs.length = 2 := by simpa using congrArg List.length hSizesL
      obtain ⟨word0, word1, rfl⟩ : ∃ word0 word1, outputs = [word0, word1] :=
        ⟨_, _, List.eq_getElem_of_length_eq_two outputs hLength⟩
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hSizesL
      have hShownL := hShown hZero
      simp only [flatRegions, reporterCall_params, flatArgs, flatPointers, outputRegions,
        ShownAt, ite_true, List.headD_cons, List.tail_cons] at hShownL
      obtain ⟨count, hc⟩ : ∃ count, littleEndian word0 = count := ⟨_, rfl⟩
      obtain ⟨size, hz⟩ : ∃ size, littleEndian word1 = size := ⟨_, rfl⟩
      have hCount32 : count.toNat < 4294967296 := by
        rw [← hc]; exact littleEndian_four_lt hSizesL.1
      have hSize32 : size.toNat < 4294967296 := by
        rw [← hz]; exact littleEndian_four_lt hSizesL.2
      have hTwo : call.reporterCall.params.countP Param.isResult = 2 := rfl
      simp only [sysReportedSizesCodeWith, List.append_assoc]
      have bL := outsideE.bounds hLow hHigh (i := base + 1) (by omega) (by omega)
      refine wp_sys_loads (errno := errno) (by rw [hScratch.pages]; exact hMemory)
        call.reporterCall.params [] 0 (base + 1) [word0, word1] _ _ _ hReporterKinds
        hReporterOutputs (by rw [hTwo]) (hShown hZero)
        (by simp [hSizesL, reporterCall_params, outputSizesOf, flatArgs]) bL.1
        (by
          rw [hTwo]
          have := (outsideE.bounds hLow hHigh (i := base + 2) (by omega) (by omega)).2
          show base + 1 + 2 ≤ sE.params.length + sE.locals.length
          omega) ?_
      intro sL outsideL heldL
      have hWords : resultWords call.reporterCall.params ⟨errno, [word0, word1]⟩ 0 =
          [count, size] := by
        simp [resultWords, reporterCall_params, Reply.word, hc, hz]
      have hCountL : sL.get (base + 1) = some (.i64 count) := by
        have := heldL 0 (by rw [hTwo]; decide)
        rw [hWords] at this
        simpa using this
      have hSizeL : sL.get (base + 2) = some (.i64 size) := by
        have := heldL 1 (by rw [hTwo]; decide)
        rw [hWords] at this
        simpa using this
      have hKeepL : ∀ j, (j < base + 1 ∨ base + 3 ≤ j) → sL.get j = sE.get j := by
        intro j hj
        exact outsideL.others j (by rw [hTwo]; omega)
      have hOutsideL : ReadAllOutside base s sL := by
        refine ⟨outsideL.params.trans outsideE.params, outsideL.length.trans outsideE.length,
          fun j hj => ?_⟩
        rw [hKeepL j (by omega)]
        exact outsideE.others j hj
      -- The block size.
      refine wp_localGet_get hSizeL ?_
      refine wp_localGet_get (by simpa using hCountL) ?_
      simp only [wp_constI64_cons, wp_mulI64_cons, wp_addI64_cons]
      have b4 := hOutsideL.bounds hLow hHigh (i := base + 4) (by omega) (by omega)
      refine wp_localSet_local b4.1 b4.2 ?_
      let sB := setLocal { sL with values := s.values } (base + 4) (.i64 (size + count * 4 + 3))
      have outsideB : ReadAllOutside base s sB := (hOutsideL.values s.values).set hLow (by omega)
        (by omega)
      change wp target _ _ after sB env
      have hGetB : sB.get (base + 4) = some (.i64 (size + count * 4 + 3)) :=
        Locals.get_setLocal_same b4.1 b4.2
      have hOtherB : ∀ j, j ≠ base + 4 → sB.get j = sL.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { sL with values := s.values }) b4.1 hj
      have hBlockNat : (size + count * 4 + 3).toNat = size.toNat + 4 * count.toNat + 3 := by
        rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (a := count.toNat * 4) (by omega),
          Nat.mod_eq_of_lt (a := size.toNat + count.toNat * 4) (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
      have hSource : (⟨0, [word0, word1]⟩ : Reply).word 1 +
          4 * (⟨0, [word0, word1]⟩ : Reply).word 0 + 3 = size + count * 4 + 3 := by
        simp only [Reply.word, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some, hc, hz]
        rw [UInt64.mul_comm]
      have hReplyZ : sysReply errno [word0, word1] = ⟨0, [word0, word1]⟩ := by
        simp [sysReply, hZero]
      refine wp_localGet_get hGetB ?_
      simp only [wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      have hCountB : sB.get (base + 1) = some (.i64 count) :=
        (hOtherB (base + 1) (by omega)).trans hCountL
      have hSizeB : sB.get (base + 2) = some (.i64 size) :=
        (hOtherB (base + 2) (by omega)).trans hSizeL
      have hRootB : sB.get (base + 3) = some (.i64 0) :=
        (hOtherB (base + 3) (by omega)).trans ((hKeepL (base + 3) (by omega)).trans zE3)
      by_cases hLarge : size + count * 4 + 3 ≥ 4294967296
      · rw [ite_eq_left (by simp [hLarge] :
          (if size + count * 4 + 3 ≥ 4294967296 then (1 : UInt32) else 0) ≠ 0)]
        have hBlockNone : reportedBlock [.sys call.reporterCall [] (.returned errno [word0, word1])]
            = none := by
          simp only [reportedBlock, hZero, true_and]
          rw [ite_eq_right]
          intro hSmall
          have : (⟨0, [word0, word1]⟩ : Reply).word 1 + 4 * (⟨0, [word0, word1]⟩ : Reply).word 0
              + 3 < 4294967296 := hSmall
          rw [hSource] at this
          exact absurd hLarge (by
            rw [ge_iff_le, UInt64.le_iff_toNat_le, hBlockNat]
            rw [UInt64.lt_iff_toNat_lt, hBlockNat] at this
            simp only [UInt64.reduceToNat] at this ⊢
            omega)
        have hExec : Exec (observedHost host) (SysForm.reported.run call values) initial.host
            [.sys call.reporterCall [] (.returned errno [word0, word1])]
            (.returned (wordsBytesValue 3 [61, 0, 0] LeanExe.Bytes.empty)) after.host := by
          refine .sys_return hFits hSys ?_
          rw [hReplyZ]
          have hCond : (4294967296 : UInt64) ≤ (⟨0, [word0, word1]⟩ : Reply).word 1 +
              4 * (⟨0, [word0, word1]⟩ : Reply).word 0 + 3 := by
            rw [hSource]; exact hLarge
          simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, hCond, ite_true]
          exact .pure _ _
        simp only [List.cons_append, List.nil_append]
        have c0 := outsideB.bounds hLow hHigh (i := base) le_rfl (by omega)
        refine wp_set_word c0.1 c0.2 ?_
        let t0 := setLocal { sB with values := sB.values } base (.i64 61)
        have o0 : ReadAllOutside base s t0 := (outsideB.values sB.values).set hLow le_rfl
          (by omega)
        change wp target _ _ after t0 env
        have c1 := o0.bounds hLow hHigh (i := base + 1) (by omega) (by omega)
        refine wp_set_word c1.1 c1.2 ?_
        let t1 := setLocal t0 (base + 1) (.i64 0)
        have o1 : ReadAllOutside base s t1 := o0.set hLow (by omega) (by omega)
        change wp target _ _ after t1 env
        have c2 := o1.bounds hLow hHigh (i := base + 2) (by omega) (by omega)
        refine wp_set_word c2.1 c2.2 ?_
        let t2 := setLocal t1 (base + 2) (.i64 0)
        have o2 : ReadAllOutside base s t2 := o1.set hLow (by omega) (by omega)
        change wp target _ _ after t2 env
        have c4 := o2.bounds hLow hHigh (i := base + 4) (by omega) (by omega)
        refine wp_set_word c4.1 c4.2 ?_
        let t4 := setLocal t2 (base + 4) (.i64 0)
        have o4 : ReadAllOutside base s t4 := o2.set hLow (by omega) (by omega)
        change wp target [] _ after t4 env
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        refine finish after t4 heap 61 0 0 0 0 .empty _ hExec
          (by simpa only [Bytes.regions, ite_true] using hStep0) (Bytes.Rep.empty _ _)
          (by simp [sysCost, hBlockNone]) o4 ?_ ?_ ?_ ?_ (Locals.get_setLocal_same c4.1 c4.2)
        · exact (Locals.get_setLocal_ne c4.1 (by omega)).trans ((Locals.get_setLocal_ne c2.1
            (by omega)).trans ((Locals.get_setLocal_ne c1.1 (by omega)).trans
              (Locals.get_setLocal_same (s := { sB with values := sB.values }) c0.1 c0.2)))
        · exact (Locals.get_setLocal_ne c4.1 (by omega)).trans ((Locals.get_setLocal_ne c2.1
            (by omega)).trans (Locals.get_setLocal_same c1.1 c1.2))
        · exact (Locals.get_setLocal_ne c4.1 (by omega)).trans
            (Locals.get_setLocal_same c2.1 c2.2)
        · exact (Locals.get_setLocal_ne c4.1 (by omega)).trans ((Locals.get_setLocal_ne c2.1
            (by omega)).trans ((Locals.get_setLocal_ne c1.1 (by omega)).trans
              ((Locals.get_setLocal_ne (s := { sB with values := sB.values }) c0.1
                (by omega)).trans hRootB)))

      · rw [ite_eq_right (by simp [hLarge] :
          ¬((if size + count * 4 + 3 ≥ 4294967296 then (1 : UInt32) else 0) ≠ 0))]
        have hSmallNat : size.toNat + 4 * count.toNat + 3 < 4294967296 := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le, hBlockNat] at hLarge
          simp only [UInt64.reduceToNat] at hLarge
          omega
        have hSys0 : (observedHost host).sys initial.host call.reporterCall []
            (.returned 0 [word0, word1]) after.host := by rw [← hZero]; exact hSys
        have hBlockSome : reportedBlock [.sys call.reporterCall [] (.returned errno [word0, word1])]
            = some (size + count * 4 + 3) := by
          simp only [reportedBlock, hZero, true_and]
          have hLt : (⟨0, [word0, word1]⟩ : Reply).word 1 +
              4 * (⟨0, [word0, word1]⟩ : Reply).word 0 + 3 < 4294967296 := by
            rw [hSource, UInt64.lt_iff_toNat_lt, hBlockNat]
            simp only [UInt64.reduceToNat]
            omega
          rw [ite_eq_left hLt, hSource]
        have hBlockNonzero : (size + count * 4 + 3).toNat ≠ 0 := by rw [hBlockNat]; omega
        have hCostEq : Bytes.allocationCost (size + count * 4 + 3).toNat =
            allocCost (allocSize (size + count * 4 + 3)).toNat :=
          Bytes.allocationCost_eq hBlockNonzero (by omega)
        simp only [sysReportedBlockCodeWith, List.cons_append, List.append_assoc]
        refine wp_localGet_get hGetB ?_
        have hCapA : (PureTransport.erase after).memoryCap source 0 ≤ 65535 := by
          rw [hStep0.cap source]; exact hCap
        refine wp_alloc_frame_with (aborts := aborts) runtime layout profile hImports sourceHost hStep0.at_
          (by omega) hCapA ?_ ?_ ?_
        · intro hAbort
          have hWithin := hRoom hAbort after [word0, word1] hSys0 _ (by rw [← hZero]; exact hBlockSome)
          rw [hCostEq] at hWithin
          have hAfter : heap.Within (PureTransport.erase after) source
              (allocCost (allocSize (size + count * 4 + 3)).toNat) :=
            Heap.Within.after (c1 := 0) (by simpa using hWithin) (by omega) (hStep0.cap source)
          exact hAfter.room hCapA
        · intro hAbort final hWorld
          exact hResource hAbort after [word0, word1] hSys0 final hWorld
        · intro final hHeapFits hStore hWorld
          obtain ⟨hAllocate, hBuffer, hCapacity, hTopAlloc⟩ :=
            read_allocation_buffer hStep0.at_ (by omega) hHeapFits hStore
          simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
            List.nil_append, List.drop_zero]
          have c3 := outsideB.bounds hLow hHigh (i := base + 3) (by omega) (by omega)
          refine wp_localSet_local c3.1 c3.2 ?_
          let root := FixedArrayAllocate.root heap.top (allocSize (size + count * 4 + 3)) heap.free
          let sA := setLocal { sB with values := s.values } (base + 3) (.i64 root)
          have outsideA : ReadAllOutside base s sA := (outsideB.values s.values).set hLow
            (by omega) (by omega)
          change wp target _ _ final sA env
          have hOtherA : ∀ j, j ≠ base + 3 → sA.get j = sB.get j := fun j hj =>
            Locals.get_setLocal_ne (s := { sB with values := s.values }) c3.1 hj
          have hBefore : Step heap (PureTransport.erase initial)
              (fun region => regionsDisjoint region ABI.scratch)
              (heap.allocate (allocSize (size + count * 4 + 3))) (PureTransport.erase final)
              (Bytes.regions (PureTransport.erase final) root) := by
            have hRootNonzero : root ≠ 0 := hBuffer.nonzero
            rw [Bytes.regions, ite_eq_right hRootNonzero]
            exact hStep0.trans (hAllocate.mono (keep' := fun _ => True)
              (fresh' := [block (PureTransport.erase final) root]) (fun _ _ => True.intro)
              (fun _ h => h)) (fun _ h => ⟨h, fun _ => True.intro⟩)
          have hSizes : host.reported final.host.world call = [4 * count.toNat, size.toNat] := by
            rw [hWorld, host.sys_reports hSys0.1 hName]
            simp [Call.sizesOf, hParams, reportedSizesOf, hc, hz]
          refine wp_sys_reported_call_with (s0 := s) runtime layout profile hImports sourceHost
            hHost hCall hParams hSizes hSmallNat hBuffer (by rw [← hBlockNat]; exact hCapacity)
            hBefore (budget := Bytes.allocationCost (size + count * 4 + 3).toNat)
            (by rw [hCostEq]; exact hTopAlloc) hLow hHigh outsideA
            ((hOtherA (base + 1) (by omega)).trans hCountB)
            ((hOtherA (base + 2) (by omega)).trans hSizeB)
            (Locals.get_setLocal_same c3.1 c3.2) ?_ ?_
          · intro heap' final2 sF e2 root' length outs2 hSys2 hStep2 hRep2 hTop2 outsideF hValuesF
              g0 g1 g2 g3 g4
            simp only [List.take_zero, List.nil_append, List.drop_zero]
            have hSys2' : (observedHost host).sys after.host call [] (.returned e2 outs2)
                final2.host := by rw [← hWorld]; exact hSys2
            have hFits2 : call.reject [] = 0 := by simp [Call.reject, hParams, rejectArgs]
            have hBlockTwo : reportedBlock [.sys call.reporterCall [] (.returned errno
                [word0, word1]), .sys call [] (.returned e2 outs2)] =
                some (size + count * 4 + 3) := hBlockSome
            refine finish final2 sF heap' e2 _ _ root' length _
              [.sys call.reporterCall [] (.returned errno [word0, word1]),
                .sys call [] (.returned e2 outs2)] ?_ hStep2 hRep2
              (by simp only [sysCost, hBlockTwo]; exact hTop2) outsideF g0 g1 g2 g3 g4
            refine .sys_return hFits hSys ?_
            rw [hReplyZ]
            have hCond : ¬((4294967296 : UInt64) ≤ (⟨0, [word0, word1]⟩ : Reply).word 1 +
                4 * (⟨0, [word0, word1]⟩ : Reply).word 0 + 3) := by
              rw [hSource]; exact hLarge
            simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, hCond]
            refine .sys_return hFits2 hSys2' ?_
            by_cases hZero2 : e2 = 0
            · simp only [sysReply, hZero2, bne_self_eq_false, Bool.false_eq_true, ite_true,
                ite_false, Reply.word, List.getElem?_cons_succ, List.getElem?_cons_zero,
                Option.map_some, Option.getD_some, hc, hz]
              exact .pure _ _
            · simp only [sysReply, hZero2, bne_iff_ne, ne_eq, not_false_eq_true, ite_true,
                ite_false, Reply.bytes, List.getElem?_nil, Option.getD_none]
              exact .pure _ _
          · intro final2 message outs2 hSys2
            simp only []
            refine hTrap final2 message [.sys call.reporterCall [] (.returned errno [word0, word1]),
              .sys call [] (.trapped message outs2)] (.sys_return hFits hSys ?_)
            rw [hReplyZ]
            have hCond : ¬((4294967296 : UInt64) ≤ (⟨0, [word0, word1]⟩ : Reply).word 1 +
                4 * (⟨0, [word0, word1]⟩ : Reply).word 0 + 3) := by
              rw [hSource]; exact hLarge
            simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, hCond]
            exact .sys_trap (by simp [Call.reject, hParams, rejectArgs])
              (by rw [← hWorld]; exact hSys2)

    · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      have hExec : Exec (observedHost host) (SysForm.reported.run call values) initial.host
          [.sys call.reporterCall [] (.returned errno outputs)]
          (.returned (wordsBytesValue 3 [errno, 0, 0] LeanExe.Bytes.empty)) after.host := by
        refine .sys_return hFits hSys ?_
        simp only [sysReply, hZero, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
        exact .pure _ _
      exact finish after sE heap errno 0 0 0 0 .empty _ hExec
        (by simpa only [Bytes.regions, ite_true] using hStep0) (Bytes.Rep.empty _ _)
        (by omega) outsideE hGetE zE1 zE2 zE3 zE4

  · intro final message outputs hSys hFrame
    refine hTrap final message _ (.sys_trap (by rw [Call.reject, reporterCall_params]; rfl) hSys)

end Verified.Wasi
