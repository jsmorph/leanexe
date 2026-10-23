import Verified.ExprSpec
import Verified.ArgsCorrect
import Verified.Bytes.AfterWrite
import Verified.Bytes.BuildControl
import Verified.Bytes.BuildLoop

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem spec_bytesBuild {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) {Γ : List Ty} {count : Expr S Γ .word}
    {elem : Expr S (.word :: Γ) .word}
    (countSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv count env
      slots paid live)
    (elemSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv elem env
      slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.bytesBuild count elem)
      env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace
    rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (3 + elem.width)
  have he := Nat.le_max_right count.width (3 + elem.width)
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  let all := fun i => live i || elem.uses (i + 1)
  let n := (count.denote funs env).toNat
  let output := LeanExe.Bytes.build (count.denote funs env)
    fun i => elem.denote funs (.cons i env)
  let countCost := count.allocs funs flags bounds (slots.map Slot.mode) paid all env
  let bodyCost := fun k => elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode)
    (false :: paid) (shift 1 all) (.cons (UInt64.ofNat k) env)
  have hBodyCost (k : Nat) : bodyCost k =
      elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode) (false :: paid)
        (shift 1 all) (.cons (UInt64.ofNat k) env) := rfl
  let countPot := dyingPot store s env slots paid (fun i => all i || count.uses i) all
  have hT : (Expr.bytesBuild count elem).allocs funs flags bounds (slots.map Slot.mode)
      paid live env = countCost + Bytes.allocationCost n + sumBelow bodyCost n := rfl
  have hOutputSize : output.data.size = n := LeanExe.Bytes.data_size_build ..
  have hdK : (Expr.bytesBuild count elem).fits funs fits env = true →
      count.fits funs fits env = true ∧
        ∀ k, k < n → elem.fits funs fits (.cons (UInt64.ofNat k) env) = true := fun hd => by
    simp only [Expr.fits, Bool.and_eq_true] at hd
    exact ⟨hd.1, allBelow_get hd.2⟩
  have hTrapW : ¬heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || (Expr.bytesBuild count elem).uses i)
          live +
        (Expr.bytesBuild count elem).allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      TrapOK true Q := fun hw => hTrap.of_imp fun _ => by simp [trapFlag, Expr.aborts, hw]
  have hCountIn : ∀ i, (all i || count.uses i) = true →
      (live i || (Expr.bytesBuild count elem).uses i) = true := fun i hi => by
    simp only [Expr.uses]
    exact live_seq _ _ _ hi
  have hDk : countPot ≤ dyingPot store s env slots paid
      (fun i => live i || (Expr.bytesBuild count elem).uses i) live :=
    dyingPot_mono hCountIn fun i hi => by simp [all, hi]
  have hDe : ∀ (v : UInt64) (st' : Store Unit) (s' : Locals) (sl : Slot),
      dyingPot st' s' (Env.cons (t := .word) v env) (sl :: slots) (false :: paid)
        (fun j => shift 1 all j || elem.uses j) (shift 1 all) = 0 := fun _ _ _ _ =>
    dyingPot_eq_zero_unpaid fun j h0 h1 => by
      match j with
      | 0 => rfl
      | k + 1 =>
        have hk : ¬k + 1 < 1 := by omega
        simp only [shift, hk, ↓reduceIte, Nat.add_sub_cancel] at h0 h1
        simp only [all] at h0 h1
        revert h0 h1
        cases live k <;> cases elem.uses (k + 1) <;> simp
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  refine countSpec env slots paid all h base heap store s hh hpv
    (hVars.live_mono hCountIn) hAt (hSafe.mono hCountIn) hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun hd => by simp only [Bool.not_eq_true'] at hd; simp [Expr.fits, hd])
      (fun _ => by simp [Expr.aborts]) fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopK => ?_
  have hRepK := a1.rep
  simp only [Ty.rep_word] at hRepK
  subst hRepK
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base
    rw [hp1]
    exact hBase
  have hHigh1 : base < s1.positions := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  set s2 := setLocal { s1 with values := s.values } base (.i64 (count.denote funs env)) with hs2
  have f2 : Frame base s1 s2 := Frame.setValues hLow1 le_rfl hHigh1
  have hN2 : s2.get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hh2 : s2.positions = h := f2.positions.trans hh1
  have hp2 : s2.params = s.params := f2.params.trans hp1
  have hVars1 : Holds env slots all base heap1 store1 s2 := e1.holds.agree f2
  have hFinish : ∀ (heapF : Heap) (storeF : Store Unit) (sf : Locals) (root : UInt64),
      After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
        heap store s .bytes .owned output heapF storeF sf [.i64 root, .i64 (count.denote funs env)] →
      ((Expr.bytesBuild count elem).fits funs fits env = true →
        heapF.top.toNat ≤ heap.top.toNat + countPot + countCost + Bytes.allocationCost n +
          sumBelow bodyCost n) →
      wp m (releaseWhere Γ slots (fun i => elem.uses (i + 1) && !live i) ++ rest) Q storeF
        { sf with values := .i64 (count.denote funs env) :: .i64 root :: s.values } host := by
    intro heapF storeF sf root aF hTopF
    refine After.release hm (s1 := sf) (live := live)
      (sel := fun i => elem.uses (i + 1) && !live i) hVars aF
      (fun i hi => by simp only [Expr.uses]; exact live_build _ _ _ hi)
      (fun i hi => by simp only [Bool.and_eq_true] at hi; simp [all, hi.1])
      (fun i hi => by simp [all, hi]) fun heap' store' a' hTopR _ => ?_
    have hDone := hNext heap' store' sf [.i64 root, .i64 (count.denote funs env)] a'
      fun hd => top_unpaid rfl (by
        have := hTopF hd
        have := congrArg UInt64.toNat hTopR
        rw [hT]
        omega)
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using hDone
  by_cases hZero : count.denote funs env = 0
  · have hn : n = 0 := by simp only [n, hZero, UInt64.toNat_zero]
    have hEmpty : output.data.size = 0 := hOutputSize.trans hn
    have aZero : After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all
        base heap store s .bytes .owned output heap1 store1 s2 [.i64 0, .i64 (count.denote funs env)] := by
      refine ⟨?_, e1.frame.trans f2, hVars1,
        ⟨0, count.denote funs env, rfl, ⟨by rw [hZero, UInt64.toNat_zero, hEmpty],
          Or.inl ⟨rfl, hEmpty⟩⟩⟩, ?_⟩
      · simpa only [Mode.fresh, Ty.blocks, Bytes.roots, ↓reduceIte, List.map_nil] using
          (e1.step.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) fun _ h => h)
      · intro _ _ _ _ _ _ _ _ hb
        exact nomatch hb
    refine Bytes.wp_build_zero (by simpa only [hZero] using hN2) ?_
    have hDone := hFinish heap1 store1 s2 0 aZero fun hd => by
      have := hTopK (hdK hd).1
      simp only [n, hZero, UInt64.toNat_zero, sumBelow, Bytes.allocationCost]
      omega
    simpa only [hZero, hs2, setLocal] using hDone
  by_cases hBig : 4294967296 ≤ count.denote funs env
  · refine Bytes.wp_build_overflow hN2 hBig (hTrapW fun hw => ?_)
    have hLarge := UInt64.le_iff_toNat_le.mp hBig
    simp only [UInt64.reduceToNat] at hLarge
    have hn : n ≠ 0 := by dsimp only [n]; omega
    have hCost := Bytes.allocationCost_ge hn
    unfold Heap.Within at hw
    rw [hT] at hw
    dsimp only [n] at hCost hw
    omega
  have h32 : (count.denote funs env).toNat < 4294967296 := by
    have hLess := UInt64.not_le.mp hBig
    simpa only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] using hLess
  simp only [Bytes.buildCode, List.cons_append, List.nil_append, wp_localGet_cons,
    hN2, wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte, wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons,
    hN2, wp_constI64_cons, wp_eqI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp only [hZero, ite_false]
  rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
  simp only [wp_localGet_cons, hN2]
  have hLowD : s2.params.length ≤ base + 1 := by rw [hp2]; omega
  have hHighD : base + 1 < s2.positions := by rw [hh2]; omega
  refine Bytes.wp_allocate hm e1.step.at_ (by omega)
    (by rw [e1.step.cap m]; exact hCap)
    (c := Bytes.allocationCost n)
    (by rw [← Bytes.allocationCost_eq (by exact fun hz => hZero (UInt64.toNat_inj.mp hz)) (by omega)])
    ((hTrap.alloc (by simp [Expr.aborts]) fun hd hw => by
      have := hTopK (hdK (fits_of_not hd)).1
      exact hw.shift (c1 := countPot + countCost) (by omega) (by rw [hT]; omega)
        (e1.step.cap m)).imp fun _ ht => ht)
    fun heap2 store2 root initial hSize hStepA hBuffer _ hTopA => ?_
  refine wp_localSet_local (s := s2) (vs := s2.values) hLowD (Locals.lt_total hHighD) ?_
  set s3 := setLocal { s2 with values := s2.values } (base + 1) (.i64 root) with hs3
  have f3 : Frame base s2 s3 := Frame.setValues hLowD (by omega) hHighD
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne (s := { s2 with values := s2.values }) hLowD (by omega),
      Locals.get_values]
    exact hN2
  have hRoot3 : s3.get (base + 1) = some (.i64 root) :=
    Locals.get_setLocal_same hLowD (Locals.lt_total hHighD)
  have hh3 : s3.positions = h := f3.positions.trans hh2
  have hp3 : s3.params = s.params := f3.params.trans hp2
  have hVars3 : Holds env slots all base heap1 store1 s3 := hVars1.agree f3
  have a0 : After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
      heap store s .bytes .owned initial heap2 store2 s3
      [.i64 root, .i64 (count.denote funs env)] := by
    refine ⟨?_, e1.frame.trans (f2.trans f3),
      hVars3.step hStepA (fun _ _ _ _ _ _ _ _ => trivial),
      ⟨root, count.denote funs env, rfl, hSize.symm, Or.inr hBuffer⟩, ?_⟩
    · simpa only [Mode.fresh, Ty.blocks, Bytes.roots, ite_eq_right hBuffer.nonzero,
        List.map_cons, List.map_nil] using
        ((e1.step.trans hStepA fun _ hr => ⟨hr, fun _ => trivial⟩).mono
          (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) fun _ hi => hi)
    · intro u y hy _ wy hwy hly b hb c hc
      obtain ⟨hSame, hFresh⟩ := hVars3.regions_after hStepA hy hwy hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b (by
        simpa only [Ty.regions, Ty.blocks, Bytes.roots, ite_eq_right hBuffer.nonzero,
          List.map_cons, List.map_nil] using hb))
  have hSizes : output.data.size = initial.data.size := hOutputSize.trans hSize.symm
  let P := fun i heapI st si =>
    After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
      heap store s .bytes .owned (Bytes.overlay output initial hSizes i) heapI st si
      [.i64 root, .i64 (count.denote funs env)] ∧
    ((Expr.bytesBuild count elem).fits funs fits env = true →
      heapI.top.toNat ≤ heap.top.toNat + countPot + countCost + Bytes.allocationCost n +
        sumBelow bodyCost i)
  refine Bytes.wp_buildLoop P hStepA.at_ hBuffer hSizes hOutputSize hN3 hRoot3
    (by rw [hp3]; omega) (by rw [hh3]; omega) (hTrap.imp fun _ ht => ht) ?_ ?_ ?_
  · refine ⟨?_, fun hd => ?_⟩
    · simpa only [Bytes.overlay_zero] using a0.reframe
        (Frame.setValues (s := s3) (vs := s3.values) (by rw [hp3]; omega) (by omega)
          (by rw [hh3]; omega))
    · have := hTopK (hdK hd).1
      simp only [sumBelow]
      omega
  · intro i hi heapI st si hHeapI hBufferI hFrameI hNi hRooti hIdxi hValuesI hPI
      tail Post hTrapPost hNextE
    obtain ⟨aI, hInv⟩ := hPI
    have hiN : i < n := by rw [← hOutputSize]; exact hi
    have hi64 : (UInt64.ofNat i).toNat = i :=
      UInt64.toNat_ofNat_of_lt' (by change i < 18446744073709551616; dsimp only [n] at hiN; omega)
    have holdIdx : LocalsHold si (base + 2) Ty.word.types [.i64 (UInt64.ofNat i)] := by
      intro j hj
      obtain rfl : j = 0 := by simpa using hj
      simpa [Ty.types, slotIndex] using hIdxi
    have hhi : si.positions = h := aI.frame.positions.trans hh
    have hLE : ∀ j, (shift 1 all (j + 1) || elem.uses (j + 1)) = true → all j = true :=
      fun j hj => by simp only [shift_add] at hj; exact live_dup _ _ hj
    have hVarsI : Holds env slots all (base + 2) heapI st si := aI.holds.mono (by omega)
    have hVarsE := (Holds.push (t := .word) (v := UInt64.ofNat i) (mode := .borrowed)
      (live' := fun j => shift 1 all j || elem.uses j) (hVarsI.live_mono hLE)
      holdIdx rfl (Holds.Apart.ofScalar rfl)).mono (base' := base + 3) (by simp [Ty.width])
    have hSafeI := (hSafe.after hVars aI (fun i hi => by
      simp only [Expr.uses]
      exact live_build _ _ _ hi)).1
    have hSafeE : pool.Safe (.cons (UInt64.ofNat i) env)
        (⟨base + 2, .borrowed⟩ :: slots) (fun j => shift 1 all j || elem.uses j) heapI st si :=
      (hSafeI.mono hLE).push holdIdx
        (show Ty.word.Rep .borrowed heapI st [.i64 (UInt64.ofNat i)] (UInt64.ofNat i) from rfl)
        (by simp [Mode.fresh])
    refine elemSpec _ _ (false :: paid) (shift 1 all) h (base + 3) heapI st
      { si with values := .i32 (root + UInt64.ofNat i).toUInt32 :: si.values } hhi
      (aI.frame.params.trans hpv) (hVarsE.agree Frame.ofValues) hHeapI
      (hSafeE.values _)
      (by rw [aI.step.cap m]; exact hCap)
      (by show si.params.length ≤ base + 3; rw [aI.frame.params]; omega) (by omega)
      hPlace.2 tail Post
      ((hTrapPost.part (fun hd => by
          cases hw : (Expr.bytesBuild count elem).fits funs fits env
          · rfl
          · exact absurd ((hdK hw).2 i hiN) (by simpa using hd))
        (fun _ => by simp [Expr.aborts]) fun hd hw => hw.of_le (by
          have := hInv (fits_of_not hd)
          have := sumBelow_mono bodyCost (show i + 1 ≤ n by omega)
          simp only [sumBelow] at this
          rw [hDe]
          simp only [List.map_cons]
          rw [← hBodyCost i]
          rw [hT]
          omega) (aI.step.cap m)).imp fun _ ht => ht)
      fun heapE stE sE wsE aE hTopE => ?_
    have hRE := aE.rep
    simp only [Ty.rep_word] at hRE
    subst hRE
    have aE1 := After.bind (base := base + 2) hVarsI
      (After.refl (t := .word) (mode := .borrowed) (v := UInt64.ofNat i)
        (ws := [.i64 (UInt64.ofNat i)]) aI.step.at_ hVarsI (fun _ hi => hi) rfl rfl
        (Holds.Apart.ofScalar rfl))
      (Frame.refl _ _) holdIdx aE.ofValues hLE (fun _ hi => hi) fun _ hi => hi
    have aE2 := aE1.lower aI.holds (by omega) fun _ hi => hi
    obtain ⟨hStep, hFrame, hRep, hApart, -⟩ := After.seq hVars aI aE2
      (fun i hi => by simp only [Expr.uses]; exact live_build _ _ _ hi) fun _ hi => hi
    have aI2 : After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
        heap store s .bytes .owned (Bytes.overlay output initial hSizes i) heapE stE sE
        [.i64 root, .i64 (count.denote funs env)] :=
      ⟨hStep.mono (fun _ hi => hi) fun _ hb => List.mem_append_left _ hb,
        hFrame, aE2.holds, hRep, hApart⟩
    have hOutput : (UInt64.ofNat i).toNat < (Bytes.overlay output initial hSizes i).data.size := by
      rw [hi64, Bytes.overlay_size, ← hSizes]
      exact hi
    have hValue : (elem.denote funs (.cons (UInt64.ofNat i) env)).toUInt8 = output.data[i] := by
      simp only [output, LeanExe.Bytes.build, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
    have hBufferE := aI2.bytes_rep.buffer.resolve_left fun hz => by
      have := hz.2
      rw [Bytes.overlay_size, hSize] at this
      have hn : (count.denote funs env).toNat ≠ 0 :=
        fun hz => hZero (UInt64.toNat_inj.mp hz)
      exact hn this
    refine hNextE heapE stE sE _ aE.step.at_ hBufferE aE.frame.values hValue ?_
    refine ⟨?_, fun hd => ?_⟩
    · have hWrite := aI2.writeByte hOutput
        (elem.denote funs (.cons (UInt64.ofNat i) env)).toUInt8
      have hLowE : sE.params.length ≤ base + 2 := by rw [aE.frame.params, aI.frame.params]; omega
      have hHighE : base + 2 < sE.positions := by
        rw [aE.frame.positions, Locals.positions_values, hhi]
        omega
      simpa only [hi64, hValue, Bytes.overlay_succ output initial hSizes i (by omega)] using
        hWrite.reframe (Frame.setValues hLowE (by omega) hHighE)
    · have := hInv hd
      have hE := hTopE ((hdK hd).2 i hiN)
      rw [hDe] at hE
      simp only [List.map_cons] at hE
      rw [← hBodyCost i] at hE
      simp only [sumBelow]
      omega
  · intro heapF storeF sf hHeapF hOutput hFrameF hCountF hRootF _ hPF hValuesF
    obtain ⟨aF, hTopF⟩ := hPF
    rw [Bytes.overlay_all] at aF
    simp only [wp_localGet_cons, hRootF, wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append, List.take_succ_cons,
      List.take_zero, List.nil_append, List.cons_append, Locals.get_values, hCountF]
    have hDone := hFinish heapF storeF sf root aF (by simpa only [hOutputSize] using hTopF)
    simpa only [hs3, hs2, setLocal, hValuesF] using hDone

end Verified
