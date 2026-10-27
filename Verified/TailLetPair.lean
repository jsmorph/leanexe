import Verified.TailLet

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def TailAfter.bind2 {Γ params : List Ty} {result valueTy firstTy secondTy : Ty}
    {env : Env Γ} {slots : List Slot} {L0 L1 LB : Nat → Bool}
    {base stateBase resultBase : Nat} {modes : List Mode}
    {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 s2 s3 : Locals}
    {mode : Mode} {value : valueTy.denote} {first : firstTy.denote} {second : secondTy.denote}
    {sl0 sl1 : Slot} {words : List Value} {out : Sum (Env params) result.denote}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s valueTy mode value heap1 store1 s1 words)
    (frame : Frame base s1 s2)
    (aB : TailAfter (Env.cons first (Env.cons second env)) (sl0 :: sl1 :: slots) LB modes
      stateBase resultBase heap1 store1 s2 out heap2 store2 s3)
    (hNew : ∀ r, (∀ b ∈ mode.fresh store1 valueTy words value, regionsDisjoint r b) →
      (sl0.mode = .owned → ∀ w, LocalsHold s2 sl0.loc firstTy.types w → w.length = firstTy.width →
        ∀ b ∈ firstTy.blocks store1 w first, regionsDisjoint r b) ∧
      (sl1.mode = .owned → ∀ w, LocalsHold s2 sl1.loc secondTy.types w → w.length = secondTy.width →
        ∀ b ∈ secondTy.blocks store1 w second, regionsDisjoint r b))
    (hLB : ∀ i, LB (i + 2) = true → L1 i = true)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hBase : stateBase ≤ base) :
    TailAfter env slots L0 modes stateBase resultBase heap store s out heap2 store2 s3 := by
  refine ⟨aB.words, a1.step.trans aB.step fun r hr =>
    ⟨hr.mono fun _ hi _ => ⟨hi, rfl⟩, fun hFresh => ?_⟩,
    (a1.frame.mono hBase).trans ((frame.mono hBase).trans aB.frame), aB.rep⟩
  have hr1 : Holds.KeepDying env slots L1 (fun _ => false) store1 s1 r :=
    Holds.KeepDying.transfer h0 a1.step a1.frame hL1 (fun _ hi _ => hi)
      (hr.mono fun i hi _ => ⟨hL1 i hi, rfl⟩)
  obtain ⟨hNew0, hNew1⟩ := hNew r hFresh
  intro t x hx _ hxMode wx hxHold hxLength b hb
  cases x with
  | here => exact hNew0 hxMode wx hxHold hxLength b hb
  | there x =>
    cases x with
    | here => exact hNew1 hxMode wx hxHold hxLength b hb
    | there x =>
      change (slots.getD x.index default).mode = .owned at hxMode
      change LocalsHold s2 (slots.getD x.index default).loc t.types wx at hxHold
      have hx1 : L1 x.index = true := hLB _ hx
      exact hr1 t x hx1 rfl hxMode wx ((a1.holds.hold_agree frame hx1 hxLength).mp hxHold)
        hxLength b hb

theorem tail_letPair_spec {S : List Sig} {Γ params : List Ty} {result firstTy secondTy : Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (value : Expr S Γ (.pair firstTy secondTy))
    (body : TailBody S params result (secondTy :: firstTy :: Γ))
    (valueSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv value env slots paid live)
    (bodySpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes body) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.letPair value body) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.letPair value body
  let mid := fun i => body.uses (i + 2)
  let input := fun i => mid i || value.uses i
  have hInput : input = outer.uses := by
    funext i
    simp only [input, mid, outer, TailBody.uses, Bool.or_comm]
  have hMid : ∀ i, mid i = true → input i = true := fun i hi => by simp [input, hi]
  have hSplit : dyingPot store s env slots paid outer.uses (fun _ => false) =
      dyingPot store s env slots paid input mid +
        dyingPot store s env slots paid mid (fun _ => false) := by
    rw [← hInput]
    exact dyingPot_split _ _ _ hMid nofun
  have hvWidth := Nat.le_max_left value.width (body.width targetModes)
  have hbWidth := Nat.le_max_right value.width (body.width targetModes)
  simp only [TailBody.width] at hRoom
  simp only [TailBody.placeArgs, Bool.and_eq_true] at hPlace
  simp only [TailBody.code, TailBody.codeWith, TailBody.usesFast_eq, List.append_assoc]
  refine valueSpec env slots paid mid h (base + firstTy.width + secondTy.width) heap store s hh hpv
    ((hVars.mono (by omega)).live_mono fun i hi => by rw [← hInput]; exact hi)
    hAt (hSafe.mono fun i hi => by rw [← hInput]; exact hi)
    hCap (by omega) (by omega) hPlace.1 _ _
    (hTrap.part (by simp only [TailBody.fits]; flag_tac)
      (fun ha => by simp only [TailBody.aborts, Bool.or_eq_true] at ha ⊢; tauto)
      fun _ hw => hw.mono (by
        rw [hSplit]
        simp only [TailBody.allocs]
        dsimp only [input, mid]
        omega))
    fun heap1 store1 s1 ws1 a1 top1 => ?_
  have vars0 : Holds env slots input base heap store s := by rw [hInput]; exact hVars
  have a1' := a1.lower vars0 (by omega) hMid
  obtain ⟨wFirst, wSecond, rfl, repFirst, repSecond, apart⟩ := a1.rep
  have lenFirst := repFirst.length
  have lenSecond := repSecond.length
  rw [List.reverse_append, List.append_assoc]
  refine wp_storeCode wSecond h (base + firstTy.width) secondTy.types s1
    (wFirst.reverse ++ s.values) repSecond.typed (a1.frame.positions.trans hh)
    (by rw [a1.frame.params]; omega) (by rw [Ty.types_length, a1.frame.positions, hh]; omega)
    fun s2 frame2 holdSecond _ => ?_
  refine wp_storeCode wFirst h base firstTy.types s2 s.values repFirst.typed
    (frame2.positions.trans (a1.frame.positions.trans hh))
    (by rw [frame2.params, a1.frame.params]; omega)
    (by rw [Ty.types_length, frame2.positions, a1.frame.positions, hh]; omega)
    fun s3 frame3 holdFirst above3 => ?_
  have holdFirst' : LocalsHold { s3 with values := s.values } base firstTy.types wFirst := holdFirst
  have holdSecond' : LocalsHold { s3 with values := s.values } (base + firstTy.width)
      secondTy.types wSecond := holdSecond.keep frame3.positions above3 (by rw [Ty.types_length])
        (by rw [lenSecond, frame2.positions, a1.frame.positions, hh]; omega)
  have f3 : Frame base s1 { s3 with values := s.values } :=
    (frame2.mono (by omega)).trans (frame3.trans Frame.ofValues)
  have vars1 := a1'.holds.agree f3
  have apart1 := a1'.apart.agree a1'.holds f3
  have varsB : Holds (Env.cons (value.denote funs env).2 (Env.cons (value.denote funs env).1 env))
      (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
        ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || body.uses i) (base + firstTy.width + secondTy.width)
      heap1 store1 { s3 with values := s.values } := by
    refine Holds.push (Holds.push (vars1.live_mono fun _ hi => by simpa [mid] using hi)
      holdFirst' repFirst ((apart1.fst lenFirst).live_mono fun _ hi => by simpa [mid] using hi))
      holdSecond' repSecond ?_
    refine Holds.Apart.push ((apart1.snd lenFirst).live_mono fun _ hi => by simpa [mid] using hi)
      holdFirst' lenFirst fun hm b hb c hc => ?_
    have hm' : value.mode (slots.map Slot.mode) = .owned := by simpa using hm
    rw [hm'] at hb hc apart
    exact regionsDisjoint_symm (apart rfl c hc b hb)
  have safeB : pool.Safe
      (Env.cons (value.denote funs env).2 (Env.cons (value.denote funs env).1 env))
      (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
        ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || body.uses i) heap1 store1 { s3 with values := s.values } :=
    (hSafe.mono fun i hi => by rw [← hInput]; exact hi).bind2 vars0 a1' hMid
      (fun _ hi => by simpa [mid] using hi) f3 repFirst repSecond holdFirst' holdSecond'
  have releaseEq : ∀ rest : Program,
      (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 1 = false then
        releaseCode firstTy base else []) ++
      ((if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
        releaseCode secondTy (base + firstTy.width) else []) ++ rest) =
      ((if body.uses 1 = false then [1] else []) ++
        (if body.uses 0 = false then [0] else [])).flatMap
        (releaseVar (secondTy :: firstTy :: Γ)
          (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
            ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) ++ rest := by
    intro rest
    cases body.uses 1 <;> cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;>
      simp [releaseVar]
  rw [releaseEq]
  refine wp_releaseVars hm _ (by split <;> split <;> simp) varsB a1.step.at_
    (by split <;> split <;> simp) fun heap2 store2 release top2 => ?_
  have release' := release.mono (live' := body.uses) fun i hi => by
    match i with
    | 0 => simp [hi]
    | 1 => simp [hi]
    | k + 2 => split <;> split <;> simpa using hi
  have hDb : dyingPot store2 { s3 with values := s.values }
      (Env.cons (value.denote funs env).2 (Env.cons (value.denote funs env).1 env))
      (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
        ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots) (false :: false :: paid)
      body.uses (fun _ => false) = dyingPot store s env slots paid mid (fun _ => false) := by
    rw [dyingPot_evolves varsB release' (fun i hi => by simp [hi]) _ _ (fun _ hi => hi),
      dyingPot_cons, dyingPot_cons]
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact dyingPot_step vars0 a1'.step (a1'.frame.trans f3) hMid _ _ (fun _ hi => hi)
  have hFitsValue : outer.fits funs fits env = true → value.fits funs fits env = true := by
    intro hf
    simp only [outer, TailBody.fits, Bool.and_eq_true] at hf
    exact hf.1
  have hFitsBody : outer.fits funs fits env = true →
      body.fits funs fits (.cons (value.denote funs env).2 (.cons (value.denote funs env).1 env)) =
        true := by
    intro hf
    simp only [outer, TailBody.fits, Bool.and_eq_true] at hf
    exact hf.2
  refine bodySpec _ _ (false :: false :: paid) nextPaid resultPaid h stateBase resultBase
    (base + firstTy.width + secondTy.width) exitLabel nextLabel heap2 store2
    { s3 with values := s.values } (f3.positions.trans (a1.frame.positions.trans hh))
    (f3.params.trans (a1.frame.params.trans hpv)) release'.holds release'.step.at_
    (safeB.evolves varsB release' (fun i hi => by
      match i with
      | 0 => simp [hi]
      | 1 => simp [hi]
      | k + 2 => simp [hi]))
    (by rw [release'.step.cap m, a1.step.cap m]; exact hCap)
    (by change s3.params.length ≤ stateBase; rw [frame3.params, frame2.params, a1.frame.params]; exact hLow)
    hState (by omega) (by omega) hPlace.2 hPaid _
    (hTrap.part
      (fun hd => by
        cases hf : outer.fits funs fits env
        · rfl
        · simp [hFitsBody hf] at hd)
      (fun ha => by
        have hOwned := value.mode_owned (slots.map Slot.mode)
        rw [Slot.any_map] at hOwned
        simp only [List.any_cons, TailBody.aborts] at ha ⊢
        have hb := let_trap_body2 value.aborts
          (body.aborts || !result.scalar || (paramModes params targetModes).any (· == .owned))
          (value.mode (slots.map Slot.mode) == .owned) (slots.any (·.mode == .owned))
          (fun hv => hOwned (beq_iff_eq.mp hv)) ha
        simpa only [Bool.or_assoc] using hb)
      fun hd hw => by
        have hf : outer.fits funs fits env = true := by simpa using hd
        have h1 := top1 (hFitsValue hf)
        have hr := congrArg UInt64.toNat top2
        refine hw.of_le ?_ (by rw [release'.step.cap m, a1.step.cap m])
        rw [hSplit, hDb]
        simp only [TailBody.allocs, List.map_cons]
        dsimp only [input, mid] at h1 ⊢
        omega)
    fun heap3 store3 s4 after4 top4 => ?_
  let afterB := TailAfter.prepend varsB release' after4 (fun i hi => by simp [hi]) (by omega)
  have hNew : ∀ r,
      (∀ b ∈ (value.mode (slots.map Slot.mode)).fresh store1 (.pair firstTy secondTy)
        (wFirst ++ wSecond) (value.denote funs env), regionsDisjoint r b) →
      (value.mode (slots.map Slot.mode) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } (base + firstTy.width) secondTy.types w →
          w.length = secondTy.width →
            ∀ b ∈ secondTy.blocks store1 w (value.denote funs env).2, regionsDisjoint r b) ∧
      (value.mode (slots.map Slot.mode) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } base firstTy.types w → w.length = firstTy.width →
          ∀ b ∈ firstTy.blocks store1 w (value.denote funs env).1, regionsDisjoint r b) := by
    intro r hf
    rw [Mode.fresh_pair lenFirst] at hf
    refine ⟨fun hm w hw hl b hb => ?_, fun hm w hw hl b hb => ?_⟩
    · obtain rfl := LocalsHold.unique hw holdSecond' (hl.trans lenSecond.symm)
      rw [hm] at hf
      exact hf b (List.mem_append_right _ hb)
    · obtain rfl := LocalsHold.unique hw holdFirst' (hl.trans lenFirst.symm)
      rw [hm] at hf
      exact hf b (List.mem_append_left _ hb)
  let final := TailAfter.bind2 vars0 a1' f3 afterB hNew (fun _ hi => hi) hMid (by omega)
  let final' := final.liveIn (L0 := outer.uses) (fun i hi => by rw [← hInput]; exact hi)
  refine hNext heap3 store3 s4 final' fun hf => ?_
  have h1 := top1 (hFitsValue hf)
  have h4 := top4 (hFitsBody hf)
  have hr := congrArg UInt64.toNat top2
  rw [hDb] at h4
  change heap3.top.toNat + tailPot targetModes nextPaid resultPaid store3 after4.words
    (body.denote funs (.cons (value.denote funs env).2 (.cons (value.denote funs env).1 env))) ≤ _
  rw [hSplit]
  simp only [TailBody.allocs, List.map_cons] at h4 ⊢
  dsimp only [input, mid] at h1 h4 ⊢
  omega

#print axioms TailAfter.bind2
#print axioms tail_letPair_spec

end Verified
