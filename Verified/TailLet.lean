import Verified.TailBind

namespace Verified

open Wasm LeanExe.Pipeline

theorem tail_let_spec {S : List Sig} {Γ params : List Ty} {result valueTy : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (value : Expr S Γ valueTy) (body : TailBody S params result (valueTy :: Γ))
    (valueSpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv value env slots paid live)
    (bodySpec : TailCodeSpec m funs flags bounds fits host pv targetModes body) :
    TailCodeSpec m funs flags bounds fits host pv targetModes (.letE value body) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.letE value body
  let mid := fun i => body.uses (i + 1)
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
  simp only [TailBody.code, TailBody.usesFast_eq, List.append_assoc]
  refine valueSpec env slots paid mid h (base + valueTy.width) heap store s hh hpv
    ((hVars.mono (by omega)).live_mono fun i hi => by rw [← hInput]; exact hi)
    hAt hCap (by omega) (by omega) hPlace.1 _ _
    (hTrap.part (by simp only [TailBody.fits]; flag_tac)
      (fun ha => by simp only [TailBody.aborts, Bool.or_eq_true] at ha ⊢; tauto)
      fun _ hw => hw.mono (by
        rw [hSplit]
        simp only [TailBody.allocs]
        dsimp only [input, mid]
        omega))
    fun heap1 store1 s1 ws1 a1 top1 => ?_
  have vars0 : Holds env slots input base heap store s := by rw [hInput]; exact hVars
  have a1' := a1.lower vars0 (Nat.le_add_right _ _) hMid
  refine wp_storeCode ws1 h base valueTy.types s1 s.values a1.rep.typed (a1.frame.positions.trans hh)
    (by rw [a1.frame.params]; omega) (by rw [Ty.types_length, a1.frame.positions, hh]; omega)
    fun s2 frame2 hold2 _ => ?_
  have f2 : Frame base s1 { s2 with values := s.values } := frame2.trans Frame.ofValues
  have hold2' : LocalsHold { s2 with values := s.values } base valueTy.types ws1 := hold2
  have varsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots) (fun i => i == 0 || body.uses i)
      (base + valueTy.width) heap1 store1 { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree f2).live_mono fun _ hi => by simpa [mid] using hi)
      hold2' a1.rep ((a1'.apart.agree a1'.holds f2).live_mono fun _ hi => by simpa [mid] using hi)
  have releaseEq : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode valueTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (valueTy :: Γ) (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [releaseEq]
  refine wp_releaseVars hm _ (by split <;> simp) varsB a1.step.at_ (by split <;> simp)
    fun heap2 store2 release top2 => ?_
  have release' := release.mono (live' := body.uses) fun i hi => by
    cases i with
    | zero => simp [hi]
    | succ k => split <;> simpa using hi
  have hDb : dyingPot store2 { s2 with values := s.values }
      (Env.cons (value.denote funs env) env) (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (value.paid flags (slots.map Slot.mode) paid mid :: paid) body.uses (fun _ => false) ≤
      (if value.paid flags (slots.map Slot.mode) paid mid = true then
        valueTy.pot store1 ws1 (value.denote funs env) else 0) +
        dyingPot store s env slots paid mid (fun _ => false) := by
    rw [dyingPot_evolves varsB release' (fun i hi => by simp [hi]) _ _ (fun _ hi => hi),
      dyingPot_cons]
    have hTail : dyingPot store1 { s2 with values := s.values } env slots paid
        (fun i => body.uses (i + 1)) (fun _ => false) =
        dyingPot store s env slots paid mid (fun _ => false) :=
      dyingPot_step vars0 a1'.step (a1'.frame.trans f2) hMid _ _ (fun _ hi => hi)
    rw [hTail, hold2'.read_eq (by rw [a1.rep.length, Ty.types_length])]
    refine Nat.add_le_add_right ?_ _
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      simp only [hc.1.2, ↓reduceIte, le_refl]
    · exact Nat.zero_le _
  have hFitsValue : outer.fits funs fits env = true → value.fits funs fits env = true := by
    intro hf
    simp only [outer, TailBody.fits, Bool.and_eq_true] at hf
    exact hf.1
  have hFitsBody : outer.fits funs fits env = true →
      body.fits funs fits (.cons (value.denote funs env) env) = true := by
    intro hf
    simp only [outer, TailBody.fits, Bool.and_eq_true] at hf
    exact hf.2
  refine bodySpec _ _ (value.paid flags (slots.map Slot.mode) paid mid :: paid) nextPaid resultPaid
    h stateBase resultBase (base + valueTy.width) exitLabel nextLabel heap2 store2
    { s2 with values := s.values } (f2.positions.trans (a1.frame.positions.trans hh))
    (f2.params.trans (a1.frame.params.trans hpv)) release'.holds release'.step.at_
    (by rw [release'.step.cap m, a1.step.cap m]; exact hCap)
    (by change s2.params.length ≤ stateBase; rw [frame2.params, a1.frame.params]; exact hLow)
    hState (by omega) (by omega) hPlace.2 hPaid _
    (hTrap.part
      (fun hd => by
        cases hf : outer.fits funs fits env
        · rfl
        · simp [hFitsBody hf] at hd)
      (fun ha => by
        have hOwned := value.mode_owned (slots.map Slot.mode)
        rw [Slot.any_map] at hOwned
        simp only [List.any_cons, TailBody.aborts, Bool.or_eq_true] at ha ⊢
        rcases ha with ((ha | ha) | ha) | (ha | ha)
        · exact Or.inl (Or.inl (Or.inl (Or.inr ha)))
        · exact Or.inl (Or.inl (Or.inr ha))
        · exact Or.inl (Or.inr ha)
        · have ho := hOwned (by simpa using ha)
          simp only [Bool.or_eq_true] at ho
          rcases ho with ho | ho
          · exact Or.inl (Or.inl (Or.inl (Or.inl ho)))
          · exact Or.inr ho
        · exact Or.inr ha)
      fun hd hw => by
        have hf : outer.fits funs fits env = true := by simpa using hd
        have h1 := top1 (hFitsValue hf)
        have hr := congrArg UInt64.toNat top2
        refine hw.of_le ?_ (by rw [release'.step.cap m, a1.step.cap m])
        rw [hSplit]
        simp only [TailBody.allocs, List.map_cons]
        dsimp only [input, mid] at h1 hDb ⊢
        omega)
    fun heap3 store3 s3 after3 top3 => ?_
  let afterB := TailAfter.prepend varsB release' after3 (fun i hi => by simp [hi]) (by omega)
  let final := TailAfter.bind vars0 a1' f2 hold2' afterB (fun _ hi => hi) hMid (by omega)
  let final' := final.liveIn (L0 := outer.uses) (fun i hi => by rw [← hInput]; exact hi)
  refine hNext heap3 store3 s3 final' fun hf => ?_
  have h1 := top1 (hFitsValue hf)
  have h3 := top3 (hFitsBody hf)
  have hr := congrArg UInt64.toNat top2
  change heap3.top.toNat + tailPot targetModes nextPaid resultPaid store3 after3.words
    (body.denote funs (.cons (value.denote funs env) env)) ≤ _
  rw [hSplit]
  simp only [TailBody.allocs, List.map_cons] at h3 ⊢
  dsimp only [input, mid] at h1 hDb h3 ⊢
  omega

#print axioms tail_let_spec

end Verified
