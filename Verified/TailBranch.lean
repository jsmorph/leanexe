import Verified.TailNext

namespace Verified

open Wasm LeanExe.Pipeline

theorem tail_ite_spec {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (cond : Expr S Γ .bool) (yes no : TailBody S params result Γ)
    (condSpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv cond env slots paid live)
    (yesSpec : TailCodeSpec m funs flags bounds fits host pv targetModes yes)
    (noSpec : TailCodeSpec m funs flags bounds fits host pv targetModes no) :
    TailCodeSpec m funs flags bounds fits host pv targetModes (.ite cond yes no) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let body := TailBody.ite cond yes no
  let mid := fun i => yes.uses i || no.uses i
  let condLive := fun i => mid i || cond.uses i
  have hEntry : ∀ i, mid i = true → body.uses i = true := by
    intro i hi
    simp only [mid, Bool.or_eq_true] at hi
    simp only [body, TailBody.uses, Bool.or_eq_true]
    tauto
  have hCond : condLive = body.uses := by
    funext i
    simp only [condLive, mid, body, TailBody.uses]
    cases cond.uses i <;> cases yes.uses i <;> cases no.uses i <;> rfl
  have hSplit : dyingPot store s env slots paid body.uses (fun _ => false) =
      dyingPot store s env slots paid condLive mid +
        dyingPot store s env slots paid mid (fun _ => false) := by
    rw [hCond]
    exact dyingPot_split _ _ _ hEntry nofun
  have hcWidth := Nat.le_max_left cond.width (max (yes.width targetModes) (no.width targetModes))
  have hbWidth := Nat.le_max_right cond.width (max (yes.width targetModes) (no.width targetModes))
  simp only [TailBody.width] at hRoom
  simp only [TailBody.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨hCondPlace, hYesPlace⟩, hNoPlace⟩ := hPlace
  simp only [TailBody.code, TailBody.usesFast_eq]
  refine condSpec env slots paid mid h base heap store s hh hpv
    (hVars.live_mono fun i hi => by rw [← hCond]; exact hi) hAt hCap (by omega)
    (by omega) hCondPlace _ _
    (hTrap.part (by simp only [TailBody.fits]; flag_tac)
      (fun ha => by simp only [TailBody.aborts, Bool.or_eq_true] at ha ⊢; tauto)
      fun _ hw => hw.mono (by
        rw [hSplit]
        simp only [TailBody.allocs]
        dsimp only [condLive, mid]
        omega))
    fun heap1 store1 s1 ws1 after1 top1 => ?_
  have boolRep := after1.rep
  simp only [Ty.rep_bool] at boolRep
  subst boolRep
  have e1 : Evolves env slots body.uses mid base heap store s heap1 store1
      { s1 with values := s.values } := by
    have e := (after1.toEvolves rfl).values s.values
    change Evolves env slots condLive mid base heap store s heap1 store1 _ at e
    rw [hCond] at e
    exact e
  have runBranch (b : TailBody S params result Γ)
      (bSpec : TailCodeSpec m funs flags bounds fits host pv targetModes b)
      (hSub : ∀ i, b.uses i = true → mid i = true)
      (hWidth : b.width targetModes ≤ max (yes.width targetModes) (no.width targetModes))
      (hPlaceB : b.placeArgs targetModes (slots.map Slot.mode) = true)
      (hAborts : b.aborts = true → body.aborts = true)
      (hFits : body.fits funs fits env = true → b.fits funs fits env = true)
      (hAlloc : body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env =
        cond.allocs funs flags bounds (slots.map Slot.mode) paid mid env +
          b.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env)
      (hValue : b.denote funs env = body.denote funs env)
      (hPaidB : resultPaid = true → b.paidResult flags (slots.map Slot.mode) paid = true)
      (Qb : Assertion Unit)
      (hQTrap : ∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable"))
      (hQBreak : ∀ k st ss, Q (.Break k st ss) → Qb (.Break (k + 1) st ss)) :
      wp m (releaseWhere Γ slots (fun i => mid i && !b.uses i) ++
        b.code targetModes h stateBase resultBase slots base (exitLabel + 1) (nextLabel + 1))
        Qb store1 { s1 with values := s.values } host := by
    refine wp_releaseWhere hm e1.holds e1.step.at_
      (fun i hi => by simp only [Bool.and_eq_true] at hi; exact hi.1)
      fun heap2 store2 e2 top2 => ?_
    have hReleased : (fun i => mid i && !(mid i && !b.uses i)) = b.uses := by
      funext i
      exact live_released _ _ (hSub i)
    rw [hReleased] at e2
    have hPot : dyingPot store2 { s1 with values := s.values } env slots paid b.uses
        (fun _ => false) = dyingPot store s env slots paid b.uses (fun _ => false) := by
      rw [dyingPot_evolves e1.holds e2 hSub _ _ (fun _ hi => hi),
        dyingPot_evolves hVars e1 hEntry _ _ hSub]
    have hPotLe : dyingPot store s env slots paid b.uses (fun _ => false) ≤
        dyingPot store s env slots paid mid (fun _ => false) := dyingPot_mono hSub nofun
    have hFitsCond : body.fits funs fits env = true → cond.fits funs fits env = true := by
      intro hf
      simp only [body, TailBody.fits, Bool.and_eq_true] at hf
      exact hf.1
    have topCond : body.fits funs fits env = true → heap1.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid condLive mid +
          cond.allocs funs flags bounds (slots.map Slot.mode) paid mid env := by
      intro hf
      have ht := top1 (hFitsCond hf)
      simpa only [Ty.pot, ite_self, Nat.add_zero] using ht
    refine bSpec env slots paid nextPaid resultPaid h stateBase resultBase base
      (exitLabel + 1) (nextLabel + 1) heap2 store2 { s1 with values := s.values }
      (e1.frame.half.trans hh) (e1.frame.params.trans hpv) e2.holds e2.step.at_
      (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
      (by change s1.params.length ≤ stateBase; rw [e1.frame.params]; exact hLow)
      hState hResult (by omega) hPlaceB hPaidB _
      ((hTrap.imp hQTrap).part
        (fun hd => by
          cases hf : body.fits funs fits env
          · rfl
          · simp [hFits hf] at hd)
        (fun ha => by
          simp only [Bool.or_eq_true] at ha ⊢
          rcases ha with ((ha | ha) | ha) | ha
          · exact Or.inl (Or.inl (Or.inl (hAborts ha)))
          · exact Or.inl (Or.inl (Or.inr ha))
          · exact Or.inl (Or.inr ha)
          · exact Or.inr ha)
        fun hd hw => by
          have hf : body.fits funs fits env = true := by simpa using hd
          exact hw.shift (heap1 := heap2) (store1 := store2)
            (c1 := dyingPot store s env slots paid condLive mid +
              cond.allocs funs flags bounds (slots.map Slot.mode) paid mid env)
            (by have := topCond hf; have := congrArg UInt64.toNat top2; omega)
            (by rw [hSplit, hAlloc, hPot]; omega)
            (by rw [e2.step.cap m, e1.step.cap m]))
      fun heap3 store3 s3 after3 top3 => ?_
    have e12 := Evolves.trans hVars e1 e2 hSub hEntry
    let final := TailAfter.prepend hVars e12 after3 (fun i hi => hEntry i (hSub i hi))
      (by omega)
    let final' := TailAfter.congr hValue final
    have hDone := hNext heap3 store3 s3 final' fun hf => by
      have ht := top3 (hFits hf)
      have hc := topCond hf
      have hr := congrArg UInt64.toNat top2
      change heap3.top.toNat + tailPot targetModes nextPaid resultPaid store3 after3.words
        (body.denote funs env) ≤ _
      rw [hPot] at ht
      rw [← hValue]
      rw [hSplit, hAlloc]
      omega
    have labelEq : (b.denote funs env).elim (fun _ => nextLabel + 1) (fun _ => exitLabel + 1) =
        (body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel) + 1 := by
      rw [hValue]
      cases body.denote funs env <;> rfl
    rw [labelEq]
    exact hQBreak _ _ _ hDone
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, wp_eqzI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  cases hc : cond.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    exact runBranch no noSpec (fun i hi => by simp [mid, hi]) (Nat.le_max_right ..)
      hNoPlace (fun ha => by simp [body, TailBody.aborts, ha])
      (fun hf => by simp only [body, TailBody.fits, hc, Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true] at hf; exact hf.2)
      (by simp only [body, TailBody.allocs, hc, Bool.false_eq_true, ↓reduceIte]; rfl)
      (by simp [body, TailBody.denote, hc])
      (fun hp => by have hp' := hPaid hp; simp only [TailBody.paidResult, Bool.and_eq_true] at hp'; exact hp'.2)
      _ (fun _ ht => ht)
      (fun _ _ _ hb => hb)
  · simp (config := { decide := true }) only [↓reduceIte]
    exact runBranch yes yesSpec (fun i hi => by simp [mid, hi]) (Nat.le_max_left ..)
      hYesPlace (fun ha => by simp [body, TailBody.aborts, ha])
      (fun hf => by simp only [body, TailBody.fits, hc, ↓reduceIte,
        Bool.and_eq_true] at hf; exact hf.2)
      (by simp only [body, TailBody.allocs, hc, ↓reduceIte]; rfl)
      (by simp [body, TailBody.denote, hc])
      (fun hp => by have hp' := hPaid hp; simp only [TailBody.paidResult, Bool.and_eq_true] at hp'; exact hp'.1)
      _ (fun _ ht => ht)
      (fun _ _ _ hb => hb)

#print axioms tail_ite_spec

end Verified
