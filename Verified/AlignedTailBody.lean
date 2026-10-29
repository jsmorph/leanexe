import Verified.AlignedTail
import Verified.TailLetPair
import Verified.TailCorrect

/-!
The tail body's constructs that pass the next state, choose, and bind, under the flag.  Each is its
original with `TailCodeSpecX strict` for `TailCodeSpec`, `CodeSpecX strict` for `CodeSpec`, the
flagged rules for the code, `HoldsA` carried beside `Holds`, and the alignment of the outcome for
the continuation.  The next state's alignment comes from the arguments' (`args_specX`) and
persists across the release of the variables that die there (`Env.AlignedVals.step`).  A bound
variable's alignment is the value's (`HoldsA.push`), and a pair's components are aligned when the
pair is.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem tail_next_specX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (targetModes : List Mode)
    (args : (i : Fin params.length) → Expr S Γ (params.get i))
    (argsSpec : ∀ i env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (args i) env slots paid live) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (.next (result := result) args) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let g := tailSig params result targetModes
  let all := fun k => argsAny fun i => (args i).uses k
  let kept := fun k => all k && !(argsAny fun i => callMoves slots (fun _ => false) (g := g)
    args i && (args i).uses k)
  let nextEnv := Env.ofFn fun i => (args i).denote funs env
  let charge := argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all kept
    g.mode args env)
  let a := (argsAny fun i => (args i).aborts) || !result.scalar ||
    (paramModes params targetModes).any (· == .owned) || slots.any (·.mode == .owned)
  let d := !(argsAll fun i => (args i).fits funs fits env)
  have vars0 : Holds env slots all base heap store s := hVars
  have hUses : ∀ i k, (args i).uses k = true → all k = true :=
    fun i k hi => le_argsAny _ i hi
  have hKept : ∀ k, kept k = true → all k = true := by
    intro k hk
    simp only [kept, Bool.and_eq_true] at hk
    exact hk.1
  have hProps := TailBody.next_placeArgs (result := result) args targetModes
    (slots.map Slot.mode) hPlace
  have hVar : ∀ i : Fin params.length, g.mode i = .owned → ∃ x, args i = .var x := hProps.2.1
  have hMoved := callMoves_moved slots (fun _ => false) (sig := g) args hVar
  have hCharge :
      (TailBody.next (result := result) args).allocs funs flags bounds targetModes nextPaid
        (slots.map Slot.mode) paid env =
      charge + tailCredits (result := result) funs targetModes nextPaid
        (slots.map Slot.mode) paid args env := by
    simp only [TailBody.allocs, charge, kept, all]
    rw [callMovesAt_eq (g := g) slots (fun _ => false) args]
    rfl
  have hRoomArgs : ∀ i : Fin params.length,
      base + (if g.mode i = .owned then copyWidth (params.get i) else (args i).width) ≤ h := by
    intro i
    exact (Nat.add_le_add_left (le_argsMax _ i) base).trans hRoom
  have hSelected : ∀ k, (argsAny fun i => g.mode i == .owned && (args i).uses k &&
      !kept k) = true → all k = true := by
    intro k hk
    obtain ⟨i, hi⟩ := argsAny_true.mp hk
    simp only [Bool.and_eq_true] at hi
    exact hUses i k hi.1.2
  simp only [TailBody.code, TailBody.codeWith, Expr.usesFast_eq, List.append_assoc]
  refine args_specX hCopy (paid := paid) (all := all) (kept := kept) (d := d) (a := a)
    g.mode args argsSpec hUses
    hKept (fun i hi => paramMode_owned hi) (fun i hs hi => (hProps.2.2 i hs hi).1)
    (fun i hi => ?_) hProps.1 (fun i hi => ?_) (fun i hi => ?_)
    heap store s hh hpv vars0 hAt hAl hSafe hCap (by omega) hRoomArgs _ _
    (hTrap.part id id fun _ hw => hw.mono (by rw [hCharge]; dsimp [charge]; omega))
    fun heap1 store1 s1 ws1 fresh step1 frame1 vars1 rep1 hAl1 separate1 movedApart readsApart top1 pot1 => ?_
  · obtain ⟨x, hx⟩ := hVar i hi
    refine ⟨x, hx, fun hk => ?_⟩
    have hxUses : (args i).uses x.index = true := by rw [hx]; simp [Expr.uses]
    have hxAll := hUses i x.index hxUses
    simp only [kept, hxAll, Bool.true_and, Bool.not_eq_false'] at hk
    obtain ⟨j, y, hy, hyx, -, hyOwned, -, others⟩ := hMoved _ hk
    have hj : j = i := by
      by_contra hne
      have bad := others i (Ne.symm hne) (paramMode_owned hi)
      exact Bool.noConfusion (hxUses.symm.trans bad)
    subst hj
    exact ⟨hyOwned, others⟩
  · simp only [d, Bool.not_eq_true'] at hi ⊢
    exact argsAll_false _ i hi
  · simp only [Bool.or_eq_true] at hi
    rcases hi with (hi | hi) | hi
    · have ha := le_argsAny (fun j => (args j).aborts) i hi
      simp only [a, ha, Bool.true_or]
    · have ha := paramModes_any_owned (show paramMode params targetModes i = .owned from
        beq_iff_eq.mp hi)
      simp [a, ha]
    · simp [a, hi]
  have keptApart := args_moves_apart_kept g.mode args hUses hKept vars0 step1 frame1 movedApart
  have borrowedVars : ∀ k, (argsAny fun i => g.mode i == .borrowed &&
      !(params.get i).scalar && (args i).uses k) = true →
      modeAt (slots.map Slot.mode) k = .borrowed :=
    TailBody.next_borrowed_vars (result := result) args targetModes (slots.map Slot.mode) hPlace
  have borrowedApart := args_reads_apart_owned g.mode args hUses borrowedVars vars0
    step1 frame1 readsApart
  have potArgs : Env.argPot store1 (g.paidSel nextPaid) ws1 nextEnv ≤
      dyingPot store s env slots paid all (fun _ => false) +
        tailCredits (result := result) funs targetModes nextPaid (slots.map Slot.mode) paid args env := by
    have hp := args_pot_le_credits (sig := g) (pf := nextPaid) (slots := slots) (live := fun _ => false)
        (paid := paid) (env := env) (s := s) (ws := ws1) (funs := funs) (base := base)
        args hVar (vars0.live_mono fun _ hi => by
          simpa only [Bool.false_or, all, g, tailSig] using hi) step1 pot1
    dsimp (config := { instances := true }) only [tailCredits, all, nextEnv, g, tailSig] at hp ⊢
    simpa only [Bool.false_or] using hp
  have prepared : Step heap store (Holds.KeepDying env slots all (fun _ => false) store s)
      heap1 store1 ((Env.moves store1 g.mode ws1 nextEnv).map (block store1)) := by
    refine ⟨step1.at_, step1.caps, fun r hr hp hk => ?_⟩
    obtain ⟨bytes, region, freshApart⟩ := step1.keeps r hr hp trivial
    refine ⟨bytes, region, fun b hb => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact movedApart r freshApart (hk.mono fun k hi _ => ⟨hSelected k hi, rfl⟩) q hq
  refine wpX_releaseWhere hm hRA ((vars1.live_mono hKept).agree Frame.ofValues) step1.at_
    (fun hs => ((hAl1 hs).1.live_mono hKept).values _)
    (fun _ hi => hi) fun heap2 store2 release topRelease hAl2 => ?_
  have release' := release.mono (live' := fun _ => false) fun _ hi => nomatch hi
  have releaseStep : Step heap1 store1 (Holds.KeepDying env slots kept (fun _ => false) store1 s1)
      heap2 store2 [] :=
    release'.step.mono (fun _ hr => Holds.keepDying_values.mpr hr) (fun _ hb => hb)
  have keepOwned : ∀ q ∈ Env.moves store1 g.mode ws1 nextEnv,
      Holds.KeepDying env slots kept (fun _ => false) store1 s1 (block store1 q) := by
    intro q hq t x hx _ hxOwned wx hold length b hb
    have hb' : b ∈ t.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hxOwned]; exact hb
    exact regionsDisjoint_symm (keptApart t x hx wx hold length b hb' q hq)
  have keepBorrowed : ∀ r ∈ Env.reads store1 g.mode ws1 nextEnv,
      Holds.KeepDying env slots kept (fun _ => false) store1 s1 r := by
    intro r hr t x hx _ hxOwned wx hold length b hb
    exact regionsDisjoint_symm (borrowedApart t x (hKept _ hx) hxOwned wx hold length b hb r hr)
  obtain ⟨rep2, sameBlocks, sameMoves, sameReads⟩ := Env.Rep.step releaseStep nextEnv g.mode ws1 rep1 keepOwned keepBorrowed
  have alignedNext : strict = true → Env.AlignedVals store2 g.mode ws1 nextEnv := fun hs =>
    Env.AlignedVals.step releaseStep nextEnv g.mode ws1 rep1 keepOwned keepBorrowed (hAl1 hs).2
  have separate2 : Separate store2 (Env.moves store2 g.mode ws1 nextEnv)
      (Env.reads store2 g.mode ws1 nextEnv) := by
    rw [sameMoves, sameReads]
    exact Separate.of_block_eq separate1 sameBlocks
  have keepRelease : ∀ r, Holds.KeepDying env slots all (fun _ => false) store s r →
      Holds.KeepDying env slots kept (fun _ => false) store1 s1 r := by
    intro r hr
    exact Holds.KeepDying.transfer vars0
      (step1.mono (fun _ _ => trivial) (fun _ hb => hb)) frame1 (fun _ hi => hi)
      (fun i hi _ => hKept i hi) (hr.mono fun i hi _ => ⟨hKept i hi, rfl⟩)
  have combined := prepared.transBoth releaseStep (keep := Holds.KeepDying env slots all
      (fun _ => false) store s) fun r hr => ⟨hr, fun _ => keepRelease r hr⟩
  have sameFresh : (Env.moves store2 g.mode ws1 nextEnv).map (block store2) =
      (Env.moves store1 g.mode ws1 nextEnv).map (block store1) := by
    rw [sameMoves]
    exact List.map_congr_left sameBlocks
  have finalStep : Step heap store (Holds.KeepDying env slots all (fun _ => false) store s)
      heap2 store2 ((Env.moves store2 g.mode ws1 nextEnv).map (block store2)) := by
    simpa only [List.append_nil, sameFresh] using combined
  have samePot := Env.argPot_of_blocks nextEnv g.mode ws1 rep1 sameBlocks (g.paidSel nextPaid)
    (fun i hi => by simp only [Sig.paidSel, Bool.and_eq_true, beq_iff_eq] at hi; exact hi.2)
  rw [storeParamsCode_eq]
  refine wpX_storeCode ws1 h stateBase (params.flatMap Ty.types) s1 s.values
    (by rw [rep1.length, flatMap_types_length]) (frame1.positions.trans hh)
    (by rw [frame1.params]; exact hLow)
    (by rw [flatMap_types_length, frame1.positions, hh]; omega) fun s2 frame2 hold2 _ => ?_
  rw [wpX_br_cons]
  refine hNext heap2 store2 s2
    ⟨ws1, finalStep, (frame1.mono (by omega)).trans frame2, rep2, separate2, hold2⟩
    (fun hs => ⟨(hAl2 hs).1, alignedNext hs⟩) ?_
  intro hf
  have ht := top1 (by simpa only [d, TailBody.fits, Bool.not_eq_false'] using hf)
  change heap1.top.toNat ≤ heap.top.toNat + charge at ht
  have htr := congrArg UInt64.toNat topRelease
  change heap2.top.toNat + Env.argPot store2 (g.paidSel nextPaid) ws1 nextEnv ≤
    heap.top.toNat + dyingPot store s env slots paid all (fun _ => false) +
      (TailBody.next (result := result) args).allocs funs flags bounds targetModes nextPaid
        (slots.map Slot.mode) paid env
  rw [samePot]
  rw [hCharge]
  omega

theorem tail_next_spec {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (args : (i : Fin params.length) → Expr S Γ (params.get i))
    (argsSpec : ∀ i env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env slots paid live) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.next (result := result) args) :=
  TailCodeSpecX.false_iff.mp (tail_next_specX (strict := false) hm nofun (copyCodeX hm) targetModes
    args (fun i env slots paid live => CodeSpecX.false_iff.mpr (argsSpec i env slots paid live)))
#print axioms tail_next_spec

theorem tail_ite_specX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (targetModes : List Mode)
    (cond : Expr S Γ .bool) (yes no : TailBody S params result Γ)
    (condSpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv cond env slots paid live)
    (yesSpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes yes)
    (noSpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes no) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (.ite cond yes no) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let body := TailBody.ite cond yes no
  let mid := fun i => yes.uses i || no.uses i
  let condLive := fun i => mid i || cond.uses i
  have hEntry : ∀ i, mid i = true → body.uses i = true := by
    intro i hi
    simp only [mid, Bool.or_eq_true] at hi
    simp only [body, TailBody.uses, Bool.or_eq_true]
    clear hAl hRA
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
  simp only [TailBody.code, TailBody.codeWith, TailBody.usesFast_eq]
  refine condSpec env slots paid mid h base heap store s hh hpv
    (hVars.live_mono fun i hi => by rw [← hCond]; exact hi) hAt
    (fun hs => (hAl hs).live_mono fun i hi => by rw [← hCond]; exact hi)
    (hSafe.mono fun i hi => by rw [← hCond]; exact hi) hCap (by omega)
    (by omega) hCondPlace _ _
    (hTrap.part (by clear hAl hRA; simp only [TailBody.fits]; flag_tac)
      (fun ha => by clear hAl hRA; simp only [TailBody.aborts, Bool.or_eq_true] at ha ⊢; tauto)
      fun _ hw => hw.mono (by
        rw [hSplit]
        simp only [TailBody.allocs]
        dsimp only [condLive, mid]
        omega))
    fun heap1 store1 s1 ws1 after1 hAl1 top1 => ?_
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
      (bSpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes b)
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
      wpX strict m (releaseWhere Γ slots (fun i => mid i && !b.uses i) ++
        b.code (pool := pool) targetModes h stateBase resultBase slots base (exitLabel + 1) (nextLabel + 1))
        Qb store1 { s1 with values := s.values } host := by
    refine wpX_releaseWhere hm hRA e1.holds e1.step.at_ (fun hs => (hAl1 hs).1.values _)
      (fun i hi => by simp only [Bool.and_eq_true] at hi; exact hi.1)
      fun heap2 store2 e2 top2 hAl2 => ?_
    have hReleased : (fun i => mid i && !(mid i && !b.uses i)) = b.uses := by
      funext i
      exact live_released _ _ (hSub i)
    rw [hReleased] at e2 hAl2
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
      (e1.frame.positions.trans hh) (e1.frame.params.trans hpv) e2.holds e2.step.at_ hAl2
      ((hSafe.evolves hVars e1 hEntry).evolves e1.holds e2 hSub)
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
      fun heap3 store3 s3 after3 hAl3 top3 => ?_
    have e12 := Evolves.trans hVars e1 e2 hSub hEntry
    let final := TailAfter.prepend hVars e12 after3 (fun i hi => hEntry i (hSub i hi))
      (by omega)
    let final' := TailAfter.congr hValue final
    have hDone := hNext heap3 store3 s3 final'
      (fun hs => ⟨(hAl3 hs).1, by
        show TailAligned targetModes store3 after3.words _
        rw [← hValue]; exact (hAl3 hs).2⟩) fun hf => by
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
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, wpX_eqzI64_cons]
  refine wpX_iff_cons rfl ?_
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

theorem tail_ite_spec {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (cond : Expr S Γ .bool) (yes no : TailBody S params result Γ)
    (condSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv cond env slots paid live)
    (yesSpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes yes)
    (noSpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes no) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.ite cond yes no) :=
  TailCodeSpecX.false_iff.mp (tail_ite_specX (strict := false) hm nofun targetModes cond yes no
    (fun env slots paid live => CodeSpecX.false_iff.mpr (condSpec env slots paid live))
    (TailCodeSpecX.false_iff.mpr yesSpec) (TailCodeSpecX.false_iff.mpr noSpec))
#print axioms tail_ite_spec

theorem tail_let_specX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result valueTy : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (targetModes : List Mode)
    (value : Expr S Γ valueTy) (body : TailBody S params result (valueTy :: Γ))
    (valueSpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv value env slots paid live)
    (bodySpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes body) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (.letE value body) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
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
  simp only [TailBody.code, TailBody.codeWith, TailBody.usesFast_eq, List.append_assoc]
  refine valueSpec env slots paid mid h (base + valueTy.width) heap store s hh hpv
    ((hVars.mono (by omega)).live_mono fun i hi => by rw [← hInput]; exact hi)
    hAt (fun hs => (hAl hs).live_mono fun i hi => by rw [← hInput]; exact hi)
    (hSafe.mono fun i hi => by rw [← hInput]; exact hi)
    hCap (by omega) (by omega) hPlace.1 _ _
    (hTrap.part (by clear hAl hRA; simp only [TailBody.fits]; flag_tac)
      (fun ha => by clear hAl hRA; simp only [TailBody.aborts, Bool.or_eq_true] at ha ⊢; tauto)
      fun _ hw => hw.mono (by
        rw [hSplit]
        simp only [TailBody.allocs]
        dsimp only [input, mid]
        omega))
    fun heap1 store1 s1 ws1 a1 hAl1 top1 => ?_
  have vars0 : Holds env slots input base heap store s := by rw [hInput]; exact hVars
  have a1' := a1.lower vars0 (Nat.le_add_right _ _) hMid
  refine wpX_storeCode ws1 h base valueTy.types s1 s.values a1.rep.typed (a1.frame.positions.trans hh)
    (by rw [a1.frame.params]; omega) (by rw [Ty.types_length, a1.frame.positions, hh]; omega)
    fun s2 frame2 hold2 _ => ?_
  have f2 : Frame base s1 { s2 with values := s.values } := frame2.trans Frame.ofValues
  have hold2' : LocalsHold { s2 with values := s.values } base valueTy.types ws1 := hold2
  have varsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots) (fun i => i == 0 || body.uses i)
      (base + valueTy.width) heap1 store1 { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree f2).live_mono fun _ hi => by simpa [mid] using hi)
      hold2' a1.rep ((a1'.apart.agree a1'.holds f2).live_mono fun _ hi => by simpa [mid] using hi)
  have alB : strict = true → HoldsA (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || body.uses i) heap1 store1 { s2 with values := s.values } := fun hs =>
    HoldsA.push ((HoldsA.agree a1'.holds (hAl1 hs).1 f2).live_mono fun _ hi => by
      simpa [mid] using hi) hold2' a1.rep.length (hAl1 hs).2
  have safeB : pool.Safe (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || body.uses i) heap1 store1 { s2 with values := s.values } :=
    (hSafe.mono fun i hi => by rw [← hInput]; exact hi).bind vars0 a1' hMid
      (fun _ hi => by simpa [mid] using hi) f2 hold2'
  have releaseEq : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode valueTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (valueTy :: Γ) (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [releaseEq]
  refine wpX_releaseVars hm hRA _ (by split <;> simp) varsB a1.step.at_ alB (by split <;> simp)
    fun heap2 store2 release top2 hAl2 => ?_
  have release' := release.mono (live' := body.uses) fun i hi => by
    cases i with
    | zero => simp [hi]
    | succ k => split <;> simpa using hi
  have alB2 : strict = true → HoldsA (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      body.uses heap2 store2 { s2 with values := s.values } := fun hs =>
    (hAl2 hs).live_mono fun i hi => by
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
    (f2.params.trans (a1.frame.params.trans hpv)) release'.holds release'.step.at_ alB2
    (safeB.evolves varsB release' (fun i hi => by simp [hi]))
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
    fun heap3 store3 s3 after3 hAl3 top3 => ?_
  let afterB := TailAfter.prepend varsB release' after3 (fun i hi => by simp [hi]) (by omega)
  let final := TailAfter.bind vars0 a1' f2 hold2' afterB (fun _ hi => hi) hMid (by omega)
  let final' := final.liveIn (L0 := outer.uses) (fun i hi => by rw [← hInput]; exact hi)
  refine hNext heap3 store3 s3 final' hAl3 fun hf => ?_
  have h1 := top1 (hFitsValue hf)
  have h3 := top3 (hFitsBody hf)
  have hr := congrArg UInt64.toNat top2
  change heap3.top.toNat + tailPot targetModes nextPaid resultPaid store3 after3.words
    (body.denote funs (.cons (value.denote funs env) env)) ≤ _
  rw [hSplit]
  simp only [TailBody.allocs, List.map_cons] at h3 ⊢
  dsimp only [input, mid] at h1 hDb h3 ⊢
  omega

theorem tail_let_spec {S : List Sig} {Γ params : List Ty} {result valueTy : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (value : Expr S Γ valueTy) (body : TailBody S params result (valueTy :: Γ))
    (valueSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv value env slots paid live)
    (bodySpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes body) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.letE value body) :=
  TailCodeSpecX.false_iff.mp (tail_let_specX (strict := false) hm nofun targetModes value body
    (fun env slots paid live => CodeSpecX.false_iff.mpr (valueSpec env slots paid live))
    (TailCodeSpecX.false_iff.mpr bodySpec))
#print axioms tail_let_spec

theorem tail_letPair_specX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result firstTy secondTy : Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (targetModes : List Mode)
    (value : Expr S Γ (.pair firstTy secondTy))
    (body : TailBody S params result (secondTy :: firstTy :: Γ))
    (valueSpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv value env slots paid live)
    (bodySpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes body) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (.letPair value body) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
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
    hAt (fun hs => (hAl hs).live_mono fun i hi => by rw [← hInput]; exact hi)
    (hSafe.mono fun i hi => by rw [← hInput]; exact hi)
    hCap (by omega) (by omega) hPlace.1 _ _
    (hTrap.part (by clear hAl hRA; simp only [TailBody.fits]; flag_tac)
      (fun ha => by clear hAl hRA; simp only [TailBody.aborts, Bool.or_eq_true] at ha ⊢; tauto)
      fun _ hw => hw.mono (by
        rw [hSplit]
        simp only [TailBody.allocs]
        dsimp only [input, mid]
        omega))
    fun heap1 store1 s1 ws1 a1 hAl1 top1 => ?_
  have vars0 : Holds env slots input base heap store s := by rw [hInput]; exact hVars
  have a1' := a1.lower vars0 (by omega) hMid
  obtain ⟨wFirst, wSecond, rfl, repFirst, repSecond, apart⟩ := a1.rep
  have lenFirst := repFirst.length
  have lenSecond := repSecond.length
  rw [List.reverse_append, List.append_assoc]
  refine wpX_storeCode wSecond h (base + firstTy.width) secondTy.types s1
    (wFirst.reverse ++ s.values) repSecond.typed (a1.frame.positions.trans hh)
    (by rw [a1.frame.params]; omega) (by rw [Ty.types_length, a1.frame.positions, hh]; omega)
    fun s2 frame2 holdSecond _ => ?_
  refine wpX_storeCode wFirst h base firstTy.types s2 s.values repFirst.typed
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
  have alB : strict = true → HoldsA (Env.cons (value.denote funs env).2 (Env.cons (value.denote funs env).1 env))
      (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
        ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || body.uses i) heap1 store1 { s3 with values := s.values } :=
    fun hs => HoldsA.push (HoldsA.push ((HoldsA.agree a1'.holds (hAl1 hs).1 f3).live_mono
      fun _ hi => by simpa [mid] using hi) holdFirst' lenFirst ((hAl1 hs).2.fst lenFirst))
      holdSecond' lenSecond ((hAl1 hs).2.snd lenFirst)
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
  refine wpX_releaseVars hm hRA _ (by split <;> split <;> simp) varsB a1.step.at_ alB
    (by split <;> split <;> simp) fun heap2 store2 release top2 hAl2 => ?_
  have release' := release.mono (live' := body.uses) fun i hi => by
    match i with
    | 0 => simp [hi]
    | 1 => simp [hi]
    | k + 2 => split <;> split <;> simpa using hi
  have alB2 : strict = true → HoldsA (Env.cons (value.denote funs env).2 (Env.cons (value.denote funs env).1 env))
      (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
        ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      body.uses heap2 store2 { s3 with values := s.values } := fun hs =>
    (hAl2 hs).live_mono fun i hi => by
      match i with
      | 0 => simp [hi]
      | 1 => simp [hi]
      | k + 2 => split <;> split <;> simpa using hi
  -- The body's dying variables: the components, paid when the pair is, whose potential is the
  -- pair's, and the others, whose potential the pair's code and the releases keep.
  have hPotE : (Ty.pair firstTy secondTy).pot store1 (wFirst ++ wSecond) (value.denote funs env) =
      firstTy.pot store1 wFirst (value.denote funs env).1 +
        secondTy.pot store1 wSecond (value.denote funs env).2 := by
    simp only [Ty.pot, List.take_left' lenFirst, List.drop_left' lenFirst]
  have hDb : dyingPot store2 { s3 with values := s.values }
      (Env.cons (value.denote funs env).2 (Env.cons (value.denote funs env).1 env))
      (⟨base + firstTy.width, value.mode (slots.map Slot.mode)⟩ ::
        ⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (value.paid flags (slots.map Slot.mode) paid mid ::
        value.paid flags (slots.map Slot.mode) paid mid :: paid)
      body.uses (fun _ => false) ≤
        (if value.paid flags (slots.map Slot.mode) paid mid = true then
          (Ty.pair firstTy secondTy).pot store1 (wFirst ++ wSecond) (value.denote funs env)
        else 0) + dyingPot store s env slots paid mid (fun _ => false) := by
    rw [dyingPot_evolves varsB release' (fun i hi => by simp [hi]) _ _ (fun _ hi => hi),
      dyingPot_cons, dyingPot_cons]
    rw [dyingPot_step vars0 a1'.step (a1'.frame.trans f3) hMid _ _ (fun _ hi => hi)]
    dsimp only
    rw [holdSecond'.read_eq (by rw [lenSecond, Ty.types_length]),
      holdFirst'.read_eq (by rw [lenFirst, Ty.types_length]), hPotE]
    by_cases hpp : value.paid flags (slots.map Slot.mode) paid mid = true
    · rw [ite_eq_left hpp]
      split <;> split <;> omega
    · simp only [hpp, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;> omega
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
  refine bodySpec _ _
    (value.paid flags (slots.map Slot.mode) paid mid ::
      value.paid flags (slots.map Slot.mode) paid mid :: paid) nextPaid resultPaid h stateBase
    resultBase
    (base + firstTy.width + secondTy.width) exitLabel nextLabel heap2 store2
    { s3 with values := s.values } (f3.positions.trans (a1.frame.positions.trans hh))
    (f3.params.trans (a1.frame.params.trans hpv)) release'.holds release'.step.at_ alB2
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
        have hDb' := hDb
        refine hw.of_le ?_ (by rw [release'.step.cap m, a1.step.cap m])
        rw [hSplit]
        simp only [TailBody.allocs, List.map_cons]
        dsimp only [input, mid] at h1 hDb' ⊢
        by_cases hpp : value.paid flags (slots.map Slot.mode) paid (fun i => body.uses (i + 2)) = true
        · rw [ite_eq_left hpp] at h1 hDb'; omega
        · rw [ite_eq_right hpp] at h1 hDb'; omega)
    fun heap3 store3 s4 after4 hAl4 top4 => ?_
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
  refine hNext heap3 store3 s4 final' hAl4 fun hf => ?_
  have h1 := top1 (hFitsValue hf)
  have h4 := top4 (hFitsBody hf)
  have hr := congrArg UInt64.toNat top2
  have hDb' := hDb
  change heap3.top.toNat + tailPot targetModes nextPaid resultPaid store3 after4.words
    (body.denote funs (.cons (value.denote funs env).2 (.cons (value.denote funs env).1 env))) ≤ _
  rw [hSplit]
  simp only [TailBody.allocs, List.map_cons] at h4 ⊢
  dsimp only [input, mid] at h1 h4 hDb' ⊢
  by_cases hpp : value.paid flags (slots.map Slot.mode) paid (fun i => body.uses (i + 2)) = true
  · rw [ite_eq_left hpp] at h1 hDb'; omega
  · rw [ite_eq_right hpp] at h1 hDb'; omega

theorem tail_letPair_spec {S : List Sig} {Γ params : List Ty} {result firstTy secondTy : Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (value : Expr S Γ (.pair firstTy secondTy))
    (body : TailBody S params result (secondTy :: firstTy :: Γ))
    (valueSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv value env slots paid live)
    (bodySpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes body) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.letPair value body) :=
  TailCodeSpecX.false_iff.mp (tail_letPair_specX (strict := false) hm nofun targetModes value body
    (fun env slots paid live => CodeSpecX.false_iff.mpr (valueSpec env slots paid live))
    (TailCodeSpecX.false_iff.mpr bodySpec))
#print axioms tail_letPair_spec

end Verified
