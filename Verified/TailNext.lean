import Verified.TailCorrect
import Verified.TailArgs

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem tail_next_spec {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (args : (i : Fin params.length) → Expr S Γ (params.get i))
    (argsSpec : ∀ i env slots paid live,
      CodeSpec m funs flags bounds fits host pv (args i) env slots paid live) :
    TailCodeSpec m funs flags bounds fits host pv targetModes (.next (result := result) args) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
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
  simp only [TailBody.code, Expr.usesFast_eq, List.append_assoc]
  refine args_spec hm (paid := paid) (all := all) (kept := kept) (d := d) (a := a)
    g.mode args argsSpec hUses
    hKept (fun i hi => paramMode_owned hi) (fun i hs hi => (hProps.2.2 i hs hi).1)
    (fun i hi => ?_) hProps.1 (fun i hi => ?_) (fun i hi => ?_)
    heap store s hh hpv vars0 hAt hCap (by omega) hRoomArgs _ _
    (hTrap.part id id fun _ hw => hw.mono (by rw [hCharge]; dsimp [charge]; omega))
    fun heap1 store1 s1 ws1 fresh step1 frame1 vars1 rep1 separate1 movedApart readsApart top1 pot1 => ?_
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
      heap1 store1 ((Env.moves g.mode ws1 nextEnv).map (block store1)) := by
    refine ⟨step1.at_, step1.caps, fun r hr hp hk => ?_⟩
    obtain ⟨bytes, region, freshApart⟩ := step1.keeps r hr hp trivial
    refine ⟨bytes, region, fun b hb => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact movedApart r freshApart (hk.mono fun k hi _ => ⟨hSelected k hi, rfl⟩) q hq
  refine wp_releaseWhere hm ((vars1.live_mono hKept).agree Frame.ofValues) step1.at_
    (fun _ hi => hi) fun heap2 store2 release topRelease => ?_
  have release' := release.mono (live' := fun _ => false) fun _ hi => nomatch hi
  have releaseStep : Step heap1 store1 (Holds.KeepDying env slots kept (fun _ => false) store1 s1)
      heap2 store2 [] :=
    release'.step.mono (fun _ hr => Holds.keepDying_values.mpr hr) (fun _ hb => hb)
  have keepOwned : ∀ q ∈ Env.moves g.mode ws1 nextEnv,
      Holds.KeepDying env slots kept (fun _ => false) store1 s1 (block store1 q) := by
    intro q hq t x hx _ hxOwned wx hold length b hb
    have hb' : b ∈ t.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hxOwned]; exact hb
    exact regionsDisjoint_symm (keptApart t x hx wx hold length b hb' q hq)
  have keepBorrowed : ∀ r ∈ Env.reads g.mode ws1 nextEnv,
      Holds.KeepDying env slots kept (fun _ => false) store1 s1 r := by
    intro r hr t x hx _ hxOwned wx hold length b hb
    exact regionsDisjoint_symm (borrowedApart t x (hKept _ hx) hxOwned wx hold length b hb r hr)
  obtain ⟨rep2, sameBlocks⟩ := Env.Rep.step releaseStep nextEnv g.mode ws1 rep1 keepOwned keepBorrowed
  have separate2 := Separate.of_block_eq separate1 sameBlocks
  have keepRelease : ∀ r, Holds.KeepDying env slots all (fun _ => false) store s r →
      Holds.KeepDying env slots kept (fun _ => false) store1 s1 r := by
    intro r hr
    exact Holds.KeepDying.transfer vars0
      (step1.mono (fun _ _ => trivial) (fun _ hb => hb)) frame1 (fun _ hi => hi)
      (fun i hi _ => hKept i hi) (hr.mono fun i hi _ => ⟨hKept i hi, rfl⟩)
  have combined := prepared.transBoth releaseStep (keep := Holds.KeepDying env slots all
      (fun _ => false) store s) fun r hr => ⟨hr, fun _ => keepRelease r hr⟩
  have sameFresh : (Env.moves g.mode ws1 nextEnv).map (block store2) =
      (Env.moves g.mode ws1 nextEnv).map (block store1) := List.map_congr_left sameBlocks
  have finalStep : Step heap store (Holds.KeepDying env slots all (fun _ => false) store s)
      heap2 store2 ((Env.moves g.mode ws1 nextEnv).map (block store2)) := by
    simpa only [List.append_nil, sameFresh] using combined
  have samePot := Env.argPot_of_blocks nextEnv g.mode ws1 rep1 sameBlocks (g.paidSel nextPaid)
    (fun i hi => by simp only [Sig.paidSel, Bool.and_eq_true, beq_iff_eq] at hi; exact hi.2)
  rw [storeParamsCode_eq]
  refine wp_storeCode ws1 h stateBase (params.flatMap Ty.types) s1 s.values
    (by rw [rep1.length, flatMap_types_length]) (frame1.positions.trans hh)
    (by rw [frame1.params]; exact hLow)
    (by rw [flatMap_types_length, frame1.positions, hh]; omega) fun s2 frame2 hold2 _ => ?_
  rw [wp_br_cons]
  refine hNext heap2 store2 s2
    ⟨ws1, finalStep, (frame1.mono (by omega)).trans frame2, rep2, separate2, hold2⟩ ?_
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

#print axioms tail_next_spec

end Verified
