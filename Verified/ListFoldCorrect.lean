import Verified.ListFoldLoop

namespace Verified

open Wasm LeanExe.Pipeline

theorem spec_listFold {S : List Sig} {Γ : List Ty} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i))
    (body : Expr S (ListFold.context e captures) (.elem e))
    (argsSpec : ∀ i env slots paid live,
      CodeSpec m funs flags bounds fits host pv (args i) env slots paid live)
    (bodySpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv body env slots paid live) :
    ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv (.listFold args body) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  let value := Expr.listFold args body
  let all := fun i => live i || argsAny fun j => (args j).uses i
  let state := Env.ofFn fun i => (args i).denote funs env
  let charge := argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all all
    (fun _ => .borrowed) args env)
  simp only [Expr.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at hPlace
  obtain ⟨⟨hPlaces, hArgs⟩, hBody⟩ := hPlace
  let f := ListFold.func body hBody
  have allocEq : value.allocs funs flags bounds (slots.map Slot.mode) paid live env =
      charge + f.bound funs flags bounds state := by
    rw [ListFold.func_bound_env]
    rfl
  have fitsEq : value.fits funs fits env =
      ((argsAll fun i => (args i).fits funs fits env) && f.fits funs fits state) := by
    rw [ListFold.func_fits_env]
    rfl
  have argsFits (hf : value.fits funs fits env = true) :
      (argsAll fun i => (args i).fits funs fits env) = true := by
    rw [fitsEq] at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.1
  have loopFits (hf : value.fits funs fits env = true) : f.fits funs fits state = true := by
    rw [fitsEq] at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.2
  have trap : TrapOK (!value.fits funs fits env ||
      !decide (heap.Within store m (dyingPot store s env slots paid all live +
        value.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q := by
    convert hTrap using 1 <;>
      simp only [value, all, Expr.uses, trapFlag, Expr.aborts, Bool.true_or, Bool.true_and] <;> rfl
  have roomArgs (i : Fin (ListFold.params e captures).length) : base + (args i).width ≤ h := by
    simp only [Expr.width] at hRoom
    have hi := le_argsMax (fun j => (args j).width) i
    have hm := Nat.le_max_left (argsMax fun j => (args j).width)
      (widthSum (ListFold.params e captures) + e.width + 3 +
        max treeCopyScratch (e.width + max body.width treeCopyScratch))
    omega
  have roomLoop : base + widthSum (ListFold.params e captures) + e.width +
      (ListFold.tailBody body).width [] ≤ h := by
    simp only [Expr.width] at hRoom
    have ht := ListFold.tail_width body
    have hm := Nat.le_max_right (argsMax fun j => (args j).width)
      (widthSum (ListFold.params e captures) + e.width + 3 +
        max treeCopyScratch (e.width + max body.width treeCopyScratch))
    omega
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine args_spec hm (paid := paid) (all := all) (kept := all) (d := !(argsAll fun i =>
      (args i).fits funs fits env)) (a := true) (fun _ => .borrowed) args argsSpec
    (fun i k hk => by
      change (live k || argsAny fun j => (args j).uses k) = true
      simp only [Bool.or_eq_true]
      exact .inr (le_argsAny _ i hk))
    (fun _ hk => hk) (fun _ => nofun)
    (fun i hs _ => by
      have hi := argsAny_eq_false hPlaces i
      simpa only [hs, Bool.not_false, Bool.true_and, Bool.not_eq_false'] using hi)
    (fun _ => nofun)
    (fun i => by simpa only [Bool.not_eq_false'] using argsAny_eq_false hArgs i)
    (fun i hf => by simpa only [Bool.not_eq_true'] using argsAll_false _ i (by simpa using hf))
    (fun _ _ => rfl) heap store s hh hpv hVars hAt hCap hBase
    (fun i => roomArgs i) _ _
    (trap.part (a := true) (fun hd => by
        simp only [Bool.not_eq_true'] at hd ⊢
        rw [fitsEq, hd, Bool.false_and])
      (fun _ => rfl) (fun _ hw => hw.mono (by rw [allocEq]; omega)))
    fun heap1 store1 s1 ws fresh step1 frame1 vars1 rep1 sep1 _ _ top1 _ => ?_
  rw [storeParamsCode_eq]
  refine wp_storeCode ws h base ((ListFold.params e captures).flatMap Ty.types) s1 s.values
    (by rw [flatMap_types_length]; exact rep1.length)
    (frame1.positions.trans hh) (by rw [frame1.params]; exact hBase)
    (by rw [flatMap_types_length, frame1.positions, hh]; omega)
    fun s2 frame2 hold2 _ => ?_
  refine ListFold.loop_spec hm body hBody bodySpec h base state heap1 store1
    { s2 with values := s.values } ws
    (frame2.positions.trans (frame1.positions.trans hh))
    (frame2.params.trans (frame1.params.trans hpv))
    (by simpa only [ListFold.paramMode_eq_borrowed] using rep1)
    (by simpa only [ListFold.paramMode_eq_borrowed] using sep1)
    hold2 step1.at_ (by rw [step1.cap m]; exact hCap)
    (by rw [frame2.params, frame1.params]; exact hBase) roomLoop _ _
    (trap.part (a := true) (a' := true)
      (fun hd => by
        simp only [Bool.not_eq_true'] at hd ⊢
        rw [fitsEq, hd, Bool.and_false]) (fun _ => rfl)
      (fun good hw => by
        have hf : value.fits funs fits env = true := by simpa using good
        exact hw.shift (top1 (by simp only [argsFits hf, Bool.not_true]))
          (by rw [allocEq]; dsimp only [f, charge]; omega) (step1.cap m)))
    fun heap2 store2 s3 words step2 frame3 result held top2 => ?_
  rw [ListFold.moves_eq_nil] at step2
  have finalFrame : Frame base s s3 := frame1.trans (frame2.trans frame3.values)
  have finalVars : Holds env slots all base heap2 store2 s3 :=
    ((vars1.agree frame2).step step2 (fun _ _ _ _ _ _ _ _ => Apart.nil)).agree frame3.values
  have after : After env slots all all base heap store s (.elem e) .borrowed
      (value.denote funs env) heap2 store2 s3 words := by
    refine ⟨step1.trans step2 (fun _ _ => ⟨trivial, fun _ => Apart.nil⟩),
      finalFrame, finalVars, result.borrow, Holds.Apart.ofScalar rfl⟩
  refine After.release hm (live := live) (sel := fun i => all i && !live i)
    hVars after (fun _ hk => hk)
    (fun _ hk => by simp only [Bool.and_eq_true] at hk; exact hk.1)
    (fun i hi => by simp [all, hi])
    fun heap3 store3 released topRelease _ => ?_
  refine wp_loadCode words released.rep.typed (finalFrame.positions.trans hh) held ?_
  apply hNext heap3 store3 s3 words released
  intro hf
  have ha := top1 (by simp only [argsFits hf, Bool.not_true])
  have hl := top2 (loopFits hf)
  have hr := congrArg UInt64.toNat topRelease
  simp only [Expr.paid, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [allocEq]
  dsimp only [f, charge]
  omega

#print axioms spec_listFold

end Verified
