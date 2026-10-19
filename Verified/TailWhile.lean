import Verified.TailStep

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem tail_loop_spec {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (func : TailFunc S) (decreases : func.Decreases funs)
    (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (bodySpec : TailCodeSpec m funs flags bounds fits host pv func.modes func.body)
    (h stateBase resultBase base : Nat) (env : Env func.params)
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (hRep : Env.Rep (paramMode func.params func.modes) heap store ws env)
    (hSep : Separate store (Env.moves (paramMode func.params func.modes) ws env)
      (Env.reads (paramMode func.params func.modes) ws env))
    (hold : LocalsHold s stateBase (func.params.flatMap Ty.types) ws)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ stateBase)
    (hState : stateBase + widthSum func.params ≤ resultBase)
    (hResult : resultBase + func.result.width ≤ base)
    (hRoom : base + func.body.width func.modes ≤ h) (Q : Assertion Unit)
    (hTrap : TrapOK (!func.fits funs fits env || (func.aborts &&
      !decide (heap.Within store m (Env.argPot store
        (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
        ws env + func.bound funs flags bounds env)))) Q)
    (hNext : ∀ heap' store' s' words,
      Step heap store (Apart store (Env.moves (paramMode func.params func.modes) ws env))
        heap' store' (func.result.blocks store' words (meaning env)) →
      Frame stateBase s s' → func.result.Rep .owned heap' store' words (meaning env) →
      LocalsHold s' resultBase func.result.types words →
      (func.fits funs fits env = true →
        heap'.top.toNat + (if func.paidResult flags then
          func.result.pot store' words (meaning env) else 0) ≤
          heap.top.toNat + Env.argPot store
            (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
            ws env + func.bound funs flags bounds env) →
      Q (.Break 0 store' { s' with values := s.values })) :
    wp m [.loop 0 0
      (releaseWhere func.params (paramSlots func.params func.modes stateBase)
        (fun i => !func.body.usesFast i) ++
        func.body.code func.modes h stateBase resultBase
          (paramSlots func.params func.modes stateBase) base 1 0) [] []] Q store s host := by
  let pf := func.paidParams flags
  let sel := fun i => paidAt pf i && paramMode func.params func.modes i == .owned
  let budget := heap.top.toNat + Env.argPot store sel ws env + func.bound funs flags bounds env
  let keep := Apart store (Env.moves (paramMode func.params func.modes) ws env)
  let Inv : (Env func.params × Heap × List Value) → AssertionF Unit := fun q st ss =>
    let state := q.1
    let hp := q.2.1
    let words := q.2.2
    Step heap store keep hp st
        ((Env.moves (paramMode func.params func.modes) words state).map (block st)) ∧
      Env.Rep (paramMode func.params func.modes) hp st words state ∧
      Separate st (Env.moves (paramMode func.params func.modes) words state)
        (Env.reads (paramMode func.params func.modes) words state) ∧
      LocalsHold ss stateBase (func.params.flatMap Ty.types) words ∧
      Frame stateBase s ss ∧ ss.values = s.values ∧ meaning state = meaning env ∧
      (func.fits funs fits env = true → func.fits funs fits state = true ∧
        hp.top.toNat + Env.argPot st sel words state + func.bound funs flags bounds state ≤ budget)
  have initial : Inv (env, heap, ws) store s := by
    refine ⟨⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr, ?_⟩⟩,
      hRep, hSep, hold, Frame.refl _ _, rfl, rfl, fun hf => ⟨hf, le_rfl⟩⟩
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact hk q hq
  refine Tail.wp_loop_indexed (Inv := Inv) (rank := fun q => func.rank funs q.1) initial ?_
  intro q store1 s1 hi
  rcases q with ⟨state, heap1, words1⟩
  rcases hi with ⟨before, rep1, sep1, hold1, frame1, values1, meaning1, remaining⟩
  let Qstep : Assertion Unit := fun cont => match cont with
    | .Fallthrough st ss => wp m [] Q st { ss with values := s1.values } host
    | .Break 0 st ss => ∃ next, Inv next st { ss with values := s1.values } ∧
        func.rank funs next.1 < func.rank funs state
    | .Break (k + 1) st ss => Q (.Break k st ss)
    | other => Q other
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  refine wp.conseq (Q := Qstep) ?_ ?_
  · intro cont hc
    cases cont with
    | Break k st ss => cases k <;> exact hc
    | _ => exact hc
  have boundEq := func.bound_eq funs flags bounds decreases state
  have fitsEq := func.fits_eq funs fits decreases state
  have hFits : func.fits funs fits env = true → func.body.fits funs fits state = true := by
    intro hf
    have hc := (remaining hf).1
    rw [fitsEq] at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1
  have allocLe : func.body.allocs funs flags bounds func.modes pf
      (entryModes func.params func.modes) pf state ≤ func.bound funs flags bounds state := by
    rw [boundEq]
    exact Nat.le_add_right _ _
  have hPaid : func.paidResult flags = true →
      func.body.paidResult flags (entryModes func.params func.modes) pf = true := by
    intro hp
    simp only [TailFunc.paidResult, Bool.and_eq_true] at hp
    exact hp.2
  refine tail_step_spec hm func.modes func.body bodySpec
    (by simpa only [entryModes, paramSlots_modes] using func.placeArgs)
    pf (func.paidResult flags) hPaid h stateBase resultBase base 1 0 state heap1 store1 s1 words1
    (frame1.positions.trans hh) (frame1.params.trans hpv) rep1 sep1 hold1 before.at_
    (by rw [before.cap m]; exact hCap)
    (by rw [frame1.params]; exact hLow) hState hResult hRoom _
    ((hTrap.imp (Q' := Qstep) (fun _ ht => ht)).part
      (d' := !func.body.fits funs fits state) (a' := func.aborts)
      (P' := heap1.Within store1 m (Env.argPot store1 sel words1 state +
        func.body.allocs funs flags bounds func.modes pf (entryModes func.params func.modes) pf state))
      (fun hd => by
        cases hf : func.fits funs fits env
        · rfl
        · simp [hFits hf] at hd)
      (fun ha => ha)
      fun hd hw => by
        have hf : func.fits funs fits env = true := by simpa using hd
        have hr := (remaining hf).2
        exact hw.of_le (by dsimp only [budget, sel, pf] at hr ⊢; omega) (before.cap m))
    fun heap2 store2 s2 after2 top2 => ?_
  generalize hWords : after2.words = outWords at top2
  let after := after2
  cases stepEq : func.body.denote funs state with
  | inl next =>
    let a := after.congr stepEq
    have chain := TailAfter.chain before rep1 hold1 a
    rcases a.rep with ⟨rep2, sep2, hold2⟩
    have meaningNext : meaning next = meaning env := by
      have hm := fixed state
      rw [stepEq] at hm
      exact hm.symm.trans meaning1
    simp only [Sum.elim_inl]
    refine ⟨(next, heap2, a.words), ?_, decreases state next stepEq⟩
    refine ⟨chain, rep2, sep2, hold2, frame1.trans (a.frame.trans Frame.ofValues),
      values1, meaningNext, fun hf => ?_⟩
    have hfCurrent := (remaining hf).1
    rw [fitsEq, stepEq] at hfCurrent
    simp only [Bool.and_eq_true, Sum.elim_inl] at hfCurrent
    refine ⟨hfCurrent.2, ?_⟩
    have ht := top2 hfCurrent.1
    have hr := (remaining hf).2
    rw [stepEq] at ht boundEq
    simp only [tailPot, Sum.elim_inl] at ht boundEq
    rw [← hWords] at ht
    change heap2.top.toNat + Env.argPot store2 sel a.words next +
      func.bound funs flags bounds next ≤ budget
    dsimp only [budget, sel, pf, a, after, TailAfter.congr] at ht hr boundEq ⊢
    omega
  | inr value =>
    have valueEq : value = meaning env := by
      have hm := fixed state
      rw [stepEq] at hm
      exact hm.symm.trans meaning1
    let a := after.congr (stepEq.trans (congrArg Sum.inr valueEq))
    have chain := TailAfter.chain before rep1 hold1 a
    rcases a.rep with ⟨rep2, hold2⟩
    simp only [Sum.elim_inr]
    rw [values1]
    refine hNext heap2 store2 s2 a.words chain (frame1.trans a.frame) rep2 hold2 ?_
    intro hf
    have ht := top2 (hFits hf)
    have hr := (remaining hf).2
    rw [stepEq] at ht boundEq
    simp only [tailPot, Sum.elim_inr, Nat.add_zero] at ht boundEq
    rw [valueEq] at ht
    rw [← hWords] at ht
    change heap2.top.toNat + (if func.paidResult flags then
      func.result.pot store2 a.words (meaning env) else 0) ≤ budget
    dsimp only [budget, sel, pf, a, after, TailAfter.congr] at ht hr boundEq ⊢
    omega

#print axioms tail_loop_spec

end Verified
