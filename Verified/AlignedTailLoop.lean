import Verified.AlignedTail
import Verified.TailHeap

/-!
The tail loop under the flag.  `tail_step_specX` runs one pass: it releases the owned parameters
that the body does not use and runs the body, whose variables, the state's values in the slots
that `paramSlots` assigns, satisfy `HoldsA` by `HoldsA.ofEnvAligned`.  `tail_loop_specX` adds to
the invariant of each pass an aligned heap and an aligned state, which the body's continuation
gives for the next state, and gives the owned result's alignment on exit.  Each is its original
with these changes.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem tail_step_specX {strict : Bool} {S : List Sig} {params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (modes : List Mode)
    (body : TailBody S params result params)
    (bodySpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv modes body)
    (place : body.placeArgs modes (entryModes params modes) = true)
    (pf : List Bool) (rf : Bool)
    (hPaid : rf = true → body.paidResult flags (entryModes params modes) pf = true)
    (h stateBase resultBase base exitLabel nextLabel : Nat) (env : Env params)
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (hRep : Env.Rep (paramMode params modes) heap store ws env)
    (hSep : Separate store (Env.moves store (paramMode params modes) ws env)
      (Env.reads store (paramMode params modes) ws env))
    (hold : LocalsHold s stateBase (params.flatMap Ty.types) ws)
    (hAt : heap.At store)
    (hAl : strict = true → heap.Aligned ∧ Env.AlignedVals store (paramMode params modes) ws env)
    (hSafe : pool.Safe env (paramSlots params modes stateBase) (fun _ => true) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ stateBase) (hState : stateBase + widthSum params ≤ resultBase)
    (hResult : resultBase + result.width ≤ base) (hRoom : base + body.width modes ≤ h)
    (Q : Assertion Unit)
    (hTrap : TrapOK (!body.fits funs fits env ||
      ((body.aborts || !result.scalar || (paramModes params modes).any (· == .owned)) &&
        !decide (heap.Within store m (Env.argPot store
          (fun i => paidAt pf i && paramMode params modes i == .owned) ws env +
            body.allocs funs flags bounds modes pf (entryModes params modes) pf env)))) Q)
    (hNext : ∀ heap' store' s'
      (after : TailAfter env (paramSlots params modes stateBase) (fun _ => true) modes
        stateBase resultBase heap store s (body.denote funs env) heap' store' s'),
      (strict = true → heap'.Aligned ∧
        TailAligned modes store' after.words (body.denote funs env)) →
      (body.fits funs fits env = true →
        heap'.top.toNat + tailPot modes pf rf store' after.words (body.denote funs env) ≤
          heap.top.toNat + Env.argPot store
            (fun i => paidAt pf i && paramMode params modes i == .owned) ws env +
              body.allocs funs flags bounds modes pf (entryModes params modes) pf env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel)) store'
        { s' with values := s.values })) :
    wpX strict m (releaseWhere params (paramSlots params modes stateBase) (fun i => !body.usesFast i) ++
      body.code (pool := pool) modes h stateBase resultBase (paramSlots params modes stateBase) base
        exitLabel nextLabel) Q store s host := by
  have vars0 := Holds.ofEnvRep hRep hSep hold
  have al0 : strict = true →
      HoldsA env (paramSlots params modes stateBase) (fun _ => true) heap store s :=
    fun hs => HoldsA.ofEnvAligned hRep hold (hAl hs).1 (hAl hs).2
  have modesEq : (paramSlots params modes stateBase).map Slot.mode = entryModes params modes := by
    rw [entryModes, paramSlots_modes, paramSlots_modes]
  have potEq : env.pot store s (paramSlots params modes stateBase)
      (fun i => paidAt pf i && paramMode params modes i == .owned) =
      Env.argPot store (fun i => paidAt pf i && paramMode params modes i == .owned) ws env :=
    Env.pot_paramSlots modes stateBase _ ws env hRep.length (fun x => hold.var x)
  simp only [TailBody.usesFast_eq]
  refine wpX_releaseWhere hm hRA vars0 hAt al0 (fun _ _ => rfl)
    fun heap1 store1 release top1 hAl1 => ?_
  have release' := release.mono (live' := body.uses) (fun _ hi => by simp [hi])
  have hAl1' : strict = true →
      HoldsA env (paramSlots params modes stateBase) body.uses heap1 store1 s :=
    fun hs => (hAl1 hs).live_mono fun _ hi => by simp [hi]
  have potLe : dyingPot store1 s env (paramSlots params modes stateBase) pf body.uses
      (fun _ => false) ≤ Env.argPot store
        (fun i => paidAt pf i && paramMode params modes i == .owned) ws env := by
    rw [dyingPot_evolves vars0 release' (fun _ _ => rfl) _ _ (fun _ hi => hi), ← potEq]
    refine Env.pot_mono env _ _ _ fun i hi => ?_
    simp only [Bool.and_eq_true, beq_iff_eq] at hi ⊢
    exact ⟨hi.1.2, by rw [← paramSlots_getD_mode params modes stateBase]; exact hi.2⟩
  refine bodySpec env (paramSlots params modes stateBase) pf pf rf h stateBase resultBase base
    exitLabel nextLabel heap1 store1 s hh hpv (release'.holds.mono (by omega)) release'.step.at_ hAl1'
    (hSafe.evolves vars0 release' (fun _ _ => rfl))
    (by rw [release'.step.cap m]; exact hCap) hLow hState hResult hRoom
    (by rw [modesEq]; exact place) (by rw [modesEq]; exact hPaid) _
    (hTrap.part (fun hd => hd)
      (fun ha => by
        rw [← Slot.any_map, paramSlots_modes] at ha
        simpa only [Bool.or_assoc, Bool.or_self] using ha)
      fun _ hw => hw.of_le (by rw [top1, modesEq]; omega) (release'.step.cap m))
    fun heap2 store2 s2 after2 hAl2 top2 => ?_
  let final := TailAfter.prepend vars0 release' after2 (fun _ _ => rfl) (by omega)
  refine hNext heap2 store2 s2 final hAl2 fun hf => ?_
  have ht := top2 hf
  rw [modesEq] at ht
  rw [top1] at ht
  exact ht.trans (by omega)

theorem tail_step_spec {S : List Sig} {params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (modes : List Mode)
    (body : TailBody S params result params)
    (bodySpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv modes body)
    (place : body.placeArgs modes (entryModes params modes) = true)
    (pf : List Bool) (rf : Bool)
    (hPaid : rf = true → body.paidResult flags (entryModes params modes) pf = true)
    (h stateBase resultBase base exitLabel nextLabel : Nat) (env : Env params)
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (hRep : Env.Rep (paramMode params modes) heap store ws env)
    (hSep : Separate store (Env.moves store (paramMode params modes) ws env)
      (Env.reads store (paramMode params modes) ws env))
    (hold : LocalsHold s stateBase (params.flatMap Ty.types) ws)
    (hAt : heap.At store)
    (hSafe : pool.Safe env (paramSlots params modes stateBase) (fun _ => true) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ stateBase) (hState : stateBase + widthSum params ≤ resultBase)
    (hResult : resultBase + result.width ≤ base) (hRoom : base + body.width modes ≤ h)
    (Q : Assertion Unit)
    (hTrap : TrapOK (!body.fits funs fits env ||
      ((body.aborts || !result.scalar || (paramModes params modes).any (· == .owned)) &&
        !decide (heap.Within store m (Env.argPot store
          (fun i => paidAt pf i && paramMode params modes i == .owned) ws env +
            body.allocs funs flags bounds modes pf (entryModes params modes) pf env)))) Q)
    (hNext : ∀ heap' store' s'
      (after : TailAfter env (paramSlots params modes stateBase) (fun _ => true) modes
        stateBase resultBase heap store s (body.denote funs env) heap' store' s'),
      (body.fits funs fits env = true →
        heap'.top.toNat + tailPot modes pf rf store' after.words (body.denote funs env) ≤
          heap.top.toNat + Env.argPot store
            (fun i => paidAt pf i && paramMode params modes i == .owned) ws env +
              body.allocs funs flags bounds modes pf (entryModes params modes) pf env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel)) store'
        { s' with values := s.values })) :
    wp m (releaseWhere params (paramSlots params modes stateBase) (fun i => !body.usesFast i) ++
      body.code (pool := pool) modes h stateBase resultBase (paramSlots params modes stateBase) base
        exitLabel nextLabel) Q store s host :=
  tail_step_specX (strict := false) hm nofun modes body (TailCodeSpecX.false_iff.mpr bodySpec) place
    pf rf hPaid h stateBase resultBase base exitLabel nextLabel env heap store s ws hh hpv hRep hSep
    hold hAt nofun hSafe hCap hLow hState hResult hRoom Q hTrap
    (fun heap' store' s' after _ a2 => hNext heap' store' s' after a2)
#print axioms tail_step_spec

theorem tail_loop_specX {strict : Bool} {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (func : TailFunc S) (decreases : func.Decreases funs)
    (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (bodySpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv func.modes func.body)
    (h stateBase resultBase base : Nat) (env : Env func.params)
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (hRep : Env.Rep (paramMode func.params func.modes) heap store ws env)
    (hSep : Separate store (Env.moves store (paramMode func.params func.modes) ws env)
      (Env.reads store (paramMode func.params func.modes) ws env))
    (hold : LocalsHold s stateBase (func.params.flatMap Ty.types) ws)
    (hAt : heap.At store)
    (hAl : strict = true →
      heap.Aligned ∧ Env.AlignedVals store (paramMode func.params func.modes) ws env)
    (hInput : @Bytes.LiteralPool.Input (Env func.params) (Env.represent func.params func.modes)
      pool heap store ws env)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ stateBase)
    (hState : stateBase + widthSum func.params ≤ resultBase)
    (hResult : resultBase + func.result.width ≤ base)
    (hRoom : base + func.body.width func.modes ≤ h) (Q : Assertion Unit)
    (hTrap : TrapOK (!func.fits funs fits env || (func.aborts &&
      !decide (heap.Within store m (Env.argPot store
        (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
        ws env + func.bound funs flags bounds env)))) Q)
    (hNext : ∀ heap' store' s' words,
      Step heap store (Apart store (Env.moves store (paramMode func.params func.modes) ws env))
        heap' store' (func.result.blocks store' words (meaning env)) →
      Frame stateBase s s' → func.result.Rep .owned heap' store' words (meaning env) →
      LocalsHold s' resultBase func.result.types words →
      (strict = true → heap'.Aligned ∧
        Ty.AlignedVal .owned store' func.result words (meaning env)) →
      (func.fits funs fits env = true →
        heap'.top.toNat + (if func.paidResult flags then
          func.result.pot store' words (meaning env) else 0) ≤
          heap.top.toNat + Env.argPot store
            (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
            ws env + func.bound funs flags bounds env) →
      Q (.Break 0 store' { s' with values := s.values })) :
    wpX strict m [.loop 0 0
      (releaseWhere func.params (paramSlots func.params func.modes stateBase)
        (fun i => !func.body.usesFast i) ++
        func.body.code (pool := pool) func.modes h stateBase resultBase
          (paramSlots func.params func.modes stateBase) base 1 0) [] []] Q store s host := by
  let pf := func.paidParams flags
  let sel := fun i => paidAt pf i && paramMode func.params func.modes i == .owned
  let budget := heap.top.toNat + Env.argPot store sel ws env + func.bound funs flags bounds env
  let keep := Apart store (Env.moves store (paramMode func.params func.modes) ws env)
  let Inv : (Env func.params × Heap × List Value) → AssertionF Unit := fun q st ss =>
    let state := q.1
    let hp := q.2.1
    let words := q.2.2
    Step heap store keep hp st
        ((Env.moves st (paramMode func.params func.modes) words state).map (block st)) ∧
      Env.Rep (paramMode func.params func.modes) hp st words state ∧
      Separate st (Env.moves st (paramMode func.params func.modes) words state)
        (Env.reads st (paramMode func.params func.modes) words state) ∧
      LocalsHold ss stateBase (func.params.flatMap Ty.types) words ∧
      (strict = true →
        hp.Aligned ∧ Env.AlignedVals st (paramMode func.params func.modes) words state) ∧
      Frame stateBase s ss ∧ ss.values = s.values ∧ meaning state = meaning env ∧
      (func.fits funs fits env = true → func.fits funs fits state = true ∧
        hp.top.toNat + Env.argPot st sel words state + func.bound funs flags bounds state ≤ budget)
  have initial : Inv (env, heap, ws) store s := by
    refine ⟨⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr, ?_⟩⟩,
      hRep, hSep, hold, hAl, Frame.refl _ _, rfl, rfl, fun hf => ⟨hf, le_rfl⟩⟩
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact hk q hq
  refine Tail.wpX_loop_indexed (Inv := Inv) (rank := fun q => func.rank funs q.1) initial ?_
  intro q store1 s1 hi
  rcases q with ⟨state, heap1, words1⟩
  rcases hi with ⟨before, rep1, sep1, hold1, al1, frame1, values1, meaning1, remaining⟩
  obtain ⟨static1, fresh1⟩ := hInput.1.step before hInput.2
  have input1 : @Bytes.LiteralPool.Input (Env func.params)
      (Env.represent func.params func.modes) pool heap1 store1 words1 state := by
    refine ⟨static1, fun region hRegion pointer hPointer => ?_⟩
    exact fresh1 region hRegion _ (List.mem_map.mpr ⟨pointer, hPointer, rfl⟩)
  have safe1 := input1.params rep1 (fun x => hold1.var x)
  let Qstep : Assertion Unit := fun cont => match cont with
    | .Fallthrough st ss => wpX strict m [] Q st { ss with values := s1.values } host
    | .Break 0 st ss => ∃ next, Inv next st { ss with values := s1.values } ∧
        func.rank funs next.1 < func.rank funs state
    | .Break (k + 1) st ss => Q (.Break k st ss)
    | other => Q other
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  refine wpX.conseq (Q := Qstep) ?_ ?_
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
  refine tail_step_specX hm hRA func.modes func.body bodySpec
    (by simpa only [entryModes, paramSlots_modes] using func.placeArgs)
    pf (func.paidResult flags) hPaid h stateBase resultBase base 1 0 state heap1 store1 s1 words1
    (frame1.positions.trans hh) (frame1.params.trans hpv) rep1 sep1 hold1 before.at_ al1 safe1
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
    fun heap2 store2 s2 after2 hAl2 top2 => ?_
  generalize hWords : after2.words = outWords at top2 hAl2
  let after := after2
  cases stepEq : func.body.denote funs state with
  | inl next =>
    rw [stepEq] at hAl2
    let a := after.congr stepEq
    have chain := TailAfter.chain before rep1 hold1 a
    rcases a.rep with ⟨rep2, sep2, hold2⟩
    have meaningNext : meaning next = meaning env := by
      have hm := fixed state
      rw [stepEq] at hm
      exact hm.symm.trans meaning1
    simp only [Sum.elim_inl]
    refine ⟨(next, heap2, a.words), ?_, decreases state next stepEq⟩
    refine ⟨chain, rep2, sep2, hold2,
      fun hs => by have h := hAl2 hs; rw [← hWords] at h; exact h,
      frame1.trans (a.frame.trans Frame.ofValues),
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
    rw [stepEq] at hAl2
    have valueEq : value = meaning env := by
      have hm := fixed state
      rw [stepEq] at hm
      exact hm.symm.trans meaning1
    let a := after.congr (stepEq.trans (congrArg Sum.inr valueEq))
    have chain := TailAfter.chain before rep1 hold1 a
    rcases a.rep with ⟨rep2, hold2⟩
    simp only [Sum.elim_inr]
    rw [values1]
    refine hNext heap2 store2 s2 a.words chain (frame1.trans a.frame) rep2 hold2
      (fun hs => by have h := hAl2 hs; rw [← hWords, valueEq] at h; exact h) ?_
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

theorem tail_loop_spec {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (func : TailFunc S) (decreases : func.Decreases funs)
    (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (bodySpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv func.modes func.body)
    (h stateBase resultBase base : Nat) (env : Env func.params)
    (heap : Heap) (store : Store Unit) (s : Locals) (ws : List Value)
    (hh : s.positions = h) (hpv : s.params = pv)
    (hRep : Env.Rep (paramMode func.params func.modes) heap store ws env)
    (hSep : Separate store (Env.moves store (paramMode func.params func.modes) ws env)
      (Env.reads store (paramMode func.params func.modes) ws env))
    (hold : LocalsHold s stateBase (func.params.flatMap Ty.types) ws)
    (hAt : heap.At store)
    (hInput : @Bytes.LiteralPool.Input (Env func.params) (Env.represent func.params func.modes)
      pool heap store ws env)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ stateBase)
    (hState : stateBase + widthSum func.params ≤ resultBase)
    (hResult : resultBase + func.result.width ≤ base)
    (hRoom : base + func.body.width func.modes ≤ h) (Q : Assertion Unit)
    (hTrap : TrapOK (!func.fits funs fits env || (func.aborts &&
      !decide (heap.Within store m (Env.argPot store
        (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
        ws env + func.bound funs flags bounds env)))) Q)
    (hNext : ∀ heap' store' s' words,
      Step heap store (Apart store (Env.moves store (paramMode func.params func.modes) ws env))
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
        func.body.code (pool := pool) func.modes h stateBase resultBase
          (paramSlots func.params func.modes stateBase) base 1 0) [] []] Q store s host :=
  tail_loop_specX (strict := false) hm nofun func decreases meaning fixed
    (TailCodeSpecX.false_iff.mpr bodySpec) h stateBase resultBase base env heap store s ws hh hpv
    hRep hSep hold hAt nofun hInput hCap hLow hState hResult hRoom Q hTrap
    (fun heap' store' s' words a1 a2 a3 a4 _ a6 => hNext heap' store' s' words a1 a2 a3 a4 a6)
#print axioms tail_loop_spec

end Verified

namespace Verified.Tail

open Wasm

variable {ι α : Type}

theorem wp_loop_indexed {Inv : ι → AssertionF α} {rank : ι → Nat}
    {m : Module} {body rest : Program} {Q : Assertion α} {host : HostEnv α}
    {store : Store α} {s : Locals} {ps rs : Nat} {initial : ι}
    (hInit : Inv initial store s)
    (hStep : ∀ state store s, Inv state store s →
      wp m body (fun cont => match cont with
        | .Fallthrough store' s' =>
          wp m rest Q store' { s' with values := s'.values.take rs ++ s.values.drop ps } host
        | .Break 0 store' s' =>
          ∃ next, Inv next store' { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
            rank next < rank state
        | .Break (k + 1) store' s' => Q (.Break k store' s')
        | other => Q other) store s host) :
    wp m (.loop ps rs body :: rest) Q store s host :=
  wpX_loop_indexed (strict := false) hInit hStep
#print axioms wp_loop_indexed


end Verified.Tail
