import Verified.Potential
import Verified.ArgumentMoves

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem callMoves_owned {S : List Sig} {Γ : List Ty} {g : Sig} {slots : List Slot}
    {live : Nat → Bool} {args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)}
    {i : Fin g.params.length} (h : callMoves slots live args i = true) : g.mode i = .owned := by
  simp only [callMoves, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem callMovesAt_eq {S : List Sig} {Γ : List Ty} {g : Sig} (slots : List Slot)
    (live : Nat → Bool) (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) :
    callMovesAt (slots.map Slot.mode) live args = callMoves slots live args := by
  funext i
  cases hv : (args i).varIndex? <;>
    simp only [callMovesAt, callMoves, Expr.usesFast_eq, hv, modeAt, Slot.modes_getD]

def Expr.paramPot (funs : Funs S) (store : Store Unit) (s : Locals) {Γ : List Ty} (env : Env Γ)
    (slots : List Slot) (paid : List Bool) (kept : Nat → Bool) : {t : Ty} → Expr S Γ t → Nat
  | t, .var x =>
    if (!kept x.index && paidAt paid x.index) = true then env.potOf store s slots x
    else t.credit (env.get x)
  | t, e => t.credit (e.denote funs env)

theorem Expr.paramPot_frame {Γ : List Ty} {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {kept all : Nat → Bool} {base : Nat} {heap : Heap} {store st : Store Unit} {s s' : Locals}
    (hVars : Holds env slots all base heap store s) (hF : Frame base s s') {t : Ty}
    (e : Expr S Γ t) (hu : ∀ k, e.uses k = true → all k = true) :
    e.paramPot funs st s' env slots paid kept = e.paramPot funs st s env slots paid kept := by
  cases e
  case var x =>
    have hx := hu x.index (by simp [Expr.uses])
    obtain ⟨-, ws, hold, hRep⟩ := hVars.get x hx
    have hold' := (hVars.hold_agree hF hx hRep.length).mpr hold
    have hl : ws.length = t.types.length := by rw [hRep.length, Ty.types_length]
    simp only [Expr.paramPot, Env.potOf, hold.read_eq hl, hold'.read_eq hl]
  all_goals rfl

theorem Expr.paramPot_values {Γ : List Ty} (e : Expr S Γ t) (funs : Funs S)
    (store : Store Unit) (s : Locals) (values : List Value) (env : Env Γ) (slots : List Slot)
    (paid : List Bool) (kept : Nat → Bool) :
    e.paramPot funs store { s with values } env slots paid kept =
      e.paramPot funs store s env slots paid kept := by
  cases e <;> rfl

theorem Expr.place_modes {modes : List Mode} (e : Expr S Γ t) :
    e.isPlace = true → e.mode modes = .borrowed →
      ∀ k, e.uses k = true → modeAt modes k = .borrowed := by
  induction e with
  | var x =>
    intro _ hm k hk
    simp only [Expr.uses, beq_iff_eq] at hk
    subst hk
    exact hm
  | pair first second ihFirst ihSecond =>
    intro hp hm k hk
    simp only [Expr.isPlace, Bool.and_eq_true] at hp
    have both : first.mode modes = .borrowed ∧ second.mode modes = .borrowed := by
      cases hf : first.mode modes <;> cases hs : second.mode modes <;>
        simp_all [Expr.mode, Mode.join]
    simp only [Expr.uses, Bool.or_eq_true] at hk
    exact hk.elim (ihFirst hp.1 both.1 k) (ihSecond hp.2 both.2 k)
  | _ => intro hp; simp [Expr.isPlace] at hp

theorem callMoves_moved {S : List Sig} {Γ : List Ty} {sig : Sig} (slots : List Slot)
    (live : Nat → Bool) (args : (i : Fin sig.params.length) → Expr S Γ (sig.params.get i))
    (hVar : ∀ i : Fin sig.params.length, sig.mode i = .owned → ∃ x, args i = .var x) :
    ∀ k, (argsAny fun j => callMoves slots live args j && (args j).uses k) = true →
      ∃ j x, args j = .var x ∧ x.index = k ∧ sig.mode j = .owned ∧
        (slots.getD k default).mode = .owned ∧ live k = false ∧
        ∀ j', j' ≠ j → (sig.params.get j').scalar = false → (args j').uses k = false :=
  arguments_moved sig.mode slots live args (callMoves slots live args) (fun _ => rfl) hVar

theorem callMoves_kept {S : List Sig} {Γ : List Ty} {sig : Sig} (slots : List Slot)
    (live : Nat → Bool) (args : (i : Fin sig.params.length) → Expr S Γ (sig.params.get i))
    (hVar : ∀ i : Fin sig.params.length, sig.mode i = .owned → ∃ x, args i = .var x)
    (i : Fin sig.params.length) (x : Var Γ (sig.params.get i))
    (hmo : sig.mode i = .owned) (hx : args i = .var x) :
    (!((live x.index || argsAny fun j => (args j).uses x.index) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses x.index))) =
      callMoves slots live args i := by
  have hMoved := callMoves_moved slots live args hVar
  have hux : (args i).uses x.index = true := by rw [hx]; simp [Expr.uses]
  have hAll := le_argsAny (fun j => (args j).uses x.index) i hux
  simp only [hAll, Bool.or_true, Bool.true_and, Bool.not_not]
  cases hc : callMoves slots live args i
  · cases hm' : argsAny fun j => callMoves slots live args j && (args j).uses x.index
    · rfl
    · obtain ⟨j, hj⟩ := argsAny_true.mp hm'
      obtain ⟨j', y, -, -, -, -, -, hOthers⟩ := hMoved _ hm'
      simp only [Bool.and_eq_true] at hj
      have hji : j = i := by
        by_contra hne
        by_cases hj'i : j' = i
        · subst hj'i
          have := hOthers j hne (paramMode_owned (callMoves_owned hj.1))
          rw [hj.2] at this
          exact nomatch this
        · have := hOthers i (Ne.symm hj'i) (paramMode_owned hmo)
          rw [hux] at this
          exact nomatch this
      subst hji
      rw [hj.1] at hc
      exact nomatch hc
  · exact le_argsAny (fun j => callMoves slots live args j && (args j).uses x.index) i
      (by rw [hc, hux]; rfl)

theorem args_pot_le_credits {S : List Sig} {Γ : List Ty} {sig : Sig} {funs : Funs S}
    {slots : List Slot} {live : Nat → Bool} {paid pf : List Bool}
    {env : Env Γ} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s : Locals}
    {ws : List Value} {fresh : List (Nat × Nat)}
    (args : (i : Fin sig.params.length) → Expr S Γ (sig.params.get i))
    (hVar : ∀ i : Fin sig.params.length, sig.mode i = .owned → ∃ x, args i = .var x)
    (hVars : Holds env slots (fun i => live i || argsAny fun j => (args j).uses i)
      base heap store s)
    (hStep : Step heap store (fun _ => True) heap1 store1 fresh)
    (hPot : ∀ sel : Nat → Bool, (∀ i, sel i = true → sig.mode i = .owned) →
      Env.argPot store1 sel ws (Env.ofFn fun i => (args i).denote funs env) ≤
        argsSum fun i => if sel i = true then
          (args i).paramPot funs store1 s env slots paid
            (fun k => (live k || argsAny fun j => (args j).uses k) &&
              !(argsAny fun j => callMoves slots live args j && (args j).uses k)) else 0) :
    Env.argPot store1 (sig.paidSel pf) ws (Env.ofFn fun i => (args i).denote funs env) ≤
      dyingPot store s env slots paid (fun i => live i || argsAny fun j => (args j).uses i) live +
        argsSum fun i => if sig.paidSel pf i &&
            !(callMovesAt (slots.map Slot.mode) live args i && (args i).paidVar paid) then
          (sig.params.get i).credit ((args i).denote funs env) else 0 := by
  have hMoved := callMoves_moved slots live args hVar
  let msel : Fin sig.params.length → Nat → Bool := fun i k =>
    sig.paidSel pf i && callMoves slots live args i && (args i).paidVar paid && (args i).uses k
  have h1 := hPot (sig.paidSel pf) fun i h => by
    simp only [Sig.paidSel, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  refine h1.trans ?_
  have hTerm : ∀ i : Fin sig.params.length,
      (if sig.paidSel pf i = true then (args i).paramPot funs store1 s env slots paid
          (fun k => (live k || argsAny fun j => (args j).uses k) &&
            !(argsAny fun j => callMoves slots live args j && (args j).uses k)) else 0) ≤
        env.pot store1 s slots (msel i) +
          (if sig.paidSel pf i &&
              !(callMovesAt (slots.map Slot.mode) live args i && (args i).paidVar paid) then
            (sig.params.get i).credit ((args i).denote funs env) else 0) := by
    intro i
    cases hps : sig.paidSel pf i
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      exact Nat.zero_le _
    have hmo : sig.mode i = .owned := by
      simp only [Sig.paidSel, Bool.and_eq_true, beq_iff_eq] at hps
      exact hps.2
    obtain ⟨x, hx⟩ := hVar i hmo
    have hk := callMoves_kept slots live args hVar i x hmo hx
    rw [callMovesAt_eq]
    simp only [↓reduceIte, Bool.true_and]
    rw [hx]
    simp only [Expr.paramPot, Expr.paidVar, hk]
    by_cases hmp : (callMoves slots live args i && paidAt paid x.index) = true
    · have hsel : msel i = fun k => k == x.index := by
        funext k
        simp only [Bool.and_eq_true] at hmp
        simp only [msel, hps, hmp.1, hx, Expr.paidVar, hmp.2, Expr.uses, Bool.true_and]
      rw [if_pos hmp, hsel, Env.pot_single]
      simp only [hmp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact Nat.le_refl _
    · rw [if_neg hmp]
      simp only [Bool.not_eq_true] at hmp
      simp only [hmp, Bool.not_false, ↓reduceIte]
      exact Nat.le_add_left _ _
  refine (argsSum_le hTerm).trans ?_
  rw [argsSum_add]
  refine Nat.add_le_add ?_ (Nat.le_of_eq rfl)
  rw [Env.pot_argsSum env slots msel fun i j k hij hi => ?_]
  · rw [Env.pot_step hVars (hStep.mono (fun _ _ => trivial) fun _ h => h)
      (Frame.refl base s) (fun i h => h) _ fun k hk => ?_]
    · refine Env.pot_mono env slots _ _ fun k hk => ?_
      obtain ⟨i, hi⟩ := argsAny_true.mp hk
      simp only [msel, Bool.and_eq_true] at hi
      obtain ⟨⟨⟨hps, hcm⟩, hpv⟩, huk⟩ := hi
      obtain ⟨j, y, hy, hyk, -, hmy, hly, -⟩ := hMoved k
        (le_argsAny (fun j => callMoves slots live args j && (args j).uses k) i
          (by rw [hcm, huk]; rfl))
      have hxk : ∃ x : Var Γ (sig.params.get i), args i = .var x ∧ x.index = k := by
        obtain ⟨x, hx⟩ := hVar i (callMoves_owned hcm)
        refine ⟨x, hx, ?_⟩
        rw [hx] at huk
        exact (by simpa [Expr.uses] using huk : k = x.index).symm
      obtain ⟨x, hx, rfl⟩ := hxk
      rw [hx] at hpv
      simp only [Expr.paidVar] at hpv
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
      refine ⟨⟨⟨?_, hly⟩, hpv⟩, hmy⟩
      simp only [Bool.or_eq_true]
      exact Or.inr (le_argsAny _ i (by rw [hx]; simp [Expr.uses]))
    · obtain ⟨i, hi⟩ := argsAny_true.mp hk
      simp only [msel, Bool.and_eq_true] at hi
      obtain ⟨⟨⟨-, hcm⟩, -⟩, huk⟩ := hi
      obtain ⟨-, -, -, -, -, hmy, -, -⟩ := hMoved k
        (le_argsAny (fun j => callMoves slots live args j && (args j).uses k) i
          (by rw [hcm, huk]; rfl))
      exact ⟨by simp only [Bool.or_eq_true]; exact Or.inr (le_argsAny _ i huk), hmy⟩
  · simp only [msel, Bool.and_eq_true] at hi
    obtain ⟨⟨⟨-, hcm⟩, -⟩, huk⟩ := hi
    obtain ⟨j', y, -, -, -, -, -, hOthers⟩ := hMoved k
      (le_argsAny (fun j => callMoves slots live args j && (args j).uses k) i
        (by rw [hcm, huk]; rfl))
    cases hj : msel j k
    · rfl
    · simp only [msel, Bool.and_eq_true] at hj
      obtain ⟨⟨⟨-, hcmj⟩, -⟩, hukj⟩ := hj
      have hi' : i = j' := by
        by_contra hne
        have := hOthers i hne (paramMode_owned (callMoves_owned hcm))
        rw [huk] at this
        exact nomatch this
      have hj' : j = j' := by
        by_contra hne
        have := hOthers j hne (paramMode_owned (callMoves_owned hcmj))
        rw [hukj] at this
        exact nomatch this
      exact absurd (hi'.trans hj'.symm) hij

theorem args_moves_apart_kept {S : List Sig} {Γ ps : List Ty} {funs : Funs S}
    (modes : Nat → Mode) (args : (i : Fin ps.length) → Expr S Γ (ps.get i))
    {env : Env Γ} {slots : List Slot} {all kept : Nat → Bool} {base : Nat}
    {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals}
    {words : List Value} {fresh : List (Nat × Nat)}
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (keptAll : ∀ k, kept k = true → all k = true)
    (vars : Holds env slots all base heap store s)
    (step : Step heap store (fun _ => True) heap1 store1 fresh) (frame : Frame base s s1)
    (apart : ∀ r, (∀ b ∈ fresh, regionsDisjoint r b) →
      Holds.KeepDying env slots
        (fun k => argsAny fun i => modes i == .owned && (args i).uses k && !kept k)
        (fun _ => false) store s r →
      Apart store1 (Env.moves store1 modes words (Env.ofFn fun i => (args i).denote funs env)) r) :
    ∀ (t : Ty) (x : Var Γ t), kept x.index = true →
      ∀ wx, LocalsHold s1 (slots.getD x.index default).loc t.types wx → wx.length = t.width →
      ∀ r ∈ t.regions (slots.getD x.index default).mode store1 wx (env.get x),
        Apart store1 (Env.moves store1 modes words (Env.ofFn fun i => (args i).denote funs env)) r := by
  intro t x hx wx hold length r hr
  have hxAll := keptAll _ hx
  have hold' := (vars.hold_agree frame hxAll length).mp hold
  obtain ⟨same, freshApart⟩ := vars.regions_after step hxAll hold' length fun _ _ => trivial
  rw [same] at hr
  refine apart r (freshApart r hr) ?_
  intro u y hy _ hyOwned wy holdY lengthY b hb
  obtain ⟨i, hi⟩ := argsAny_true.mp hy
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
  have hyAll := uses i y.index hi.1.2
  have different : y.index ≠ x.index := fun he => by
    rw [he, hx] at hi
    exact nomatch hi.2
  exact regionsDisjoint_symm
    (vars.2 u t y x hyAll hxAll different hyOwned wy wx holdY lengthY hold' length b hb r hr)

#print axioms args_pot_le_credits
#print axioms args_moves_apart_kept

end Verified
