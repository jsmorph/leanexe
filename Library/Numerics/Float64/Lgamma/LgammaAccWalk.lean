import Library.Numerics.Float64.Lgamma.LgammaWalk

/-!
Reading the block of `Lgamma.accurate`, with the steps of `LgammaWalk` and two more.  `acc_step`
takes one step as `walk_step` does and also enters the matcher `Lgamma.accurate.match_1` on the
4-tuple of `rootRange`.  `spec_step P` splits a goal `S (match p with (a, b) => f a b)` on a pair or
triple into `P p` and `∀ a b, P (a, b) → S (f a b)`, so that a specification `P` of the matched
value, proved by its own walk, carries into the rest of the block.  Both instantiate their lemmas
with the goal's own subterms, as `walk_step` does.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccWalk
open Library.Numerics.Float64.Lgamma LgammaWalk

theorem m4_walk {β : Type} (S : β → Prop) (p : UInt64 × UInt64 × UInt64 × Float)
    (f : UInt64 → UInt64 → UInt64 → Float → β)
    (h : ∀ a b c d, p = (a, b, c, d) → S (f a b c d)) :
    S (accurate.match_1 (fun _ => β) p f) := by
  obtain ⟨a, b, c, d⟩ := p
  exact h a b c d rfl

theorem m1_spec {β : Type} (S : β → Prop) (P : Float × Float → Prop) (p : Float × Float)
    (f : Float → Float → β) (hp : P p) (h : ∀ a b, P (a, b) → S (f a b)) :
    S (polyDD.match_1 (fun _ => β) p f) := by
  obtain ⟨a, b⟩ := p
  exact h a b hp

theorem m3_spec {β : Type} (S : β → Prop) (P : Float × Float × Float → Prop)
    (p : Float × Float × Float) (f : Float → Float → Float → β) (hp : P p)
    (h : ∀ a b c, P (a, b, c) → S (f a b c)) :
    S (asLgammaAsymAccurate.match_3 (fun _ => β) p f) := by
  obtain ⟨a, b, c⟩ := p
  exact h a b c hp

open Lean Elab Tactic Meta in
/-- One step into the goal `S e`, as `walk_step`, or into `Lgamma.accurate.match_1`. -/
elab "acc_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isApp do throwError "acc_step: the goal is not `S e`"
    let S := t.appFn!
    let e := t.appArg!.consumeMData
    if e.isAppOfArity ``accurate.match_1 3 then
      let args := e.getAppArgs
      replaceMainGoal (← g.apply (← mkAppM ``m4_walk #[S, args[1]!, args[2]!]))
    else
      evalTactic (← `(tactic| walk_step))

open Lean Elab Tactic Meta in
/-- Split `S (match p with ...)` on a pair or triple into `P p` and the rest of the block. -/
elab "spec_step " P:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isApp do throwError "spec_step: the goal is not `S e`"
    let S := t.appFn!
    let e := t.appArg!.consumeMData
    if e.isAppOfArity ``polyDD.match_1 3 then
      let args := e.getAppArgs
      let Pe ← Term.elabTermEnsuringType P (← mkArrow (← mkAppM ``Prod #[mkConst ``Float,
        mkConst ``Float]) (mkSort .zero))
      replaceMainGoal (← g.apply (← mkAppM ``m1_spec #[S, Pe, args[1]!, args[2]!]))
    else if e.isAppOfArity ``asLgammaAsymAccurate.match_3 3 then
      let args := e.getAppArgs
      let Pe ← Term.elabTermEnsuringType P (← mkArrow (← mkAppM ``Prod #[mkConst ``Float,
        ← mkAppM ``Prod #[mkConst ``Float, mkConst ``Float]]) (mkSort .zero))
      replaceMainGoal (← g.apply (← mkAppM ``m3_spec #[S, Pe, args[1]!, args[2]!]))
    else throwError "spec_step: no pair or triple matcher"

end Library.Numerics.Float64.Lgamma.LgammaAccWalk
