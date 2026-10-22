import Library.Numerics.Float64.Lgamma.LgammaRoundTest
import Library.Numerics.Float64.Lgamma.Compiled

/-!
The step from the fast path's block to the result of `Lgamma.lgammaWith`, and a way to read the
block.  `FastSpec L (fh, fl, eps, sign)` states the bounds that make `fh + (fl + eps)` one step from
the reference of `L`: either the error of `fh + fl` is at most `2 eps`, for the rounding test
(`LgammaRoundTest.round_test`), with `|fl| ≤ 2^48 eps`, or the error plus `2 eps` and the
rounding of `fl + eps` is at most `|L|/2^54`, which needs no test (`rel_within`) and allows a low
part as large as `asLogd`'s.  `select_within` gives one step for the code's choice between the fast
result and the accurate path.

The block is a tree of `if`, `have`, and `match` on pairs (`Lgamma.polyDD.match_1`) and triples
(`Lgamma.asLgammaAsymAccurate.match_3`).  `walk_step` takes one step into a goal `S e`, for a
predicate `S` such as `FastSpec L`: for a `match` it leaves `∀ a b, p = (a, b) → S (f a b)`, for an
`if` the two branches, and for `have y := v; b y` the statement `∀ y, y = v → S (b y)`.  It
instantiates its lemmas with the goal's own subterms, because `apply` with metavariables unfolds
the matcher by structure eta and fails, and it never changes a term by definitional unfolding: the
kernel checks such a change by evaluating the block, which ran out of memory in `LgammaSign`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaWalk
open CodeLib.IEEE64 LeanExe.ProofKit F64RoundNearest F64Approx LgammaRoundTest
open Library.Numerics.Float64.Lgamma

set_option exponentiation.threshold 4096
set_option linter.auxLemma false

/-! ### The fast result -/

/-- The bounds on the fast path's `(fh, fl, eps, sign)` that put `fh + (fl + eps)` within one step
of the reference of `L` when the code takes it: the error of `fh + fl` within `2 eps`, for the
rounding test, or the error with `2 eps` and the rounding of `fl + eps` within `|L|/2^54`. -/
def FastSpec (L : ℝ) (r : Float × Float × Float × Float) : Prop :=
  Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.1.toBits ∧
    1 / 2 ^ 1000 ≤ value r.2.2.1.toBits ∧
    ((|value r.2.1.toBits| ≤ 2 ^ 48 * value r.2.2.1.toBits ∧
        |value r.1.toBits| + 2 ^ 49 * value r.2.2.1.toBits ≤ 2 ^ 1020 ∧
        |L - (value r.1.toBits + value r.2.1.toBits)| ≤ 2 * value r.2.2.1.toBits) ∨
      (|value r.2.1.toBits| ≤ 2 ^ 1000 ∧ 1 / 2 ^ 1000 ≤ |L| ∧ |L| ≤ 2 ^ 1020 ∧
        |L - (value r.1.toBits + value r.2.1.toBits)| + 2 * value r.2.2.1.toBits +
          (|value r.2.1.toBits| + value r.2.2.1.toBits) / 2 ^ 52 ≤ |L| / 2 ^ 54))

/-- Without the test: `fh + (fl + eps)` is within one step when the error of `fh + fl`, `2 eps`,
and the rounding of `fl + eps` together are at most `|L|/2^54`. -/
theorem rel_within (fh fl eps : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits)
    (he : Finite eps.toBits) (he0 : 0 ≤ value eps.toBits) (hfl0 : |value fl.toBits| ≤ 2 ^ 1000)
    (L : ℝ) (hL1 : 1 / 2 ^ 1000 ≤ |L|) (hL2 : |L| ≤ 2 ^ 1020)
    (hrel : |L - (value fh.toBits + value fl.toBits)| + 2 * value eps.toBits +
      (|value fl.toBits| + value eps.toBits) / 2 ^ 52 ≤ |L| / 2 ^ 54) :
    F64SignedRounding.WithinSteps 1 L (fh + (fl + eps)).toBits := by
  have hL0 : 0 < |L| := lt_of_lt_of_le (by positivity) hL1
  have hLd : |L| / 2 ^ 54 ≤ |L| := div_le_self hL0.le (by norm_num)
  have hle : |value fl.toBits + value eps.toBits| ≤ |value fl.toBits| + value eps.toBits := by
    have := abs_add_le (value fl.toBits) (value eps.toBits)
    rw [abs_of_nonneg he0] at this; exact this
  have heb : value eps.toBits ≤ 2 ^ 1020 := by
    have := abs_nonneg (L - (value fh.toBits + value fl.toBits))
    have : 0 ≤ (|value fl.toBits| + value eps.toBits) / 2 ^ 52 := by positivity
    linarith
  have ha := fapprox_add (approx_self _ hfl) (approx_self _ he)
    |value fl.toBits + value eps.toBits| (by rw [add_zero, add_zero])
    (by linarith [(by norm_num : (2 : ℝ) ^ 1000 + 2 ^ 1020 < 2 ^ 1023)])
  have hda : |value (fl + eps).toBits - (value fl.toBits + value eps.toBits)| ≤
      (|value fl.toBits| + value eps.toBits) / 2 ^ 52 := by
    have h1 := ha.2
    simp only [zero_add] at h1
    have : |value fl.toBits + value eps.toBits| / 2 ^ 53 ≤
        (|value fl.toBits| + value eps.toBits) / 2 ^ 52 := by
      have h2 : |value fl.toBits + value eps.toBits| / 2 ^ 53 ≤
          (|value fl.toBits| + value eps.toBits) / 2 ^ 53 :=
        div_le_div_of_nonneg_right hle (by positivity)
      have h3 : (|value fl.toBits| + value eps.toBits) / 2 ^ 53 ≤
          (|value fl.toBits| + value eps.toBits) / 2 ^ 52 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num)
      linarith
    linarith
  set A := value fh.toBits + value (fl + eps).toBits with hA
  have hAL : |A - L| ≤ |L| / 2 ^ 54 := by
    have : A - L = (value (fl + eps).toBits - (value fl.toBits + value eps.toBits)) +
        value eps.toBits - (L - (value fh.toBits + value fl.toBits)) := by rw [hA]; ring
    rw [this]
    have h3 := abs_add_le (value (fl + eps).toBits - (value fl.toBits + value eps.toBits) +
      value eps.toBits) (-(L - (value fh.toBits + value fl.toBits)))
    have h4 := abs_add_le (value (fl + eps).toBits - (value fl.toBits + value eps.toBits))
      (value eps.toBits)
    rw [abs_neg] at h3
    rw [abs_of_nonneg he0] at h4
    rw [sub_eq_add_neg]
    linarith
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hAL
    have : |L| / 2 ^ 54 < |L| := div_lt_self hL0 (by norm_num)
    linarith
  have hAt : |A| < 2 ^ 1023 := by
    have := abs_sub_abs_le_abs_sub A L
    linarith [(by norm_num : (2 : ℝ) ^ 1020 * 2 < 2 ^ 1023)]
  have hR := F64RoundNearest.add_rounded fh.toBits (fl + eps).toBits hfh ha.1 hA0 hAt
  rw [← F64Bits.toBits_add] at hR
  exact F64RoundNearest.within_one_of_rounded_rel _ A L hR (1 / 2 ^ 54) (by positivity)
    (by norm_num) (by rw [one_div_mul_eq_div]; exact hAL)
    (le_trans (by norm_num) hL1) (lt_of_le_of_lt hL2 (by norm_num))

/-- **One step for the fast result** when the code takes it. -/
theorem fast_within (fh fl eps sign : Float) (L : ℝ) (hs : FastSpec L (fh, fl, eps, sign))
    (htest : ¬ (fh + (fl + eps) != fh + (fl - eps)) = true) :
    F64SignedRounding.WithinSteps 1 L (fh + (fl + eps)).toBits := by
  obtain ⟨hfh, hfl, he, he0, hcase⟩ := hs
  rcases hcase with ⟨hfle, hbig, h⟩ | ⟨hfl0, hL1, hL2, h⟩
  · exact round_test fh fl eps hfh hfl he he0 hfle hbig htest L h
  · exact rel_within fh fl eps hfh hfl he (le_trans (by positivity) he0) hfl0 L hL1 hL2 h

/-- **One step for the code's choice** between the fast result and the accurate path. -/
theorem select_within (fh fl eps sign acc : Float) (L : ℝ) (hs : FastSpec L (fh, fl, eps, sign))
    (hacc : F64SignedRounding.WithinSteps 1 L acc.toBits) :
    F64SignedRounding.WithinSteps 1 L
      (if (fh + (fl + eps) != fh + (fl - eps)) = true then (acc, sign)
        else (fh + (fl + eps), sign)).1.toBits := by
  by_cases h : (fh + (fl + eps) != fh + (fl - eps)) = true
  · rw [ite_eq_left h]; exact hacc
  · rw [ite_eq_right h]; exact fast_within fh fl eps sign L hs h

/-! ### Reading the block -/

theorem m1_walk {β : Type} (S : β → Prop) (p : Float × Float) (f : Float → Float → β)
    (h : ∀ a b, p = (a, b) → S (f a b)) : S (polyDD.match_1 (fun _ => β) p f) := by
  obtain ⟨a, b⟩ := p
  exact h a b rfl

theorem m3_walk {β : Type} (S : β → Prop) (p : Float × Float × Float)
    (f : Float → Float → Float → β) (h : ∀ a b c, p = (a, b, c) → S (f a b c)) :
    S (asLgammaAsymAccurate.match_3 (fun _ => β) p f) := by
  obtain ⟨a, b, c⟩ := p
  exact h a b c rfl

theorem ite_walk {β : Type} (S : β → Prop) {c : Prop} [inst : Decidable c] (A B : β)
    (hA : c → S A) (hB : ¬ c → S B) : S (if c then A else B) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact hA h
  · rw [ite_eq_right h]; exact hB h

open Lean Elab Tactic Meta in
/-- One step into the goal `S e`: a pair or triple `match` of `Lgamma`, an `if`, or a `have`. -/
elab "walk_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isApp do throwError "walk_step: the goal is not `S e`"
    let S := t.appFn!
    let e := t.appArg!.consumeMData
    if let .letE n ty val body _ := e then
      let g2Type ← withLocalDeclD n ty fun y => do
        withLocalDeclD `h (← mkEq y val) fun hy => do
          mkForallFVars #[y, hy] (mkApp S (body.instantiate1 y))
      let g2 ← mkFreshExprSyntheticOpaqueMVar g2Type
      g.assign (mkApp2 g2 val (← mkEqRefl val))
      replaceMainGoal [g2.mvarId!]
    else if e.isAppOfArity ``polyDD.match_1 3 then
      let args := e.getAppArgs
      replaceMainGoal (← g.apply (← mkAppM ``m1_walk #[S, args[1]!, args[2]!]))
    else if e.isAppOfArity ``asLgammaAsymAccurate.match_3 3 then
      let args := e.getAppArgs
      replaceMainGoal (← g.apply (← mkAppM ``m3_walk #[S, args[1]!, args[2]!]))
    else if e.isAppOfArity ``ite 5 then
      let args := e.getAppArgs
      replaceMainGoal (← g.apply (mkAppN (mkConst ``ite_walk)
        #[args[0]!, S, args[1]!, args[2]!, args[3]!, args[4]!]))
    else throwError "walk_step: no `have`, `if`, or pair or triple matcher"

#print axioms rel_within
#print axioms fast_within
#print axioms select_within

end Library.Numerics.Float64.Lgamma.LgammaWalk
