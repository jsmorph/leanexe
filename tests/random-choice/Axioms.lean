import Demos.RandomChoice.Compiled
import Demos.RandomChoice.CommandProof

/-! The theorem statements and the axiom audit of the unbiased random choice.  The call theorems
are restated here against the specifications, as `tools/verified-request-check` states the call
theorem of a request: `Verified.CallSpec` of the pure module, its tables, the export's function
index, the specification, and the generated bound.  The counting theorems are restated with their
statements.  The check fails when a theorem uses an axiom other than `propext`, `Classical.choice`, and
`Quot.sound`. -/

namespace RandomChoiceCheck

open Demos.RandomChoice

theorem parseArgCall :
    Verified.CallSpec compiled.module compiled.tables 3 parseSpec compiled.parseArg.bound :=
  parseArg_callSpec

theorem pickCall :
    Verified.CallSpec compiled.module compiled.tables 4 pickSpec compiled.pick.bound :=
  pick_callSpec

theorem renderCall :
    Verified.CallSpec compiled.module compiled.tables 9 renderSpec compiled.render.bound :=
  render_callSpec

theorem perWord (n v : UInt64) (hv : 1 ≤ v.toNat) (hvn : v.toNat ≤ n.toNat) :
    (Finset.univ.filter fun w : UInt64 => accepts n w = true ∧ pickSpec (n, w) = v).card =
      2 ^ 64 / n.toNat :=
  pick_count n v hv hvn

theorem perRun (n : UInt64) (K : Nat) (o : Fin K → UInt64)
    (ho : ∀ i, 1 ≤ (o i).toNat ∧ (o i).toNat ≤ n.toNat) :
    (Finset.univ.filter fun ws : Fin K → UInt64 =>
      ∀ i, accepts n (ws i) = true ∧ pickSpec (n, ws i) = o i).card = (2 ^ 64 / n.toNat) ^ K :=
  picks_count n K o ho

theorem acceptance (n : UInt64) (hn : n ≠ 0) :
    2 ^ 63 ≤ (Finset.univ.filter fun w : UInt64 => accepts n w = true).card :=
  accepted_half n hn

theorem capReached (n k : UInt64) (hn : n ≠ 0) :
    2 ^ 512 * (Finset.univ.filter fun ws : Fin (512 * (passes k).toNat) → UInt64 =>
      (Finset.univ.filter fun i => accepts n (ws i) = true).card < k.toNat).card ≤
        2 ^ (64 * (512 * (passes k).toNat)) :=
  cap_count n k hn

end RandomChoiceCheck

open Lean Elab Command in
elab "check_random_choice_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``RandomChoiceCheck.parseArgCall,
    ``RandomChoiceCheck.pickCall,
    ``RandomChoiceCheck.renderCall,
    ``RandomChoiceCheck.perWord,
    ``RandomChoiceCheck.perRun,
    ``RandomChoiceCheck.acceptance,
    ``RandomChoiceCheck.capReached,
    ``Demos.RandomChoice.exports,
    ``Demos.RandomChoice.parseArg_bound,
    ``Demos.RandomChoice.pick_bound,
    ``Demos.RandomChoice.render_bound,
    ``Demos.RandomChoice.accepted_count,
    ``Demos.RandomChoice.short_count,
    ``Demos.RandomChoice.choose_eq,
    ``Demos.RandomChoice.compiled.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"random choice axiom check passed for {theorems.size} theorems"

check_random_choice_axioms
