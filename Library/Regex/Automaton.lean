import Library.Regex.Glushkov

/-! The position automaton of `Library.Regex.Glushkov` run forward on sets of states, as the
matcher runs it.  State 0 is the start, and state `p ≥ 1` is position `p` of the expression
numbered from 0.  `Next r p q` gives the states that may follow state `p` on some byte, the
first positions from the start and `Follow` from a position, and a step keeps those whose set
holds the byte.  `matches_iff_steps` states that a word is in the language exactly when the
states reached from the start hold a final state: a last position, or the start when the
expression is nullable. -/

namespace Library.Regex.Automaton

open Library.Regex.Spec Library.Regex.Glushkov

/-- The states that may follow state `p`: the first positions from the start, and the positions
that may follow position `p`. -/
def Next (r : Re) (p q : Nat) : Prop := if p = 0 then First r 0 q else Follow r 0 p q

/-- The states that may end a word: the last positions, and the start when `r` is nullable. -/
def Final (r : Re) (q : Nat) : Prop := if q = 0 then nullable r = true else Last r 0 q

/-- The states after the byte `c` from the states `S`. -/
def step (r : Re) (S : Nat → Prop) (c : UInt8) (q : Nat) : Prop :=
  ∃ p, S p ∧ Next r p q ∧ Class r 0 q c

/-- The states after the word `w` from the states `S`. -/
def steps (r : Re) : (Nat → Prop) → List UInt8 → Nat → Prop
  | S, [] => S
  | S, c :: w => steps r (step r S c) w

/-- From states that are positions, the states after `w` hold a final state exactly when one
of the states accepts `w`. -/
theorem steps_final (r : Re) :
    ∀ (w : List UInt8) (S : Nat → Prop), (∀ p, S p → p ≠ 0) →
      ((∃ q, steps r S w q ∧ Final r q) ↔ ∃ p, S p ∧ Accepts r 0 p w)
  | [], S, hS => by
    simp only [steps, Accepts]
    exact ⟨fun ⟨q, hq, hf⟩ => ⟨q, hq, by simpa [Final, hS q hq] using hf⟩,
      fun ⟨q, hq, hl⟩ => ⟨q, hq, by simpa [Final, hS q hq] using hl⟩⟩
  | c :: w, S, hS => by
    have hstep : ∀ q, step r S c q → q ≠ 0 := fun q ⟨_, _, _, hc⟩ => by
      have := class_range hc; simp only [InRange] at this; omega
    rw [show steps r S (c :: w) = steps r (step r S c) w from rfl,
      steps_final r w (step r S c) hstep]
    constructor
    · rintro ⟨q, ⟨p, hp, hn, hc⟩, hw⟩
      refine ⟨p, hp, q, ?_, hc, hw⟩
      simpa [Next, hS p hp] using hn
    · rintro ⟨p, hp, q, hf, hc, hw⟩
      exact ⟨q, ⟨p, hp, by simpa [Next, hS p hp] using hf, hc⟩, hw⟩

/-- A word is in the language of `r` exactly when the states reached from the start hold a final
state. -/
theorem lang_iff_steps (r : Re) (w : List UInt8) :
    w ∈ r.lang ↔ ∃ q, steps r (· = 0) w q ∧ Final r q := by
  rw [glushkov r 0 w]
  cases w with
  | nil =>
    simp only [Matches, steps, Final]
    constructor
    · rintro (⟨_, hn⟩ | ⟨_, _, h, _⟩)
      · exact ⟨0, rfl, by simpa using hn⟩
      · exact absurd h (List.cons_ne_nil _ _).symm
    · rintro ⟨q, rfl, hn⟩
      exact Or.inl ⟨trivial, by simpa using hn⟩
  | cons c w =>
    have hstart : ∀ q, step r (· = 0) c q → q ≠ 0 := fun q ⟨_, _, _, hc⟩ => by
      have := class_range hc; simp only [InRange] at this; omega
    rw [show steps r (· = 0) (c :: w) = steps r (step r (· = 0) c) w from rfl,
      steps_final r w _ hstart]
    simp only [Matches]
    constructor
    · rintro (⟨h, _⟩ | ⟨c', w', h, p, hf, hc, hw⟩)
      · exact absurd h (List.cons_ne_nil _ _)
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨p, ⟨0, rfl, by simpa [Next] using hf, hc⟩, hw⟩
    · rintro ⟨p, ⟨_, rfl, hn, hc⟩, hw⟩
      exact Or.inr ⟨c, w, rfl, p, by simpa [Next] using hn, hc, hw⟩

#print axioms lang_iff_steps

end Library.Regex.Automaton
