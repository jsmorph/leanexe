import LeanExe.A64.Gen

/-!
Facts about runs of the AArch64 model that the simulation proof uses: `Reach`, the states that
zero or more steps reach; `CodeAt`, instructions placed at an address; the step at a placed
instruction, which executes it; and the arithmetic of `after`.
-/

namespace LeanExe.A64

variable {P : Platform} {code : UInt64 → Option UInt32}

/-- The states that zero or more steps reach from a state. -/
inductive Reach (P : Platform) (code : UInt64 → Option UInt32) : State → State → Prop
  | refl (s : State) : Reach P code s s
  | next {s t u : State} : step P code s = some t → Reach P code t u → Reach P code s u

theorem Reach.trans {s t u : State} (h1 : Reach P code s t) (h2 : Reach P code t u) :
    Reach P code s u := by
  induction h1 with
  | refl => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem Reach.single {s t : State} (h : LeanExe.A64.step P code s = some t) : Reach P code s t :=
  .next h (.refl t)

/-- The instructions `is` lie at `a`, one word each. -/
def CodeAt (code : UInt64 → Option UInt32) (a : UInt64) (is : List Instr) : Prop :=
  ∀ i (h : i < is.length), code (after a i) = some (encode is[i])

theorem after_zero (a : UInt64) : after a 0 = a := by
  simp [after]

theorem after_after (a : UInt64) (m n : Nat) : after (after a m) n = after a (m + n) := by
  simp only [after, UInt64.ofNat_add, UInt64.mul_add, UInt64.add_assoc]

theorem CodeAt.append {a : UInt64} {l1 l2 : List Instr} :
    CodeAt code a (l1 ++ l2) ↔ CodeAt code a l1 ∧ CodeAt code (after a l1.length) l2 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      simpa [List.getElem_append, hi] using this
    · have := h (l1.length + i) (by simp; omega)
      rw [after_after]
      simpa [List.getElem_append] using this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hl : i < l1.length
    · simpa [List.getElem_append, hl] using h1 i hl
    · have hi2 : i - l1.length < l2.length := by simp at hi; omega
      have := h2 (i - l1.length) hi2
      rw [after_after, Nat.add_sub_cancel' (by omega)] at this
      simpa [List.getElem_append, hl] using this

theorem CodeAt.cons {a : UInt64} {i : Instr} {l : List Instr} :
    CodeAt code a (i :: l) ↔ code a = some (encode i) ∧ CodeAt code (after a 1) l := by
  have := CodeAt.append (code := code) (a := a) (l1 := [i]) (l2 := l)
  simp only [List.singleton_append] at this
  rw [this]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [after_zero] using h1 0 (by simp), by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj => by
      have : j = 0 := by simp at hj; omega
      subst this; simpa [after_zero] using h1, by simpa using h2⟩

/-- At a placed instruction, a step executes it. -/
theorem step_at {s : State} {i : Instr} (h : code s.pc = some (encode i)) :
    step P code s = exec P i s := by
  simp [step, h, decode_encode]

end LeanExe.A64
