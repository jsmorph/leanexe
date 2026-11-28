module

public import Demos.Scheme.Semantics.Outcome
public import Demos.Scheme.Acceptance

@[expose] public section

/-! The three results of milestone 1, derived from the rules of the reference semantics under the
fixnum profile: 42 for the `or` case, `(13 3)` for repeated escape, and `(10 1)` for re-entry into
a `letrec` initializer.  `Determines P src d` states that the rules lead the program to a final
value that denotes the datum `d` and that every final configuration they reach is such a value.
The rules form a function, so a run reaches at most one final configuration (`final_unique`), and
the kernel's evaluation of the run gives the configuration. -/

namespace Demos.Scheme.Semantics

open Numeric

/-- Whether a configuration is final. -/
def Config.isFinal : Config → Bool
  | .halt .. | .fault .. => true
  | _ => false

/-- The rules lead the program whose bytes are `src` to a final value that denotes `d`, and every
final configuration that they reach from it is a value that denotes `d`. -/
def Determines (P : Profile) (src : List UInt8) (d : Datum) : Prop :=
  (∃ v s, Steps P (start P src) (.halt v s) ∧ extern s s.fuel v = some d) ∧
    ∀ c, Steps P (start P src) c → c.isFinal → resultDatum c = some d

theorem run_of_final (P : Profile) {c : Config} (h : c.isFinal) : ∀ n, run P n c = c
  | 0 => rfl
  | _ + 1 => by
    cases c <;> simp_all [Config.isFinal, run]

theorem run_add (P : Profile) : ∀ (m n : Nat) (c : Config), run P (m + n) c = run P n (run P m c)
  | 0, _, _ => by simp [run]
  | m + 1, n, c => by
    rw [Nat.add_right_comm]
    cases c with
    | halt v s => simp [run, run_of_final P (c := .halt v s) rfl]
    | fault f => simp [run, run_of_final P (c := .fault f) rfl]
    | eval e ρ k s => simp only [run]; exact run_add P m n _
    | apply f args k s => simp only [run]; exact run_add P m n _
    | ret v k s => simp only [run]; exact run_add P m n _

/-- A run reaches at most one final configuration. -/
theorem final_unique (P : Profile) {c c₁ c₂ : Config} (h₁ : Steps P c c₁) (h₂ : Steps P c c₂)
    (f₁ : c₁.isFinal) (f₂ : c₂.isFinal) : c₁ = c₂ := by
  obtain ⟨n₁, rfl⟩ := h₁
  obtain ⟨n₂, rfl⟩ := h₂
  rcases Nat.le_total n₁ n₂ with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_add, run_of_final P f₁]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_add, run_of_final P f₂]

theorem isFinal_of_resultDatum {c : Config} {d : Datum} (h : resultDatum c = some d) :
    c.isFinal := by
  cases c <;> simp_all [resultDatum, Config.isFinal]

/-- `Determines` from the datum of a run of `n` rules. -/
theorem determines_of_run {P : Profile} {src : List UInt8} {d : Datum} (n : Nat)
    (h : resultDatum (run P n (start P src)) = some d) : Determines P src d := by
  have hf := isFinal_of_resultDatum h
  refine ⟨?_, fun c hc fc => ?_⟩
  · generalize hr : run P n (start P src) = r at h
    cases r with
    | halt v s => exact ⟨v, s, ⟨n, hr⟩, h⟩
    | _ => simp [resultDatum] at h
  · rw [← final_unique P ⟨n, rfl⟩ hc hf fc, h]

end Demos.Scheme.Semantics

namespace Demos.Scheme.Semantics.Results

open Demos.Scheme.Acceptance Demos.Scheme.Semantics Numeric

/-- `(let ((_ 42)) (or #f _))` yields 42. -/
theorem or_case : Determines fixnum orCase (.int 42) :=
  determines_of_run 100 (by decide +kernel)

/-- The repeated-escape program yields `(13 3)`. -/
theorem repeated_escape : Determines fixnum repeatedEscape (Datum.list [.int 13, .int 3]) :=
  determines_of_run 200 (by decide +kernel)

/-- The `letrec` re-entry program yields `(10 1)`. -/
theorem letrec_reentry : Determines fixnum letrecReentry (Datum.list [.int 10, .int 1]) :=
  determines_of_run 200 (by decide +kernel)

/-- The bytes of each outcome, a status byte 0 and the written value, which the executable
interpreter writes for the same programs. -/
theorem outcomes :
    outcome fixnum 100 orCase = some (0 :: bytes "42") ∧
    outcome fixnum 200 repeatedEscape = some (0 :: bytes "(13 3)") ∧
    outcome fixnum 200 letrecReentry = some (0 :: bytes "(10 1)") := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

#print axioms or_case
#print axioms repeated_escape
#print axioms letrec_reentry
#print axioms outcomes

end Demos.Scheme.Semantics.Results
