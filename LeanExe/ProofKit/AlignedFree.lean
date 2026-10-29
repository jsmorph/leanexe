import LeanExe.ProofKit.AlignedFlag
import LeanExe.ProofKit.Sequencing

/-!
Code without a 64-bit access or a call.  `freeCode` holds of code none of whose instructions, in
its bodies too, is a `load64`, a `store64`, or a `call`.  Every run of such code meets
`AlignedExec`, so `wpX_append_free` turns Talos's `wp` of it, with `wpX` of the code after it as
the continuation, into `wpX` of the whole, and the original lemmas about such code apply with
`[]` for the code after it.
-/

namespace LeanExe.ProofKit

open Wasm

mutual

/-- The instruction makes no 64-bit access and no call, in its bodies too. -/
def freeInst : Instruction → Bool
  | .load64 _ | .store64 _ | .call _ => false
  | .block _ _ body _ _ | .loop _ _ body _ _ => freeCode body
  | .iff _ _ thn els _ _ => freeCode thn && freeCode els
  | _ => true

/-- No instruction of the code makes a 64-bit access or a call, in its bodies too. -/
def freeCode : List Instruction → Bool
  | [] => true
  | i :: rest => freeInst i && freeCode rest

end

variable {α : Type} {m : Module} {env : HostEnv α}

mutual

theorem AlignedOne.of_free : (f : Nat) → (st : Store α) → (s : Locals) → (i : Instruction) →
    freeInst i = true → AlignedOne f m st s i env
  | 0, _, _, _, _ => by simp only [AlignedOne]
  | f + 1, st, s, i, h => by
    cases i with
    | load64 _ | store64 _ | call _ => simp [freeInst] at h
    | block ps rs body pt rt =>
      simp only [AlignedOne]
      exact AlignedExec.of_free f st s body (by simpa [freeInst] using h)
    | loop pa ra body pt rt =>
      simp only [AlignedOne]
      refine ⟨AlignedExec.of_free f st s body (by simpa [freeInst] using h), ?_⟩
      split
      · exact AlignedOne.of_free f _ _ _ h
      · trivial
    | iff ps rs thn els pt rt =>
      simp only [freeInst, Bool.and_eq_true] at h
      simp only [AlignedOne]
      split
      · exact AlignedExec.of_free f _ _ _ (by split <;> simp [h.1, h.2])
      · trivial
    | _ => simp [AlignedOne]
termination_by f _ _ i _ => (f, sizeOf i)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; omega)

theorem AlignedExec.of_free : (f : Nat) → (st : Store α) → (s : Locals) → (p : Program) →
    freeCode p = true → AlignedExec f m st s p env
  | _, _, _, [], _ => by simp [AlignedExec]
  | f, st, s, i :: rest, h => by
    simp only [freeCode, Bool.and_eq_true] at h
    simp only [AlignedExec]
    refine ⟨AlignedOne.of_free f st s i h.1, ?_⟩
    split
    · exact AlignedExec.of_free f _ _ rest h.2
    · trivial
termination_by f _ _ p _ => (f, sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; omega)

end

theorem freeCode_append (a b : Program) : freeCode (a ++ b) = (freeCode a && freeCode b) := by
  induction a with
  | nil => simp [freeCode]
  | cons i a ih => simp [freeCode, ih, Bool.and_assoc]

theorem AlignedExec.append (f : Nat) (st : Store α) (s : Locals) (P rest : Program) :
    AlignedExec f m st s (P ++ rest) env ↔
      AlignedExec f m st s P env ∧ match exec f m st s P env with
        | .Fallthrough st' s' => AlignedExec f m st' s' rest env
        | _ => True := by
  induction P generalizing st s with
  | nil => simp [AlignedExec, exec]
  | cons i P ih =>
    simp only [List.cons_append, AlignedExec, exec]
    generalize execOne f m st s i env = k
    cases k <;> simp [ih, and_assoc]

section

variable {Q : Assertion α} {st : Store α} {s : Locals}

/-- The continuation of code that `rest` follows: `wpX` of `rest` on a fall-through, and `Q` of
every other continuation. -/
def ThenX (strict : Bool) (m : Module) (rest : Program) (Q : Assertion α) (env : HostEnv α) :
    Assertion α
  | .Fallthrough st' s' => wpX strict m rest Q st' s' env
  | other => Q other

/-- `wp` of `P ++ rest` from `wp` of `P` whose continuation is `wp` of `rest`. -/
theorem wp_append_cont {P rest : Program} (h : wp m P (ThenX false m rest Q env) st s env) :
    wp m (P ++ rest) Q st s env := by
  unfold Wasm.wp at h ⊢
  obtain ⟨N, hN⟩ := h
  by_cases hOOF : ∀ f ≥ N, exec f m st s P env = .OutOfFuel
  · refine ⟨N, fun f hf => ?_⟩
    have hQ := hN f hf
    rw [hOOF f hf] at hQ
    rw [exec_append_match, hOOF f hf]
    exact hQ
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hne⟩ := hOOF
    have hstable : ∀ f ≥ f₀, exec f m st s P env = exec f₀ m st s P env :=
      fun f hf => exec_fuel_mono hf hne
    have hK := hN f₀ hf₀
    generalize hk : exec f₀ m st s P env = k at hstable hK hne
    cases k with
    | Fallthrough st' s' =>
      have hK' : wp m rest Q st' s' env := hK
      unfold Wasm.wp at hK'
      obtain ⟨Nr, hNr⟩ := hK'
      refine ⟨f₀ + Nr, fun f hf => ?_⟩
      rw [exec_append_match, hstable f (by omega)]
      exact hNr f (by omega)
    | OutOfFuel => exact absurd rfl hne
    | Break _ _ _ | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
      refine ⟨f₀, fun f hf => ?_⟩
      rw [exec_append_match, hstable f hf]
      exact hK

/-- `wpA` of `P ++ rest` for free `P`, from `wp` of `P` whose continuation is `wpA` of `rest`. -/
theorem wpA_append_free {P rest : Program} (hP : freeCode P = true)
    (h : wp m P (ThenX true m rest Q env) st s env) :
    wpA m (P ++ rest) Q st s env := by
  unfold Wasm.wp at h
  obtain ⟨N, hN⟩ := h
  have hal : ∀ f, AlignedExec f m st s P env := fun f => AlignedExec.of_free f st s P hP
  by_cases hOOF : ∀ f ≥ N, exec f m st s P env = .OutOfFuel
  · refine ⟨N, fun f hf => ?_⟩
    have hQ := hN f hf
    rw [hOOF f hf] at hQ
    refine ⟨?_, ?_⟩
    · rw [exec_append_match, hOOF f hf]; exact hQ
    · rw [AlignedExec.append, hOOF f hf]; exact ⟨hal f, trivial⟩
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hne⟩ := hOOF
    have hstable : ∀ f ≥ f₀, exec f m st s P env = exec f₀ m st s P env :=
      fun f hf => exec_fuel_mono hf hne
    have hK := hN f₀ hf₀
    generalize hk : exec f₀ m st s P env = k at hstable hK hne
    cases k with
    | Fallthrough st' s' =>
      have hK' : wpA m rest Q st' s' env := hK
      unfold wpA at hK'
      obtain ⟨Nr, hNr⟩ := hK'
      refine ⟨f₀ + Nr, fun f hf => ?_⟩
      have hr := hNr f (by omega)
      refine ⟨?_, ?_⟩
      · rw [exec_append_match, hstable f (by omega)]; exact hr.1
      · rw [AlignedExec.append, hstable f (by omega)]; exact ⟨hal f, hr.2⟩
    | OutOfFuel => exact absurd rfl hne
    | Break _ _ _ | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
      refine ⟨f₀, fun f hf => ?_⟩
      refine ⟨?_, ?_⟩
      · rw [exec_append_match, hstable f hf]; exact hK
      · rw [AlignedExec.append, hstable f hf]; exact ⟨hal f, trivial⟩

/-- `wpX` of `P ++ rest` for free `P`, from `wp` of `P` whose continuation is `wpX` of `rest`. -/
theorem wpX_append_free {strict : Bool} {P rest : Program} (hP : freeCode P = true)
    (h : wp m P (ThenX strict m rest Q env) st s env) :
    wpX strict m (P ++ rest) Q st s env := by
  cases strict
  · exact wp_append_cont h
  · exact wpA_append_free hP h

end

end LeanExe.ProofKit
