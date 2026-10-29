import LeanExe.ProofKit.AlignedFlag
import LeanExe.TalosCompat

/-!
More rules for `wpX`.  `wpX_cons_simple` reduces `wpX` of an instruction without a 64-bit access
or a body to Talos's `wp` of that instruction alone, at either value of the flag, so that Talos's
atomic `wp_*_cons` rules, which `simp` applies, finish the step; `wp_cons_wp` is its form for `wp`.
`wpX_iff_cons` is the conditional with any block types.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type}

section

variable {strict : Bool} {m : Module} {Q : Assertion α} {st : Store α} {s : Locals}
  {env : HostEnv α}

/-- `wpA_cons_wp` for `wp`. -/
theorem wp_cons_wp {i : Instruction} {rest : Program} :
    wp m (i :: rest) Q st s env ↔
      wp m [i] (fun c => match c with
        | .Fallthrough st' s' => wp m rest Q st' s' env
        | other => Q other) st s env := by
  have hone : ∀ f, exec f m st s [i] env = execOne f m st s i env := by
    intro f
    simp only [exec]
    cases execOne f m st s i env <;> rfl
  constructor
  · intro h
    unfold Wasm.wp at h ⊢
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun f hf => ?_⟩
    rw [hone f]
    have hf' := hN f hf
    rw [exec] at hf'
    generalize hk : execOne f m st s i env = k at hf'
    cases k with
    | Fallthrough st' s' =>
      refine ⟨N + f, fun g hg => ?_⟩
      have hg' := hN g (by omega)
      have hmono : execOne g m st s i env = .Fallthrough st' s' := by
        rw [execOne_fuel_mono (by omega : f ≤ g) (by rw [hk]; simp)]
        exact hk
      rw [exec, hmono] at hg'
      exact hg'
    | _ => exact hf'
  · intro h
    unfold Wasm.wp at h ⊢
    obtain ⟨N, hN⟩ := h
    by_cases hOOF : ∀ f ≥ N, execOne f m st s i env = .OutOfFuel
    · refine ⟨N, fun f hf => ?_⟩
      have hQ := hN f hf
      rw [hone f, hOOF f hf] at hQ
      rw [exec, hOOF f hf]
      exact hQ
    · push Not at hOOF
      obtain ⟨f₀, hf₀, hne⟩ := hOOF
      have hstable : ∀ f ≥ f₀, execOne f m st s i env = execOne f₀ m st s i env :=
        fun f hf => execOne_fuel_mono hf hne
      have hK := hN f₀ hf₀
      rw [hone f₀] at hK
      generalize hk : execOne f₀ m st s i env = k at hstable hK hne
      cases k with
      | Fallthrough st' s' =>
        obtain ⟨Nr, hNr⟩ := hK
        refine ⟨f₀ + Nr, fun f hf => ?_⟩
        rw [exec, hstable f (by omega)]
        exact hNr f (by omega)
      | OutOfFuel => exact absurd rfl hne
      | Break _ _ _ | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
        refine ⟨f₀, fun f hf => ?_⟩
        rw [exec, hstable f hf]
        exact hK

/-- An instruction without a 64-bit access or a body, at either value of the flag. -/
theorem wpX_cons_simple {i : Instruction} {rest : Program}
    (hal : ∀ f, AlignedOne (f + 1) m st s i env) :
    wpX strict m (i :: rest) Q st s env ↔
      wp m [i] (fun c => match c with
        | .Fallthrough st' s' => wpX strict m rest Q st' s' env
        | other => Q other) st s env := by
  cases strict
  · exact wp_cons_wp
  · exact wpA_cons_wp hal

theorem wpX_unreachable_cons {rest : Program} :
    wpX strict m (.unreachable :: rest) Q st s env ↔ Q (.Trap st "unreachable") := by
  cases strict
  · exact wp_unreachable_cons
  · exact wpA_cons_stop (fun f => by simp [execOne.eq_def]) (by simp) (fun f => by simp [AlignedOne])

/-- The conditional with any block types. -/
theorem wpX_iff_cons {ps rs : Nat} {pt rt : List ValueType} {thn els rest : Program}
    {c : UInt32} {vs : List Value} (hStack : s.values = .i32 c :: vs)
    (h : wpX strict m (if c ≠ 0 then thn else els)
          (fun cont => match cont with
            | .Fallthrough st' s' =>
              wpX strict m rest Q st' { s' with values := s'.values.take rs ++ vs.drop ps } env
            | .Break 0 st' s' =>
              wpX strict m rest Q st' { s' with values := s'.values.take rs ++ vs.drop ps } env
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st { s with values := vs } env) :
    wpX strict m (.iff ps rs thn els pt rt :: rest) Q st s env := by
  cases strict
  · show wp m (.iff ps rs thn els pt rt :: rest) Q st s env
    rw [wp_iff_control_types]
    exact wp_iff_cons hStack h
  · exact wpA_iff_cons hStack h

end

end LeanExe.ProofKit
