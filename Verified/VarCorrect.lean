import Verified.ExprSpec

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value}

/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem spec_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.var (S := S) x) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt _ hCap hBase hRoom _
      rest Q hTrap hNext
  have hx : (fun i => live i || (Expr.var (S := S) x).uses i) x.index = true := by
    simp [Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  have hl := hRep.length
  have hMode : (Expr.var (S := S) x).mode (slots.map Slot.mode) =
      (slots.getD x.index default).mode := Slot.modes_getD slots x.index
  have hLiveIn : ∀ i, live i = true → (live i || (Expr.var (S := S) x).uses i) = true :=
    fun i h => by simp [h]
  by_cases hCopy : (slots.getD x.index default).mode = .owned ∧ live x.index = true
  · -- A copy into new blocks.
    obtain ⟨hOwned, hLiveX⟩ := hCopy
    simp only [Expr.code, Expr.usesFast_eq, Var.code, hOwned, hLiveX, and_self, ↓reduceIte]
    have hc : (Expr.var (S := S) x).allocs funs flags bounds (slots.map Slot.mode) paid live env =
        tTy.copyCost (env.get x) := by
      simp only [Expr.allocs, Var.cost, modeAt, Slot.modes_getD, hOwned, hLiveX, and_self,
        ↓reduceIte]
    have hT : TrapOK (false || (true && !decide (heap.Within store m (tTy.copyCost (env.get x)))))
        Q := hTrap.part nofun (fun _ => by simp [Slot.any_owned hOwned])
      fun _ hw => hw.mono (by rw [hc]; omega)
    refine wp_copyCode hm tTy hAt hCap hT hh hRep hold hBelow hBase
      (by rw [hh]; simpa [Expr.width] using hRoom) fun heap' store' s' ws' hStep hRep' hF hTop => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
      (fun _ => top_unpaid_le (by simp [Expr.paid, hLiveX]) (by rw [hc]; exact hTop))
    · rw [hMode, hOwned]
      exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · rw [hMode, hOwned]; exact hRep'
    · rw [hMode, hOwned]
      intro u y hy _ wy hwy hly b hb c hc
      have hwy' := ((hVars.live_mono hLiveIn).hold_agree hF hy hly).mp
        hwy
      obtain ⟨hSame, hFresh⟩ := (hVars.live_mono hLiveIn).regions_after hStep hy hwy' hly
        fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · simp only [Expr.code, Expr.usesFast_eq, Var.code, hCopy, ↓reduceIte]
    by_cases hOwned : (slots.getD x.index default).mode = .owned
    · -- A move: the variable dies here, and the value owns its blocks.
      have hDead : live x.index = false := by
        cases h : live x.index
        · rfl
        · exact absurd ⟨hOwned, h⟩ hCopy
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws ⟨?_, Frame.refl base s,
        hVars.live_mono hLiveIn, ?_, ?_⟩ fun _ => top_move x hold hl hOwned hDead)
      · rw [hMode, hOwned]
        exact ⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr,
          fun b hb => hk tTy x hx hDead hOwned ws hold hl b hb⟩⟩
      · rw [hMode]; exact hRep
      · rw [hMode, hOwned]
        intro u y hy _ wy hwy hly b hb c hc
        have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 tTy u x y hx (hLiveIn _ hy) hne hOwned ws wy hold hl hwy hly b hb c hc
    · -- A view of a borrowed variable.
      have hBorrowed : (slots.getD x.index default).mode = .borrowed := by
        cases h : (slots.getD x.index default).mode
        · rfl
        · exact absurd h hOwned
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
        (by rw [hMode]; exact hRep) (by rw [hMode, hBorrowed]; rfl) ?_)
        fun _ => top_unpaid_le
          (by simp only [Expr.paid, modeAt, Slot.modes_getD, hBorrowed]; rfl)
          (Nat.le_add_right _ _))
      rw [hMode]
      intro u y hy hm wy hwy hly b hb c hc
      rcases hm with hm | hm
      · exact absurd hm hOwned
      · have hne : y.index ≠ x.index := fun he => by
          rw [he] at hm; exact hOwned hm
        rw [hm] at hc
        exact regionsDisjoint_symm
          (hVars.2 u tTy y x (hLiveIn _ hy) hx hne hm wy ws hwy hly hold hl c hc b hb)


end Cases

end Verified
