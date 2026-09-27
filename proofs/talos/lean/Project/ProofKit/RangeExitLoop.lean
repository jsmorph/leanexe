import Project.ProofKit.RangeFoldLoop

namespace Project.ProofKit.RangeExitLoop
open Wasm RangeFoldLoop

theorem program_spec (indexLocal stopLocal : Nat) (stepCode : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (count : Nat) (P Exit : Nat → Locals → Prop)
    (hcount : count < UInt64.size)
    (hready : Ready indexLocal stopLocal count 0 frame) (hP : P 0 frame)
    (hstep : ∀ index next, index < count →
      Ready indexLocal stopLocal count index next → P index next →
      ∀ (Q : Assertion Unit) rest,
      (∀ result, Ready indexLocal stopLocal count (index + 1) result →
        P (index + 1) result → wp module_ rest Q initial result env) →
      (∀ result, result.values = [] → Exit index result → Q (.Break 1 initial result)) →
      wp module_ (stepCode ++ rest) Q initial next env)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hdone : ∀ result, Ready indexLocal stopLocal count count result →
      P count result → wp module_ rest Q initial result env)
    (hexit : ∀ index result, index < count → result.values = [] → Exit index result →
      wp module_ rest Q initial result env) :
    wp module_ (program indexLocal stopLocal stepCode ++ rest) Q initial frame env := by
  let Inv : AssertionF Unit := fun current next => current = initial ∧
    ∃ index, index ≤ count ∧ Ready indexLocal stopLocal count index next ∧ P index next
  have hentry := hready.1
  simp only [program, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Inv) (μ := measure indexLocal count)
  · exact ⟨rfl, 0, Nat.zero_le _, hready, hP⟩
  · rintro current next ⟨rfl, index, hindex, hready, hP⟩
    have hindex64 : index < UInt64.size := lt_of_le_of_lt hindex hcount
    simp only [body, List.cons_append, List.nil_append, wp_localGet_cons,
      Frame.withValues_get, hready.1, hready.2.1, hready.2.2,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases hlast : index = count
    · subst index
      rw [ite_eq_left (show UInt64.ofNat count ≥ UInt64.ofNat count by simp)]
      simp [hentry]
      have hframeValues : ({ next with values := [] } : Locals) = next :=
        Frame.ext _ _ rfl rfl hready.1.symm
      simpa only [hframeValues] using hdone next hready hP
    · have hlt : index < count := by omega
      have hguard : ¬ UInt64.ofNat count ≤ UInt64.ofNat index := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hcount,
          UInt64.toNat_ofNat_of_lt' hindex64]
        omega
      simp only [ge_iff_le, hguard, ite_false]
      have hframeValues : ({ next with values := [] } : Locals) = next :=
        Frame.ext _ _ rfl rfl hready.1.symm
      rw [hframeValues]
      apply hstep index next hlt hready hP
      · intro result hresult hPresult
        simp only [wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
        have hresultValues : ({ result with values := [] } : Locals) = result :=
          Frame.ext _ _ rfl rfl hresult.1.symm
        change Inv current { result with values := [] } ∧
          measure indexLocal count current { result with values := [] } < measure indexLocal count current next
        rw [hresultValues]
        refine ⟨⟨rfl, index + 1, by omega, hresult, hPresult⟩, ?_⟩
        simp only [RangeFoldLoop.measure, hresult.2.1, hready.2.1,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega),
          UInt64.toNat_ofNat_of_lt' hindex64]
        omega
      · intro result hValues hExit
        have hFrame : ({ result with values := [] } : Locals) = result :=
          Frame.ext _ _ rfl rfl hValues.symm
        simpa only [List.take_zero, List.drop_zero, List.nil_append, hentry, hFrame] using
          hexit index result hlt hValues hExit

#print axioms program_spec
end Project.ProofKit.RangeExitLoop
