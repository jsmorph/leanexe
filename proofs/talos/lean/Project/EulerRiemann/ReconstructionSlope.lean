import Project.EulerRiemann.ReconstructionSafety
import Project.ProofKit.F64RoundingResidual

namespace Project.EulerRiemann.Reconstruction
open Project.Euler2DCellStep.Sweep (State StateSafe)
open Project.ProofKit.F64Order (finiteBits_iff)
open CodeLib.IEEE64

def words (state : State) : Fin 4 → UInt64 :=
  ![state.density, state.mx, state.my, state.energy]

theorem finiteState_iff (state : State) :
    finiteState state = true ↔ ∀ i, CodeLib.IEEE64.Finite (words state i) := by
  simp only [finiteState, Bool.and_eq_true, finiteBits_iff]
  constructor
  · rintro ⟨⟨⟨hr, hx⟩, hy⟩, he⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

theorem safe_finite (state : State) (h : StateSafe state) : finiteState state = true := by
  simp only [finiteState, Bool.and_eq_true, finiteBits_iff]
  exact ⟨⟨⟨h.1.densityFinite, h.1.momentumFinite⟩, h.1.transverseFinite⟩, h.1.energyFinite⟩

theorem words_difference (a b : State) (i : Fin 4) :
    words (difference a b) i = Wasm.IEEE64.sub (words a i) (words b i) := by
  fin_cases i <;> rfl

theorem words_sum (a b : State) (i : Fin 4) :
    words (sum a b) i = Wasm.IEEE64.add (words a i) (words b i) := by
  fin_cases i <;> rfl

theorem words_scale (factor : UInt64) (state : State) (i : Fin 4) :
    words (scale factor state) i = Wasm.IEEE64.mul factor (words state i) := by
  fin_cases i <;> rfl

theorem words_minmod (a b : State) (i : Fin 4) :
    words (minmodState a b) i = Project.ProofKit.F64Minmod.minmod (words a i) (words b i) := by
  fin_cases i <;> rfl

theorem minmodState_finite (a b : State) (ha : finiteState a = true)
    (hb : finiteState b = true) : finiteState (minmodState a b) = true := by
  apply (finiteState_iff _).mpr
  intro i
  rw [words_minmod]
  exact Project.ProofKit.F64Minmod.minmod_finite _ _
    ((finiteState_iff _).mp ha i) ((finiteState_iff _).mp hb i)

theorem slope_accepted (left center right : State)
    (h : (slope left center right).status = 0) :
    (slope left center right).state = minmodState (difference center left) (difference right center) ∧
    finiteState (difference center left) = true ∧ finiteState (difference right center) = true := by
  unfold slope at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · exact ⟨rfl, by simpa only [Bool.and_eq_true] using hg⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem slope_finite (left center right : State) (h : (slope left center right).status = 0) :
    finiteState (slope left center right).state = true := by
  have hs := slope_accepted left center right h
  rw [hs.1]
  exact minmodState_finite _ _ hs.2.1 hs.2.2

theorem slope_value (left center right : State) (h : (slope left center right).status = 0)
    (i : Fin 4) :
    value (words (slope left center right).state i) = Project.ProofKit.RealMinmod.minmod
      (value (Wasm.IEEE64.sub (words center i) (words left i)))
      (value (Wasm.IEEE64.sub (words right i) (words center i))) := by
  rw [(slope_accepted left center right h).1, words_minmod,
    Project.ProofKit.F64Minmod.minmod_value, words_difference, words_difference]

#print axioms slope_finite
#print axioms slope_value

end Project.EulerRiemann.Reconstruction
