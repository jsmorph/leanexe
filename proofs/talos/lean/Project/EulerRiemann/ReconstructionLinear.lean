import Project.EulerRiemann.ReconstructionAccuracy

namespace Project.EulerRiemann.Reconstruction
open Project.Euler2DCellStep.Sweep (State)
open CodeLib.IEEE64
noncomputable section

def ExactLinearStencil (left center right : State) (delta : Fin 4 → ℝ) : Prop :=
  ∀ i : Fin 4,
    decoded left i = decoded center i - delta i ∧
    decoded right i = decoded center i + delta i ∧
    value (Wasm.IEEE64.sub (words center i) (words left i)) = decoded center i - decoded left i ∧
    value (Wasm.IEEE64.sub (words right i) (words center i)) = decoded right i - decoded center i

def ExactFaceArithmetic (center delta : State) : Prop :=
  ∀ i : Fin 4,
    value (words (scale 0x3FE0000000000000 delta) i) = decoded delta i / 2 ∧
    value (words (difference center (scale 0x3FE0000000000000 delta)) i) =
      decoded center i - value (words (scale 0x3FE0000000000000 delta) i) ∧
    value (words (sum center (scale 0x3FE0000000000000 delta)) i) =
      decoded center i + value (words (scale 0x3FE0000000000000 delta) i)

theorem slope_linear_exact (left center right : State) (delta : Fin 4 → ℝ)
    (hs : (slope left center right).status = 0) (h : ExactLinearStencil left center right delta) :
    decoded (slope left center right).state = delta := by
  funext i
  have hi := h i
  change value (words (slope left center right).state i) = delta i
  rw [slope_value left center right hs i, hi.2.2.1, hi.2.2.2, hi.1, hi.2.1]
  rw [show decoded center i - (decoded center i - delta i) = delta i by ring,
    show decoded center i + delta i - decoded center i = delta i by ring]
  exact Project.ProofKit.RealMinmod.minmod_self _

theorem reconstruct_linear (fuel : Nat) (left center right : State) (delta : Fin 4 → ℝ)
    (hl : admissibleState left = true) (hc : admissibleState center = true)
    (hr : admissibleState right = true) (hs : (slope left center right).status = 0)
    (hf : (candidate center (slope left center right).state 0x3FE0000000000000).status = 0)
    (hlinear : ExactLinearStencil left center right delta)
    (hexact : ExactFaceArithmetic center (slope left center right).state) :
    ∀ i : Fin 4,
      decoded (reconstruct (fuel+1) left center right).left i = decoded center i - delta i/2 ∧
      decoded (reconstruct (fuel+1) left center right).right i = decoded center i + delta i/2 := by
  rw [reconstruct_unrestricted fuel left center right hl hc hr hs hf,
    (candidate_accepted center (slope left center right).state 0x3FE0000000000000 hf).1]
  intro i
  have hdelta := congrFun (slope_linear_exact left center right delta hs hlinear) i
  have he := hexact i
  change value (words (difference center (scale 0x3FE0000000000000
      (slope left center right).state)) i) = _ ∧
    value (words (sum center (scale 0x3FE0000000000000
      (slope left center right).state)) i) = _
  rw [he.2.1, he.2.2, he.1, hdelta]
  exact ⟨rfl, rfl⟩

#print axioms slope_linear_exact
#print axioms reconstruct_linear

end
end Project.EulerRiemann.Reconstruction
