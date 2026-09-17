import Project.TinyGpt2.CheckpointFinalNorm

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64

theorem hidden_decomposition (tokens : Fin 4 → UInt64) (position : Fin 4) :
    let rows := Context.mk (embedding words (tokens 0) 0) (embedding words (tokens 1) 1)
      (embedding words (tokens 2) 2) (embedding words (tokens 3) 3)
    let r1 := computedResidual (UInt64.ofNat (position.val+1)) (contextRows rows position) rows
    hidden words (tokens 0) (tokens 1) (tokens 2) (tokens 3) (UInt64.ofNat position.val) =
      norm words 2480 (addRows r1 (contractRow words (computedActivated r1))) := by
  fin_cases position <;> rfl

theorem hidden_bounded (tokens : Fin 4 → UInt64) (ht : ∀ i, (tokens i).toNat < 256)
    (position i : Fin 4) :
    Affine.Bounded (rowWords
      (hidden words (tokens 0) (tokens 1) (tokens 2) (tokens 3) (UInt64.ofNat position.val)) i) 7 := by
  rw [hidden_decomposition]
  exact computedFinal_bound _ (embedding_residual_valid tokens ht position) i

#print axioms hidden_bounded
end Project.TinyGpt2.Checkpoint
