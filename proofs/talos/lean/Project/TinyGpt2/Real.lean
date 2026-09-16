import Project.LayerNorm.Real
import Project.Gelu.Real
import Project.Softmax.RealPerturbation

namespace Project.TinyGpt2.Real

abbrev Row := Fin 4 → ℝ
abbrev Tokens := Fin 4 → Fin 256
abbrev Matrix (m n : Nat) := Fin m → Fin n → ℝ

structure NormParameters where
  scale : Row
  bias : Row

structure Parameters where
  token : Fin 256 → Row
  position : Fin 4 → Row
  query : Matrix 4 4
  key : Matrix 4 4
  value : Matrix 4 4
  attention : Matrix 4 4
  attentionBias : Row
  expand : Matrix 4 8
  expandBias : Fin 8 → ℝ
  contract : Matrix 8 4
  contractBias : Row
  head : Matrix 4 256
  headBias : Fin 256 → ℝ
  norm1 : NormParameters
  norm2 : NormParameters
  normFinal : NormParameters

noncomputable def matrixApply {m n : Nat} (w : Matrix m n) (x : Fin m → ℝ) (j : Fin n) : ℝ :=
  ∑ i, x i*w i j

noncomputable def norm (p : NormParameters) (x : Row) : Row :=
  LayerNorm.Real.layerNorm (1/100000) x p.scale p.bias

noncomputable def embedding (p : Parameters) (tokens : Tokens) (i : Fin 4) : Row :=
  fun j => p.token (tokens i) j+p.position i j

noncomputable def normalizedEmbedding (p : Parameters) (tokens : Tokens) (i : Fin 4) : Row :=
  norm p.norm1 (embedding p tokens i)

def coordinate (head k : Fin 2) : Fin 4 := ⟨2*head.val+k.val, by omega⟩
def headOf (j : Fin 4) : Fin 2 := ⟨j.val/2, by omega⟩
def withinHead (j : Fin 4) : Fin 2 := ⟨j.val%2, by omega⟩
def visible (i j : Fin 4) : Bool := decide (j ≤ i)

noncomputable def score (p : Parameters) (tokens : Tokens) (i : Fin 4) (head : Fin 2)
    (j : Fin 4) : ℝ :=
  (∑ k : Fin 2, matrixApply p.query (normalizedEmbedding p tokens i) (coordinate head k)*
    matrixApply p.key (normalizedEmbedding p tokens j) (coordinate head k))/Real.sqrt 2

noncomputable def probability (p : Parameters) (tokens : Tokens) (i : Fin 4) (head : Fin 2) :
    Fin 4 → ℝ :=
  Softmax.Real.probability (visible i) (score p tokens i head)

noncomputable def attended (p : Parameters) (tokens : Tokens) (i : Fin 4) (j : Fin 4) : ℝ :=
  ∑ k, probability p tokens i (headOf j) k*
    matrixApply p.value (normalizedEmbedding p tokens k) j

noncomputable def residual1 (p : Parameters) (tokens : Tokens) (i : Fin 4) : Row :=
  fun j => embedding p tokens i j+matrixApply p.attention (attended p tokens i) j+p.attentionBias j

noncomputable def expanded (p : Parameters) (tokens : Tokens) (i : Fin 4) (j : Fin 8) : ℝ :=
  matrixApply p.expand (norm p.norm2 (residual1 p tokens i)) j+p.expandBias j

noncomputable def activated (p : Parameters) (tokens : Tokens) (i : Fin 4) (j : Fin 8) : ℝ :=
  Gelu.Real.gelu (expanded p tokens i j)

noncomputable def residual2 (p : Parameters) (tokens : Tokens) (i : Fin 4) : Row :=
  fun j => residual1 p tokens i j+matrixApply p.contract (activated p tokens i) j+p.contractBias j

noncomputable def hidden (p : Parameters) (tokens : Tokens) (i : Fin 4) : Row :=
  norm p.normFinal (residual2 p tokens i)

noncomputable def logits (p : Parameters) (tokens : Tokens) (i : Fin 4) (j : Fin 256) : ℝ :=
  matrixApply p.head (hidden p tokens i) j+p.headBias j

theorem coordinate_decomposition (j : Fin 4) : coordinate (headOf j) (withinHead j) = j := by
  apply Fin.ext
  simp only [coordinate, headOf, withinHead]
  omega

end Project.TinyGpt2.Real
