import Project.TinyGpt2.Model
import Project.TinyGpt2.Real

namespace Project.TinyGpt2
open CodeLib.IEEE64

def rowWords (x : Row) : Fin 4 → UInt64 := ![x.x0, x.x1, x.x2, x.x3]
def wideWords (x : WideRow) : Fin 8 → UInt64 :=
  ![x.low.x0, x.low.x1, x.low.x2, x.low.x3, x.high.x0, x.high.x1, x.high.x2, x.high.x3]

noncomputable def decodeRow (x : Row) : Real.Row := fun j => value (rowWords x j)

def matrixWords (w : Array UInt64) (offset m n : Nat) (i : Fin m) (j : Fin n) : UInt64 :=
  w[offset+i.val*n+j.val]!

noncomputable def decodeMatrix (w : Array UInt64) (offset m n : Nat) : Real.Matrix m n :=
  fun i j => value (matrixWords w offset m n i j)

noncomputable def decodeNorm (w : Array UInt64) (offset : Nat) : Real.NormParameters :=
  ⟨decodeRow (loadRow w offset), decodeRow (loadRow w (offset+4))⟩

noncomputable def parameters (w : Array UInt64) : Real.Parameters where
  token := fun t => decodeRow (loadRow w (Layout.token+4*t.val))
  position := fun i => decodeRow (loadRow w (Layout.position+4*i.val))
  query := decodeMatrix w Layout.query 4 4
  key := decodeMatrix w Layout.key 4 4
  value := decodeMatrix w Layout.value 4 4
  attention := decodeMatrix w Layout.attention 4 4
  attentionBias := decodeRow (loadRow w Layout.attentionBias)
  expand := decodeMatrix w Layout.expand 4 8
  expandBias := fun j => value w[Layout.expandBias+j.val]!
  contract := decodeMatrix w Layout.contract 8 4
  contractBias := decodeRow (loadRow w Layout.contractBias)
  head := decodeMatrix w Layout.head 4 256
  headBias := fun j => value w[Layout.headBias+j.val]!
  norm1 := decodeNorm w Layout.norm1
  norm2 := decodeNorm w Layout.norm2
  normFinal := decodeNorm w Layout.normFinal

theorem loadRow_words (w : Array UInt64) (offset : Nat) (i : Fin 4) :
    rowWords (loadRow w offset) i = w[offset+i.val]! := by
  fin_cases i <;> simp [rowWords, loadRow]

end Project.TinyGpt2
