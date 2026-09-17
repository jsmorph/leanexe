import Project.TinyGpt2.Rows
import Project.TinyGpt2.AttentionValue

namespace Project.TinyGpt2

def contextRows (x : Context) : Fin 4 → Row := ![x.r0, x.r1, x.r2, x.r3]

def normContext (w : Array UInt64) (offset : Nat) (x : Context) : Context :=
  ⟨norm w offset x.r0, norm w offset x.r1, norm w offset x.r2, norm w offset x.r3⟩

theorem normContext_rows (w : Array UInt64) (offset : Nat) (x : Context) (i : Fin 4) :
    contextRows (normContext w offset x) i = norm w offset (contextRows x i) := by
  fin_cases i <;> rfl

def attentionProbabilities (n : UInt64) (q : Row) (k : Context) (head : Fin 2) :
    Softmax.Result :=
  let score (i : Fin 4) := attentionScore
    (rowWords q (Real.coordinate head 0)) (rowWords q (Real.coordinate head 1))
    (rowWords (contextRows k i) (Real.coordinate head 0))
    (rowWords (contextRows k i) (Real.coordinate head 1))
  Softmax.compute n (score 0) (score 1) (score 2) (score 3)

theorem attentionRow_words (n : UInt64) (q : Row) (k v : Context) (j : Fin 4) :
    rowWords (attentionRow n q k v) j =
      weightedValue (attentionProbabilities n q k (Real.headOf j))
        (rowWords (contextRows v 0) j) (rowWords (contextRows v 1) j)
        (rowWords (contextRows v 2) j) (rowWords (contextRows v 3) j) := by
  fin_cases j <;> rfl

theorem projectContext_rows (w : Array UInt64) (offset : Nat) (x : Context) (i : Fin 4) :
    contextRows (projectContext w offset x) i = project4 w offset (contextRows x i) := by
  fin_cases i <;> rfl

end Project.TinyGpt2
