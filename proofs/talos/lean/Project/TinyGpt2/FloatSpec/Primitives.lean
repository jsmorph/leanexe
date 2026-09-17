import Project.TinyGpt2.FloatSpec.Algorithm
import Project.TinyGpt2.Model
import Mathlib.Tactic.FinCases

namespace Project.TinyGpt2.FloatSpec.Correspondence

/-- Only this adapter knows the implementation's row representation. -/
def row (x : Row) : Vec 4 := vector4 x.x0 x.x1 x.x2 x.x3

def wide (x : WideRow) : Vec 8 := fun i => match i.val with
  | 0 => x.low.x0 | 1 => x.low.x1 | 2 => x.low.x2 | 3 => x.low.x3
  | 4 => x.high.x0 | 5 => x.high.x1 | 6 => x.high.x2 | _ => x.high.x3

def context (x : Context) : Matrix 4 4 := fun i => match i.val with
  | 0 => row x.r0 | 1 => row x.r1 | 2 => row x.r2 | _ => row x.r3

def vector (w : Array UInt64) (offset : Nat) : Vec n := fun i => w[offset+i.val]!
def matrix (w : Array UInt64) (offset : Nat) : Matrix m n := fun i j => w[offset+i.val*n+j.val]!
def normalization (w : Array UInt64) (offset : Nat) : Normalization :=
  ⟨vector w offset, vector w (offset+4)⟩

/-- The packed-word layout is outside the algorithm specification. -/
def parameters (w : Array UInt64) : Parameters where
  token := matrix w Layout.token
  position := matrix w Layout.position
  query := matrix w Layout.query
  key := matrix w Layout.key
  value := matrix w Layout.value
  attention := matrix w Layout.attention
  attentionBias := vector w Layout.attentionBias
  expand := matrix w Layout.expand
  expandBias := vector w Layout.expandBias
  contract := matrix w Layout.contract
  contractBias := vector w Layout.contractBias
  head := matrix w Layout.head
  headBias := vector w Layout.headBias
  norm1 := normalization w Layout.norm1
  norm2 := normalization w Layout.norm2
  normFinal := normalization w Layout.normFinal

def tokenWord (x : Fin 256) : UInt64 := UInt64.ofNat x.val
def positionWord (x : Fin 4) : UInt64 := UInt64.ofNat x.val

theorem tokenWord_nat (x : Fin 256) : (tokenWord x).toNat = x.val :=
  UInt64.toNat_ofNat_of_lt' (by change x.val < 2^64; omega)
theorem positionWord_nat (x : Fin 4) : (positionWord x).toNat = x.val :=
  UInt64.toNat_ofNat_of_lt' (by change x.val < 2^64; omega)

theorem row_add (x y : Row) : row (addRows x y) = FloatSpec.add (row x) (row y) := by
  funext i; fin_cases i <;> rfl

theorem row_load (w : Array UInt64) (offset : Nat) : row (loadRow w offset) = vector w offset := by
  funext i; fin_cases i <;> rfl

theorem row_norm (w : Array UInt64) (offset : Nat) (x : Row) :
    row (norm w offset x) = normalize (normalization w offset) (row x) := by
  funext i; fin_cases i <;> rfl

theorem dot4_eq (w : Array UInt64) (offset : Nat) (x : Row) (j : Fin n) :
    dotColumn4 w offset n j.val x = FloatSpec.dot4 (row x) (fun i => matrix w offset i j) := by
  simp [dotColumn4, FloatSpec.dot4, sum4, matrix, row, vector4, Affine.dot4,
    Affine.dot2, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.add_assoc]

theorem dot8_eq (w : Array UInt64) (offset : Nat) (x : WideRow) (j : Fin n) :
    dotColumn8 w offset n j.val x = FloatSpec.dot8 (wide x) (fun i => matrix w offset i j) := by
  simp [dotColumn8, FloatSpec.dot8, sum8, sum4, matrix, wide, Affine.dot8,
    Affine.dot4, Affine.dot2, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.add_assoc]

theorem polynomial_eq (x : UInt64) : expPolynomial x = Project.ExpNeg.polynomial x := rfl

theorem reduce_eq (n : Nat) (x : UInt64) (count : Nat) :
    reduceExp n x count = ((Project.ExpNeg.reduce n x count).word, (Project.ExpNeg.reduce n x count).squares) := by
  induction n generalizing x count with
  | zero => rfl
  | succ n ih =>
    simp only [reduceExp, Project.ExpNeg.reduce]
    split <;> simp_all only [ih]

theorem square_eq (n : Nat) (x : UInt64) : squareRepeated n x = Project.ExpNeg.square n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih _

theorem exp_eq (x : UInt64) : expNegative x = Project.ExpNeg.evaluate x := by
  simp only [expNegative, Project.ExpNeg.evaluate, reduce_eq, polynomial_eq, square_eq]

theorem gelu_eq (x : UInt64) : FloatSpec.gelu x = Project.GeluWide.evaluateAll x := by
  have core : (Project.GeluWide.inCore x = true) ↔ x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x4020000000000000 := by
    change (decide (x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x4020000000000000) = true) ↔ _
    exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩
  simp only [FloatSpec.gelu, Project.GeluWide.evaluateAll, core]
  split
  · simp only [Project.GeluWide.evaluate, Project.Gelu.argumentMagnitude,
      Project.ProofKit.F64Order.negativeAbsBits, Project.ProofKit.F64Order.absBits,
      negativeMagnitude, exp_eq]
  · rfl

/-- Causal masks are specified using finite indices, and implemented using
word comparisons. Four index cases establish their exact agreement. -/
theorem softmax_eq (last : Fin 4) (x : Row) (i : Fin 4) :
    FloatSpec.softmax last (row x) i =
      (let p := Project.SoftmaxWide.compute (positionWord last+1) x.x0 x.x1 x.x2 x.x3
       vector4 p.p0 p.p1 p.p2 p.p3 i) := by
  fin_cases last <;> fin_cases i <;>
    simp only [FloatSpec.softmax, positionWord, row, vector4, Project.SoftmaxWide.compute,
      Project.Softmax.rowMaximum, Project.Softmax.activeScore, Project.SoftmaxWide.weight,
      Project.Softmax.probability, Project.Softmax.total, sum4, maximum,
      Project.Softmax.maximum, exp_eq] <;> rfl

#print axioms row_norm
#print axioms exp_eq
#print axioms gelu_eq
#print axioms softmax_eq
end Project.TinyGpt2.FloatSpec.Correspondence
