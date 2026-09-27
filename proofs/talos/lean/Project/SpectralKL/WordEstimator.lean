import Project.SpectralKL.WordMoments

namespace Project.SpectralKL.WordMoments
open MatrixPolynomial MatrixEstimator Samples
variable {m : Nat}

def decodeRows (rows : List (Fin m → Sample)) (scale : ℚ) : List (Fin m → ℚ) :=
  rows.map fun v i => ((v i).val-32768:ℚ)/scale

def columnSum (rows : List (Fin m → Sample)) (i : Fin m) : Nat :=
  (rows.map fun v => (v i).val).sum
def productSum (rows : List (Fin m → Sample)) (i j : Fin m) : Nat :=
  (rows.map fun v => (v i).val*(v j).val).sum

structure Totals (m : Nat) where
  columns : Vector Sum64 m
  products : Vector (Vector Sum64 m) m

def totals (rows : List (Fin m → Sample)) : Totals m :=
  ⟨store (column rows),store (fun i => store (gram rows i))⟩

def meanOf (t : Totals m) (count : Nat) (scale : ℚ) : Vector ℚ m :=
  store fun i => ((view t.columns i).value-32768*(count:ℚ))/((count:ℚ)*scale)

def momentOf (t : Totals m) (count : Nat) (scale : ℚ) : StoredMatrix m :=
  matrixStore (Matrix.of fun i j =>
    ((view (view t.products i) j).value-
      32768*((view t.columns i).value+(view t.columns j).value:ℚ)+
      (count:ℚ)*32768^2)/((count:ℚ)*scale^2))

theorem decode_sum (rows : List (Fin m → Sample)) (scale : ℚ) (i : Fin m) :
    meanSum (decodeRows rows scale) i =
      ((columnSum rows i:ℚ)-32768*(rows.length:ℚ))/scale := by
  induction rows with
  | nil => simp [decodeRows,meanSum,columnSum]
  | cons v vs ih =>
    simp only [decodeRows,columnSum,List.map_cons,meanSum,Pi.add_apply,List.sum_cons,List.length_cons,
      Nat.cast_add,Nat.cast_one] at *
    rw [ih]
    ring

theorem decode_gram (rows : List (Fin m → Sample)) (scale : ℚ) (i j : Fin m) :
    gramSum (decodeRows rows scale) i j =
      ((productSum rows i j:ℚ)-32768*((columnSum rows i:ℚ)+(columnSum rows j:ℚ))+
        (rows.length:ℚ)*32768^2)/scale^2 := by
  induction rows with
  | nil => simp [decodeRows,gramSum,columnSum,productSum]
  | cons v vs ih =>
    simp only [decodeRows,columnSum,productSum,List.map_cons,gramSum,Matrix.add_apply,Matrix.vecMulVec,Matrix.of_apply,List.sum_cons,
      List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_mul] at *
    rw [ih]
    simp only [div_eq_mul_inv,inv_pow]
    ring

theorem meanOf_eq (rows : List (Fin m → Sample)) (h : rows.length ≤ 1048576) (scale : ℚ) :
    view (meanOf (totals rows) rows.length scale) = mean (decodeRows rows scale) := by
  ext i
  have hlen : (decodeRows rows scale).length = rows.length := by simp [decodeRows]
  simp only [meanOf,totals,view_store,column_value rows h,mean,Pi.smul_apply,smul_eq_mul,
    hlen]
  rw [decode_sum]
  simp only [columnSum,div_eq_mul_inv,mul_inv_rev]
  ring

theorem momentOf_eq (rows : List (Fin m → Sample)) (h : rows.length ≤ 1048576) (scale : ℚ) :
    matrixView (momentOf (totals rows) rows.length scale) = moment (decodeRows rows scale) := by
  rw [momentOf,matrixView_store]
  ext i j
  have hlen : (decodeRows rows scale).length = rows.length := by simp [decodeRows]
  simp only [totals,view_store,gram_value rows h,column_value rows h,
    moment,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,hlen]
  rw [decode_gram]
  simp only [columnSum,productSum,div_eq_mul_inv,mul_inv_rev]
  ring

def finish (tp tq : Totals m) (np nq : Nat) (scale eta : ℚ) : Int × Nat :=
  let d := store (view (meanOf tp np scale)-view (meanOf tq nq scale))
  MatrixGeneral.computeMoments (momentOf tp np scale) (momentOf tq nq scale) d eta

def compute (p q : List (Fin m → Sample)) (scale eta : ℚ) : Option (Int × Nat) :=
  if p.isEmpty || q.isEmpty || p.length > 1048576 || q.length > 1048576 || scale ≤ 0 || eta ≤ 0 then none
  else
    let tp := totals p
    let tq := totals q
    some (finish tp tq p.length q.length scale eta)

def Valid (p q : List (Fin m → Sample)) (scale eta : ℚ) : Prop :=
  p ≠ [] ∧ q ≠ [] ∧ p.length ≤ 1048576 ∧ q.length ≤ 1048576 ∧ 0 < scale ∧ 0 < eta

theorem compute_eq (p q : List (Fin m → Sample)) (scale eta : ℚ) (h : Valid p q scale eta) :
    compute p q scale eta = MatrixGeneral.computeAuto (decodeRows p scale) (decodeRows q scale) eta := by
  simp only [compute,finish,MatrixGeneral.computeAuto,MatrixGeneral.computeMoments]
  simp [h.1,h.2.1,not_lt.mpr h.2.2.1,not_lt.mpr h.2.2.2.1,
    not_le.mpr h.2.2.2.2.1,not_le.mpr h.2.2.2.2.2,meanOf_eq p h.2.2.1,
    meanOf_eq q h.2.2.2.1,momentOf_eq p h.2.2.1,momentOf_eq q h.2.2.2.1,decodeRows]

theorem compute_correct (p q : List (Fin m → Sample)) (scale eta : ℚ) (h : Valid p q scale eta) :
    ∃ z k, compute p q scale eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows (decodeRows p scale))
        (realRows (decodeRows q scale)) (eta:ℝ)| ≤ 1/1000000 := by
  rw [compute_eq p q scale eta h]
  apply MatrixGeneral.computeAuto_correct
  exact ⟨by simpa [decodeRows] using h.1,by simpa [decodeRows] using h.2.1,h.2.2.2.2.2⟩

#print axioms meanOf_eq
#print axioms momentOf_eq
#print axioms compute_correct
end Project.SpectralKL.WordMoments
