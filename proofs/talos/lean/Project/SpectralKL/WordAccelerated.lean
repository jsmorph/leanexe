import Project.SpectralKL.WordShaderEstimator
import Project.SpectralKL.MatrixAccelerated

namespace Project.SpectralKL.WordAccelerated
open WordMoments MatrixPolynomial MatrixEstimator Samples
variable {m : Nat}

def finish (tp tq : Totals m) (np nq : Nat) (scale eta : ℚ) : Int × Nat :=
  let d := store (view (meanOf tp np scale)-view (meanOf tq nq scale))
  MatrixAccelerated.computeMoments (momentOf tp np scale) (momentOf tq nq scale) d eta

def compute (p q : List (Fin m → Sample)) (scale eta : ℚ) : Option (Int × Nat) :=
  if p.isEmpty || q.isEmpty || p.length > 1048576 || q.length > 1048576 || scale ≤ 0 || eta ≤ 0 then none
  else some (finish (totals p) (totals q) p.length q.length scale eta)

theorem compute_eq (p q : List (Fin m → Sample)) (scale eta : ℚ) (h : Valid p q scale eta) :
    compute p q scale eta = MatrixAccelerated.compute (decodeRows p scale) (decodeRows q scale) eta := by
  simp only [compute,finish,MatrixAccelerated.compute,MatrixAccelerated.computeMoments]
  simp [h.1,h.2.1,not_lt.mpr h.2.2.1,not_lt.mpr h.2.2.2.1,
    not_le.mpr h.2.2.2.2.1,not_le.mpr h.2.2.2.2.2,meanOf_eq p h.2.2.1,
    meanOf_eq q h.2.2.2.1,momentOf_eq p h.2.2.1,momentOf_eq q h.2.2.2.1,decodeRows]

theorem compute_correct (p q : List (Fin m → Sample)) (scale eta : ℚ) (h : Valid p q scale eta) :
    ∃ z k, compute p q scale eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows (decodeRows p scale))
        (realRows (decodeRows q scale)) (eta:ℝ)| ≤ 1/1000000 := by
  rw [compute_eq p q scale eta h]
  apply MatrixAccelerated.compute_correct
  exact ⟨by simpa [decodeRows] using h.1,by simpa [decodeRows] using h.2.1,h.2.2.2.2.2⟩

def computeSource (m : Nat) (ip iq : Nat → UInt32) (np nq : Nat) (scale eta : ℚ) : Option (Int × Nat) :=
  if m == 0 || m > 32 || np == 0 || nq == 0 || np > 1048576 || nq > 1048576 || scale ≤ 0 || eta ≤ 0 then none
  else some (finish (WordShader.sourceTotals ip m np) (WordShader.sourceTotals iq m nq) np nq scale eta)

theorem computeSource_eq (p q : List (Fin m → Sample)) (scale eta : ℚ)
    (h : Valid p q scale eta) (hm : 0 < m ∧ m ≤ 32)
    (ip iq : Nat → UInt32) (hp : WordShader.Layout ip p) (hq : WordShader.Layout iq q) :
    computeSource m ip iq p.length q.length scale eta = compute p q scale eta := by
  have hnp : p.length ≠ 0 := by simpa using h.1
  have hnq : q.length ≠ 0 := by simpa using h.2.1
  simp [computeSource,compute,hm.1.ne',not_lt.mpr hm.2,hnp,hnq,h.1,h.2.1,
    not_lt.mpr h.2.2.1,not_lt.mpr h.2.2.2.1,not_le.mpr h.2.2.2.2.1,not_le.mpr h.2.2.2.2.2,
    WordShader.sourceTotals_eq ip p hm.2 h.2.2.1 hp,WordShader.sourceTotals_eq iq q hm.2 h.2.2.2.1 hq]

theorem computeSource_correct (p q : List (Fin m → Sample)) (scale eta : ℚ)
    (h : Valid p q scale eta) (hm : 0 < m ∧ m ≤ 32)
    (ip iq : Nat → UInt32) (hp : WordShader.Layout ip p) (hq : WordShader.Layout iq q) :
    ∃ z k, computeSource m ip iq p.length q.length scale eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows (decodeRows p scale))
        (realRows (decodeRows q scale)) (eta:ℝ)| ≤ 1/1000000 := by
  rw [computeSource_eq p q scale eta h hm ip iq hp hq]
  exact compute_correct p q scale eta h

#print axioms compute_correct
#print axioms computeSource_correct
end Project.SpectralKL.WordAccelerated
