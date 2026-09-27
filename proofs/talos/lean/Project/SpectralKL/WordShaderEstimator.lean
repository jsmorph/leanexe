import Project.SpectralKL.WordShaderSource
import Project.SpectralKL.WordShaderBounds

namespace Project.SpectralKL.WordShader
open WordMoments MatrixPolynomial Samples
variable {m : Nat}

def outputAt (input : Nat → UInt32) (m count entry : Nat) : Sum64 :=
  (runSource kernel.source input (u m) (u entry) (u count) (u (m+m*m))).getD ⟨0,0⟩

def sourceTotals (input : Nat → UInt32) (m count : Nat) : Totals m :=
  ⟨store (fun i => outputAt input m count i.val),
    store (fun i => store (fun j => outputAt input m count (m+i.val*m+j.val)))⟩

theorem output_column (input : Nat → UInt32) (rows : List (Fin m → Sample))
    (hm : m ≤ 32) (hn : rows.length ≤ 1048576) (hl : Layout input rows) (i : Fin m) :
    outputAt input m rows.length i.val = column rows i := by
  have hm2 := Nat.mul_le_mul hm hm
  have hb : m+m*m < 4294967296 := by nlinarith
  have hi := mean_output_bound i
  have ha : u i.val < u (m+m*m) := by
    rw [UInt32.lt_iff_toNat_lt,u_nat _ (by omega),u_nat _ hb]
    exact hi
  rw [outputAt,source_run _ _ _ _ _ ha,run_column input rows hm hn hl i]
  rfl

theorem output_product (input : Nat → UInt32) (rows : List (Fin m → Sample))
    (hm : m ≤ 32) (hn : rows.length ≤ 1048576) (hl : Layout input rows) (i j : Fin m) :
    outputAt input m rows.length (m+i.val*m+j.val) = gram rows i j := by
  have hm2 := Nat.mul_le_mul hm hm
  have hb : m+m*m < 4294967296 := by nlinarith
  have hi := product_output_bound i j
  have ha : u (m+i.val*m+j.val) < u (m+m*m) := by
    rw [UInt32.lt_iff_toNat_lt,u_nat _ (by omega),u_nat _ hb]
    exact hi
  rw [outputAt,source_run _ _ _ _ _ ha,run_product input rows hm hn hl i j]
  rfl

theorem sourceTotals_eq (input : Nat → UInt32) (rows : List (Fin m → Sample))
    (hm : m ≤ 32) (hn : rows.length ≤ 1048576) (hl : Layout input rows) :
    sourceTotals input m rows.length = totals rows := by
  unfold sourceTotals totals
  exact congrArg₂ Totals.mk
    (congrArg store (funext fun i => output_column input rows hm hn hl i))
    (congrArg store (funext fun i =>
      congrArg store (funext fun j => output_product input rows hm hn hl i j)))

/-- Full algorithm under the parsed WGSL kernel's semantics, followed by the
same exact rational score computation used by the CPU variant. -/
def compute (m : Nat) (ip iq : Nat → UInt32) (np nq : Nat) (scale eta : ℚ) : Option (Int × Nat) :=
  if m == 0 || m > 32 || np == 0 || nq == 0 || np > 1048576 || nq > 1048576 || scale ≤ 0 || eta ≤ 0 then none
  else some (finish (sourceTotals ip m np) (sourceTotals iq m nq) np nq scale eta)

theorem compute_eq (p q : List (Fin m → Sample)) (scale eta : ℚ)
    (h : WordMoments.Valid p q scale eta) (hm : 0 < m ∧ m ≤ 32)
    (ip iq : Nat → UInt32) (hp : Layout ip p) (hq : Layout iq q) :
    compute m ip iq p.length q.length scale eta = WordMoments.compute p q scale eta := by
  have hnp : p.length ≠ 0 := by simpa using h.1
  have hnq : q.length ≠ 0 := by simpa using h.2.1
  simp [compute,WordMoments.compute,hm.1.ne',not_lt.mpr hm.2,hnp,hnq,h.1,h.2.1,
    not_lt.mpr h.2.2.1,not_lt.mpr h.2.2.2.1,not_le.mpr h.2.2.2.2.1,not_le.mpr h.2.2.2.2.2,
    sourceTotals_eq ip p hm.2 h.2.2.1 hp,sourceTotals_eq iq q hm.2 h.2.2.2.1 hq]

theorem compute_correct (p q : List (Fin m → Sample)) (scale eta : ℚ)
    (h : WordMoments.Valid p q scale eta) (hm : 0 < m ∧ m ≤ 32)
    (ip iq : Nat → UInt32) (hp : Layout ip p) (hq : Layout iq q) :
    ∃ z k, compute m ip iq p.length q.length scale eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows (decodeRows p scale))
        (realRows (decodeRows q scale)) (eta:ℝ)| ≤ 1/1000000 := by
  rw [compute_eq p q scale eta h hm ip iq hp hq]
  exact WordMoments.compute_correct p q scale eta h

#print axioms sourceTotals_eq
#print axioms compute_correct
end Project.SpectralKL.WordShader
