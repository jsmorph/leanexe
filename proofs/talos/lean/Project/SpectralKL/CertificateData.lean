import Project.SpectralKL.Samples

namespace Project.SpectralKL.Certificate
open Matrix Samples
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

structure Bounds (K : Type*) where
  lower : K
  upper : K
  deriving Repr

/-- Exact rational certificate arithmetic. The candidate vector is unrestricted.
Only matrix-vector products against the observations are checked. -/
def cell {K : Type*} [Field K] (p q : List (n → K))
    (eta a b : K) (x : n → K) : Bounds K :=
  let d := mean p - mean q
  let px := action p x
  let qx := action q x
  let u := 2 * (d ⬝ᵥ x) - x ⬝ᵥ (qx + eta • x)
  let v := x ⬝ᵥ (qx-px)
  let ra := d - (a • px + (1-a) • qx + eta • x)
  let rb := d - (b • px + (1-b) • qx + eta • x)
  let e := ((ra ⬝ᵥ ra) + (rb ⬝ᵥ rb)) / eta
  let w := (b-a) - (b^2-a^2)/2
  let z := (b^2-a^2)/2 - (b^3-a^3)/3
  let lower := u*w+v*z
  ⟨lower, lower+e*w⟩

def add (a b : Bounds ℚ) : Bounds ℚ := ⟨a.lower+b.lower,a.upper+b.upper⟩

/-- The accepted partition starts at zero, advances monotonically, and ends
at one. Rational arithmetic determines both enclosure endpoints exactly. -/
def enclose (p q : List (n → ℚ)) (eta : ℚ) : ℚ → List (ℚ × (n → ℚ)) → Option (Bounds ℚ)
  | a, [] => if a = 1 then some ⟨0,0⟩ else none
  | a, (b,x) :: xs =>
      if 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 then
        match enclose p q eta b xs with
        | none => none
        | some rest => some (add (cell p q eta a b x) rest)
      else none

/-- Public acceptance function. This function is the subject of the soundness
theorem. A proposed CPU/GPU score is returned only after this check succeeds. -/
def accepts (p q : List (n → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (n → ℚ))) : Bool :=
  if p.isEmpty || q.isEmpty || eta ≤ 0 || tolerance < 0 then false
  else match enclose p q eta 0 cells with
    | none => false
    | some bound => decide (score-tolerance ≤ bound.lower ∧ bound.upper ≤ score+tolerance)

noncomputable def integrand (p q : List (n → ℝ)) (eta r : ℝ) : ℝ :=
  (1-r) * Residual.quadratic (system p q eta r) (mean p-mean q)

noncomputable def target (p q : List (n → ℝ)) (eta : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..1, integrand p q eta r

end Project.SpectralKL.Certificate
