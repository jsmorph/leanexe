import Project.SpectralKL.MatrixIteration

namespace Project.SpectralKL.DensePolynomial
open MeasureTheory intervalIntegral
abbrev Poly := List ℚ

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def scale (c : ℚ) (p : Poly) : Poly := p.map (c * ·)
def sub (p q : Poly) : Poly := add p (scale (-1) q)
def mul : Poly → Poly → Poly
  | [], _ => []
  | a::p, q => add (scale a q) (0::mul p q)

def sum : List Poly → Poly
  | [] => []
  | p::ps => add p (sum ps)

def integrateFrom : Nat → Poly → ℚ
  | _, [] => 0
  | k, a::p => a/(k+1) + integrateFrom (k+1) p
def integrate (p : Poly) : ℚ := integrateFrom 0 p

noncomputable def eval : Poly → ℝ → ℝ
  | [], _ => 0
  | a::p, r => (a:ℝ)+r*eval p r

theorem eval_continuous (p : Poly) : Continuous (eval p) := by
  induction p with
  | nil => exact continuous_const
  | cons a p ih => exact continuous_const.add (continuous_id.mul ih)

@[simp] theorem eval_add (p q : Poly) (r : ℝ) : eval (add p q) r = eval p r+eval q r := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp [add,eval,ih]; ring

@[simp] theorem eval_scale (c : ℚ) (p : Poly) (r : ℝ) : eval (scale c p) r = (c:ℝ)*eval p r := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,Rat.cast_mul] at ih ⊢; rw [ih]; ring

@[simp] theorem eval_sub (p q : Poly) (r : ℝ) : eval (sub p q) r = eval p r-eval q r := by
  simp [sub,sub_eq_add_neg]

@[simp] theorem eval_mul (p q : Poly) (r : ℝ) : eval (mul p q) r = eval p r*eval q r := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => simp [mul,eval,ih]; ring

@[simp] theorem eval_sum (ps : List Poly) (r : ℝ) : eval (sum ps) r = (ps.map (eval · r)).sum := by
  induction ps with
  | nil => simp [sum,eval]
  | cons p ps ih => simp [sum,ih]

theorem integrateFrom_correct (p : Poly) (k : Nat) :
    (integrateFrom k p : ℝ) = ∫ r in (0:ℝ)..1, r^k*eval p r := by
  induction p generalizing k with
  | nil => simp [integrateFrom,eval]
  | cons a p ih =>
    have he : (fun r : ℝ => r^k*eval (a::p) r) =
        (fun r => (a:ℝ)*r^k + r^(k+1)*eval p r) := by
      ext r; simp only [eval,pow_succ]; ring
    have h1 : Continuous (fun r : ℝ => (a:ℝ)*r^k) := continuous_const.mul (continuous_pow k)
    have h2 : Continuous (fun r : ℝ => r^(k+1)*eval p r) :=
      (continuous_pow (k+1)).mul (eval_continuous p)
    rw [he, intervalIntegral.integral_add
      (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_pow, ← ih (k+1)]
    simp [integrateFrom, div_eq_mul_inv]

theorem integrate_correct (p : Poly) :
    (integrate p : ℝ) = ∫ r in (0:ℝ)..1, eval p r := by
  simpa [integrate] using integrateFrom_correct p 0

#print axioms integrate_correct
end Project.SpectralKL.DensePolynomial
