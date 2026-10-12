import LeanExe.ProofKit.PolyCalculus
import LeanExe.ProofKit.RatExpLog

/-!
Taylor models over `ℚ`, evaluated by the kernel.  A Taylor model `⟨p, e⟩` approximates a real
function `f` on `[-r, r]` when `|f t - eval p t| ≤ e` there (`Approx`).  `Expr` describes functions
of one variable built from rational constants, polynomials, polynomials of expressions, sums,
products, negation, inverses, `exp`, `log (1 + a)`, `log (1 + a) / a`, `sin`, `cos`, `sin a / a`,
logarithms of positive rationals, and `π`.  `tm` computes a Taylor model of an expression or fails, and `tm_sound` proves
that every computed model approximates the expression's value.

Each product keeps the coefficients up to degree `deg`, bounds the rest by its absolute sum on
`[-r, r]`, and rounds the kept coefficients down to multiples of `2 ^ -bits`, adding the rounding
error.  The inverse, exponential, logarithm, sine, and cosine compose a truncated series with the model
of the argument, with the fewest terms up to `terms` for which the argument's bound `W` gives
`W ^ k ≤ tol`, and add the series' remainder at that bound: the
geometric remainder for `1/(1 - w)`, `Real.exp_bound` for `exp`, `log1p_remainder` for the
logarithm, and `sin_remainder` and `cos_remainder`.  `exp` first removes the constant coefficient
`a`, encloses `exp a` with `RatExpLog` for `|a| ≤ 4` by halving and squaring, and requires the rest
to stay within 1.  The constant `log q` is enclosed by two given rationals whose exponentials the
kernel compares with `q`, and `π` by the configuration's bounds, which the caller proves.
-/

namespace LeanExe.ProofKit.TaylorModel

open Real Finset PolyBound PolyChecks PolyCalculus TaylorRemainder RatExpLog

/-- A polynomial and an error bound. -/
structure TM where
  p : List ℚ
  e : ℚ

/-- The radius, the degree kept, the rounding precision, the largest number of series terms, the
target for a series' remainder, and bounds on `π`. -/
structure Cfg where
  r : ℚ
  deg : ℕ
  bits : ℕ
  terms : ℕ
  tol : ℚ
  piLo : ℚ
  piHi : ℚ

/-- `T` approximates `f` within `T.e` on `[-r, r]`. -/
def Approx (r : ℚ) (f : ℝ → ℝ) (T : TM) : Prop :=
  ∀ t : ℝ, |t| ≤ r → |f t - eval T.p t| ≤ T.e

/-- Expressions in one real variable. -/
inductive Expr where
  | var
  | const (q : ℚ)
  | poly (cs : List ℚ)
  | polyOf (cs : List ℚ) (a : Expr)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  | inv (a : Expr)
  | exp (a : Expr)
  | log1p (a : Expr)
  | log1pDiv (a : Expr)
  | sin (a : Expr)
  | cos (a : Expr)
  | sinc (a : Expr)
  | logC (q lo hi : ℚ)
  | pi

/-- The value of an expression at `t`; `log1pDiv` and `sinc` take their limit 1 at 0. -/
noncomputable def Expr.eval : Expr → ℝ → ℝ
  | .var, t => t
  | .const q, _ => q
  | .poly cs, t => PolyBound.eval cs t
  | .polyOf cs a, t => PolyBound.eval cs (a.eval t)
  | .add a b, t => a.eval t + b.eval t
  | .mul a b, t => a.eval t * b.eval t
  | .neg a, t => -a.eval t
  | .inv a, t => (a.eval t)⁻¹
  | .exp a, t => Real.exp (a.eval t)
  | .log1p a, t => Real.log (1 + a.eval t)
  | .log1pDiv a, t => if a.eval t = 0 then 1 else Real.log (1 + a.eval t) / a.eval t
  | .sin a, t => Real.sin (a.eval t)
  | .cos a, t => Real.cos (a.eval t)
  | .sinc a, t => if a.eval t = 0 then 1 else Real.sin (a.eval t) / a.eval t
  | .logC q _ _, _ => Real.log q
  | .pi, _ => Real.pi

/-- `q` rounded down to a multiple of `2 ^ -bits`. -/
def roundQ (bits : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ bits⌋ : ℚ) / 2 ^ bits

/-- Truncation to degree `deg` and rounding, with the error they add. -/
def norm (c : Cfg) (p : List ℚ) (e : ℚ) : TM :=
  let low := p.take (c.deg + 1)
  let low' := low.map (roundQ c.bits)
  ⟨low', e + absSum c.r (subP low low') + c.r ^ low.length * absSum c.r (p.drop (c.deg + 1))⟩

/-- A bound on `|f t|` on `[-r, r]` for a function that `T` approximates. -/
def bnd (c : Cfg) (T : TM) : ℚ := absSum c.r T.p + T.e

def addT (c : Cfg) (A B : TM) : TM := norm c (addP A.p B.p) (A.e + B.e)

def negT (A : TM) : TM := ⟨scaleP (-1) A.p, A.e⟩

def mulT (c : Cfg) (A B : TM) : TM :=
  norm c (mulP A.p B.p) (absSum c.r A.p * B.e + absSum c.r B.p * A.e + A.e * B.e)

/-- `Σ cs k U ^ k` by Horner's rule. -/
def horner (c : Cfg) : List ℚ → TM → TM
  | [], _ => ⟨[], 0⟩
  | a :: cs, U => addT c ⟨[a], 0⟩ (mulT c U (horner c cs U))

/-- The least `k ≤ fuel` with `W ^ k ≤ tol`, or `fuel`, and at least 1. -/
def termsFor (tol W : ℚ) (fuel : ℕ) : ℕ := go 0 1 fuel
where
  go (k : ℕ) (p : ℚ) : ℕ → ℕ
    | 0 => max k 1
    | f + 1 => if p ≤ tol then max k 1 else go (k + 1) (p * W) f

/-- The number of series terms for an argument bounded by `W`. -/
def nt (c : Cfg) (W : ℚ) : ℕ := termsFor c.tol (qabs W) c.terms

theorem termsFor_pos (tol W : ℚ) (fuel : ℕ) : 0 < termsFor tol W fuel := by
  unfold termsFor
  suffices h : ∀ f k p, 0 < termsFor.go tol W k p f from h fuel 0 1
  intro f
  induction f with
  | zero => intro k p; simp [termsFor.go]
  | succ f ih =>
    intro k p
    simp only [termsFor.go]
    split_ifs
    · omega
    · exact ih _ _

/-- The model `T` with `a` subtracted. -/
def subConst (T : TM) (a : ℚ) : TM := ⟨addP T.p [-a], T.e⟩

/-- The number `s` of halvings that bring `a` with `|a| ≤ 4` into `[-1, 1]`. -/
def expShift (a : ℚ) : ℕ := if qabs a ≤ 1 then 0 else if qabs a ≤ 2 then 1 else 2

/-- Bounds on `exp a` for `|a| ≤ 4`, from `exp (a / 2 ^ s) ^ (2 ^ s)`. -/
def expEnclose (n : ℕ) (a : ℚ) : Option (ℚ × ℚ) :=
  if 0 < n ∧ qabs a ≤ 4 ∧ 0 < qeval (expCoeffs n) (a / 2 ^ expShift a) - expRem n then
    some ((qeval (expCoeffs n) (a / 2 ^ expShift a) - expRem n) ^ 2 ^ expShift a,
      (qeval (expCoeffs n) (a / 2 ^ expShift a) + expRem n) ^ 2 ^ expShift a)
  else none

def expT (c : Cfg) (U : TM) : Option TM :=
  let a := U.p.headD 0
  let V := subConst U a
  let W := bnd c V
  match expEnclose c.terms a with
  | some (lo, hi) =>
    if W ≤ 1 then
      let S := horner c (expCoeffs (nt c W)) V
      some (mulT c ⟨[(lo + hi) / 2], (hi - lo) / 2⟩ ⟨S.p, S.e + W ^ nt c W * expRem (nt c W)⟩)
    else none
  | none => none

def log1pT (c : Cfg) (U : TM) : Option TM :=
  let W := bnd c U
  if W < 1 then
    let S := horner c (log1pCoeffs (nt c W)) U
    some ⟨S.p, S.e + W ^ (nt c W + 1) / (1 - W)⟩
  else none

def log1pDivT (c : Cfg) (U : TM) : Option TM :=
  let W := bnd c U
  if W < 1 then
    let S := horner c (log1pQuotCoeffs (nt c W)) U
    some ⟨S.p, S.e + W ^ nt c W / (1 - W)⟩
  else none

def invT (c : Cfg) (U : TM) : Option TM :=
  let a := U.p.headD 0
  let V := subConst U a
  let W := bnd c V / qabs a
  if a ≠ 0 ∧ W < 1 then
    let G := horner c (List.replicate (nt c W) 1) ⟨scaleP (-1 / a) V.p, qabs (-1 / a) * V.e⟩
    some (mulT c ⟨[1 / a], 0⟩ ⟨G.p, G.e + W ^ nt c W / (1 - W)⟩)
  else none

def sinT (c : Cfg) (U : TM) : Option TM :=
  let W := bnd c U
  if W ≤ 1 then
    let S := mulT c U (horner c (sinCoeffs (nt c W)) (mulT c U U))
    some ⟨S.p, S.e + 2 * W ^ (2 * nt c W + 1) / (2 * nt c W + 1).factorial⟩
  else none

def cosT (c : Cfg) (U : TM) : Option TM :=
  let W := bnd c U
  if W ≤ 1 then
    let S := horner c (cosCoeffs (nt c W)) (mulT c U U)
    some ⟨S.p, S.e + 2 * W ^ (2 * nt c W) / (2 * nt c W).factorial⟩
  else none

def sincT (c : Cfg) (U : TM) : Option TM :=
  let W := bnd c U
  if W ≤ 1 then
    let S := horner c (sinCoeffs (nt c W)) (mulT c U U)
    some ⟨S.p, S.e + 2 * W ^ (2 * nt c W) / (2 * nt c W + 1).factorial⟩
  else none

def logCT (c : Cfg) (q lo hi : ℚ) : Option TM :=
  if 0 < c.terms ∧ 0 < q ∧ qabs lo ≤ 1 ∧ qabs hi ≤ 1 ∧
      qeval (expCoeffs c.terms) lo + expRem c.terms ≤ q ∧
      q ≤ qeval (expCoeffs c.terms) hi - expRem c.terms then
    some ⟨[(lo + hi) / 2], (hi - lo) / 2⟩
  else none

/-- A Taylor model of an expression, or `none` when a series condition fails. -/
def tm (c : Cfg) : Expr → Option TM
  | .var => some (norm c [0, 1] 0)
  | .const q => some ⟨[q], 0⟩
  | .poly cs => some (norm c cs 0)
  | .polyOf cs a => (tm c a).map (horner c cs)
  | .add a b =>
    match tm c a, tm c b with
    | some A, some B => some (addT c A B)
    | _, _ => none
  | .mul a b =>
    match tm c a, tm c b with
    | some A, some B => some (mulT c A B)
    | _, _ => none
  | .neg a => (tm c a).map negT
  | .inv a => (tm c a).bind (invT c)
  | .exp a => (tm c a).bind (expT c)
  | .log1p a => (tm c a).bind (log1pT c)
  | .log1pDiv a => (tm c a).bind (log1pDivT c)
  | .sin a => (tm c a).bind (sinT c)
  | .cos a => (tm c a).bind (cosT c)
  | .sinc a => (tm c a).bind (sincT c)
  | .logC q lo hi => logCT c q lo hi
  | .pi => some ⟨[(c.piLo + c.piHi) / 2], (c.piHi - c.piLo) / 2⟩

/-! ### Soundness -/

section Sound

variable (c : Cfg)

theorem eval_take_drop (p : List ℚ) (n : ℕ) (t : ℝ) :
    eval p t = eval (p.take n) t + t ^ (p.take n).length * eval (p.drop n) t := by
  conv_lhs => rw [← List.take_append_drop n p]
  exact eval_append _ _ t

theorem approx_norm (hr : 0 ≤ c.r) {f : ℝ → ℝ} {p : List ℚ} {e : ℚ}
    (h : Approx c.r f ⟨p, e⟩) : Approx c.r f (norm c p e) := by
  intro t ht
  have h1 : |f t - eval p t| ≤ e := h t ht
  set low := p.take (c.deg + 1) with hlow
  set low' := low.map (roundQ c.bits) with hlow'
  have hsplit := eval_take_drop p (c.deg + 1) t
  rw [← hlow] at hsplit
  have hsub := abs_eval_le c.r hr (subP low low') t ht
  rw [eval_subP] at hsub
  have hhigh := abs_eval_le c.r hr (p.drop (c.deg + 1)) t ht
  have hpow : |t ^ low.length| ≤ (c.r : ℝ) ^ low.length := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg t) ht _
  have hprod : |t ^ low.length * eval (p.drop (c.deg + 1)) t| ≤
      (c.r : ℝ) ^ low.length * ((absSum c.r (p.drop (c.deg + 1)) : ℚ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hpow hhigh (abs_nonneg _) (pow_nonneg (by exact_mod_cast hr) _)
  show |f t - eval low' t| ≤ ((e + absSum c.r (subP low low') +
    c.r ^ low.length * absSum c.r (p.drop (c.deg + 1)) : ℚ) : ℝ)
  push_cast
  have hkey : f t - eval low' t = (f t - eval p t) +
      t ^ low.length * eval (p.drop (c.deg + 1)) t + (eval low t - eval low' t) := by
    rw [hsplit]
    ring
  rw [hkey]
  calc _ ≤ |f t - eval p t| + |t ^ low.length * eval (p.drop (c.deg + 1)) t| +
        |eval low t - eval low' t| := abs_add_three _ _ _
    _ ≤ _ := by linarith

theorem approx_bnd (hr : 0 ≤ c.r) {f : ℝ → ℝ} {T : TM} (h : Approx c.r f T) (t : ℝ)
    (ht : |t| ≤ c.r) : |f t| ≤ bnd c T := by
  have h1 := h t ht
  have h2 := abs_eval_le c.r hr T.p t ht
  rw [bnd]
  push_cast
  calc |f t| = |(f t - eval T.p t) + eval T.p t| := by ring_nf
    _ ≤ |f t - eval T.p t| + |eval T.p t| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem approx_e_nonneg {f : ℝ → ℝ} {T : TM} (h : Approx c.r f T) (hr : 0 ≤ c.r) :
    (0 : ℝ) ≤ T.e :=
  le_trans (abs_nonneg _) (h 0 (by rw [abs_zero]; exact_mod_cast hr))

theorem approx_const (q : ℚ) : Approx c.r (fun _ => (q : ℝ)) ⟨[q], 0⟩ := by
  intro t _
  simp

theorem approx_interval {v : ℝ} {lo hi : ℚ} (hlo : (lo : ℝ) ≤ v) (hhi : v ≤ hi) :
    Approx c.r (fun _ => v) ⟨[(lo + hi) / 2], (hi - lo) / 2⟩ := by
  intro t _
  simp only [eval_cons, eval_nil, mul_zero, add_zero]
  push_cast
  rw [abs_le]
  constructor <;> linarith

theorem approx_add (hr : 0 ≤ c.r) {f g : ℝ → ℝ} {A B : TM} (hA : Approx c.r f A)
    (hB : Approx c.r g B) : Approx c.r (fun t => f t + g t) (addT c A B) := by
  apply approx_norm c hr
  intro t ht
  have h1 := hA t ht
  have h2 := hB t ht
  show |f t + g t - eval (addP A.p B.p) t| ≤ ((A.e + B.e : ℚ) : ℝ)
  rw [eval_addP]
  push_cast
  calc |f t + g t - (eval A.p t + eval B.p t)|
      = |(f t - eval A.p t) + (g t - eval B.p t)| := by ring_nf
    _ ≤ |f t - eval A.p t| + |g t - eval B.p t| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem approx_neg {f : ℝ → ℝ} {A : TM} (hA : Approx c.r f A) :
    Approx c.r (fun t => -f t) (negT A) := by
  intro t ht
  have h1 := hA t ht
  show |-f t - eval (scaleP (-1) A.p) t| ≤ A.e
  rw [eval_scaleP]
  push_cast
  calc |-f t - -1 * eval A.p t| = |f t - eval A.p t| := by
        rw [← abs_neg]
        ring_nf
    _ ≤ _ := h1

theorem approx_mul (hr : 0 ≤ c.r) {f g : ℝ → ℝ} {A B : TM} (hA : Approx c.r f A)
    (hB : Approx c.r g B) : Approx c.r (fun t => f t * g t) (mulT c A B) := by
  apply approx_norm c hr
  intro t ht
  have h1 := hA t ht
  have h2 := hB t ht
  have hPA := abs_eval_le c.r hr A.p t ht
  have hPB := abs_eval_le c.r hr B.p t ht
  have heA := approx_e_nonneg c hA hr
  have heB := approx_e_nonneg c hB hr
  show |f t * g t - eval (mulP A.p B.p) t| ≤
    ((absSum c.r A.p * B.e + absSum c.r B.p * A.e + A.e * B.e : ℚ) : ℝ)
  rw [eval_mulP]
  push_cast
  set a := f t - eval A.p t
  set b := g t - eval B.p t
  have hfg : f t * g t - eval A.p t * eval B.p t =
      eval A.p t * b + eval B.p t * a + a * b := by
    simp only [a, b]
    ring
  rw [hfg]
  have hab : |a * b| ≤ A.e * B.e := by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) heA
  have hx : |eval A.p t * b| ≤ ((absSum c.r A.p : ℚ) : ℝ) * B.e := by
    rw [abs_mul]
    exact mul_le_mul hPA h2 (abs_nonneg _) (absSum_nonneg c.r hr A.p)
  have hy : |eval B.p t * a| ≤ ((absSum c.r B.p : ℚ) : ℝ) * A.e := by
    rw [abs_mul]
    exact mul_le_mul hPB h1 (abs_nonneg _) (absSum_nonneg c.r hr B.p)
  calc |eval A.p t * b + eval B.p t * a + a * b|
      ≤ |eval A.p t * b| + |eval B.p t * a| + |a * b| := by
        have := abs_add_le (eval A.p t * b + eval B.p t * a) (a * b)
        have := abs_add_le (eval A.p t * b) (eval B.p t * a)
        linarith
    _ ≤ _ := by linarith

theorem approx_horner (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U : TM} (hU : Approx c.r u U) :
    ∀ cs : List ℚ, Approx c.r (fun t => eval cs (u t)) (horner c cs U) := by
  intro cs
  induction cs with
  | nil =>
    intro t _
    simp [horner]
  | cons a cs ih =>
    have h := approx_add c hr (approx_const c a) (approx_mul c hr hU ih)
    intro t ht
    have h1 := h t ht
    simp only [eval_cons] at h1 ⊢
    exact h1

theorem approx_subConst {f : ℝ → ℝ} {T : TM} (h : Approx c.r f T) (a : ℚ) :
    Approx c.r (fun t => f t - a) (subConst T a) := by
  intro t ht
  have h1 := h t ht
  show |f t - a - eval (addP T.p [-a]) t| ≤ T.e
  rw [eval_addP]
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_neg]
  calc |f t - a - (eval T.p t + -a)| = |f t - eval T.p t| := by ring_nf
    _ ≤ _ := h1

theorem approx_scale {f : ℝ → ℝ} {T : TM} (h : Approx c.r f T) (k : ℚ) :
    Approx c.r (fun t => k * f t) ⟨scaleP k T.p, qabs k * T.e⟩ := by
  intro t ht
  have h1 := h t ht
  show |k * f t - eval (scaleP k T.p) t| ≤ ((qabs k * T.e : ℚ) : ℝ)
  rw [eval_scaleP]
  push_cast
  rw [qabs_cast, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem approx_widen {f g : ℝ → ℝ} {T : TM} (h : Approx c.r f T) (ρ : ℚ)
    (hg : ∀ t : ℝ, |t| ≤ c.r → |g t - f t| ≤ ρ) : Approx c.r g ⟨T.p, T.e + ρ⟩ := by
  intro t ht
  have h1 := h t ht
  have h2 := hg t ht
  show |g t - eval T.p t| ≤ ((T.e + ρ : ℚ) : ℝ)
  push_cast
  calc |g t - eval T.p t| = |(g t - f t) + (f t - eval T.p t)| := by ring_nf
    _ ≤ |g t - f t| + |f t - eval T.p t| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem approx_congr {f g : ℝ → ℝ} {T : TM} (h : Approx c.r f T)
    (hfg : ∀ t : ℝ, |t| ≤ c.r → g t = f t) : Approx c.r g T := by
  intro t ht
  rw [hfg t ht]
  exact h t ht

theorem rem_mono {x W : ℝ} (hx : |x| ≤ W) (hW : W < 1) (k : ℕ) :
    |x| ^ k / (1 - |x|) ≤ W ^ k / (1 - W) :=
  div_le_div₀ (pow_nonneg ((abs_nonneg x).trans hx) k) (pow_le_pow_left₀ (abs_nonneg x) hx k)
    (by linarith) (by linarith)

theorem log1pT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : log1pT c U = some T) : Approx c.r (fun t => Real.log (1 + u t)) T := by
  simp only [log1pT] at hT
  split_ifs at hT with hW
  obtain rfl := Option.some.inj hT
  apply approx_widen c (approx_horner c hr hU (log1pCoeffs (nt c (bnd c U))))
  intro t ht
  have hb := approx_bnd c hr hU t ht
  have hW' : ((bnd c U : ℚ) : ℝ) < 1 := by exact_mod_cast hW
  have h := log1p_remainder (u t) (by linarith) (nt c (bnd c U))
  push_cast
  exact h.trans (rem_mono hb hW' _)

theorem eval_log1pQuot_zero (n : ℕ) :
    eval (log1pQuotCoeffs n) 0 = if n = 0 then 0 else 1 := by
  cases n with
  | zero => simp [log1pQuotCoeffs]
  | succ n =>
    rw [log1pQuotCoeffs, List.range_succ_eq_map, List.map_cons, eval_cons]
    norm_num

theorem eval_sinCoeffs_zero (n : ℕ) : eval (sinCoeffs n) 0 = if n = 0 then 0 else 1 := by
  cases n with
  | zero => simp [sinCoeffs]
  | succ n =>
    rw [sinCoeffs, List.range_succ_eq_map, List.map_cons, eval_cons]
    norm_num

theorem log1pDivT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : log1pDivT c U = some T) :
    Approx c.r (fun t => if u t = 0 then 1 else Real.log (1 + u t) / u t) T := by
  simp only [log1pDivT] at hT
  split_ifs at hT with hW
  obtain rfl := Option.some.inj hT
  apply approx_widen c (approx_horner c hr hU (log1pQuotCoeffs (nt c (bnd c U))))
  intro t ht
  have hb := approx_bnd c hr hU t ht
  have hW' : ((bnd c U : ℚ) : ℝ) < 1 := by exact_mod_cast hW
  have hW0 : (0 : ℝ) ≤ bnd c U := (abs_nonneg _).trans hb
  push_cast
  split_ifs with hu
  · rw [hu, eval_log1pQuot_zero]
    have hq : (0 : ℝ) ≤ ((bnd c U : ℚ) : ℝ) ^ (nt c (bnd c U)) / (1 - bnd c U) :=
      div_nonneg (pow_nonneg hW0 _) (by linarith)
    split_ifs with hn
    · rw [hn, pow_zero, sub_zero, abs_one, le_div_iff₀ (by linarith), one_mul]
      linarith
    · rw [sub_self, abs_zero]
      exact hq
  · have h := log1p_remainder (u t) (by linarith) (nt c (bnd c U))
    rw [eval_log1pCoeffs] at h
    have hpos : 0 < |u t| := abs_pos.mpr hu
    have heq : Real.log (1 + u t) / u t - eval (log1pQuotCoeffs (nt c (bnd c U))) (u t) =
        (Real.log (1 + u t) - u t * eval (log1pQuotCoeffs (nt c (bnd c U))) (u t)) / u t := by
      field_simp
    rw [heq, abs_div, div_le_iff₀ hpos]
    calc _ ≤ |u t| ^ ((nt c (bnd c U)) + 1) / (1 - |u t|) := h
      _ = |u t| ^ (nt c (bnd c U)) / (1 - |u t|) * |u t| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (rem_mono hb hW' _) (abs_nonneg _)

theorem geom_eval (n : ℕ) (w : ℝ) : (1 - w) * eval (List.replicate n 1) w = 1 - w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, eval_cons, Rat.cast_one, pow_succ]
    linear_combination w * ih

theorem invT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : invT c U = some T) : Approx c.r (fun t => (u t)⁻¹) T := by
  simp only [invT] at hT
  split_ifs at hT with hc
  obtain ⟨ha, hW⟩ := hc
  obtain rfl := Option.some.inj hT
  set a := U.p.headD 0 with hadef
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hV := approx_subConst c hU a
  have hw := approx_scale c hV (-1 / a)
  set W := bnd c (subConst U a) / qabs a with hWdef
  have hWr : (W : ℝ) < 1 := by exact_mod_cast hW
  have hG := approx_horner c hr hw (List.replicate (nt c W) 1)
  have hwb : ∀ t : ℝ, |t| ≤ c.r → |((-1 / a : ℚ) : ℝ) * (u t - a)| ≤ W := by
    intro t ht
    have hb := approx_bnd c hr hV t ht
    rw [hWdef]
    push_cast
    rw [qabs_cast, abs_mul, abs_div, abs_neg, abs_one, one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right hb (abs_nonneg _)
  have hwide := approx_widen c hG (W ^ (nt c W) / (1 - W))
    (g := fun t => (1 - ((-1 / a : ℚ) : ℝ) * (u t - a))⁻¹) (by
      intro t ht
      have hb := hwb t ht
      set w := ((-1 / a : ℚ) : ℝ) * (u t - a)
      have hw1 : 0 < 1 - w := by linarith [le_abs_self w]
      have hgeom := geom_eval (nt c W) w
      have hdiff : (1 - w)⁻¹ - eval (List.replicate (nt c W) 1) w = w ^ (nt c W) / (1 - w) := by
        field_simp
        linear_combination -hgeom
      rw [hdiff, abs_div, abs_pow, abs_of_pos hw1]
      push_cast
      apply div_le_div₀ (pow_nonneg ((abs_nonneg _).trans hb) _)
        (pow_le_pow_left₀ (abs_nonneg _) hb _) (by linarith) (by linarith [le_abs_self w]))
  have hm := approx_mul c hr (approx_const c (1 / a)) hwide
  refine approx_congr c hm fun t _ => ?_
  have h1 : 1 - ((-1 / a : ℚ) : ℝ) * (u t - a) = u t / a := by
    push_cast
    field_simp
    ring
  show (u t)⁻¹ = ((1 / a : ℚ) : ℝ) * (1 - ((-1 / a : ℚ) : ℝ) * (u t - a))⁻¹
  rw [h1, inv_div]
  push_cast
  rw [one_div, ← mul_div_assoc, inv_mul_cancel₀ har, one_div]

theorem expShift_le (a : ℚ) (ha : qabs a ≤ 4) : |((a / 2 ^ expShift a : ℚ) : ℝ)| ≤ 1 := by
  have har : |(a : ℝ)| ≤ 4 := by rw [← qabs_cast]; exact_mod_cast ha
  unfold expShift
  split_ifs with h1 h2
  · have : |(a : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast h1
    push_cast
    simpa using this
  · have : |(a : ℝ)| ≤ 2 := by rw [← qabs_cast]; exact_mod_cast h2
    push_cast
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 1)]
    rw [div_le_one (by norm_num)]
    linarith
  · push_cast
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 2)]
    rw [div_le_one (by norm_num)]
    linarith

theorem expRem_cast (n : ℕ) : ((expRem n : ℚ) : ℝ) = (n + 1 : ℝ) / (n.factorial * n) := by
  simp [expRem]

theorem exp_qeval_le (b : ℚ) (hb : |(b : ℝ)| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.exp b - ((qeval (expCoeffs n) b : ℚ) : ℝ)| ≤ expRem n := by
  rw [qeval_cast, expRem_cast]
  refine (exp_remainder b hb n hn).trans ?_
  have hp : |(b : ℝ)| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have : (0 : ℝ) ≤ (n + 1 : ℝ) / (n.factorial * n) := by positivity
  nlinarith

theorem expEnclose_sound {n : ℕ} {a lo hi : ℚ} (h : expEnclose n a = some (lo, hi)) :
    0 < n ∧ (lo : ℝ) ≤ Real.exp a ∧ Real.exp a ≤ hi := by
  simp only [expEnclose] at h
  split_ifs at h with hc
  obtain ⟨hn, ha4, hlo⟩ := hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨hn, ?_⟩
  set s := expShift a
  set b := a / 2 ^ s with hb
  have hbb := expShift_le a ha4
  have he := exp_qeval_le b hbb n hn
  rw [abs_le] at he
  have hlor : (0 : ℝ) < ((qeval (expCoeffs n) b - expRem n : ℚ) : ℝ) := by exact_mod_cast hlo
  push_cast at hlor ⊢
  have hexp : Real.exp a = Real.exp b ^ 2 ^ s := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hb]
    push_cast
    field_simp
  rw [hexp]
  constructor
  · exact pow_le_pow_left₀ hlor.le (by linarith) _
  · exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) _

theorem expT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : expT c U = some T) : Approx c.r (fun t => Real.exp (u t)) T := by
  simp only [expT] at hT
  set a := U.p.headD 0
  split at hT
  · rename_i lo hi hE
    split_ifs at hT with hW
    obtain rfl := Option.some.inj hT
    obtain ⟨-, hlo, hhi⟩ := expEnclose_sound hE
    have hV := approx_subConst c hU a
    have hWr : ((bnd c (subConst U a) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hW
    have hS := approx_horner c hr hV (expCoeffs (nt c (bnd c (subConst U a))))
    have hwide := approx_widen c hS (bnd c (subConst U a) ^ (nt c (bnd c (subConst U a))) * expRem (nt c (bnd c (subConst U a))))
      (g := fun t => Real.exp (u t - a)) (by
        intro t ht
        have hb := approx_bnd c hr hV t ht
        have h := exp_remainder (u t - a) (hb.trans hWr) (nt c (bnd c (subConst U a))) (termsFor_pos _ _ _)
        push_cast
        rw [expRem_cast]
        refine h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb _)
          (by positivity)))
    have hm := approx_mul c hr (approx_interval c hlo hhi) hwide
    refine approx_congr c hm fun t _ => ?_
    rw [← Real.exp_add]
    ring_nf
  · exact absurd hT (by simp)

theorem sinT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : sinT c U = some T) : Approx c.r (fun t => Real.sin (u t)) T := by
  simp only [sinT] at hT
  split_ifs at hT with hW
  obtain rfl := Option.some.inj hT
  have hS := approx_mul c hr hU (approx_horner c hr (approx_mul c hr hU hU) (sinCoeffs (nt c (bnd c U))))
  apply approx_widen c hS
  intro t ht
  have hb := approx_bnd c hr hU t ht
  have hW' : ((bnd c U : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hW
  have h := sin_remainder (u t) (hb.trans hW') (nt c (bnd c U))
  rw [sq] at h
  push_cast
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb _) (by norm_num)

theorem cosT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : cosT c U = some T) : Approx c.r (fun t => Real.cos (u t)) T := by
  simp only [cosT] at hT
  split_ifs at hT with hW
  obtain rfl := Option.some.inj hT
  have hS := approx_horner c hr (approx_mul c hr hU hU) (cosCoeffs (nt c (bnd c U)))
  apply approx_widen c hS
  intro t ht
  have hb := approx_bnd c hr hU t ht
  have hW' : ((bnd c U : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hW
  have h := cos_remainder (u t) (hb.trans hW') (nt c (bnd c U))
  rw [sq] at h
  push_cast
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb _) (by norm_num)

theorem sincT_sound (hr : 0 ≤ c.r) {u : ℝ → ℝ} {U T : TM} (hU : Approx c.r u U)
    (hT : sincT c U = some T) :
    Approx c.r (fun t => if u t = 0 then 1 else Real.sin (u t) / u t) T := by
  simp only [sincT] at hT
  split_ifs at hT with hW
  obtain rfl := Option.some.inj hT
  have hS := approx_horner c hr (approx_mul c hr hU hU) (sinCoeffs (nt c (bnd c U)))
  apply approx_widen c hS
  intro t ht
  have hb := approx_bnd c hr hU t ht
  have hW' : ((bnd c U : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hW
  have hW0 : (0 : ℝ) ≤ bnd c U := (abs_nonneg _).trans hb
  push_cast
  split_ifs with hu
  · rw [hu, mul_zero, eval_sinCoeffs_zero]
    split_ifs with hn
    · rw [hn]
      norm_num
    · rw [sub_self, abs_zero]
      positivity
  · have h := sin_remainder (u t) (hb.trans hW') (nt c (bnd c U))
    rw [sq] at h
    have hpos : 0 < |u t| := abs_pos.mpr hu
    have heq : Real.sin (u t) / u t - eval (sinCoeffs (nt c (bnd c U))) (u t * u t) =
        (Real.sin (u t) - u t * eval (sinCoeffs (nt c (bnd c U))) (u t * u t)) / u t := by
      field_simp
    rw [heq, abs_div, div_le_iff₀ hpos]
    calc _ ≤ 2 * |u t| ^ (2 * (nt c (bnd c U)) + 1) / ((2 * (nt c (bnd c U)) + 1).factorial : ℝ) := h
      _ = 2 * |u t| ^ (2 * (nt c (bnd c U))) / ((2 * (nt c (bnd c U)) + 1).factorial : ℝ) * |u t| := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb _) (by norm_num)

theorem logCT_sound {q lo hi : ℚ} {T : TM} (hT : logCT c q lo hi = some T) :
    Approx c.r (fun _ => Real.log q) T := by
  simp only [logCT] at hT
  split_ifs at hT with hc
  obtain ⟨hn, hq, hlo, hhi, h1, h2⟩ := hc
  obtain rfl := Option.some.inj hT
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo' : |(lo : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast hlo
  have hhi' : |(hi : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast hhi
  have e1 := (abs_le.mp (exp_qeval_le lo hlo' c.terms hn)).2
  have e2 := (abs_le.mp (exp_qeval_le hi hhi' c.terms hn)).1
  have h1r : (((qeval (expCoeffs c.terms) lo + expRem c.terms : ℚ)) : ℝ) ≤ q := by
    exact_mod_cast h1
  have h2r : (q : ℝ) ≤ ((qeval (expCoeffs c.terms) hi - expRem c.terms : ℚ) : ℝ) := by
    exact_mod_cast h2
  push_cast at h1r h2r
  apply approx_interval c
  · rw [le_log_iff_exp_le hqr]
    linarith
  · rw [log_le_iff_le_exp hqr]
    linarith

theorem tm_sound (hr : 0 ≤ c.r) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) :
    ∀ (x : Expr) {T : TM}, tm c x = some T → Approx c.r x.eval T := by
  intro x
  induction x with
  | var =>
    intro T h
    simp only [tm, Option.some.injEq] at h
    subst h
    exact approx_norm c hr fun t _ => by simp [Expr.eval]
  | const q =>
    intro T h
    simp only [tm, Option.some.injEq] at h
    subst h
    exact approx_const c q
  | poly cs =>
    intro T h
    simp only [tm, Option.some.injEq] at h
    subst h
    exact approx_norm c hr fun t _ => by simp [Expr.eval]
  | polyOf cs a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.map_some, Option.some.injEq] at h
      subst h
      exact approx_horner c hr (iha ha) cs
  | add a b iha ihb =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      cases hb : tm c b with
      | none => simp [tm, ha, hb] at h
      | some B =>
        simp only [tm, ha, hb, Option.some.injEq] at h
        subst h
        exact approx_add c hr (iha ha) (ihb hb)
  | mul a b iha ihb =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      cases hb : tm c b with
      | none => simp [tm, ha, hb] at h
      | some B =>
        simp only [tm, ha, hb, Option.some.injEq] at h
        subst h
        exact approx_mul c hr (iha ha) (ihb hb)
  | neg a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.map_some, Option.some.injEq] at h
      subst h
      exact approx_neg c (iha ha)
  | inv a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact invT_sound c hr (iha ha) h
  | exp a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact expT_sound c hr (iha ha) h
  | log1p a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact log1pT_sound c hr (iha ha) h
  | log1pDiv a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact log1pDivT_sound c hr (iha ha) h
  | sin a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact sinT_sound c hr (iha ha) h
  | cos a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact cosT_sound c hr (iha ha) h
  | sinc a iha =>
    intro T h
    cases ha : tm c a with
    | none => simp [tm, ha] at h
    | some A =>
      simp only [tm, ha, Option.bind_some] at h
      exact sincT_sound c hr (iha ha) h
  | logC q lo hi =>
    intro T h
    exact logCT_sound c h
  | pi =>
    intro T h
    simp only [tm, Option.some.injEq] at h
    subst h
    exact approx_interval c hpi.1 hpi.2

end Sound

#print axioms tm_sound

end LeanExe.ProofKit.TaylorModel
