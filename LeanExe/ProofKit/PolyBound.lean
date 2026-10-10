import CodeLib.IEEE64.Roundoff
import Mathlib.Tactic

/-!
A bound on a polynomial with rational coefficients over a rational interval, checked by the
kernel.  `check p lo hi ε d` evaluates, over `ℚ`, the coefficients of `p` shifted to the center
`c` of `[lo, hi]` and accepts when `Σ |q k| h ^ k ≤ ε` for the half-width `h`.  Otherwise it
bisects the interval, at most `d` times along each branch.  `check_sound` turns an accepted check
into `|eval p x| ≤ ε` for every real `x` in the interval.  The computation uses structural
recursion only, so `decide +kernel` evaluates it.  `ratOfWord` gives the exact rational value of
a binary64 word, so a kernel's coefficients `value 0x...` enter a polynomial as `ratOfWord 0x...`.
-/

namespace LeanExe.ProofKit.PolyBound

/-- The real value at `x` of the polynomial with coefficients `p`, lowest degree first. -/
noncomputable def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * eval p x

/-- The sum of two polynomials. -/
def addP : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addP p q

/-- The product of a polynomial and a constant. -/
def scaleP (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => c * a :: scaleP c p

/-- The difference of two polynomials. -/
def subP (p q : List ℚ) : List ℚ := addP p (scaleP (-1) q)

/-- The product of `X + c` and a polynomial. -/
def mulLinear (c : ℚ) (q : List ℚ) : List ℚ := addP (scaleP c q) (0 :: q)

/-- The coefficients of `p (c + X)`. -/
def shift (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => addP [a] (mulLinear c (shift c p))

/-- The absolute value, written with one comparison so that the kernel evaluates it directly. -/
def qabs (a : ℚ) : ℚ := if a < 0 then -a else a

/-- `Σ |p k| h ^ k`. -/
def absSum (h : ℚ) : List ℚ → ℚ
  | [] => 0
  | a :: p => qabs a + h * absSum h p

/-- The bound from the coefficients at the center of `[lo, hi]`. -/
def pieceOk (p : List ℚ) (lo hi ε : ℚ) : Bool :=
  decide (absSum ((hi - lo) / 2) (shift ((lo + hi) / 2) p) ≤ ε)

/-- The bound on `[lo, hi]`, bisecting at most `d` times along each branch. -/
def check (p : List ℚ) (lo hi ε : ℚ) : Nat → Bool
  | 0 => pieceOk p lo hi ε
  | d + 1 => pieceOk p lo hi ε ||
      (check p lo ((lo + hi) / 2) ε d && check p ((lo + hi) / 2) hi ε d)

/-- The exact rational value of a binary64 word. -/
def ratOfWord (w : UInt64) : ℚ := (Wasm.IEEE64.scaledValue w : ℚ) / 2 ^ 1074

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : ℚ) (p : List ℚ) (x : ℝ) :
    eval (a :: p) x = (a : ℝ) + x * eval p x := rfl

theorem ratOfWord_cast (w : UInt64) : ((ratOfWord w : ℚ) : ℝ) = CodeLib.IEEE64.value w := by
  simp [ratOfWord, CodeLib.IEEE64.value]

theorem eval_addP (p q : List ℚ) (x : ℝ) : eval (addP p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [addP]
  | cons a p ih =>
    cases q with
    | nil => simp [addP]
    | cons b q =>
      simp only [addP, eval_cons, ih, Rat.cast_add]
      ring

theorem eval_scaleP (c : ℚ) (q : List ℚ) (x : ℝ) : eval (scaleP c q) x = c * eval q x := by
  induction q with
  | nil => simp [scaleP]
  | cons a q ih =>
    simp only [scaleP, eval_cons, ih, Rat.cast_mul]
    ring

theorem eval_subP (p q : List ℚ) (x : ℝ) : eval (subP p q) x = eval p x - eval q x := by
  simp only [subP, eval_addP, eval_scaleP, Rat.cast_neg, Rat.cast_one]
  ring

theorem eval_mulLinear (c : ℚ) (q : List ℚ) (x : ℝ) :
    eval (mulLinear c q) x = ((c : ℝ) + x) * eval q x := by
  simp only [mulLinear, eval_addP, eval_scaleP, eval_cons, Rat.cast_zero]
  ring

theorem eval_shift (c : ℚ) (p : List ℚ) (t : ℝ) : eval (shift c p) t = eval p (c + t) := by
  induction p with
  | nil => simp [shift]
  | cons a p ih =>
    simp only [shift, eval_addP, eval_mulLinear, ih, eval_cons, eval_nil]
    ring

theorem qabs_cast (a : ℚ) : ((qabs a : ℚ) : ℝ) = |(a : ℝ)| := by
  unfold qabs
  split_ifs with h
  · have h' : (a : ℝ) < 0 := by exact_mod_cast h
    rw [abs_of_neg h', Rat.cast_neg]
  · have h' : (0 : ℝ) ≤ a := by exact_mod_cast not_lt.mp h
    rw [abs_of_nonneg h']

theorem absSum_nonneg (h : ℚ) (hh : 0 ≤ h) (p : List ℚ) : 0 ≤ ((absSum h p : ℚ) : ℝ) := by
  induction p with
  | nil => simp [absSum]
  | cons a p ih =>
    simp only [absSum, Rat.cast_add, Rat.cast_mul, qabs_cast]
    have hh' : (0 : ℝ) ≤ h := by exact_mod_cast hh
    positivity

theorem abs_eval_le (h : ℚ) (hh : 0 ≤ h) (p : List ℚ) (t : ℝ) (ht : |t| ≤ h) :
    |eval p t| ≤ ((absSum h p : ℚ) : ℝ) := by
  induction p with
  | nil => simp [absSum]
  | cons a p ih =>
    simp only [eval_cons, absSum, Rat.cast_add, Rat.cast_mul, qabs_cast]
    have hs := absSum_nonneg h hh p
    calc |(a : ℝ) + t * eval p t| ≤ |(a : ℝ)| + |t| * |eval p t| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ |(a : ℝ)| + (h : ℝ) * ((absSum h p : ℚ) : ℝ) := by
          gcongr

theorem pieceOk_sound (p : List ℚ) (lo hi ε : ℚ) (hp : pieceOk p lo hi ε = true)
    (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) : |eval p x| ≤ ε := by
  have hq : absSum ((hi - lo) / 2) (shift ((lo + hi) / 2) p) ≤ ε := of_decide_eq_true hp
  have hle : (lo : ℝ) ≤ hi := hlo.trans hhi
  have hh : (0 : ℚ) ≤ (hi - lo) / 2 := by
    have : lo ≤ hi := by exact_mod_cast hle
    linarith
  have ht : |x - (((lo + hi) / 2 : ℚ) : ℝ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have he := abs_eval_le ((hi - lo) / 2) hh (shift ((lo + hi) / 2) p) _ ht
  rw [eval_shift, add_sub_cancel] at he
  exact he.trans (by exact_mod_cast hq)

theorem check_sound (p : List ℚ) (lo hi ε : ℚ) (d : Nat) (hc : check p lo hi ε d = true)
    (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) : |eval p x| ≤ ε := by
  induction d generalizing lo hi with
  | zero => exact pieceOk_sound p lo hi ε hc x hlo hhi
  | succ d ih =>
    simp only [check, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨hl, hr⟩
    · exact pieceOk_sound p lo hi ε hc x hlo hhi
    · rcases le_total x (((lo + hi) / 2 : ℚ) : ℝ) with hm | hm
      · exact ih lo ((lo + hi) / 2) hl hlo hm
      · exact ih ((lo + hi) / 2) hi hr hm hhi

#print axioms eval_addP
#print axioms eval_subP
#print axioms eval_shift
#print axioms abs_eval_le
#print axioms check_sound
#print axioms ratOfWord_cast

end LeanExe.ProofKit.PolyBound
