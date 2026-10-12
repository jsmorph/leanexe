import LeanExe.ProofKit.BesselAsym

/-!
Kernel checks that compare the approximations of `BesselChain` with fdlibm's rational functions
for `P` and `Q`.  In `z = 1/x²`, fdlibm's `pzero` and `pone` are `pFd R S x = 1 + R(z)/(1 + z S(z))`,
and `qzero` and `qone` are `qFd q₀ R S x = (R(z)/(1 + z S(z)) + q₀)/x` with `q₀ = -1/8` and `3/8`.

On a piece, multiplying by `x ^ (2d)` with `d = S.length` turns both into polynomials in `x`
(`revEven`), shifted to `h = x - c`.  The differences `A - pFd` and `B - qFd` are then quotients
`E/W` of polynomials in `h`, and `ratioCheck` accepts when, on each subinterval `[L/2^t, H/2^t]` of a
bisection, the bound `Σ |e_k| R ^ k` of `|E|` from its coefficients at the center is at most `ε`
times the lower bound `w₀ - R Σ |w_k| R ^ (k - 1)` of `W`.  The coefficients at the center are
integers: with `h = (M + Z)/2^(t+1)`, `2^((t+1) n) E(h)` is an integer polynomial in `Z` when `E`
has dyadic coefficients scaled to integers (`toInt`), so the kernel works with `Int` alone.  On `[X, ∞)` the same check runs in `t = 1/x`, where
`z = t ²` (`evenP`).
-/

namespace LeanExe.ProofKit.BesselRatio

open Set PolyBound PolyChecks PolyCalc BesselChain

/-- `Σ L_i x ^ (2 (d - i))`, which is `x ^ (2d) L(1/x²)` when `L` has at most `d + 1` terms. -/
def revEven : ℕ → List ℚ → List ℚ
  | _, [] => []
  | d, a :: L => addP (scaleP a (mono (2 * d))) (revEven (d - 1) L)

theorem eval_revEven (x : ℝ) (hx : x ≠ 0) :
    ∀ (L : List ℚ) (d : ℕ), L.length ≤ d + 1 → eval (revEven d L) x = x ^ (2 * d) * eval L (1 / x ^ 2)
  | [], d, _ => by simp [revEven]
  | [a], d, _ => by
    simp only [revEven, eval_addP, eval_scaleP, eval_mono, eval_cons, eval_nil]
    ring
  | a :: b :: L, d, h => by
    simp only [List.length_cons] at h
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [revEven, eval_addP, eval_scaleP, eval_mono, Nat.add_sub_cancel,
      eval_revEven x hx (b :: L) e (by simp only [List.length_cons]; omega)]
    simp only [eval_cons]
    field_simp
    ring

/-- `L(t²)`. -/
def evenP : List ℚ → List ℚ
  | [] => []
  | a :: L => a :: 0 :: evenP L

theorem eval_evenP (L : List ℚ) (t : ℝ) : eval (evenP L) t = eval L (t ^ 2) := by
  induction L with
  | nil => simp [evenP]
  | cons a L ih => simp only [evenP, eval_cons, ih]; push_cast; ring

/-! Integer polynomials and the bisection check. -/

/-- An integer polynomial as a `PolyBound` list. -/
def toQ (l : List ℤ) : List ℚ := l.map fun a => (a : ℚ)

theorem eval_toQ_cons (a : ℤ) (l : List ℤ) (x : ℝ) :
    eval (toQ (a :: l)) x = a + x * eval (toQ l) x := by
  simp [toQ]

theorem eval_toQ_nil (x : ℝ) : eval (toQ []) x = 0 := by simp [toQ]

/-- The sum of two integer polynomials. -/
def addI : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addI p q

theorem eval_addI (p q : List ℤ) (x : ℝ) :
    eval (toQ (addI p q)) x = eval (toQ p) x + eval (toQ q) x := by
  induction p generalizing q with
  | nil => simp [addI, toQ]
  | cons a p ih =>
    cases q with
    | nil => simp [addI, toQ]
    | cons b q =>
      simp only [addI, eval_toQ_cons, ih]
      push_cast
      ring

/-- `(M + X) q`. -/
def mulLinI (M : ℤ) (q : List ℤ) : List ℤ := addI (q.map fun a => M * a) (0 :: q)

theorem eval_map_mul (M : ℤ) (q : List ℤ) (x : ℝ) :
    eval (toQ (q.map fun a => M * a)) x = M * eval (toQ q) x := by
  induction q with
  | nil => simp [toQ]
  | cons a q ih =>
    simp only [List.map_cons, eval_toQ_cons, ih]
    push_cast
    ring

theorem eval_mulLinI (M : ℤ) (q : List ℤ) (x : ℝ) :
    eval (toQ (mulLinI M q)) x = (M + x) * eval (toQ q) x := by
  rw [mulLinI, eval_addI, eval_map_mul, eval_toQ_cons]
  push_cast
  ring

/-- `2 ^ (t n) p ((M + X)/2 ^ t)` for `p` with `n` coefficients, in integers. -/
def ishift (t : ℕ) (M : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => addI [a * 2 ^ (t * (p.length + 1))] (mulLinI M (ishift t M p))

theorem eval_ishift (t : ℕ) (M : ℤ) (p : List ℤ) (x : ℝ) :
    eval (toQ (ishift t M p)) x = 2 ^ (t * p.length) * eval (toQ p) ((M + x) / 2 ^ t) := by
  induction p with
  | nil => simp [ishift, toQ]
  | cons a p ih =>
    rw [ishift, eval_addI, eval_mulLinI, ih, eval_toQ_cons, eval_toQ_cons, eval_toQ_nil,
      mul_zero, add_zero, List.length_cons]
    push_cast
    have h2 : (2 : ℝ) ^ t ≠ 0 := by positivity
    rw [show t * (p.length + 1) = t * p.length + t by ring, pow_add]
    field_simp

/-- `Σ |a_k| R ^ k`. -/
def absSumI (R : ℕ) : List ℤ → ℕ
  | [] => 0
  | a :: p => a.natAbs + R * absSumI R p

theorem abs_eval_le_absSumI (R : ℕ) (q : List ℤ) (x : ℝ) (hx : |x| ≤ R) :
    |eval (toQ q) x| ≤ absSumI R q := by
  induction q with
  | nil => simp [toQ, absSumI]
  | cons a q ih =>
    have e : ((absSumI R (a :: q) : ℕ) : ℝ) = |(a : ℝ)| + R * (absSumI R q : ℝ) := by
      simp [absSumI, Nat.cast_natAbs, Int.cast_abs]
    rw [eval_toQ_cons, e]
    calc |(a : ℝ) + x * eval (toQ q) x| ≤ |(a : ℝ)| + |x| * |eval (toQ q) x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a : ℝ)| + R * (absSumI R q : ℝ) := by gcongr

theorem headD_sub_le (q : List ℤ) (R : ℕ) (Z : ℝ) (hZ : |Z| ≤ R) :
    ((q.headD 0 - R * absSumI R q.tail : ℤ) : ℝ) ≤ eval (toQ q) Z := by
  cases q with
  | nil => simp [toQ, absSumI]
  | cons a T =>
    simp only [List.headD_cons, List.tail_cons, eval_toQ_cons]
    have bT := abs_eval_le_absSumI R T Z hZ
    have h1 : |Z * eval (toQ T) Z| ≤ R * (absSumI R T : ℝ) := by
      rw [abs_mul]; exact mul_le_mul hZ bT (abs_nonneg _) (by positivity)
    have h2 := neg_abs_le (Z * eval (toQ T) Z)
    push_cast
    linarith

/-- One subinterval `[L/2^t, H/2^t]` of the check `|E|/2^sE ≤ (e/2^r) W/2^sW` with `W > 0`, from
the integer coefficients of `E` and `W` at its center. -/
def ratioPieceI (E W : List ℤ) (sE sW r e : ℕ) (L H : ℤ) (t : ℕ) : Bool :=
  let M := L + H
  let R := (H - L).toNat
  let Es := ishift (t + 1) M E
  let Ws := ishift (t + 1) M W
  let wl : ℤ := Ws.headD 0 - R * absSumI R Ws.tail
  decide (L ≤ H ∧ 0 < wl ∧
    (absSumI R Es : ℤ) * 2 ^ (sW + (t + 1) * W.length + r) ≤ e * wl * 2 ^ (sE + (t + 1) * E.length))

/-- The check on `[L/2^t, H/2^t]`, bisecting at most `d` times along each branch. -/
def ratioCheckI (E W : List ℤ) (sE sW r e : ℕ) : ℤ → ℤ → ℕ → ℕ → Bool
  | L, H, t, 0 => ratioPieceI E W sE sW r e L H t
  | L, H, t, d + 1 => ratioPieceI E W sE sW r e L H t ||
      (ratioCheckI E W sE sW r e (2 * L) (L + H) (t + 1) d &&
        ratioCheckI E W sE sW r e (L + H) (2 * H) (t + 1) d)

theorem ratioPieceI_sound (E W : List ℤ) (sE sW r e : ℕ) (L H : ℤ) (t : ℕ)
    (hp : ratioPieceI E W sE sW r e L H t = true) (h : ℝ) (hL : (L : ℝ) / 2 ^ t ≤ h)
    (hH : h ≤ (H : ℝ) / 2 ^ t) :
    0 < eval (toQ W) h ∧
      |eval (toQ E) h| / 2 ^ sE ≤ (e : ℝ) / 2 ^ r * (eval (toQ W) h / 2 ^ sW) := by
  simp only [ratioPieceI, decide_eq_true_eq] at hp
  obtain ⟨hLH, hpos, hle⟩ := hp
  set M := L + H
  set R := (H - L).toNat
  have hR : (R : ℝ) = H - L := by
    have : ((H - L).toNat : ℤ) = H - L := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  set Z := h * 2 ^ (t + 1) - M with hZ
  have hZR : |Z| ≤ R := by
    rw [hR, abs_le, hZ]
    have e1 : (L : ℝ) ≤ h * 2 ^ t := by rwa [div_le_iff₀ h2t] at hL
    have e2 : h * 2 ^ t ≤ H := by rwa [le_div_iff₀ h2t] at hH
    simp only [M]; push_cast; rw [pow_succ]
    constructor <;> nlinarith
  have hh : ((M : ℝ) + Z) / 2 ^ (t + 1) = h := by rw [hZ]; field_simp; ring
  have eE := eval_ishift (t + 1) M E Z
  have eW := eval_ishift (t + 1) M W Z
  rw [hh] at eE eW
  have bE := abs_eval_le_absSumI R (ishift (t + 1) M E) Z hZR
  set Ws := ishift (t + 1) M W
  have hWl : ((Ws.headD 0 - R * absSumI R Ws.tail : ℤ) : ℝ) ≤ eval (toQ Ws) Z :=
    headD_sub_le Ws R Z hZR
  have hpos' : (0 : ℝ) < ((Ws.headD 0 - R * absSumI R Ws.tail : ℤ) : ℝ) := by exact_mod_cast hpos
  have hle' : (absSumI R (ishift (t + 1) M E) : ℝ) * (2 ^ sW * 2 ^ ((t + 1) * W.length) * 2 ^ r) ≤
      (e : ℝ) * ((Ws.headD 0 - R * absSumI R Ws.tail : ℤ) : ℝ) * (2 ^ sE * 2 ^ ((t + 1) * E.length)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact_mod_cast hle
  have hWpos : 0 < eval (toQ W) h := by
    have : 0 < eval (toQ Ws) Z := lt_of_lt_of_le hpos' hWl
    rw [eW] at this
    exact pos_of_mul_pos_right this (by positivity)
  refine ⟨hWpos, ?_⟩
  have hE : |eval (toQ E) h| * 2 ^ ((t + 1) * E.length) ≤ (absSumI R (ishift (t + 1) M E) : ℝ) := by
    rw [eE, abs_mul, abs_of_pos (by positivity), mul_comm] at bE
    exact bE
  have hW : ((Ws.headD 0 - R * absSumI R Ws.tail : ℤ) : ℝ) ≤
      2 ^ ((t + 1) * W.length) * eval (toQ W) h := by rw [← eW]; exact hWl
  have p1 : (0 : ℝ) < 2 ^ sE := by positivity
  have p2 : (0 : ℝ) < 2 ^ sW := by positivity
  have p3 : (0 : ℝ) < 2 ^ r := by positivity
  have p4 : (0 : ℝ) < 2 ^ ((t + 1) * E.length) := by positivity
  have p5 : (0 : ℝ) < 2 ^ ((t + 1) * W.length) := by positivity
  rw [div_le_iff₀ p1]
  have key : |eval (toQ E) h| * 2 ^ ((t + 1) * E.length) * (2 ^ sW * 2 ^ ((t + 1) * W.length) * 2 ^ r) ≤
      (e : ℝ) * (2 ^ ((t + 1) * W.length) * eval (toQ W) h) * (2 ^ sE * 2 ^ ((t + 1) * E.length)) := by
    calc |eval (toQ E) h| * 2 ^ ((t + 1) * E.length) * (2 ^ sW * 2 ^ ((t + 1) * W.length) * 2 ^ r)
        ≤ (absSumI R (ishift (t + 1) M E) : ℝ) * (2 ^ sW * 2 ^ ((t + 1) * W.length) * 2 ^ r) := by
          gcongr
      _ ≤ (e : ℝ) * ((Ws.headD 0 - R * absSumI R Ws.tail : ℤ) : ℝ) *
            (2 ^ sE * 2 ^ ((t + 1) * E.length)) := by linarith
      _ ≤ (e : ℝ) * (2 ^ ((t + 1) * W.length) * eval (toQ W) h) * (2 ^ sE * 2 ^ ((t + 1) * E.length)) := by
          gcongr
  have e2 : (e : ℝ) / 2 ^ r * (eval (toQ W) h / 2 ^ sW) * 2 ^ sE =
      (e : ℝ) * (2 ^ ((t + 1) * W.length) * eval (toQ W) h) * (2 ^ sE * 2 ^ ((t + 1) * E.length)) /
        (2 ^ ((t + 1) * E.length) * (2 ^ sW * 2 ^ ((t + 1) * W.length) * 2 ^ r)) := by
    field_simp
  rw [e2, le_div_iff₀ (by positivity)]
  linarith

theorem ratioCheckI_sound (E W : List ℤ) (sE sW r e : ℕ) (d : ℕ) :
    ∀ (L H : ℤ) (t : ℕ), ratioCheckI E W sE sW r e L H t d = true → ∀ h : ℝ,
      (L : ℝ) / 2 ^ t ≤ h → h ≤ (H : ℝ) / 2 ^ t →
      0 < eval (toQ W) h ∧
        |eval (toQ E) h| / 2 ^ sE ≤ (e : ℝ) / 2 ^ r * (eval (toQ W) h / 2 ^ sW) := by
  induction d with
  | zero => exact fun L H t hc h h1 h2 => ratioPieceI_sound E W sE sW r e L H t hc h h1 h2
  | succ d ih =>
    intro L H t hc h h1 h2
    simp only [ratioCheckI, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨hl, hr⟩
    · exact ratioPieceI_sound E W sE sW r e L H t hc h h1 h2
    · have e2 : ∀ K : ℤ, ((2 * K : ℤ) : ℝ) / 2 ^ (t + 1) = (K : ℝ) / 2 ^ t := by
        intro K
        push_cast
        rw [pow_succ, mul_comm ((2 : ℝ) ^ t) 2]
        exact mul_div_mul_left _ _ two_ne_zero
      rcases le_total h (((L + H : ℤ) : ℝ) / 2 ^ (t + 1)) with hm' | hm'
      · exact ih (2 * L) (L + H) (t + 1) hl h (by rw [e2]; exact h1) hm'
      · exact ih (L + H) (2 * H) (t + 1) hr h hm' (by rw [e2]; exact h2)

/-- The integers `q 2^s` of a dyadic list. -/
def toInt (s : ℕ) (l : List ℚ) : List ℤ := l.map fun q => (q * 2 ^ s).num

/-- Every `q 2^s` is an integer. -/
def isScaled (s : ℕ) (l : List ℚ) : Bool := l.all fun q => (q * 2 ^ s).den == 1

theorem eval_toInt (s : ℕ) (l : List ℚ) (hl : isScaled s l = true) (x : ℝ) :
    eval (toQ (toInt s l)) x = 2 ^ s * eval l x := by
  induction l with
  | nil => simp [toInt, toQ]
  | cons a l ih =>
    simp only [isScaled, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hl
    have hl' : isScaled s l = true := by simpa [isScaled] using hl.2
    simp only [toInt, List.map_cons] at ih ⊢
    rw [eval_toQ_cons, ih hl', eval_cons]
    have ha : (((a * 2 ^ s).num : ℚ)) = a * 2 ^ s := Rat.coe_int_num_of_den_eq_one hl.1
    have ha' : (((a * 2 ^ s).num : ℤ) : ℝ) = (a : ℝ) * 2 ^ s := by
      have := congrArg (fun q : ℚ => (q : ℝ)) ha
      push_cast at this
      exact this
    rw [ha']
    ring

theorem ratioCheckI_eval (El Wl : List ℚ) (sE sW r e : ℕ) (L H : ℤ) (t n : ℕ)
    (hsE : isScaled sE El = true) (hsW : isScaled sW Wl = true)
    (hc : ratioCheckI (toInt sE El) (toInt sW Wl) sE sW r e L H t n = true) (h : ℝ)
    (hL : (L : ℝ) / 2 ^ t ≤ h) (hH : h ≤ (H : ℝ) / 2 ^ t) :
    0 < eval Wl h ∧ |eval El h| ≤ (e : ℝ) / 2 ^ r * eval Wl h := by
  have hk := ratioCheckI_sound _ _ sE sW r e n L H t hc h hL hH
  rw [eval_toInt sE El hsE, eval_toInt sW Wl hsW] at hk
  obtain ⟨h1, h2⟩ := hk
  have p1 : (0 : ℝ) < 2 ^ sE := by positivity
  have p2 : (0 : ℝ) < 2 ^ sW := by positivity
  refine ⟨pos_of_mul_pos_right h1 p2.le, ?_⟩
  rw [abs_mul, abs_of_pos p1] at h2
  have e1 : (2 : ℝ) ^ sE * |eval El h| / 2 ^ sE = |eval El h| := by field_simp
  have e2 : (2 : ℝ) ^ sW * eval Wl h / 2 ^ sW = eval Wl h := by field_simp
  rw [e1, e2] at h2
  exact h2

/-! fdlibm's functions and the comparisons. -/

/-- `1 + R(z)/(1 + z S(z))` with `z = 1/x²`: fdlibm's `pzero` and `pone` without rounding. -/
noncomputable def pFd (R S : List ℚ) (x : ℝ) : ℝ :=
  1 + eval R (1 / x ^ 2) / (1 + 1 / x ^ 2 * eval S (1 / x ^ 2))

/-- `(R(z)/(1 + z S(z)) + q₀)/x` with `z = 1/x²`: fdlibm's `qzero` and `qone` without rounding. -/
noncomputable def qFd (q₀ : ℚ) (R S : List ℚ) (x : ℝ) : ℝ :=
  (eval R (1 / x ^ 2) / (1 + 1 / x ^ 2 * eval S (1 / x ^ 2)) + q₀) / x

/-- `x ^ (2d) (1 + z S(z))` in `x - c`. -/
def sTilde (c : ℚ) (S : List ℚ) : List ℚ := shift c (revEven S.length (1 :: S))

/-- `x ^ (2d) R(z)` in `x - c`. -/
def rTilde (c : ℚ) (R S : List ℚ) : List ℚ := shift c (revEven S.length R)

/-- `A x ^ (2d) (1 + z S) - x ^ (2d) (1 + z S) - x ^ (2d) R` in `x - c`. -/
def pE (pc : Piece) (R S : List ℚ) : List ℚ :=
  subP (mulP pc.A (sTilde pc.c S)) (addP (sTilde pc.c S) (rTilde pc.c R S))

/-- `x B x ^ (2d) (1 + z S) - x ^ (2d) R - q₀ x ^ (2d) (1 + z S)` in `x - c`. -/
def qE (q₀ : ℚ) (pc : Piece) (R S : List ℚ) : List ℚ :=
  subP (mulP (mulP [pc.c, 1] pc.B) (sTilde pc.c S))
    (addP (rTilde pc.c R S) (scaleP q₀ (sTilde pc.c S)))

/-- `x x ^ (2d) (1 + z S)` in `x - c`. -/
def qW (pc : Piece) (S : List ℚ) : List ℚ := mulP [pc.c, 1] (sTilde pc.c S)

theorem eval_sTilde (c : ℚ) (S : List ℚ) (x : ℝ) (hx : x ≠ 0) :
    eval (sTilde c S) (x - c) = x ^ (2 * S.length) * (1 + 1 / x ^ 2 * eval S (1 / x ^ 2)) := by
  rw [sTilde, eval_shift, add_sub_cancel, eval_revEven x hx (1 :: S) S.length (by simp), eval_cons]
  push_cast
  ring

theorem eval_rTilde (c : ℚ) (R S : List ℚ) (hR : R.length ≤ S.length + 1) (x : ℝ) (hx : x ≠ 0) :
    eval (rTilde c R S) (x - c) = x ^ (2 * S.length) * eval R (1 / x ^ 2) := by
  rw [rTilde, eval_shift, add_sub_cancel, eval_revEven x hx R S.length hR]

theorem p_piece (pc : Piece) (R S : List ℚ) (hR : R.length ≤ S.length + 1) (sE sW r e : ℕ)
    (L H : ℤ) (t n : ℕ) (hsE : isScaled sE (pE pc R S) = true)
    (hsW : isScaled sW (sTilde pc.c S) = true)
    (hc : ratioCheckI (toInt sE (pE pc R S)) (toInt sW (sTilde pc.c S)) sE sW r e L H t n = true)
    (x : ℝ) (hL : (L : ℝ) / 2 ^ t ≤ x - pc.c) (hH : x - pc.c ≤ (H : ℝ) / 2 ^ t) (hx0 : 0 < x) :
    |pc.fA x - pFd R S x| ≤ (e : ℝ) / 2 ^ r := by
  have h := ratioCheckI_eval _ _ sE sW r e L H t n hsE hsW hc (x - pc.c) hL hH
  rw [pE, eval_subP, eval_mulP, eval_addP, eval_sTilde _ _ x hx0.ne',
    eval_rTilde _ _ _ hR x hx0.ne'] at h
  obtain ⟨hW, hE⟩ := h
  rw [Piece.fA, pFd]
  generalize (1 + 1 / x ^ 2 * eval S (1 / x ^ 2)) = D at hW hE ⊢
  have hXp : 0 < x ^ (2 * S.length) := by positivity
  generalize x ^ (2 * S.length) = Xp at hW hE hXp
  have hD : 0 < D := pos_of_mul_pos_right hW hXp.le
  generalize eval R (1 / x ^ 2) = rr at hE ⊢
  generalize eval pc.A (x - pc.c) = a at hE ⊢
  have hXD : 0 < Xp * D := mul_pos hXp hD
  rw [show a - (1 + rr / D) = (a * (Xp * D) - (Xp * D + Xp * rr)) / (Xp * D) by
    field_simp]
  rw [abs_div, abs_of_pos hXD, div_le_iff₀ hXD]
  exact hE

theorem q_piece (q₀ : ℚ) (pc : Piece) (R S : List ℚ) (hR : R.length ≤ S.length + 1)
    (sE sW r e : ℕ) (L H : ℤ) (t n : ℕ) (hsE : isScaled sE (qE q₀ pc R S) = true)
    (hsW : isScaled sW (qW pc S) = true)
    (hc : ratioCheckI (toInt sE (qE q₀ pc R S)) (toInt sW (qW pc S)) sE sW r e L H t n = true)
    (x : ℝ) (hL : (L : ℝ) / 2 ^ t ≤ x - pc.c) (hH : x - pc.c ≤ (H : ℝ) / 2 ^ t) (hx0 : 0 < x) :
    |pc.fB x - qFd q₀ R S x| ≤ (e : ℝ) / 2 ^ r := by
  have h := ratioCheckI_eval _ _ sE sW r e L H t n hsE hsW hc (x - pc.c) hL hH
  rw [qE, qW, eval_subP, eval_mulP, eval_mulP, eval_mulP, eval_addP, eval_scaleP,
    eval_sTilde _ _ x hx0.ne', eval_rTilde _ _ _ hR x hx0.ne'] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one, mul_one] at h
  obtain ⟨hW, hE⟩ := h
  have hcx : (pc.c : ℝ) + (x - pc.c) = x := by ring
  rw [hcx] at hW hE
  rw [Piece.fB, qFd]
  generalize (1 + 1 / x ^ 2 * eval S (1 / x ^ 2)) = D at hW hE ⊢
  have hXp : 0 < x ^ (2 * S.length) := by positivity
  generalize x ^ (2 * S.length) = Xp at hW hE hXp
  have hD : 0 < D := pos_of_mul_pos_right (pos_of_mul_pos_right hW hx0.le) hXp.le
  generalize eval R (1 / x ^ 2) = rr at hE ⊢
  generalize eval pc.B (x - pc.c) = b at hE ⊢
  have hXD : 0 < x * (Xp * D) := mul_pos hx0 (mul_pos hXp hD)
  rw [show b - (rr / D + q₀) / x = (x * b * (Xp * D) - (Xp * rr + q₀ * (Xp * D))) / (x * (Xp * D)) by
    field_simp]
  rw [abs_div, abs_of_pos hXD, div_le_iff₀ hXD]
  exact hE

/-- `1 + t² S(t²)`. -/
def sAsym (S : List ℚ) : List ℚ := 1 :: 0 :: evenP S

/-- `A (1 + t² S) - (1 + t² S) - R(t²)` in `t`. -/
def pEa (ap : AsymPiece) (R S : List ℚ) : List ℚ :=
  subP (mulP ap.A (sAsym S)) (addP (sAsym S) (evenP R))

/-- `B (1 + t² S) - t (R(t²) + q₀ (1 + t² S))` in `t`. -/
def qEa (q₀ : ℚ) (ap : AsymPiece) (R S : List ℚ) : List ℚ :=
  subP (mulP ap.B (sAsym S)) (mulP [0, 1] (addP (evenP R) (scaleP q₀ (sAsym S))))

theorem eval_sAsym (S : List ℚ) (t : ℝ) : eval (sAsym S) t = 1 + t ^ 2 * eval S (t ^ 2) := by
  simp only [sAsym, eval_cons, eval_evenP]
  push_cast
  ring

theorem p_asym (ap : AsymPiece) (R S : List ℚ) (sE sW r e : ℕ) (H : ℤ) (t n : ℕ)
    (hsE : isScaled sE (pEa ap R S) = true) (hsW : isScaled sW (sAsym S) = true)
    (hc : ratioCheckI (toInt sE (pEa ap R S)) (toInt sW (sAsym S)) sE sW r e 0 H t n = true)
    (x : ℝ) (hx0 : 0 < x) (hx : 1 / x ≤ (H : ℝ) / 2 ^ t) :
    |ap.fA x - pFd R S x| ≤ (e : ℝ) / 2 ^ r := by
  have h := ratioCheckI_eval _ _ sE sW r e 0 H t n hsE hsW hc (1 / x) (by push_cast; rw [zero_div]; positivity) hx
  rw [pEa, eval_subP, eval_mulP, eval_addP, eval_sAsym, eval_evenP] at h
  obtain ⟨hW, hE⟩ := h
  have hz : (1 / x) ^ 2 = 1 / x ^ 2 := by ring
  rw [hz] at hW hE
  rw [AsymPiece.fA, pFd]
  generalize (1 + 1 / x ^ 2 * eval S (1 / x ^ 2)) = D at hW hE ⊢
  generalize eval R (1 / x ^ 2) = rr at hE ⊢
  generalize eval ap.A (1 / x) = a at hE ⊢
  rw [show a - (1 + rr / D) = (a * D - (D + rr)) / D by field_simp]
  rw [abs_div, abs_of_pos hW, div_le_iff₀ hW]
  exact hE

theorem q_asym (q₀ : ℚ) (ap : AsymPiece) (R S : List ℚ) (sE sW r e : ℕ) (H : ℤ) (t n : ℕ)
    (hsE : isScaled sE (qEa q₀ ap R S) = true) (hsW : isScaled sW (sAsym S) = true)
    (hc : ratioCheckI (toInt sE (qEa q₀ ap R S)) (toInt sW (sAsym S)) sE sW r e 0 H t n = true)
    (x : ℝ) (hx0 : 0 < x) (hx : 1 / x ≤ (H : ℝ) / 2 ^ t) :
    |ap.fB x - qFd q₀ R S x| ≤ (e : ℝ) / 2 ^ r := by
  have h := ratioCheckI_eval _ _ sE sW r e 0 H t n hsE hsW hc (1 / x) (by push_cast; rw [zero_div]; positivity) hx
  rw [qEa, eval_subP, eval_mulP, eval_mulP, eval_addP, eval_scaleP, eval_sAsym, eval_evenP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_zero, zero_add, Rat.cast_one,
    mul_one] at h
  obtain ⟨hW, hE⟩ := h
  have hz : (1 / x) ^ 2 = 1 / x ^ 2 := by ring
  rw [hz] at hW hE
  rw [AsymPiece.fB, qFd]
  generalize (1 + 1 / x ^ 2 * eval S (1 / x ^ 2)) = D at hW hE ⊢
  generalize eval R (1 / x ^ 2) = rr at hE ⊢
  generalize eval ap.B (1 / x) = b at hE ⊢
  rw [show b - (rr / D + q₀) / x = (b * D - 1 / x * (rr + q₀ * D)) / D by field_simp]
  rw [abs_div, abs_of_pos hW, div_le_iff₀ hW]
  exact hE

#print axioms ratioCheckI_sound
#print axioms p_piece
#print axioms q_piece
#print axioms p_asym
#print axioms q_asym

end LeanExe.ProofKit.BesselRatio
