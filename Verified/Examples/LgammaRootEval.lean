import Verified.Examples.LgammaAccNorm
import Verified.Examples.TgammaExpr
import Verified.Examples.TgammaPolyLip
import Verified.Examples.LgammaAsymSeries

/-!
The tools for the polynomials of `Lgamma.accurate` about the negative zeros.  Each polynomial has
`N` double-double coefficients at `o` and `k` double coefficients after them, with a stride of 2.
The code evaluates the doubles with `Lgamma.polyD` at the high part `sh` of the argument, which
`polyD_eq` writes as an expression of `TgammaExpr` (`hornerE`), multiplies by `sh`, and passes the
product to `Lgamma.polyDD` as the low part of its top coefficient.  The exact Horner values of the
double-double part with that tail are the Horner values of the whole polynomial `cf` from step
`k` on (`horner_tail`), and the Horner values at `-w` are those of the coefficients `(-1)^j c j`
at `w` up to a sign (`horner_neg`), so interval enclosures on `[0, X]` bound them at arguments of
both signs.
-/

namespace Verified.Examples.LgammaRootEval
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD TgammaWords
  TgammaExpr LgammaPolyIv

set_option exponentiation.threshold 4096

/-- The expression of `Lgamma.polyD`'s Horner value after step `j`, with the coefficient `i` at
`o + 2 i`. -/
def hornerE (tab : Array UInt64) (o n : ℕ) : ℕ → FE
  | 0 => .const tab[o + 2 * (n - 1)]!
  | j + 1 => .add (.const tab[o + 2 * (n - 2 - j)]!) (.mul .var (hornerE tab o n j))

/-- **`polyD` is its Horner expression.** -/
theorem polyD_eq (tab : Array UInt64) (o n : UInt64) (hn1 : 1 ≤ n.toNat)
    (hon : o.toNat + 2 * n.toNat < 2 ^ 63) (x : Float) :
    Lgamma.polyD tab o n x = evalF (hornerE tab o.toNat n.toNat (n.toNat - 1)) x := by
  have hn := n.toNat_lt
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hn1' : (1 : UInt64) ≤ n := by
    rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
  have hcnt : n - 1 = UInt64.ofNat (n.toNat - 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ hn1', UInt64.toNat_ofNat_of_lt' (by omega)]
    simp only [UInt64.reduceToNat]
  obtain ⟨h0, -⟩ := idx_top o n hn1 hon
  unfold Lgamma.polyD
  have key : ∀ m, m + 1 ≤ n.toNat →
      LeanExe.loop (UInt64.ofNat m) (entry tab (o + 2 * (n - 1)))
        (fun j ch => entry tab (o + 2 * (n - 2 - j)) + x * ch) =
      evalF (hornerE tab o.toNat n.toNat m) x := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [show (UInt64.ofNat 0) = 0 from rfl, loop_zero]
      simp only [hornerE, evalF]
      exact entry_eq _ _ _ h0
    | succ m ih =>
      intro hm
      rw [loop_succ m (by omega), ih (by omega)]
      simp only [hornerE, evalF]
      rw [entry_eq _ _ _ (idx o n m (by omega) hon).1]
  have h := key (n.toNat - 1) (by omega)
  rw [← hcnt] at h
  exact h

/-- The real value of the Horner expression is the Horner value of the coefficients. -/
theorem evalR_hornerE (tab : Array UInt64) (o n : ℕ) (v : ℝ) :
    ∀ m, evalR (hornerE tab o n m) v =
      horner (fun i => (PolyBound.ratOfWord tab[o + 2 * i]! : ℝ)) n 0 v m := by
  intro m
  induction m with
  | zero => simp [hornerE, evalR, horner]
  | succ m ih => simp only [hornerE, evalR, horner, ih]

/-- The coefficients of a root polynomial: `N` double-double pairs at `o`, then `k` doubles. -/
def cf (tab : Array UInt64) (o N : ℕ) (j : ℕ) : ℚ :=
  if j < N then cq tab o j else PolyBound.ratOfWord tab[o + 2 * N + 2 * (j - N)]!

/-- The coefficients of `p (-w)`. -/
def cfNeg (tab : Array UInt64) (o N : ℕ) (j : ℕ) : ℚ := (-1) ^ j * cf tab o N j

/-- The Horner values with the coefficients `(-1)^j c j` at `w` are those of `c` at `-w`, up to
the sign `(-1)^(N - 1 - m)`. -/
theorem horner_neg (c : ℕ → ℝ) (N : ℕ) (w : ℝ) :
    ∀ m, m + 1 ≤ N →
      horner (fun j => (-1) ^ j * c j) N 0 w m = (-1) ^ (N - 1 - m) * horner c N 0 (-w) m := by
  intro m
  induction m with
  | zero => intro _; simp [horner]
  | succ m ih =>
    intro hm
    simp only [horner]
    rw [ih (by omega)]
    have e : N - 1 - m = (N - 2 - m) + 1 := by omega
    rw [show N - 1 - (m + 1) = N - 2 - m by omega, e, pow_succ]
    ring

/-- The tail `Q` of a root polynomial at `s`: the Horner value of its `k` doubles. -/
noncomputable def tailQ (tab : Array UInt64) (o N k : ℕ) (s : ℝ) : ℝ :=
  horner (fun i => (PolyBound.ratOfWord tab[o + 2 * N + 2 * i]! : ℝ)) k 0 s (k - 1)

/-- The Horner values of the whole polynomial at the steps of its tail. -/
theorem horner_cf_tail (tab : Array UInt64) (o N k : ℕ) (hk : 1 ≤ k) (s : ℝ) :
    ∀ j, j + 1 ≤ k → horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s j =
      horner (fun i => (PolyBound.ratOfWord tab[o + 2 * N + 2 * i]! : ℝ)) k 0 s j := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [horner, cf]
    rw [ite_eq_right (by omega), show N + k - 1 - N = k - 1 by omega]
  | succ j ih =>
    intro hj
    simp only [horner]
    rw [ih (by omega)]
    simp only [cf]
    rw [ite_eq_right (by omega), show N + k - 2 - j - N = k - 2 - j by omega]

/-- **The tail**: with `L = s Q (s)`, the Horner values of the double-double part are those of
the whole polynomial `k` steps later. -/
theorem horner_tail (tab : Array UInt64) (o' : UInt64) (o N k : ℕ) (ho : o'.toNat = o)
    (hk : 1 ≤ k) (hf : ∀ i < N, Wasm.IEEE64.isFinite tab[o + 2 * i]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * i + 1]! = true) (s : ℝ) :
    ∀ m, m + 1 ≤ N → horner (cDD tab o') N (s * tailQ tab o N k s) s m =
      horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s (m + k) := by
  have hc : ∀ i < N, cDD tab o' i = (cf tab o N i : ℝ) := fun i hi => by
    rw [cDD_rat tab o' i (by rw [ho]; exact (hf i hi).1) (by rw [ho]; exact (hf i hi).2), ho]
    simp only [cf, ite_eq_left hi, cq]
  intro m
  induction m with
  | zero =>
    intro hN
    have ht := horner_cf_tail tab o N k hk s (k - 1) (by omega)
    rw [show 0 + k = (k - 1) + 1 by omega]
    simp only [horner]
    rw [ht, hc (N - 1) (by omega), show N + k - 2 - (k - 1) = N - 1 by omega, tailQ]
  | succ m ih =>
    intro hm
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [horner]
    rw [ih (by omega)]
    try rw [hc (N - 2 - m) (by omega), show N + k - 2 - (m + k) = N - 2 - m by omega]

/-- The larger magnitude of the enclosure of step `j`. -/
def encl (c : ℕ → ℚ) (NK : ℕ) (a b : ℚ) (j : ℕ) : ℚ :=
  max (PolyBound.qabs (hornerIv c NK a b j).1) (PolyBound.qabs (hornerIv c NK a b j).2)

/-- The checks of `polyDD_steps` on `P` subintervals of `[0, X]` with the coefficients `c` of the
whole polynomial: step `m` of the double-double part is step `m + k` of the whole. -/
def pieceOk (tab : Array UInt64) (o N k P : ℕ) (c : ℕ → ℚ) (X Xl : ℚ) (E Λ K : List ℚ) : Bool :=
  (List.range P).all fun p => (List.range (N - 1)).all fun m =>
    decide (encl c (N + k) (X * p / P) (X * (p + 1) / P) (m + k) + E.getD m 0 + Λ.getD m 0 ≤
      K.getD m 0) &&
    decide ((encl c (N + k) (X * p / P) (X * (p + 1) / P) (m + k) + E.getD m 0 + Λ.getD m 0) *
        (X * (p + 1) / P + Xl) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]!))

/-- The conditions of `polyDD_steps` for a root polynomial at arguments in `[-Xn, Xp]`. -/
def rootIvOk (tab : Array UInt64) (o N k P : ℕ) (Xp Xn Xh Xl : ℚ) (C Cl E Λ K : List ℚ) : Bool :=
  decide (0 < P) && decide (0 ≤ Xp) && decide (0 ≤ Xn) && decide (Xh + Xl ≤ 1) &&
  (List.range N).all (fun j => Wasm.IEEE64.isFinite tab[o + 2 * j]! &&
    Wasm.IEEE64.isFinite tab[o + 2 * j + 1]! &&
    decide (PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * j]!) ≤ C.getD j 0) &&
    decide (PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * j + 1]!) ≤ Cl.getD j 0) &&
    decide (C.getD j 0 ≤ 2 ^ 797) && decide (Cl.getD j 0 ≤ 2 ^ 797)) &&
  (List.range (N - 1)).all (fun m =>
    decide (K.getD m 0 ≤ 2 ^ 797) && decide (Λ.getD m 0 ≤ 2 ^ 797) &&
    decide ((Xh + Xl) * E.getD m 0 + LgammaSinAccKern.epsQ Xh Xl (K.getD m 0) (Λ.getD m 0)
      (C.getD (N - 2 - m) 0) (Cl.getD (N - 2 - m) 0) ≤ E.getD (m + 1) 0) &&
    decide (LgammaSinAccKern.growQ Xh Xl (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0)
      (Cl.getD (N - 2 - m) 0) ≤ Λ.getD (m + 1) 0)) &&
  pieceOk tab o N k P (cf tab o N) Xp Xl E Λ K && pieceOk tab o N k P (cfNeg tab o N) Xn Xl E Λ K

/-- One piece's enclosure bounds the Horner value of step `j` at `v` in `[0, X]`. -/
theorem piece_bound (c : ℕ → ℚ) (NK P : ℕ) (X : ℚ) (hP : 0 < P) (v : ℝ) (hv0 : 0 ≤ v)
    (hvX : v ≤ X) (j : ℕ) (hj : j + 1 ≤ NK) :
    ∃ p < P, |horner (fun i => (c i : ℝ)) NK 0 v j| ≤
      (encl c NK (X * p / P) (X * (p + 1) / P) j : ℝ) ∧ v ≤ (X : ℝ) * (p + 1) / P := by
  obtain ⟨p, hp, hpa, hpb⟩ := piece_cover (X : ℝ) P v hv0 P hP
    (by rw [mul_div_assoc, div_self (by exact_mod_cast hP.ne'), mul_one]; exact hvX)
  have hX0 : (0 : ℚ) ≤ X := by exact_mod_cast hv0.trans hvX
  obtain ⟨h1, h2⟩ := horner_iv (fun i => (c i : ℝ)) c NK (fun _ _ => rfl) (X * p / P)
    (X * (p + 1) / P) (by positivity) v (by push_cast; exact hpa) (by push_cast; exact hpb) j hj
  refine ⟨p, hp, ?_, hpb⟩
  set I := hornerIv c NK (X * p / P) (X * (p + 1) / P) j
  have e : ((encl c NK (X * p / P) (X * (p + 1) / P) j : ℚ) : ℝ) = max |(I.1 : ℝ)| |(I.2 : ℝ)| := by
    simp only [encl, I]
    push_cast
    simp only [TgammaExpr.qabs_cast]
  rw [e, abs_le]
  constructor
  · have := neg_abs_le (I.1 : ℝ)
    have := le_max_left |(I.1 : ℝ)| |(I.2 : ℝ)|
    linarith
  · have := le_abs_self (I.2 : ℝ)
    have := le_max_right |(I.1 : ℝ)| |(I.2 : ℝ)|
    linarith

/-- **The checks at one argument** `s` in `[-Xn, Xp]`, of either sign. -/
theorem root_iv_at (tab : Array UInt64) (o' : UInt64) (o N k P : ℕ) (ho : o'.toNat = o)
    (hk : 1 ≤ k) (Xp Xn Xl : ℚ) (E Λ K : List ℚ) (hE0 : ∀ m, 0 ≤ E.getD m 0)
    (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0) (hP : 0 < P)
    (hf : ∀ i < N, Wasm.IEEE64.isFinite tab[o + 2 * i]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * i + 1]! = true)
    (hpos : pieceOk tab o N k P (cf tab o N) Xp Xl E Λ K = true)
    (hneg : pieceOk tab o N k P (cfNeg tab o N) Xn Xl E Λ K = true)
    (s : ℝ) (hs1 : -(Xn : ℝ) ≤ s) (hs2 : s ≤ Xp) (xh : ℝ) (hxh : |xh| ≤ |s| + Xl) :
    ∀ m, m + 2 ≤ N →
      |horner (cDD tab o') N (s * tailQ tab o N k s) s m| + (E.getD m 0 : ℝ) +
          (Λ.getD m 0 : ℝ) ≤ (K.getD m 0 : ℝ) ∧
      (|horner (cDD tab o') N (s * tailQ tab o N k s) s m| + (E.getD m 0 : ℝ) +
          (Λ.getD m 0 : ℝ)) * |xh| * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |((PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]! : ℚ) : ℝ)| := by
  intro m hm
  rw [horner_tail tab o' o N k ho hk hf s m (by omega)]
  have hE' : (0 : ℝ) ≤ E.getD m 0 := Rat.cast_nonneg.mpr (hE0 m)
  have hΛ' : (0 : ℝ) ≤ Λ.getD m 0 := Rat.cast_nonneg.mpr (hΛ0 m)
  -- the bound `B` of the subinterval and its right end `b`
  obtain ⟨B, b, hB, hb, hk', hd'⟩ : ∃ B b : ℝ,
      |horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s (m + k)| ≤ B ∧ |s| ≤ b ∧
      B + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ) ≤ (K.getD m 0 : ℝ) ∧
      (B + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ)) * (b + Xl) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |((PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]! : ℚ) : ℝ)| := by
    rcases le_total 0 s with h0 | h0
    · obtain ⟨p, hp, hB, hb⟩ := piece_bound (cf tab o N) (N + k) P Xp hP s h0 hs2 (m + k)
        (by omega)
      simp only [pieceOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
        at hpos
      obtain ⟨hk1, hd1⟩ := hpos p hp m (by omega)
      have hk1' := (Rat.cast_le (K := ℝ)).mpr hk1
      have hd1' := (Rat.cast_le (K := ℝ)).mpr hd1
      push_cast at hk1' hd1'
      simp only [TgammaExpr.qabs_cast] at hd1'
      exact ⟨_, _, hB, by rw [abs_of_nonneg h0]; exact hb, hk1', hd1'⟩
    · have hw0 : 0 ≤ -s := by linarith
      obtain ⟨p, hp, hB, hb⟩ := piece_bound (cfNeg tab o N) (N + k) P Xn hP (-s) hw0
        (by linarith) (m + k) (by omega)
      have hn := horner_neg (fun j => (cf tab o N j : ℝ)) (N + k) (-s) (m + k) (by omega)
      simp only [neg_neg] at hn
      have hc : (fun i => ((cfNeg tab o N i : ℚ) : ℝ)) = (fun j => (-1) ^ j * (cf tab o N j : ℝ)) := by
        funext i; simp only [cfNeg]; push_cast; ring
      rw [hc, hn, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at hB
      simp only [pieceOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
        at hneg
      obtain ⟨hk1, hd1⟩ := hneg p hp m (by omega)
      have hk1' := (Rat.cast_le (K := ℝ)).mpr hk1
      have hd1' := (Rat.cast_le (K := ℝ)).mpr hd1
      push_cast at hk1' hd1'
      simp only [TgammaExpr.qabs_cast] at hd1'
      exact ⟨_, _, hB, by rw [abs_of_nonpos h0]; exact hb, hk1', hd1'⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hB
  have hxb : |xh| ≤ b + Xl := by linarith
  have hS := mul_le_mul (show |horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s (m + k)| +
      (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ) ≤ B + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ) by linarith)
    hxb (abs_nonneg _) (by linarith)
  have h3 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
  exact ⟨by linarith, by linarith⟩

/-- The check that the last Horner value of `c` lies in `[lo, hi]` on `[0, X]`. -/
def rangeOk (c : ℕ → ℚ) (NK P : ℕ) (X lo hi : ℚ) : Bool :=
  (List.range P).all fun p =>
    decide (lo ≤ (hornerIv c NK (X * p / P) (X * (p + 1) / P) (NK - 1)).1) &&
    decide ((hornerIv c NK (X * p / P) (X * (p + 1) / P) (NK - 1)).2 ≤ hi)

theorem range_at (c : ℕ → ℚ) (NK P : ℕ) (X lo hi : ℚ) (hP : 0 < P) (hNK : 1 ≤ NK)
    (hok : rangeOk c NK P X lo hi = true) (v : ℝ) (hv0 : 0 ≤ v) (hvX : v ≤ X) :
    (lo : ℝ) ≤ horner (fun i => (c i : ℝ)) NK 0 v (NK - 1) ∧
      horner (fun i => (c i : ℝ)) NK 0 v (NK - 1) ≤ hi := by
  simp only [rangeOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨p, hp, hpa, hpb⟩ := piece_cover (X : ℝ) P v hv0 P hP
    (by rw [mul_div_assoc, div_self (by exact_mod_cast hP.ne'), mul_one]; exact hvX)
  have hX0 : (0 : ℚ) ≤ X := by exact_mod_cast hv0.trans hvX
  obtain ⟨h1, h2⟩ := horner_iv (fun i => (c i : ℝ)) c NK (fun _ _ => rfl) (X * p / P)
    (X * (p + 1) / P) (by positivity) v (by push_cast; exact hpa) (by push_cast; exact hpb) (NK - 1)
    (by omega)
  obtain ⟨h3, h4⟩ := hok p hp
  exact ⟨le_trans (by exact_mod_cast h3) h1, le_trans h2 (by exact_mod_cast h4)⟩

/-- **The range of a root polynomial** on `[-Xn, Xp]`. -/
theorem root_range (tab : Array UInt64) (o N k P : ℕ) (Xp Xn lo hi : ℚ) (hP : 0 < P) (hNK : 1 ≤ N + k)
    (hpos : rangeOk (cf tab o N) (N + k) P Xp lo hi = true)
    (hneg : rangeOk (cfNeg tab o N) (N + k) P Xn lo hi = true) (s : ℝ) (hs1 : -(Xn : ℝ) ≤ s)
    (hs2 : s ≤ Xp) :
    (lo : ℝ) ≤ horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s (N + k - 1) ∧
      horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s (N + k - 1) ≤ hi := by
  rcases le_total 0 s with h0 | h0
  · exact range_at _ _ P Xp lo hi hP hNK hpos s h0 hs2
  · have h := range_at _ _ P Xn lo hi hP hNK hneg (-s) (by linarith) (by linarith)
    have hc : (fun i => ((cfNeg tab o N i : ℚ) : ℝ)) = (fun j => (-1) ^ j * (cf tab o N j : ℝ)) := by
      funext i; simp only [cfNeg]; push_cast; ring
    rw [hc, horner_neg (fun j => (cf tab o N j : ℝ)) (N + k) (-s) (N + k - 1) (by omega),
      neg_neg, show N + k - 1 - (N + k - 1) = 0 by omega, pow_zero, one_mul] at h
    exact h

/-- The last Horner value of `cf` is the polynomial of `LgammaApprox.rootPoly`'s form. -/
theorem horner_cf_eval (tab : Array UInt64) (o N k : ℕ) (hNK : 1 ≤ N + k)
    (hf : ∀ i < N, Wasm.IEEE64.isFinite tab[o + 2 * i]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * i + 1]! = true) (s : ℝ) :
    horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 s (N + k - 1) =
      PolyBound.eval (LgammaApprox.ddCoeffs tab o N ++ LgammaApprox.coeffs tab (o + 2 * N) 2 k) s := by
  rw [horner_eval _ (N + k) hNK, zero_mul, add_zero, TgammaWords.eval_append,
    show LgammaApprox.ddCoeffs tab o N = (List.range N).map (fun j =>
      LgammaApprox.q tab (o + 2 * j) + LgammaApprox.q tab (o + 2 * j + 1)) from rfl,
    show LgammaApprox.coeffs tab (o + 2 * N) 2 k = (List.range k).map (fun j =>
      LgammaApprox.q tab (o + 2 * N + 2 * j)) from rfl,
    TgammaWords.eval_map_range, TgammaWords.eval_map_range, Finset.sum_range_add,
    List.length_map, List.length_range, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [cf, ite_eq_left hj, cq, LgammaApprox.q]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [cf, ite_eq_right (show ¬ (N + j < N) by omega), LgammaApprox.q,
      show N + j - N = j by omega, pow_add]
    ring

#print axioms root_range
#print axioms horner_cf_eval

#print axioms root_iv_at

set_option maxHeartbeats 2000000 in
/-- **The double-double part of a root polynomial** with its double tail `l`: `polyDD` at
`s = xh + xl` in `[-Xn, Xp]` within `E (N - 1)` of `horner cf` at the last step, given `l` within
`el` of `s Q (s)`. -/
theorem root_dd (hF : FmaSpec.FmaNearest) (tab : Array UInt64) (o N k P : ℕ) (Xp Xn Xh Xl : ℚ)
    (C Cl E Λ K : List ℚ) (hok : rootIvOk tab o N k P Xp Xn Xh Xl C Cl E Λ K = true)
    (hE0 : ∀ m, 0 ≤ E.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0)
    (o' n' : UInt64) (ho : o'.toNat = o) (hn : n'.toNat = N) (hN1 : 1 ≤ N) (hk : 1 ≤ k)
    (hon : o + 2 * N < 2 ^ 63) (xh xl l : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hXh : |value xh.toBits| ≤ (Xh : ℝ)) (hXl : |value xl.toBits| ≤ (Xl : ℝ))
    (hs1 : -(Xn : ℝ) ≤ value xh.toBits + value xl.toBits)
    (hs2 : value xh.toBits + value xl.toBits ≤ Xp)
    (el Lb tB : ℝ) (hl : Finite l.toBits)
    (hlL : |value l.toBits - (value xh.toBits + value xl.toBits) *
      tailQ tab o N k (value xh.toBits + value xl.toBits)| ≤ el)
    (hLb : |value l.toBits| ≤ Lb)
    (htop : Lb ≤ |((PolyBound.ratOfWord tab[o + 2 * (N - 1)]! : ℚ) : ℝ)|)
    (htB : Lb ≤ tB) (htBs : tB ≤ 2 ^ 797)
    (hEi : el + (tB + (Cl.getD (N - 1) 0 : ℝ)) / 2 ^ 53 ≤ E.getD 0 0)
    (hΛi : (tB + (Cl.getD (N - 1) 0 : ℝ)) * (1 + 1 / 2 ^ 53) ≤ Λ.getD 0 0) :
    Finite (Lgamma.polyDD tab o' n' xh xl l).1.toBits ∧
      Finite (Lgamma.polyDD tab o' n' xh xl l).2.toBits ∧
      |value (Lgamma.polyDD tab o' n' xh xl l).1.toBits +
          value (Lgamma.polyDD tab o' n' xh xl l).2.toBits -
          horner (fun j => (cf tab o N j : ℝ)) (N + k) 0 (value xh.toBits + value xl.toBits)
            (N - 1 + k)| ≤ (E.getD (N - 1) 0 : ℝ) ∧
      |value (Lgamma.polyDD tab o' n' xh xl l).2.toBits| ≤ (Λ.getD (N - 1) 0 : ℝ) := by
  simp only [rootIvOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hP, -⟩, -⟩, hX1⟩, hw⟩, hs⟩, hpos⟩, hneg⟩ := hok
  have hfin : ∀ i < N, Wasm.IEEE64.isFinite tab[o + 2 * i]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * i + 1]! = true := fun i hi => (hw i hi).1.1.1.1
  have hval : ∀ i < N, value (Float.ofBits tab[o + 2 * i]!).toBits =
      ((PolyBound.ratOfWord tab[o + 2 * i]! : ℚ) : ℝ) ∧
      value (Float.ofBits tab[o + 2 * i + 1]!).toBits =
        ((PolyBound.ratOfWord tab[o + 2 * i + 1]! : ℚ) : ℝ) := fun i hi =>
    ⟨ofBits_value _ (hfin i hi).1, ofBits_value _ (hfin i hi).2⟩
  set sv := value xh.toBits + value xl.toBits with hsv
  have hxb : |value xh.toBits| ≤ |sv| + Xl := by
    have h1 := abs_sub sv (value xl.toBits)
    rw [hsv, add_sub_cancel_right] at h1
    rw [hsv]
    linarith
  have hI := root_iv_at tab o' o N k P ho hk Xp Xn Xl E Λ K hE0 hΛ0 hP hfin hpos hneg sv hs1 hs2
    _ hxb
  obtain ⟨h1, h2, h3, h4⟩ := LgammaPolyDDSteps.polyDD_steps hF tab o' n' xh xl l (by rw [hn]; exact hN1)
    (by rw [ho, hn]; exact hon)
    (fun i hi => by rw [ho]; rw [hn] at hi; exact ofBits_finite _ (hfin i hi).1)
    (fun i hi => by rw [ho]; rw [hn] at hi; exact ofBits_finite _ (hfin i hi).2)
    (Xh : ℝ) (Xl : ℝ) (sv * tailQ tab o N k sv) el Lb tB (fun i => (C.getD i 0 : ℝ))
    (fun i => (Cl.getD i 0 : ℝ))
    (fun i => (E.getD i 0 : ℝ)) (fun i => (Λ.getD i 0 : ℝ)) (fun i => (K.getD i 0 : ℝ))
    hxh hxl hXh hXl (by exact_mod_cast hX1)
    (fun i hi => by
      rw [ho]; rw [hn] at hi
      rw [(hval i hi).1, ← TgammaExpr.qabs_cast]
      exact_mod_cast (hw i hi).1.1.1.2)
    (fun i hi => by
      rw [ho]; rw [hn] at hi
      rw [(hval i hi).2, ← TgammaExpr.qabs_cast]
      exact_mod_cast (hw i hi).1.1.2)
    (fun i hi => by
      rw [hn] at hi
      exact ⟨by exact_mod_cast (hw i hi).1.2, by exact_mod_cast (hw i hi).2⟩)
    hl hlL hLb
    (by rw [ho, hn, (hval (N - 1) (by omega)).1]; exact hLb.trans htop)
    (Or.inl htB) htBs
    (by rw [hn]; exact hEi)
    (by rw [hn]; exact hΛi)
    (fun m hm => by rw [hn] at hm ⊢; exact (hI m hm).1)
    (fun m hm => by
      rw [hn] at hm
      exact ⟨by exact_mod_cast (hs m (by omega)).1.1.1,
        by exact_mod_cast (hs m (by omega)).1.1.2⟩)
    (fun m hm => by
      rw [hn] at hm ⊢
      rw [ho, (hval (N - 2 - m) (by omega)).1]
      exact (hI m hm).2)
    (fun m hm => by
      rw [hn] at hm ⊢
      have := (hs m (by omega)).1.2
      have hc : ((((Xh + Xl) * E.getD m 0 + LgammaSinAccKern.epsQ Xh Xl (K.getD m 0) (Λ.getD m 0)
          (C.getD (N - 2 - m) 0) (Cl.getD (N - 2 - m) 0) : ℚ)) : ℝ) ≤ (E.getD (m + 1) 0 : ℝ) := by
        exact_mod_cast this
      rw [LgammaSinAccKern.epsS_cast]
      push_cast at hc ⊢
      exact hc)
    (fun m hm => by
      rw [hn] at hm ⊢
      have := (hs m (by omega)).2
      have hc : ((LgammaSinAccKern.growQ Xh Xl (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0)
          (Cl.getD (N - 2 - m) 0) : ℚ) : ℝ) ≤ (Λ.getD (m + 1) 0 : ℝ) := by exact_mod_cast this
      rw [LgammaSinAccKern.growS_cast]
      exact hc)
  rw [hn, horner_tail tab o' o N k ho hk hfin sv (N - 1) (by omega)] at h3
  rw [hn] at h4
  exact ⟨h1, h2, h3, h4⟩

#print axioms root_dd

#print axioms polyD_eq
#print axioms evalR_hornerE
#print axioms horner_neg
#print axioms horner_tail

end Verified.Examples.LgammaRootEval
