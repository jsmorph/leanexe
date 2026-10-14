import Verified.Examples.LgammaPolyFst
import Verified.Examples.LgammaPolyIv
import Verified.Examples.TgammaAcc2

/-!
The polynomials of `Lgamma.accurate` below 3.75 by `Lgamma.polyDDDFst` at a double point
`|x| ≤ 1/4`: the 34 pairs at offset 0 of `Lgamma.accurateTable` (`x ↦ log Γ (1 + x)/x`) and the 30
pairs at offset 68 (`d ↦ log Γ (3/2 + d)`).  `LgammaPolyFst.polyFst_damped_core` needs a bound on the
Horner value of each step at the point, which the sums of the coefficients' magnitudes give
(`hbT`), and the kernel checks its conditions with rationals (`accOk`, `acc_gen`).  The coefficient
`ψ (3/2) ≈ 0.0365` of the second polynomial is smaller than the product that `fastSum` adds to it,
so its first 28 pairs go through `acc_gen` and its last two steps through `TgammaAcc2.fts_approx`.
-/

namespace Verified.Examples.LgammaAccPoly
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD TgammaWords
  LgammaPolyIv

set_option exponentiation.threshold 4096

/-- The bound of the Horner value of step `m` at `|x| ≤ X` by the magnitudes of the coefficients. -/
def hbT (tab : Array UInt64) (o N : ℕ) (X : ℚ) : ℕ → ℚ
  | 0 => PolyBound.qabs (cq tab o (N - 1))
  | m + 1 => PolyBound.qabs (cq tab o (N - 2 - m)) + X * hbT tab o N X m

/-- `polyLow`, `polyEps`, and `polyGrow` of `TgammaPolyDDD` on rationals. -/
def lowQ (X M Cl Λ : ℚ) : ℚ := Cl + Λ * X * (1 + 1 / 2 ^ 51) + (M + 1) * X / 2 ^ 52 + 1 / 2 ^ 1071

def epsQ (X M Ch Cl Λ : ℚ) : ℚ :=
  (3 * (Λ * X) + (M + 1) * X / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 +
    (3 * lowQ X M Cl Λ + 2 * (Ch + M + 1) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53

def growQ (M Ch Cl Λ : ℚ) : ℚ :=
  Λ / 2 ^ 49 + (Cl + (M + 1) / 2 ^ 52 + 1 / 2 ^ 1071) * (1 + 1 / 2 ^ 51) +
    2 * (Ch + M + 1) / 2 ^ 51 + 1 / 2 ^ 1073

theorem eps_cast (X M Ch Cl Λ : ℚ) :
    polyEps (X : ℝ) M Ch Cl Λ = ((epsQ X M Ch Cl Λ : ℚ) : ℝ) := by
  simp only [polyEps, epsQ, polyLow, lowQ]; push_cast; ring

theorem grow_cast (M Ch Cl Λ : ℚ) :
    polyGrow (M : ℝ) Ch Cl Λ = ((growQ M Ch Cl Λ : ℚ) : ℝ) := by
  simp only [polyGrow, growQ]; push_cast; ring

/-- The conditions of `polyFst_damped_core` for the polynomial at `o` with `N` pairs at
`|x| ≤ X`, for a start `l = 0`. -/
def accOk (tab : Array UInt64) (o N : ℕ) (X M Ch Cl Λ δ Er : ℚ) : Bool :=
  decide (1 ≤ N) && decide (0 ≤ X) && decide (X ≤ 1) && decide (0 ≤ Λ) &&
  (List.range N).all (fun k => Wasm.IEEE64.isFinite tab[o + 2 * k]! &&
    Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! &&
    decide (PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * k]!) ≤ Ch) &&
    decide (PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * k + 1]!) ≤ Cl) &&
    decide (hbT tab o N X k ≤ M)) &&
  decide (Cl * (1 + 1 / 2 ^ 53) + (N - 1 : ℕ) * growQ M Ch Cl Λ ≤ Λ) &&
  decide (Cl / 2 ^ 53 + (N - 1 : ℕ) * epsQ X M Ch Cl Λ ≤ Er) && decide (Er + Λ ≤ δ) &&
  decide (δ ≤ 1) &&
  decide (Ch + M + 2 ≤ 2 ^ 797) && decide (Cl ≤ 2 ^ 797) &&
  (List.range (N - 1)).all (fun m =>
    decide ((hbT tab o N X m + δ) * X * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]!)))

/-- The bounds `hbT` hold. -/
theorem hbT_spec (tab : Array UInt64) (o' : UInt64) (o N : ℕ) (ho : o'.toNat = o) (X : ℚ)
    (hX : 0 ≤ X) (hf : ∀ k < N, Wasm.IEEE64.isFinite tab[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! = true) (v : ℝ) (hv : |v| ≤ X) :
    ∀ m, m + 1 ≤ N → |horner (cDD tab o') N 0 v m| ≤ (hbT tab o N X m : ℝ) := by
  have hc : ∀ k < N, cDD tab o' k = (cq tab o k : ℝ) := fun k hk => by
    rw [cDD_rat tab o' k (by rw [ho]; exact (hf k hk).1) (by rw [ho]; exact (hf k hk).2), ho]; rfl
  intro m
  induction m with
  | zero =>
    intro hm
    rw [show horner (cDD tab o') N 0 v 0 = cDD tab o' (N - 1) + 0 from rfl, add_zero,
      hc (N - 1) (by omega), hbT, TgammaExpr.qabs_cast]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [show horner (cDD tab o') N 0 v (m + 1) = cDD tab o' (N - 2 - m) + v * horner (cDD tab o') N 0 v m
      from rfl, hc (N - 2 - m) (by omega), hbT]
    push_cast
    rw [TgammaExpr.qabs_cast]
    have h2 := abs_add_le ((cq tab o (N - 2 - m) : ℚ) : ℝ) (v * horner (cDD tab o') N 0 v m)
    have h3 : |v * horner (cDD tab o') N 0 v m| ≤ (X : ℝ) * (hbT tab o N X m : ℝ) := by
      rw [abs_mul]; exact mul_le_mul hv h1 (abs_nonneg _) (by exact_mod_cast hX)
    linarith

set_option maxHeartbeats 1000000 in
/-- **A polynomial of the accurate path from its check**: `polyDDDFst` at a double `|x| ≤ X`
within `X^(N-1) Cl/2^53 + (N - 1) epsQ` of the polynomial of its pairs, with the low part at most
`Λ`. -/
theorem acc_gen (hF : FmaSpec.FmaNearest) (tab : Array UInt64) (o N : ℕ) (X M Ch Cl Λ δ Er : ℚ)
    (hok : accOk tab o N X M Ch Cl Λ δ Er = true) (o' n' : UInt64) (ho : o'.toNat = o)
    (hn : n'.toNat = N) (hon : o + 2 * N < 2 ^ 63) (x : Float) (hx : Finite x.toBits)
    (hX : |value x.toBits| ≤ (X : ℝ)) :
    Finite (Lgamma.polyDDDFst tab o' n' x 0.0).1.toBits ∧
      Finite (Lgamma.polyDDDFst tab o' n' x 0.0).2.toBits ∧
      |value (Lgamma.polyDDDFst tab o' n' x 0.0).1.toBits +
          value (Lgamma.polyDDDFst tab o' n' x 0.0).2.toBits -
          PolyBound.eval (LgammaApprox.ddCoeffs tab o N) (value x.toBits)| ≤ (Er : ℝ) ∧
      |value (Lgamma.polyDDDFst tab o' n' x 0.0).2.toBits| ≤ (Λ : ℝ) ∧
      |PolyBound.eval (LgammaApprox.ddCoeffs tab o N) (value x.toBits)| ≤ (M : ℝ) := by
  simp only [accOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN1, hX0⟩, hX1⟩, hΛ0⟩, hw⟩, hcap⟩, hEr⟩, hErδ⟩, hδ1⟩, hsz⟩, hClz⟩, hdom⟩ := hok
  have hfin : ∀ k < N, Wasm.IEEE64.isFinite tab[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! = true := fun k hk => (hw k hk).1.1.1
  have hval : ∀ k < N, value (Float.ofBits tab[o + 2 * k]!).toBits =
      ((PolyBound.ratOfWord tab[o + 2 * k]! : ℚ) : ℝ) ∧
      value (Float.ofBits tab[o + 2 * k + 1]!).toBits =
        ((PolyBound.ratOfWord tab[o + 2 * k + 1]! : ℚ) : ℝ) := fun k hk =>
    ⟨ofBits_value _ (hfin k hk).1, ofBits_value _ (hfin k hk).2⟩
  have z0 := TgammaMainRed.zero_finite
  have zv := TgammaMainRed.zero_value
  have hhb := hbT_spec tab o' o N ho X hX0 hfin (value x.toBits) hX
  have hhb' : ∀ m, m + 1 ≤ N → |horner (cDD tab o') N 0 (value x.toBits) m| ≤ (M : ℝ) := fun m hm =>
    (hhb m hm).trans (by exact_mod_cast (hw m (by omega)).2)
  have hCl0 : (0 : ℝ) ≤ Cl := by
    have := (hw 0 (by omega)).1.2
    have h := (Rat.cast_le (K := ℝ)).mpr this
    rw [TgammaExpr.qabs_cast] at h
    linarith [abs_nonneg ((PolyBound.ratOfWord tab[o + 2 * 0 + 1]! : ℚ) : ℝ)]
  have hcap' : ((0 : ℝ) + Cl) * (1 + 1 / 2 ^ 53) + (N - 1 : ℕ) * polyGrow (M : ℝ) Ch Cl Λ ≤ Λ := by
    rw [grow_cast]
    have := (Rat.cast_le (K := ℝ)).mpr hcap
    push_cast at this ⊢
    linarith
  have hEr' : (0 : ℝ) + (0 + Cl) / 2 ^ 53 + (N - 1 : ℕ) * polyEps (X : ℝ) M Ch Cl Λ ≤ Er := by
    rw [eps_cast]
    have := (Rat.cast_le (K := ℝ)).mpr hEr
    push_cast at this ⊢
    linarith
  have hErδ' : (Er : ℝ) + Λ ≤ δ := by
    have := (Rat.cast_le (K := ℝ)).mpr hErδ
    push_cast at this
    exact this
  have hsm' : (0 : ℝ) + (0 + Cl) / 2 ^ 53 + (N - 1 : ℕ) * polyEps (X : ℝ) M Ch Cl Λ + Λ ≤ δ := by
    linarith
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hX1' : (X : ℝ) ≤ 1 := by exact_mod_cast hX1
  obtain ⟨h1, h2, h3, h4⟩ := LgammaPolyFst.polyFst_damped_core hF tab o' n' x 0.0
    (by rw [hn]; exact hN1) (by rw [ho, hn]; exact hon)
    (fun k hk => by rw [ho]; rw [hn] at hk; exact ofBits_finite _ (hfin k hk).1)
    (fun k hk => by rw [ho]; rw [hn] at hk; exact ofBits_finite _ (hfin k hk).2)
    (X : ℝ) (M : ℝ) (Ch : ℝ) (Cl : ℝ) (Λ : ℝ) 0 0 0 0 hx hX hX1'
    (fun k hk => by
      rw [ho]; rw [hn] at hk
      rw [(hval k hk).1, ← TgammaExpr.qabs_cast]
      exact_mod_cast (hw k hk).1.1.2)
    (fun k hk => by
      rw [ho]; rw [hn] at hk
      rw [(hval k hk).2, ← TgammaExpr.qabs_cast]
      exact_mod_cast (hw k hk).1.2)
    z0 (by rw [zv]; simp) (by rw [zv]; simp) (by rw [zv]; simp)
    (fun m hm => by rw [hn] at hm ⊢; exact hhb' m hm)
    (Or.inl le_rfl) le_rfl (by norm_num) (by rw [hn]; exact hcap')
    (by rw [hn]; linarith)
    (by exact_mod_cast hsz) (by simp only [zero_add]; exact_mod_cast hClz) (by exact_mod_cast hΛ0)
    (δ : ℝ) (by rw [hn]; exact hsm') hδ1'
    (fun m hm => by
      rw [hn] at hm ⊢
      rw [ho, (hval (N - 2 - m) (by omega)).1, ← TgammaExpr.qabs_cast]
      have hd := (Rat.cast_le (K := ℝ)).mpr (hdom m (by omega))
      push_cast at hd
      have hb := hhb m (by omega)
      have h2 := mul_le_mul_of_nonneg_right
        (show |horner (cDD tab o') N 0 (value x.toBits) m| + (δ : ℝ) ≤ (hbT tab o N X m : ℝ) + δ by
          linarith) (show (0 : ℝ) ≤ X * (1 + 1 / 2 ^ 53) by
            have : (0 : ℝ) ≤ X := by exact_mod_cast hX0
            positivity)
      push_cast
      linarith [(by ring : ((hbT tab o N X m : ℝ) + δ) * (X * (1 + 1 / 2 ^ 53)) =
        ((hbT tab o N X m : ℝ) + δ) * X * (1 + 1 / 2 ^ 53)),
        (by ring : (|horner (cDD tab o') N 0 (value x.toBits) m| + (δ : ℝ)) * (X * (1 + 1 / 2 ^ 53)) =
        (|horner (cDD tab o') N 0 (value x.toBits) m| + (δ : ℝ)) * X * (1 + 1 / 2 ^ 53))])
  rw [hn, horner_dd_tab tab o' o N ho hN1 hfin] at h3
  have hval' := hhb' (N - 1) (by omega)
  rw [horner_dd_tab tab o' o N ho hN1 hfin] at hval'
  refine ⟨h1, h2, ?_, h4, hval'⟩
  have hXn : (X : ℝ) ^ (N - 1) ≤ 1 := pow_le_one₀ (by exact_mod_cast hX0) hX1'
  have hE : (X : ℝ) ^ (N - 1) * (0 + (0 + Cl) / 2 ^ 53) ≤ 0 + (0 + Cl) / 2 ^ 53 :=
    mul_le_of_le_one_left (by positivity) hXn
  linarith

/-- The check of the 34 pairs at offset 0, for `|x| ≤ 1/4`. -/
theorem small_ok : accOk Lgamma.accurateTable 0 34 (1 / 4) (95 / 100) (83 / 100) (1 / 2 ^ 54)
    (1 / 2 ^ 43) (1 / 2 ^ 42) (1 / 2 ^ 89) = true := by decide +kernel

/-- The check of the 28 pairs at offset 72, the second polynomial without its first two
coefficients, for `|d| ≤ 1/4`. -/
theorem mid_ok : accOk Lgamma.accurateTable 72 28 (1 / 4) (51 / 100) (47 / 100) (1 / 2 ^ 54)
    (1 / 2 ^ 43) (1 / 2 ^ 42) (1 / 2 ^ 89) = true := by decide +kernel


/-- A loop whose bodies agree on the first `m` indices. -/
theorem loop_congr {α : Type} (init : α) (f g : UInt64 → α → α) :
    ∀ m : ℕ, m < 2 ^ 64 → (∀ k < m, f (UInt64.ofNat k) = g (UInt64.ofNat k)) →
      LeanExe.loop (UInt64.ofNat m) init f = LeanExe.loop (UInt64.ofNat m) init g := by
  intro m
  induction m with
  | zero => intro _ _; simp [LeanExe.loop]
  | succ m ih =>
    intro hm hk
    rw [loop_succ m hm, loop_succ m hm, ih (by omega) (fun k hk' => hk k (by omega)), hk m (by omega)]

/-- One step of the loop of `polyDDDFst` at offset 68: the pair `i` added to `d` times the state. -/
def stepM (tab : Array UInt64) (d : Float) (i : UInt64) (s : Float × Float) : Float × Float :=
  fastSum (entry tab (68 + 2 * i)) (entry tab (68 + 2 * i + 1)) (mulDDD d s.1 s.2).1
    (mulDDD d s.1 s.2).2

set_option maxHeartbeats 1000000 in
/-- **The second polynomial in three parts**: the pairs from offset 72, then the steps of the
pairs 1 and 0. -/
theorem mid_split (tab : Array UInt64) (d : Float) :
    Lgamma.polyDDDFst tab 68 30 d 0.0 = stepM tab d 0 (stepM tab d 1 (Lgamma.polyDDDFst tab 72 28 d 0.0)) := by
  obtain ⟨f, hf⟩ : ∃ f : UInt64 → Float × Float → Float × Float, f = fun j s =>
      let i := (30 : UInt64) - 2 - j
      let (ch, cl) := mulDDD d s.1 s.2
      fastSum (entry tab (68 + 2 * i)) (entry tab (68 + 2 * i + 1)) ch cl := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : UInt64 → Float × Float → Float × Float, g = fun j s =>
      let i := (28 : UInt64) - 2 - j
      let (ch, cl) := mulDDD d s.1 s.2
      fastSum (entry tab (72 + 2 * i)) (entry tab (72 + 2 * i + 1)) ch cl := ⟨_, rfl⟩
  obtain ⟨init, hinit⟩ : ∃ init : Float × Float, init =
      ((fastTwoSum (entry tab (68 + 2 * (30 - 1))) 0.0).1,
        (fastTwoSum (entry tab (68 + 2 * (30 - 1))) 0.0).2 + entry tab (68 + 2 * (30 - 1) + 1)) :=
    ⟨_, rfl⟩
  have h68 : Lgamma.polyDDDFst tab 68 30 d 0.0 = LeanExe.loop (UInt64.ofNat 29) init f := by
    rw [hf, hinit]; rfl
  have h72 : Lgamma.polyDDDFst tab 72 28 d 0.0 = LeanExe.loop (UInt64.ofNat 27) init g := by
    rw [hg, hinit]; rfl
  have hfg : LeanExe.loop (UInt64.ofNat 27) init f = LeanExe.loop (UInt64.ofNat 27) init g := by
    apply loop_congr init f g 27 (by norm_num)
    intro k hk
    rw [hf, hg]
    funext s
    obtain ⟨a1, a2⟩ := idx 68 30 k (by simp only [UInt64.reduceToNat]; omega) (by decide)
    obtain ⟨b1, b2⟩ := idx 72 28 k (by simp only [UInt64.reduceToNat]; omega) (by decide)
    simp only [UInt64.reduceToNat] at a1 a2 b1 b2
    have e1 : (68 : UInt64) + 2 * (30 - 2 - UInt64.ofNat k) = 72 + 2 * (28 - 2 - UInt64.ofNat k) :=
      UInt64.toNat_inj.mp (by rw [a1, b1]; omega)
    simp only [e1]
  rw [h68, h72, ← hfg, show (29 : ℕ) = 28 + 1 from rfl, loop_succ 28 (by norm_num),
    show (28 : ℕ) = 27 + 1 from rfl, loop_succ 27 (by norm_num)]
  generalize LeanExe.loop (UInt64.ofNat 27) init f = s
  rw [hf]
  rfl


/-- **`fastSum` without the order of its high parts**, from `TgammaAcc2.fts_approx`. -/
theorem fastSum_any (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits) (A B L : ℝ)
    (hA : |value xh.toBits| ≤ A) (hB : |value yh.toBits| ≤ B)
    (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hAB : A + B ≤ 2 ^ 900) (hL1 : L ≤ 2 ^ 900) :
    Finite (fastSum xh xl yh yl).1.toBits ∧ Finite (fastSum xh xl yh yl).2.toBits ∧
      |value (fastSum xh xl yh yl).1.toBits + value (fastSum xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))| ≤
        B / 2 ^ 53 + (A + B) / 2 ^ 104 + (L + (L * (1 + 1 / 2 ^ 53) + (A + B) / 2 ^ 51)) / 2 ^ 53 ∧
      |value (fastSum xh xl yh yl).1.toBits| ≤ (A + B) * (1 + 1 / 2 ^ 53) ∧
      |value (fastSum xh xl yh yl).2.toBits| ≤ (L * (1 + 1 / 2 ^ 53) + (A + B) / 2 ^ 51) * 2 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  obtain ⟨f1, f2, fe, fb1, fb2⟩ := TgammaAcc2.fts_approx xh yh hxh hyh A B hA hB
    (by linarith [(by norm_num : (2 : ℝ) ^ 900 ≤ 2 ^ 1000)])
  have ht := fapprox_add (fapprox_self xl hxl) (fapprox_self yl hyl) L
    (by simp only [add_zero]; exact (abs_add_le _ _).trans hL)
    (by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1023)])
  simp only [zero_add] at ht
  have hu := fapprox_add ht (fapprox_self (fastTwoSum xh yh).2 f2)
    (L * (1 + 1 / 2 ^ 53) + (A + B) / 2 ^ 51) (by
      simp only [add_zero]
      have := abs_add_le (value xl.toBits + value yl.toBits) (value (fastTwoSum xh yh).2.toBits)
      have := (abs_add_le (value xl.toBits) (value yl.toBits)).trans hL
      have : L / 2 ^ 53 ≤ L * (1 / 2 ^ 53) := le_of_eq (by ring)
      nlinarith)
    (by
      have : (A + B) / 2 ^ 51 ≤ A + B := div_le_self (by linarith) (by norm_num)
      nlinarith [(by norm_num : (2 : ℝ) ^ 900 * (1 + 1 / 2 ^ 53) + 2 ^ 900 < 2 ^ 1023)])
  simp only [add_zero] at hu
  have hfs : fastSum xh xl yh yl = ((fastTwoSum xh yh).1, (xl + yl) + (fastTwoSum xh yh).2) := rfl
  rw [hfs]
  refine ⟨f1, hu.1, ?_, fb1, ?_⟩
  · have h1 := abs_add_le (value (fastTwoSum xh yh).1.toBits + value (fastTwoSum xh yh).2.toBits -
      (value xh.toBits + value yh.toBits))
      (value (xl + yl + (fastTwoSum xh yh).2).toBits -
        (value xl.toBits + value yl.toBits + value (fastTwoSum xh yh).2.toBits))
    rw [show value (fastTwoSum xh yh).1.toBits + value (fastTwoSum xh yh).2.toBits -
        (value xh.toBits + value yh.toBits) + (value (xl + yl + (fastTwoSum xh yh).2).toBits -
        (value xl.toBits + value yl.toBits + value (fastTwoSum xh yh).2.toBits)) =
      value (fastTwoSum xh yh).1.toBits + value (xl + yl + (fastTwoSum xh yh).2).toBits -
        (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits)) by ring] at h1
    have h2 := hu.2
    linarith
  · have h1 := abs_sub_abs_le_abs_sub (value (xl + yl + (fastTwoSum xh yh).2).toBits)
      (value xl.toBits + value yl.toBits + value (fastTwoSum xh yh).2.toBits)
    have h2 := hu.2
    have h3 := abs_add_le (value xl.toBits + value yl.toBits) (value (fastTwoSum xh yh).2.toBits)
    have h4 := (abs_add_le (value xl.toBits) (value yl.toBits)).trans hL
    have h5 : (L * (1 + 1 / 2 ^ 53) + (A + B) / 2 ^ 51) / 2 ^ 53 + L / 2 ^ 53 ≤
        L * (1 + 1 / 2 ^ 53) + (A + B) / 2 ^ 51 := by
      have : (0 : ℝ) ≤ (A + B) / 2 ^ 51 := by positivity
      nlinarith
    nlinarith


/-- The first two pairs of the second polynomial. -/
theorem mid_words :
    Wasm.IEEE64.isFinite Lgamma.accurateTable[68]! = true ∧
      Wasm.IEEE64.isFinite Lgamma.accurateTable[69]! = true ∧
      Wasm.IEEE64.isFinite Lgamma.accurateTable[70]! = true ∧
      Wasm.IEEE64.isFinite Lgamma.accurateTable[71]! = true ∧
      12 / 100 ≤ -PolyBound.ratOfWord Lgamma.accurateTable[68]! ∧
      -PolyBound.ratOfWord Lgamma.accurateTable[68]! ≤ 121 / 1000 ∧
      |PolyBound.ratOfWord Lgamma.accurateTable[69]!| ≤ 1 / 2 ^ 55 ∧
      |PolyBound.ratOfWord Lgamma.accurateTable[70]!| ≤ 37 / 1000 ∧
      |PolyBound.ratOfWord Lgamma.accurateTable[71]!| ≤ 1 / 2 ^ 55 := by
  decide +kernel


/-- The polynomial of the pairs at 68 in terms of those at 72. -/
theorem mid_eval (v : ℝ) :
    PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) v =
      ((PolyBound.ratOfWord Lgamma.accurateTable[68]! + PolyBound.ratOfWord Lgamma.accurateTable[69]! :
        ℚ) : ℝ) + v * (((PolyBound.ratOfWord Lgamma.accurateTable[70]! +
          PolyBound.ratOfWord Lgamma.accurateTable[71]! : ℚ) : ℝ) +
        v * PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 72 28) v) := by
  rw [show LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30 = (List.range 30).map (fun k =>
      LgammaApprox.q Lgamma.accurateTable (68 + 2 * k) +
        LgammaApprox.q Lgamma.accurateTable (68 + 2 * k + 1)) from rfl,
    show LgammaApprox.ddCoeffs Lgamma.accurateTable 72 28 = (List.range 28).map (fun k =>
      LgammaApprox.q Lgamma.accurateTable (72 + 2 * k) +
        LgammaApprox.q Lgamma.accurateTable (72 + 2 * k + 1)) from rfl,
    eval_map_range, eval_map_range, Finset.sum_range_succ', Finset.sum_range_succ']
  have hs : ∑ k ∈ Finset.range 28, ((LgammaApprox.q Lgamma.accurateTable (68 + 2 * (k + 1 + 1)) +
      LgammaApprox.q Lgamma.accurateTable (68 + 2 * (k + 1 + 1) + 1) : ℚ) : ℝ) * v ^ (k + 1 + 1) =
      v ^ 2 * ∑ k ∈ Finset.range 28, ((LgammaApprox.q Lgamma.accurateTable (72 + 2 * k) +
        LgammaApprox.q Lgamma.accurateTable (72 + 2 * k + 1) : ℚ) : ℝ) * v ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show 68 + 2 * (k + 1 + 1) = 72 + 2 * k by ring]
    ring
  rw [hs]
  have h0 : LgammaApprox.q Lgamma.accurateTable (68 + 2 * 0) +
      LgammaApprox.q Lgamma.accurateTable (68 + 2 * 0 + 1) =
      PolyBound.ratOfWord Lgamma.accurateTable[68]! + PolyBound.ratOfWord Lgamma.accurateTable[69]! := rfl
  have h1 : LgammaApprox.q Lgamma.accurateTable (68 + 2 * (0 + 1)) +
      LgammaApprox.q Lgamma.accurateTable (68 + 2 * (0 + 1) + 1) =
      PolyBound.ratOfWord Lgamma.accurateTable[70]! + PolyBound.ratOfWord Lgamma.accurateTable[71]! := rfl
  rw [h0, h1]
  ring

set_option maxHeartbeats 4000000 in
/-- **The second polynomial** at `|d| ≤ 1/4`: within `9/2^61` of the polynomial of its pairs.  The
step that adds the pair 1 has no order between its high parts, and `fastSum_any` bounds it by
the half spacing of the product, near `2^-56`, which the last product by `d` halves twice. -/
theorem mid_spec (hF : FmaSpec.FmaNearest) (d : Float) (hd : Finite d.toBits)
    (hD : |value d.toBits| ≤ 1 / 4) :
    Finite (Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0).1.toBits ∧
      Finite (Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0).2.toBits ∧
      |value (Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0).1.toBits +
          value (Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0).2.toBits -
          PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (value d.toBits)| ≤
        9 / 2 ^ 61 ∧
      |value (Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0).2.toBits| ≤ 1 / 2 ^ 40 ∧
      |value (Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0).1.toBits| ≤ 1 / 4 := by
  rw [mid_split]
  obtain ⟨w68, w69, w70, w71, c0lo, c0hi, c0l, c1h, c1l⟩ := mid_words
  have v68 := ofBits_value _ w68
  have v69 := ofBits_value _ w69
  have v70 := ofBits_value _ w70
  have v71 := ofBits_value _ w71
  have q0lo := (Rat.cast_le (K := ℝ)).mpr c0lo
  have q0hi := (Rat.cast_le (K := ℝ)).mpr c0hi
  have q0l : |((PolyBound.ratOfWord Lgamma.accurateTable[69]! : ℚ) : ℝ)| ≤ 1 / 2 ^ 55 := by
    have := (Rat.cast_le (K := ℝ)).mpr c0l; push_cast at this; exact this
  have q1h : |((PolyBound.ratOfWord Lgamma.accurateTable[70]! : ℚ) : ℝ)| ≤ 37 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).mpr c1h; push_cast at this; exact this
  have q1l : |((PolyBound.ratOfWord Lgamma.accurateTable[71]! : ℚ) : ℝ)| ≤ 1 / 2 ^ 55 := by
    have := (Rat.cast_le (K := ℝ)).mpr c1l; push_cast at this; exact this
  push_cast at q0lo q0hi
  have e68 : entry Lgamma.accurateTable (68 + 2 * 0) = Float.ofBits Lgamma.accurateTable[68]! := rfl
  have e69 : entry Lgamma.accurateTable (68 + 2 * 0 + 1) = Float.ofBits Lgamma.accurateTable[69]! := rfl
  have e70 : entry Lgamma.accurateTable (68 + 2 * 1) = Float.ofBits Lgamma.accurateTable[70]! := rfl
  have e71 : entry Lgamma.accurateTable (68 + 2 * 1 + 1) = Float.ofBits Lgamma.accurateTable[71]! := rfl
  -- the pairs from 72
  obtain ⟨s1f, s2f, se, s2b, sv⟩ := acc_gen hF Lgamma.accurateTable 72 28 (1 / 4) (51 / 100) (47 / 100)
    (1 / 2 ^ 54) (1 / 2 ^ 43) (1 / 2 ^ 42) (1 / 2 ^ 89) mid_ok 72 28 rfl rfl (by norm_num) d hd
    (by push_cast; exact hD)
  set s := Lgamma.polyDDDFst Lgamma.accurateTable 72 28 d 0.0 with hsdef
  set P := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 72 28) (value d.toBits) with hP
  push_cast at se s2b sv
  have hs1 : |value s.1.toBits| ≤ 52 / 100 := by
    have h1 := abs_sub_abs_le_abs_sub (value s.1.toBits) (value s.1.toBits + value s.2.toBits - P)
    rw [show value s.1.toBits - (value s.1.toBits + value s.2.toBits - P) = P - value s.2.toBits by ring]
      at h1
    have h2 := abs_sub P (value s.2.toBits)
    linarith [(by norm_num : (51 : ℝ) / 100 + 1 / 2 ^ 43 + 1 / 2 ^ 89 ≤ 52 / 100)]
  -- the step of the pair 1
  obtain ⟨m1f1, m1f2, m1e, m1b2, m1b1⟩ := mulDDD_spec hF d s.1 s.2 hd s1f s2f (13 / 100) (1 / 2 ^ 45)
    (by have := mul_le_mul hs1 hD (abs_nonneg _) (by norm_num)
        linarith [(by norm_num : (52 : ℝ) / 100 * (1 / 4) = 13 / 100)])
    (by have := mul_le_mul s2b hD (abs_nonneg _) (by norm_num)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 * (1 / 4) = 1 / 2 ^ 45)])
    (by norm_num) (by norm_num)
  set m1 := mulDDD d s.1 s.2 with hm1
  have hm1b1 : |value m1.1.toBits| ≤ 131 / 1000 := by
    linarith [(by norm_num : (13 : ℝ) / 100 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 131 / 1000)]
  have hm1b2 : |value m1.2.toBits| ≤ 1 / 2 ^ 44 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 45 * (1 + 1 / 2 ^ 51) + 13 / 100 / 2 ^ 52 + 1 / 2 ^ 1071 ≤
      1 / 2 ^ 44)]
  have hc1f := ofBits_finite _ w70
  have hc1lf := ofBits_finite _ w71
  obtain ⟨t1f, t2f, te, tb1, tb2⟩ := fastSum_any (Float.ofBits Lgamma.accurateTable[70]!)
    (Float.ofBits Lgamma.accurateTable[71]!) m1.1 m1.2 hc1f hc1lf m1f1 m1f2 (37 / 1000) (131 / 1000)
    (1 / 2 ^ 43) (by rw [v70]; exact q1h) hm1b1
    (by rw [v71]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 55 + 1 / 2 ^ 44 ≤ 1 / 2 ^ 43)])
    (by norm_num) (by norm_num)
  have ht : stepM Lgamma.accurateTable d 1 s = fastSum (Float.ofBits Lgamma.accurateTable[70]!)
      (Float.ofBits Lgamma.accurateTable[71]!) m1.1 m1.2 := by
    unfold stepM; rw [e70, e71]
  rw [ht]
  set t := fastSum (Float.ofBits Lgamma.accurateTable[70]!) (Float.ofBits Lgamma.accurateTable[71]!)
    m1.1 m1.2 with htdef
  have ht1 : |value t.1.toBits| ≤ 17 / 100 := by
    linarith [(by norm_num : (37 / 1000 + 131 / 1000 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 17 / 100)]
  have ht2 : |value t.2.toBits| ≤ 1 / 2 ^ 41 := by
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 43 * (1 + 1 / 2 ^ 53) + (37 / 1000 + 131 / 1000) / 2 ^ 51) *
      2 ≤ 1 / 2 ^ 41)]
  have hte : |value t.1.toBits + value t.2.toBits - (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
      value (Float.ofBits Lgamma.accurateTable[71]!).toBits + (value m1.1.toBits + value m1.2.toBits))| ≤
      132 / 1000 / 2 ^ 53 := by
    linarith [(by norm_num : (131 / 1000 : ℝ) / 2 ^ 53 + (37 / 1000 + 131 / 1000) / 2 ^ 104 +
      (1 / 2 ^ 43 + (1 / 2 ^ 43 * (1 + 1 / 2 ^ 53) + (37 / 1000 + 131 / 1000) / 2 ^ 51)) / 2 ^ 53 ≤
      132 / 1000 / 2 ^ 53)]
  -- the step of the pair 0
  obtain ⟨m0f1, m0f2, m0e, m0b2, m0b1⟩ := mulDDD_spec hF d t.1 t.2 hd t1f t2f (17 / 400) (1 / 2 ^ 43)
    (by have := mul_le_mul ht1 hD (abs_nonneg _) (by norm_num)
        linarith [(by norm_num : (17 : ℝ) / 100 * (1 / 4) = 17 / 400)])
    (by have := mul_le_mul ht2 hD (abs_nonneg _) (by norm_num)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 41 * (1 / 4) = 1 / 2 ^ 43)])
    (by norm_num) (by norm_num)
  set m0 := mulDDD d t.1 t.2 with hm0
  have hc0f := ofBits_finite _ w68
  have hc0lf := ofBits_finite _ w69
  have hdom : |value m0.1.toBits| ≤ |value (Float.ofBits Lgamma.accurateTable[68]!).toBits| := by
    rw [v68, abs_of_neg (show ((PolyBound.ratOfWord Lgamma.accurateTable[68]! : ℚ) : ℝ) < 0 by linarith)]
    linarith [(by norm_num : (17 : ℝ) / 400 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 12 / 100)]
  have hm0b2 : |value m0.2.toBits| ≤ 1 / 2 ^ 42 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 * (1 + 1 / 2 ^ 51) + 17 / 400 / 2 ^ 52 + 1 / 2 ^ 1071 ≤
      1 / 2 ^ 42)]
  have hc0b : |value (Float.ofBits Lgamma.accurateTable[68]!).toBits| < 2 ^ 898 := by
    rw [v68, abs_of_neg (show ((PolyBound.ratOfWord Lgamma.accurateTable[68]! : ℚ) : ℝ) < 0 by linarith)]
    linarith [(by norm_num : (121 : ℝ) / 1000 < 2 ^ 898)]
  obtain ⟨r1f, r2f, re, rb2⟩ := fastSum_spec (Float.ofBits Lgamma.accurateTable[68]!)
    (Float.ofBits Lgamma.accurateTable[69]!) m0.1 m0.2 hc0f hc0lf m0f1 m0f2 hdom hc0b (1 / 2 ^ 41)
    (by rw [v69]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 55 + 1 / 2 ^ 42 ≤ 1 / 2 ^ 41)]) (by norm_num)
  obtain ⟨-, -, hsum0, -, hsl0⟩ := fastTwoSum_spec (Float.ofBits Lgamma.accurateTable[68]!) m0.1 hc0f
    m0f1 hdom (by linarith [(by norm_num : (2 : ℝ) ^ 898 < 2 ^ 900)])
  have hr1 : |value (fastSum (Float.ofBits Lgamma.accurateTable[68]!)
      (Float.ofBits Lgamma.accurateTable[69]!) m0.1 m0.2).1.toBits| ≤ 1 / 4 := by
    have hb := TgammaDD.high_bound _ _ _ hsum0 hsl0
    have h1 := abs_add_le (value (Float.ofBits Lgamma.accurateTable[68]!).toBits) (value m0.1.toBits)
    rw [v68, abs_of_neg (show ((PolyBound.ratOfWord Lgamma.accurateTable[68]! : ℚ) : ℝ) < 0 by linarith)] at h1
    have h2 : |value (Float.ofBits Lgamma.accurateTable[68]!).toBits + value m0.1.toBits| ≤ 164 / 1000 := by
      rw [v68] at hb ⊢
      linarith [(by norm_num : (17 : ℝ) / 400 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 43 / 1000)]
    have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    show |value (fastTwoSum (Float.ofBits Lgamma.accurateTable[68]!) m0.1).1.toBits| ≤ 1 / 4
    linarith [(by norm_num : (164 : ℝ) / 1000 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 1 / 4)]
  have hs0 : stepM Lgamma.accurateTable d 0 t = fastSum (Float.ofBits Lgamma.accurateTable[68]!)
      (Float.ofBits Lgamma.accurateTable[69]!) m0.1 m0.2 := by
    unfold stepM; rw [e68, e69]
  rw [hs0]
  set r := fastSum (Float.ofBits Lgamma.accurateTable[68]!) (Float.ofBits Lgamma.accurateTable[69]!)
    m0.1 m0.2 with hrdef
  refine ⟨r1f, r2f, ?_, ?_, hr1⟩
  · -- the error through the identity of `mid_eval`
    rw [mid_eval]
    have hc0 : ((PolyBound.ratOfWord Lgamma.accurateTable[68]! + PolyBound.ratOfWord Lgamma.accurateTable[69]! :
        ℚ) : ℝ) = value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits := by rw [v68, v69]; push_cast; ring
    have hc1 : ((PolyBound.ratOfWord Lgamma.accurateTable[70]! + PolyBound.ratOfWord Lgamma.accurateTable[71]! :
        ℚ) : ℝ) = value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[71]!).toBits := by rw [v70, v71]; push_cast; ring
    rw [hc0, hc1]
    set D := value d.toBits with hDdef
    have hid : value r.1.toBits + value r.2.toBits -
        (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits +
          D * (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
            value (Float.ofBits Lgamma.accurateTable[71]!).toBits + D * P)) =
        (value r.1.toBits + value r.2.toBits - (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits + (value m0.1.toBits + value m0.2.toBits))) +
        (value m0.1.toBits + value m0.2.toBits - D * (value t.1.toBits + value t.2.toBits)) +
        D * (value t.1.toBits + value t.2.toBits - (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[71]!).toBits + (value m1.1.toBits + value m1.2.toBits))) +
        D * (value m1.1.toBits + value m1.2.toBits - D * (value s.1.toBits + value s.2.toBits)) +
        D * D * (value s.1.toBits + value s.2.toBits - P) := by ring
    rw [hid]
    have hrb : |value r.1.toBits| ≤ 1 / 4 := hr1
    have e1 : |value r.1.toBits + value r.2.toBits - (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
        value (Float.ofBits Lgamma.accurateTable[69]!).toBits + (value m0.1.toBits + value m0.2.toBits))| ≤
        1 / 2 ^ 92 := by
      have : |value r.1.toBits| / 2 ^ 52 ≤ 1 / 4 / 2 ^ 52 := div_le_div_of_nonneg_right hrb (by norm_num)
      linarith [(by norm_num : (3 * (1 / 2 ^ 41) + 1 / 4 / 2 ^ 52 + 1 / 2 ^ 1074 : ℝ) / 2 ^ 53 ≤
        1 / 2 ^ 92)]
    have e2 : |value m0.1.toBits + value m0.2.toBits - D * (value t.1.toBits + value t.2.toBits)| ≤
        1 / 2 ^ 93 := by
      linarith [(by norm_num : (3 * (1 / 2 ^ 43) + 17 / 400 / 2 ^ 51 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1072 ≤
        1 / 2 ^ 93)]
    have e4 : |value m1.1.toBits + value m1.2.toBits - D * (value s.1.toBits + value s.2.toBits)| ≤
        1 / 2 ^ 95 := by
      linarith [(by norm_num : (3 * (1 / 2 ^ 45) + 13 / 100 / 2 ^ 51 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1072 ≤
        1 / 2 ^ 95)]
    have f3 : |D * (value t.1.toBits + value t.2.toBits - (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
        value (Float.ofBits Lgamma.accurateTable[71]!).toBits + (value m1.1.toBits + value m1.2.toBits)))| ≤
        1 / 4 * (132 / 1000 / 2 ^ 53) := by
      rw [abs_mul]; exact mul_le_mul hD hte (abs_nonneg _) (by norm_num)
    have f4 : |D * (value m1.1.toBits + value m1.2.toBits - D * (value s.1.toBits + value s.2.toBits))| ≤
        1 / 4 * (1 / 2 ^ 95) := by
      rw [abs_mul]; exact mul_le_mul hD e4 (abs_nonneg _) (by norm_num)
    have f5 : |D * D * (value s.1.toBits + value s.2.toBits - P)| ≤ 1 / 4 * (1 / 4) * (1 / 2 ^ 89) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hD hD (abs_nonneg _) (by norm_num)) se (abs_nonneg _) (by norm_num)
    have a1 := abs_add_le ((value r.1.toBits + value r.2.toBits - (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits + (value m0.1.toBits + value m0.2.toBits))) +
        (value m0.1.toBits + value m0.2.toBits - D * (value t.1.toBits + value t.2.toBits)) +
        D * (value t.1.toBits + value t.2.toBits - (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[71]!).toBits + (value m1.1.toBits + value m1.2.toBits))) +
        D * (value m1.1.toBits + value m1.2.toBits - D * (value s.1.toBits + value s.2.toBits)))
      (D * D * (value s.1.toBits + value s.2.toBits - P))
    have a2 := abs_add_le ((value r.1.toBits + value r.2.toBits - (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits + (value m0.1.toBits + value m0.2.toBits))) +
        (value m0.1.toBits + value m0.2.toBits - D * (value t.1.toBits + value t.2.toBits)) +
        D * (value t.1.toBits + value t.2.toBits - (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[71]!).toBits + (value m1.1.toBits + value m1.2.toBits))))
      (D * (value m1.1.toBits + value m1.2.toBits - D * (value s.1.toBits + value s.2.toBits)))
    have a3 := abs_add_le ((value r.1.toBits + value r.2.toBits - (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits + (value m0.1.toBits + value m0.2.toBits))) +
        (value m0.1.toBits + value m0.2.toBits - D * (value t.1.toBits + value t.2.toBits)))
      (D * (value t.1.toBits + value t.2.toBits - (value (Float.ofBits Lgamma.accurateTable[70]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[71]!).toBits + (value m1.1.toBits + value m1.2.toBits))))
    have a4 := abs_add_le (value r.1.toBits + value r.2.toBits - (value (Float.ofBits Lgamma.accurateTable[68]!).toBits +
          value (Float.ofBits Lgamma.accurateTable[69]!).toBits + (value m0.1.toBits + value m0.2.toBits)))
      (value m0.1.toBits + value m0.2.toBits - D * (value t.1.toBits + value t.2.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 92 + 1 / 2 ^ 93 + 1 / 4 * (132 / 1000 / 2 ^ 53) +
      1 / 4 * (1 / 2 ^ 95) + 1 / 4 * (1 / 4) * (1 / 2 ^ 89) ≤ 9 / 2 ^ 61)]
  · have : |value r.1.toBits| / 2 ^ 51 ≤ 1 / 4 / 2 ^ 51 := div_le_div_of_nonneg_right hr1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 41 * (1 + 1 / 2 ^ 51) + 1 / 4 / 2 ^ 51 + 1 / 2 ^ 1073 ≤
      1 / 2 ^ 40)]

#print axioms acc_gen
#print axioms small_ok
#print axioms mid_ok
#print axioms mid_split
#print axioms fastSum_any
#print axioms mid_eval
#print axioms mid_spec

end Verified.Examples.LgammaAccPoly
