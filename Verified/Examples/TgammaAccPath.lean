import Verified.Examples.TgammaAccUpCase
import Verified.Examples.TgammaAccDownCase
import Verified.Examples.TgammaAccSmallPath
import Verified.Examples.TgammaFinal

/-!
**The accurate path of `Tgamma`** within one step of `Γ`.  From `1/4` on, `accurate_range_eq`
states the code with its loop bodies and final steps as named functions.  The range of `⌊x⌋`
(`TgammaAccSel.range_spec`), the exact reduced argument `d`, the polynomial (`poly3_range`), and
`AccRangeFact` give `Γ (x + jm)`, and the three cases of the sign of `jm` give the result
(`TgammaAccUpCase.up_case`, `TgammaAccDownCase.down_case`, `zero_case`).  When the rounding test
fails, the code looks `x` up in the database of hard cases, and `DbWithin` states its values within
one step of `Γ` (`final_step`).  `accurate_within` joins the path below `1/4` and states
`TgammaFinal.AccurateWithin` under `DbWithin`.
-/

namespace Verified.Examples.TgammaAccPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAccUp TgammaAccDown
  TgammaAccFin TgammaAccCrr TgammaAccPre

set_option exponentiation.threshold 4096

/-- The values of the database of hard cases within one step of `Γ` at their arguments. -/
def DbWithin : Prop :=
  ∀ k : ℕ, k < 57 →
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value (entry dbTable (3 * UInt64.ofNat k)).toBits))
      (entry dbTable (3 * UInt64.ofNat k + 1) + entry dbTable (3 * UInt64.ofNat k + 2)).toBits

/-- A loop that replaces its state by `v k` where `c k` holds ends with its initial state or with
some `v k`. -/
theorem loop_pick {α : Type} (c : UInt64 → Bool) (v : UInt64 → α) (init : α) (n : ℕ)
    (hn : n < 2 ^ 64) :
    LeanExe.loop (UInt64.ofNat n) init (fun k acc => if c k then v k else acc) = init ∨
      ∃ k < n, c (UInt64.ofNat k) = true ∧
        LeanExe.loop (UInt64.ofNat n) init (fun k acc => if c k then v k else acc) =
          v (UInt64.ofNat k) := by
  induction n with
  | zero => left; simp [LeanExe.loop]
  | succ m ih =>
    rw [TgammaPoly.loop_succ m hn]
    by_cases hc : c (UInt64.ofNat m) = true
    · right
      exact ⟨m, by omega, hc, by simp [hc]⟩
    · rcases ih (by omega) with h | ⟨k, hk, hck, h⟩
      · left
        simp [hc, h]
      · right
        exact ⟨k, by omega, hck, by simp [hc, h]⟩

theorem database_cases (x f : Float) :
    database dbTable x f = f ∨ ∃ k < 57, (entry dbTable (3 * UInt64.ofNat k) == x) = true ∧
      database dbTable x f =
        entry dbTable (3 * UInt64.ofNat k + 1) + entry dbTable (3 * UInt64.ofNat k + 2) :=
  loop_pick (fun k => entry dbTable (3 * k) == x)
    (fun k => entry dbTable (3 * k + 1) + entry dbTable (3 * k + 2)) f 57 (by norm_num)

theorem entries_finite : ∀ k < 57,
    Wasm.IEEE64.isFinite dbTable[(3 * UInt64.ofNat k).toNat]! = true := by
  decide +kernel

/-- **The last step**: the result, or the database's value at a hard case. -/
theorem final_step (hDb : DbWithin) (x : Float) (hx : Finite x.toBits) (c : Bool) (w : UInt64)
    (h : F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) (Float.ofBits w).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (if c then database dbTable x (Float.ofBits w) else Float.ofBits w).toBits := by
  split_ifs
  · rcases database_cases x (Float.ofBits w) with h1 | ⟨k, hk, hck, h1⟩
    · rw [h1]
      exact h
    · rw [h1]
      have hef : Finite (entry dbTable (3 * UInt64.ofNat k)).toBits :=
        TgammaWords.ofBits_finite _ (entries_finite k hk)
      have hv := (F64UpperWord.float_beq_iff _ _ hef hx).mp hck
      rw [← hv]
      exact hDb k hk
  · exact h

theorem rows_ok : ∀ r ∈ TgammaApprox.accRanges, r.2.2.2.2.2 ≤ 942 ∧
    (r.2.2.2.2.1 = 4 → r.2.2.2.2.2 ≤ 3) := by
  decide

/-- **The accurate path from `1/4`** within one step of `Γ`. -/
theorem accurate_range_within (hF : FmaSpec.FmaNearest) (hA : TgammaApprox.AccRangeFact)
    (hT : TgammaLarge.GammaBelowT0) (hGap : TgammaRefl4.SubnormalGap) (hDb : DbWithin)
    (x : Float) (hx : Finite x.toBits) (hnint : ∀ n : ℤ, value x.toBits ≠ n)
    (hq : 1 / 4 ≤ |value x.toBits|) (hlo : -184 < value x.toBits)
    (ht : value x.toBits < (GammaThresholds.t0 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accurateTable dbTable x).toBits := by
  have h025 : ¬ x.abs < 0.25 := fun h => by
    have := (TgammaSpecial.quarter_test x hx).mp h
    linarith
  rw [accurate_range_eq dbTable x h025]
  set v := value x.toBits with hvdef
  have ht172 : v < 172 := by
    have h : GammaThresholds.t0 < 172 := by unfold GammaThresholds.t0; norm_num
    have h' : (GammaThresholds.t0 : ℝ) < 172 := by exact_mod_cast h
    linarith
  -- the floor
  obtain ⟨hif, hiv⟩ := TgammaFloor.floorF_spec x hx (by rw [abs_lt]; constructor <;> linarith)
  set n := ⌊v⌋ with hndef
  have hn1 : (n : ℝ) ≤ v := Int.floor_le v
  have hn2 : v < n + 1 := Int.lt_floor_add_one v
  have hn171 : n ≤ 171 := by
    have h1 : (n : ℝ) < 172 := by linarith
    have h2 : n < 172 := by exact_mod_cast h1
    omega
  have hnlo : -184 ≤ n := by
    have h1 : (-185 : ℝ) < n := by linarith
    have h2 : -185 < n := by exact_mod_cast h1
    omega
  obtain ⟨oh, imax, ol, jmax, jN, eoff, hr, jF, hrange, hjFf, hjFv, hcase⟩ :=
    TgammaAccSel.range_spec (floorF x) hif n hiv hn171
  have hj4 : 4 ≤ jN := (TgammaAccGamma.fact_ok _ hr).2
  obtain ⟨he942, he3⟩ := rows_ok _ hr
  dsimp only at he942 he3
  -- the reduced argument and the polynomial
  obtain ⟨hdf, hdv⟩ := TgammaAccSel.d_spec x hx hq (by rw [abs_le]; constructor <;> linarith)
  have hd1 : |value (2.0 * (x - (floorF x + 0.5))).toBits| ≤ 1 := by
    rw [hdv, abs_le]
    constructor <;> linarith
  obtain ⟨hp1, hp2, hpA, hp1b, hp2b⟩ :=
    TgammaAccRanges.poly3_range hF _ hdf hd1 oh imax ol jmax jN eoff hr
  obtain ⟨hA1, hΓ⟩ := TgammaAccGamma.accPoly_lo hA oh imax ol jmax jN eoff hr _ hd1
  have hy : (jN : ℝ) + (1 + value (2.0 * (x - (floorF x + 0.5))).toBits) / 2 =
      v + ((jN : ℝ) - n) := by
    rw [hdv]
    ring
  rw [hy] at hΓ
  -- `jm`
  obtain ⟨hjmf, hjmv⟩ := int_sub jF (floorF x) hjFf hif jN n (by rw [hjFv]; norm_cast) hiv
    (by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [h2, abs_le]; constructor <;> norm_num <;> omega
      · rw [abs_le]; constructor <;> norm_num <;> omega)
  -- the code
  unfold accRangeVal
  dsimp only
  rw [hrange]
  dsimp only
  obtain ⟨jm, hjmd⟩ : ∃ jm, jF - floorF x = jm := ⟨_, rfl⟩
  rw [hjmd] at hjmf hjmv ⊢
  obtain ⟨d, hdd⟩ : ∃ d, 2.0 * (x - (floorF x + 0.5)) = d := ⟨_, rfl⟩
  rw [hdd] at hdf hdv hd1 hp1 hp2 hpA hp1b hp2b hA1 hΓ ⊢
  obtain ⟨p, hpd⟩ : ∃ p, poly3 accurateTable d (UInt64.ofNat oh) (UInt64.ofNat imax)
    (UInt64.ofNat ol) (UInt64.ofNat jmax) = p := ⟨_, rfl⟩
  rw [hpd] at hp1 hp2 hpA hp1b hp2b ⊢
  obtain ⟨p1, p2⟩ := p
  dsimp only at hp1 hp2 hpA hp1b hp2b ⊢
  unfold stW stF
  rcases lt_trichotomy n (jN : ℤ) with hlt | heq | hgt
  · -- `x < j`
    have hjN : jN = 4 := by
      rcases hcase with ⟨_, h⟩ | ⟨h8, hjn, _⟩
      · exact h
      · omega
    subst hjN
    have he3' := he3 rfl
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = 3 - n := ⟨(3 - n).toNat, by omega⟩
    have hMr : (M : ℝ) = 3 - n := by exact_mod_cast hM
    have hjm' : value jm.toBits = M + 1 := by rw [hjmv, hMr]; push_cast; ring
    have hjm0 : jm > 0.0 := (gt_zero_iff jm hjmf).mpr (by rw [hjm']; positivity)
    rw [ite_eq_left hjm0, count_up jm hjmf M hjm' (by omega), upBody_eq]
    obtain ⟨z, hz⟩ := grid54 x hx hq
    have hv54 := dist_int v z hz hnint
    have hUp := up_loop hF x (UInt64.ofNat eoff) M (by omega) hx z hz hq (by linarith)
      (by linarith) hv54 M le_rfl
    obtain ⟨s, hsd⟩ : ∃ s, LeanExe.loop (UInt64.ofNat M) (x, (0.0 : Float), x, (0.0 : Float),
      UInt64.ofNat eoff) (fun _ s => upStep s) = s := ⟨_, rfl⟩
    rw [hsd] at hUp ⊢
    obtain ⟨xph, xpl, wh, wl, e⟩ := s
    obtain ⟨-, -, hwhf, hwlf, -, -, -, -, -, r, hrM, he, hWe, hwlb, hwhb, hS⟩ := hUp
    dsimp only at hwhf hwlf he hWe hwlb hwhb hS ⊢
    subst he
    rw [ite_eq_left hjm0]
    have hyy : v + (((4 : ℕ) : ℝ) - n) = v + ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [hyy] at hΓ
    have hU := TgammaAccUpCase.up_case hF hGap x hnint hv54 hlo M (by omega) (by linarith)
      (by push_cast; linarith) eoff he3' _ hA1 hΓ p1 p2 hp1 hp2 hpA hp1b hp2b wh wl hwhf hwlf r
      hWe hwlb hwhb hS jm hjmf hjm'
    obtain ⟨f, hfd⟩ : ∃ f, mulDD3 p1 p2 (1.0 / wh)
      ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh)) = f := ⟨_, rfl⟩
    rw [hfd] at hU ⊢
    obtain ⟨f1, f2⟩ := f
    dsimp only at hU
    unfold stEnd
    dsimp only
    exact final_step hDb x hx _ _ hU
  · -- `j ≤ x < j + 1`
    have hjm0' : value jm.toBits = 0 := by rw [hjmv, heq]; push_cast; ring
    have hn0 : ¬ jm > 0.0 := fun h => by
      have := (gt_zero_iff jm hjmf).mp h
      linarith
    have hn0' : ¬ jm < 0.0 := fun h => by
      have := (lt_zero_iff jm hjmf).mp h
      linarith
    rw [ite_eq_right hn0, ite_eq_right hn0']
    dsimp only
    rw [ite_eq_right hn0, ite_eq_right hn0']
    unfold stEnd
    dsimp only
    have hyy : v + ((jN : ℝ) - n) = v := by rw [heq]; push_cast; ring
    rw [hyy] at hΓ
    have hZ := TgammaAccDownCase.zero_case hT x hx ht
      (by have : (4 : ℝ) ≤ jN := by exact_mod_cast hj4
          have : ((jN : ℤ) : ℝ) = (jN : ℝ) := by norm_cast
          rw [heq] at hn1
          linarith)
      eoff (by omega) _ hA1 hΓ p1 p2 hp1 hp2 hpA hp1b hp2b jm hjmf hjm0'
    exact final_step hDb x hx _ _ hZ
  · -- `x ≥ j + 1`
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = n - jN - 1 := ⟨(n - jN - 1).toNat, by omega⟩
    have hM31 : M + 1 ≤ 31 := by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · omega
      · omega
    have hMr : (M : ℝ) = n - jN - 1 := by exact_mod_cast hM
    have hjm' : value jm.toBits = -((M : ℝ) + 1) := by rw [hjmv, hMr]; push_cast; ring
    have hn0 : ¬ jm > 0.0 := fun h => by
      have := (gt_zero_iff jm hjmf).mp h
      rw [hjm'] at this
      linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    have hjlt : jm < 0.0 := (lt_zero_iff jm hjmf).mpr
      (by rw [hjm']; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
    rw [ite_eq_right hn0, ite_eq_left hjlt, count_down jm hjmf M hjm' (by omega), downBody_eq]
    have hj4r : (4 : ℝ) ≤ jN := by exact_mod_cast hj4
    have hv5 : ((M + 1 : ℕ) : ℝ) + 4 ≤ v := by push_cast; linarith
    obtain ⟨k0, g, hg52, hkv, hk0⟩ := grid53 x.toBits (by linarith) (by linarith)
    have hDn := down_loop hF x hx k0 g (by omega) hkv hk0 M (by omega) hv5 (by linarith) M le_rfl
    obtain ⟨s, hsd⟩ : ∃ s, LeanExe.loop (UInt64.ofNat M) (x - 1.0, (0.0 : Float), x - 1.0,
      (0.0 : Float)) (fun _ s => downStep s) = s := ⟨_, rfl⟩
    rw [hsd] at hDn ⊢
    obtain ⟨xph, xpl, wh, wl⟩ := s
    obtain ⟨-, -, hwhf, hwlf, -, -, hWe, hwlb, hwhb, -, -⟩ := hDn
    dsimp only at hwhf hwlf hWe hwlb hwhb ⊢
    rw [ite_eq_right hn0, ite_eq_left hjlt]
    have hyy : v + ((jN : ℝ) - n) = v - ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [hyy] at hΓ
    have hD := TgammaAccDownCase.down_case hF hT x hx ht M hM31 (by push_cast; linarith)
      (by linarith) eoff (by omega) _ hA1 hΓ p1 p2 hp1 hp2 hpA hp1b hp2b wh wl hwhf hwlf hWe hwlb
      hwhb jm hjmf hjm'
    obtain ⟨f, hfd⟩ : ∃ f, mulDD3 p1 p2 wh wl = f := ⟨_, rfl⟩
    rw [hfd] at hD ⊢
    obtain ⟨f1, f2⟩ := f
    dsimp only at hD
    unfold stEnd
    dsimp only
    exact final_step hDb x hx _ _ hD

/-- **`AccurateWithin`** under `DbWithin`. -/
theorem accurate_within (hF : FmaSpec.FmaNearest) (hS : TgammaApprox.AccSmallFact)
    (hA : TgammaApprox.AccRangeFact) (hT : TgammaLarge.GammaBelowT0)
    (hGap : TgammaRefl4.SubnormalGap) (hDb : DbWithin) : TgammaFinal.AccurateWithin := by
  intro x hx hnint h112 hlo ht
  by_cases h4 : |value x.toBits| < 1 / 4
  · exact TgammaAccSmallPath.accurate_small_within hF hS dbTable x hx h112 h4
  · exact accurate_range_within hF hA hT hGap hDb x hx hnint (not_lt.mp h4) hlo ht

#print axioms loop_pick
#print axioms final_step
#print axioms accurate_range_within
#print axioms accurate_within

end Verified.Examples.TgammaAccPath
