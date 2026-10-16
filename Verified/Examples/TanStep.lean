import Verified.Examples.TrigMedium
import LeanExe.ProofKit.F64SelfStep
import Mathlib.Data.Int.Log

/-!
The last step for results that are a rounded sum: a finite word that is a nearest word to `t`,
with `t` within `0.74 u |T|` of `T`, lies within one step of the nearest-even reference of `T`.
`half_spacing` provides a word within half a spacing of `t` in its binade, so a nearest word is
that close; when `t` and `T` lie in different binades, the boundary word bounds the rounding.
-/

namespace Verified.Examples.TanStep

open CodeLib.IEEE64 LeanExe.ProofKit

local notation "𝐮" => unitRoundoff64

/-- The start of binade `e`, the value of the word `e · 2 ^ 52`. -/
noncomputable def B (e : Nat) : ℝ := (2 : ℝ) ^ (e + 51) / 2 ^ 1074

/-- The spacing of binade `e`. -/
noncomputable def S (e : Nat) : ℝ := (2 : ℝ) ^ (e - 1) / 2 ^ 1074

theorem B_eq (e : Nat) (he : 1 ≤ e) : B e = 2 ^ 52 * S e := by
  unfold B S
  rw [show e + 51 = 52 + (e - 1) by omega, pow_add]
  ring

theorem B_succ (e : Nat) : B (e + 1) = 2 * B e := by
  unfold B
  rw [show e + 1 + 51 = (e + 51) + 1 by omega, pow_succ]
  ring

theorem S_succ (e : Nat) (he : 1 ≤ e) : S (e + 1) = 2 * S e := by
  unfold S
  rw [show e + 1 - 1 = (e - 1) + 1 by omega, pow_succ]
  ring

theorem S_pos (e : Nat) : 0 < S e := by unfold S; positivity

theorem B_pos (e : Nat) : 0 < B e := by unfold B; positivity

/-- The value of the word `e · 2 ^ 52 + j` in a normal binade, `j ≤ 2 ^ 52`. -/
theorem word_value (e j : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 2045) (hj : j ≤ 2 ^ 52) :
    value (UInt64.ofNat (e * 2 ^ 52 + j)) = B e + j * S e ∧
      Finite (UInt64.ofNat (e * 2 ^ 52 + j)) ∧ (UInt64.ofNat (e * 2 ^ 52 + j)).toNat < 2 ^ 63 := by
  have hn : (UInt64.ofNat (e * 2 ^ 52 + j)).toNat = e * 2 ^ 52 + j :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have h63 : (UInt64.ofNat (e * 2 ^ 52 + j)).toNat < 2 ^ 63 := by rw [hn]; omega
  have hexp : Wasm.IEEE64.exponent (UInt64.ofNat (e * 2 ^ 52 + j)) =
      if j < 2 ^ 52 then e else e + 1 := by
    unfold Wasm.IEEE64.exponent
    rw [hn]
    split <;> omega
  have hfin : Finite (UInt64.ofNat (e * 2 ^ 52 + j)) := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [hexp]
    split <;> simp only [bne_iff_ne, ne_eq] <;> omega
  refine ⟨?_, hfin, h63⟩
  have hv := TrigMedium.value_normal _ h63 (by rw [hexp]; split <;> omega)
  rw [hv, hexp, hn]
  rcases Nat.lt_or_ge j (2 ^ 52) with hlt | hge
  · rw [if_pos hlt]
    have hm : (e * 2 ^ 52 + j) % 2 ^ 52 = j := by omega
    rw [hm]
    unfold B S
    rw [show e + 51 = 52 + (e - 1) by omega, show (2 : ℝ) ^ e = 2 * 2 ^ (e - 1) by
      rw [← pow_succ']; congr 1; omega, show (2 : ℝ) ^ 1075 = 2 * 2 ^ 1074 by rw [← pow_succ'],
      pow_add]
    push_cast
    field_simp
    ring
  · have hj' : j = 2 ^ 52 := le_antisymm hj hge
    subst hj'
    rw [if_neg (by omega)]
    have hm : (e * 2 ^ 52 + 2 ^ 52) % 2 ^ 52 = 0 := by omega
    rw [hm]
    unfold B S
    rw [show e + 51 = 52 + (e - 1) by omega, show (2 : ℝ) ^ (e + 1) = 4 * 2 ^ (e - 1) by
      rw [show e + 1 = (e - 1) + 2 by omega, pow_add]; ring,
      show (2 : ℝ) ^ 1075 = 2 * 2 ^ 1074 by rw [← pow_succ'], pow_add]
    push_cast
    field_simp
    ring

/-- A word within half a spacing of every `t` in a normal binade. -/
theorem half_spacing (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 2045) (t : ℝ) (ht0 : B e ≤ t)
    (ht1 : t ≤ 2 * B e) : ∃ v : UInt64, Finite v ∧ |value v - t| ≤ S e / 2 := by
  have hS := S_pos e
  have hB := B_eq e he1
  set q := (t - B e) / S e with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hS.le
  have hq1 : q ≤ 2 ^ 52 := by
    rw [hq, div_le_iff₀ hS]
    linarith
  set j := ⌊q + 1 / 2⌋₊ with hjdef
  have hjl : (j : ℝ) ≤ q + 1 / 2 := Nat.floor_le (by linarith)
  have hju : q + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  have hj : j ≤ 2 ^ 52 := by
    have h3 : (j : ℝ) < 2 ^ 52 + 1 := by linarith
    have h4 : j < 2 ^ 52 + 1 := by exact_mod_cast h3
    omega
  obtain ⟨hv, hf, -⟩ := word_value e j he1 he2 hj
  refine ⟨_, hf, ?_⟩
  rw [hv]
  have ht : t = B e + q * S e := by
    rw [hq]
    field_simp
    ring
  rw [ht, show B e + j * S e - (B e + q * S e) = (j - q) * S e by ring, abs_mul,
    abs_of_pos hS]
  have : |(j : ℝ) - q| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg ((j : ℝ) - q)]

/-- `F64FullStep.one_step_binades` with the binade starts written as `B`. -/
theorem step_binades (y : ℝ) (c : UInt64) (a b : Nat) (ha : 1 ≤ a) (hab : a < b)
    (hb : b ≤ 2045) (hya : B a ≤ y) (hyb : y ≤ B b) (hcf : Finite c)
    (hca : B a ≤ value c) (hcb : value c ≤ B b) (he : |value c - y| < 3 * S a / 2) (hy0 : 0 ≤ y) :
    F64SignedRounding.WithinSteps 1 y c := by
  obtain ⟨hva, -, -⟩ := word_value a 0 ha (by omega) (by norm_num)
  obtain ⟨hvb, -, -⟩ := word_value b 0 (by omega) (by omega) (by norm_num)
  simp only [add_zero, Nat.cast_zero, zero_mul] at hva hvb
  have hcp : 0 < value c := lt_of_lt_of_le (B_pos a) hca
  have hlim := F64PositiveOrder.positive_finite_encoding c hcf hcp
  have hl : F64NearestNonnegative.limit = 0x7FF0000000000000 := rfl
  rw [hl] at hlim
  have h := F64FullStep.one_step_binades y c a b hab (by omega) (by rw [hva]; exact hya)
    (fun _ => by rw [hvb]; exact hyb) (by omega) (by rw [hva]; exact hca)
    (by rw [hvb]; exact hcb) (by unfold S at he; exact he)
  exact F64SignedRounding.within_of_nonneg 1 y hy0 c (by omega) h.1 h.2

theorem B_23 : B 23 = 1 / 2 ^ 1000 := by
  unfold B
  rw [show (1074 : Nat) = 74 + 1000 by norm_num, pow_add]
  field_simp

theorem B_2024 : B 2024 = 2 * 2 ^ 1000 := by
  unfold B
  rw [show 2024 + 51 = 1074 + 1001 by norm_num, pow_add, pow_succ]
  field_simp

/-- The binade of a positive number from `2 ^ -1000` to `2 ^ 1000`. -/
theorem binade (T : ℝ) (h0 : 1 / 2 ^ 1000 ≤ T) (h1 : T ≤ 2 ^ 1000) :
    ∃ e : Nat, 23 ≤ e ∧ e ≤ 2023 ∧ B e ≤ T ∧ T < 2 * B e := by
  have hlt : T < 2 * 2 ^ 1000 :=
    lt_of_le_of_lt h1 (lt_mul_of_one_lt_left (by positivity) (by norm_num))
  have hex : ∃ k, T < B (k + 24) := ⟨2000, by
    rw [show 2000 + 24 = 2024 by rfl, B_2024]
    exact hlt⟩
  classical
  set k := Nat.find hex with hk
  have hspec : T < B (k + 24) := Nat.find_spec hex
  have hle : k ≤ 2000 := Nat.find_min' hex (by
    rw [show 2000 + 24 = 2024 by rfl, B_2024]
    exact hlt)
  refine ⟨k + 23, by omega, by omega, ?_, by rw [← B_succ]; exact hspec⟩
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, B_23]
    exact h0
  · have hmin := Nat.find_min hex (show k - 1 < k by omega)
    rw [show k - 1 + 24 = k + 23 by omega] at hmin
    exact not_lt.mp hmin

/-- `near_rel` for a positive number. -/
theorem near_pos (c : UInt64) (t T : ℝ) (hcf : Finite c)
    (hnear : ∀ v : UInt64, Finite v → |value c - t| ≤ |value v - t|)
    (hT0 : 1 / 2 ^ 1000 ≤ T) (hT1 : T ≤ 2 ^ 1000) (ht : |t - T| ≤ 74 / 100 * 𝐮 * T) :
    F64SignedRounding.WithinSteps 1 T c := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨e, he1, he2, hTe, hTe'⟩ := binade T hT0 hT1
  have hS := S_pos e
  have hBS := B_eq e (by omega)
  have hBpos := B_pos e
  have hd : 74 / 100 * 𝐮 * T < 74 / 100 * S e := by
    rw [hu]
    have : T / 2 ^ 53 < 2 * B e / 2 ^ 53 := div_lt_div_of_pos_right hTe' (by positivity)
    rw [hBS] at this
    have h52 : (2 : ℝ) * (2 ^ 52 * S e) / 2 ^ 53 = S e := by
      rw [show (2 : ℝ) ^ 53 = 2 * 2 ^ 52 by rw [← pow_succ']]
      field_simp
    linarith
  have hta := abs_le.mp ht
  -- The words at the binade boundaries.
  obtain ⟨vB0, fB, -⟩ := word_value e 0 (by omega) (by omega) (by norm_num)
  obtain ⟨v2B', f2B, -⟩ := word_value e (2 ^ 52) (by omega) (by omega) le_rfl
  have vB : value (UInt64.ofNat (e * 2 ^ 52 + 0)) = B e := by rw [vB0]; simp
  have v2B : value (UInt64.ofNat (e * 2 ^ 52 + 2 ^ 52)) = 2 * B e := by
    rw [v2B', hBS]
    push_cast
    ring
  have hB1 : B (e + 1) = 2 * B e := B_succ e
  have hB2 : B (e + 2) = 4 * B e := by
    rw [show e + 2 = (e + 1) + 1 from rfl, B_succ, B_succ]
    ring
  rcases lt_or_ge t (B e) with hlow | hge
  · -- `t` below the binade of `T`.
    have hc := hnear _ fB
    rw [vB, abs_of_nonneg (show (0 : ℝ) ≤ B e - t by linarith)] at hc
    have he0 : 2 ≤ e := by omega
    have hS' := S_succ (e - 1) (by omega)
    rw [show e - 1 + 1 = e by omega] at hS'
    have hB' := B_succ (e - 1)
    rw [show e - 1 + 1 = e by omega] at hB'
    have hd' : 74 / 100 * 𝐮 * T ≤ 3700001 / 10000000 * S e := by
      have hT' : T ≤ B e + 74 / 100 * 𝐮 * T := by linarith
      rw [hu] at hT' ⊢
      rw [hBS] at hT'
      linarith
    have hca := abs_le.mp hc
    have hcv : 0 < value c := by linarith
    have hBS' : B e = 2 ^ 52 * S e := hBS
    refine step_binades T c (e - 1) (e + 1) (by omega) (by omega) (by omega) (by linarith)
      (by rw [hB1]; linarith) hcf (by linarith) (by rw [hB1]; linarith) ?_ (by linarith)
    rw [abs_lt]
    constructor <;> linarith
  rcases le_or_gt t (2 * B e) with hin | hhigh
  · -- `t` in the binade of `T`.
    obtain ⟨v, hvf, hv⟩ := half_spacing e (by omega) (by omega) t hge hin
    have hc := (hnear v hvf).trans hv
    have hcB := hnear _ fB
    have hc2B := hnear _ f2B
    rw [vB, abs_of_nonpos (show B e - t ≤ 0 by linarith)] at hcB
    rw [v2B, abs_of_nonneg (show (0 : ℝ) ≤ 2 * B e - t by linarith)] at hc2B
    have hca := abs_le.mp hc
    have hcB' := abs_le.mp hcB
    have hc2B' := abs_le.mp hc2B
    have hcl : B e ≤ value c := by linarith
    have hcu : value c ≤ 2 * B e := by linarith
    refine step_binades T c e (e + 1) (by omega) (by omega) (by omega) hTe
      (by rw [hB1]; linarith) hcf hcl (by rw [hB1]; exact hcu) ?_ (by linarith)
    rw [abs_lt]
    constructor <;> linarith
  · -- `t` above the binade of `T`.
    have hc := hnear _ f2B
    rw [v2B, abs_of_neg (show 2 * B e - t < 0 by linarith)] at hc
    have hca := abs_le.mp hc
    refine step_binades T c e (e + 2) (by omega) (by omega) (by omega) hTe
      (by rw [hB2]; linarith) hcf (by linarith) (by rw [hB2]; linarith) ?_ (by linarith)
    rw [abs_lt]
    constructor <;> linarith

/-- A finite word nearest to `t`, with `t` within `0.74 u |T|` of `T`, lies within one step of
the nearest-even reference of `T`. -/
theorem near_rel (c : UInt64) (t T : ℝ) (hcf : Finite c)
    (hnear : ∀ v : UInt64, Finite v → |value c - t| ≤ |value v - t|)
    (hT0 : 1 / 2 ^ 1000 ≤ |T|) (hT1 : |T| ≤ 2 ^ 1000) (ht : |t - T| ≤ 74 / 100 * 𝐮 * |T|) :
    F64SignedRounding.WithinSteps 1 T c := by
  rcases le_or_gt 0 T with hT | hT
  · rw [abs_of_nonneg hT] at hT0 hT1 ht
    exact near_pos c t T hcf hnear hT0 hT1 ht
  · rw [abs_of_neg hT] at hT0 hT1 ht
    obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hcf
    have h := near_pos (Wasm.IEEE64.negate c) (-t) (-T) hnf (fun v hv => by
      obtain ⟨hvf, hvv⟩ := F64Magnitude.negate_value v hv
      have := hnear _ hvf
      rw [hvv] at this
      rw [hnv, show -value c - -t = -(value c - t) by ring, abs_neg,
        show value v - -t = -(-value v - t) by ring, abs_neg]
      exact this) hT0 hT1 (by rw [show -t - -T = -(t - T) by ring, abs_neg]; exact ht)
    exact (F64SignedRounding.within_negate 1 T c).mp h


/-- A finite word nearest to `t`, with `t` and `T` in the same binade `e` and less than a
spacing apart, lies within one step of the nearest-even reference of `T`. -/
theorem near_bin_pos (c : UInt64) (t T : ℝ) (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 2044)
    (hcf : Finite c) (hnear : ∀ v : UInt64, Finite v → |value c - t| ≤ |value v - t|)
    (hT : B e ≤ T ∧ T ≤ 2 * B e) (ht : B e ≤ t ∧ t ≤ 2 * B e) (hd : |t - T| < S e) :
    F64SignedRounding.WithinSteps 1 T c := by
  obtain ⟨vB0, fB, -⟩ := word_value e 0 he1 (by omega) (by norm_num)
  obtain ⟨v2B', f2B, -⟩ := word_value e (2 ^ 52) he1 (by omega) le_rfl
  have hBS := B_eq e he1
  have vB : value (UInt64.ofNat (e * 2 ^ 52 + 0)) = B e := by rw [vB0]; simp
  have v2B : value (UInt64.ofNat (e * 2 ^ 52 + 2 ^ 52)) = 2 * B e := by
    rw [v2B', hBS]
    push_cast
    ring
  obtain ⟨v, hvf, hv⟩ := half_spacing e he1 (by omega) t ht.1 ht.2
  have hc := (hnear v hvf).trans hv
  have hcB := hnear _ fB
  have hc2B := hnear _ f2B
  rw [vB, abs_of_nonpos (show B e - t ≤ 0 by linarith)] at hcB
  rw [v2B, abs_of_nonneg (show (0 : ℝ) ≤ 2 * B e - t by linarith)] at hc2B
  have hca := abs_le.mp hc
  have hcB' := abs_le.mp hcB
  have hc2B' := abs_le.mp hc2B
  have hdd := abs_lt.mp hd
  refine step_binades T c e (e + 1) he1 (by omega) (by omega) hT.1
    (by rw [B_succ]; linarith) hcf (by linarith) (by rw [B_succ]; linarith) ?_
    (by linarith [B_pos e])
  rw [abs_lt]
  constructor <;> linarith

/-- `near_bin_pos` for numbers of either sign. -/
theorem near_bin (c : UInt64) (t T : ℝ) (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 2044)
    (hcf : Finite c) (hnear : ∀ v : UInt64, Finite v → |value c - t| ≤ |value v - t|)
    (hT : B e ≤ |T| ∧ |T| ≤ 2 * B e) (ht : B e ≤ |t| ∧ |t| ≤ 2 * B e) (hsign : 0 < t * T)
    (hd : |t - T| < S e) :
    F64SignedRounding.WithinSteps 1 T c := by
  have hB := B_pos e
  rcases le_or_gt 0 T with hT0 | hT0
  · have ht0 : 0 < t := by
      rcases lt_or_ge 0 t with h | h
      · exact h
      · nlinarith
    rw [abs_of_nonneg hT0] at hT
    rw [abs_of_pos ht0] at ht
    exact near_bin_pos c t T e he1 he2 hcf hnear hT ht hd
  · have ht0 : t < 0 := by
      rcases lt_or_ge t 0 with h | h
      · exact h
      · nlinarith
    rw [abs_of_neg hT0] at hT
    rw [abs_of_neg ht0] at ht
    obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hcf
    have h := near_bin_pos (Wasm.IEEE64.negate c) (-t) (-T) e he1 he2 hnf (fun v hv => by
      obtain ⟨hvf, hvv⟩ := F64Magnitude.negate_value v hv
      have := hnear _ hvf
      rw [hvv] at this
      rw [hnv, show -value c - -t = -(value c - t) by ring, abs_neg,
        show value v - -t = -(-value v - t) by ring, abs_neg]
      exact this) hT ht (by rw [show -t - -T = -(t - T) by ring, abs_neg]; exact hd)
    exact (F64SignedRounding.within_negate 1 T c).mp h

#print axioms near_bin

#print axioms word_value
#print axioms half_spacing
#print axioms binade
#print axioms near_rel

end Verified.Examples.TanStep
