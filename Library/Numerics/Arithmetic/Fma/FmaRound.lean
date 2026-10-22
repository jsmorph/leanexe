import Library.Numerics.Arithmetic.Fma.FmaWords
import Library.Numerics.Arithmetic.Fma.FmaGrid

/-!
The parts of `Fma.roundPack s w h l`, which rounds `N · 2 ^ (w - 2400)`, `N = h · 2 ^ 64 + l`, as
`FmaGrid.RoundsTo` describes.  `roundPack_eq` splits it into the plan (`plan`: the direction and
length of the shift and the biased exponent), the significand (`sig`), and the packing
(`assemble`).  A right shift by `r ≥ 1` rounds `N / 2 ^ r` to nearest, ties to even, from bit
`r - 1`, the bits below it, and bit `r` (`round_right`).  A shift by 0 or to the left is exact
(`roundsTo_exact`).  `FmaRoundPack.roundPack_spec` assembles the cases.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaRound
open Verified.Examples FmaWords FmaGrid

set_option exponentiation.threshold 4096

/-- The plan of `Fma.roundPack`: a left shift or not, the shift, and the biased exponent. -/
def plan (w m : UInt64) : Bool × UInt64 × UInt64 :=
  if w + m ≥ 1378 then
    if m ≥ 52 then (false, m - 52, w + m - 1377) else (true, 52 - m, w + m - 1377)
  else if w ≤ 1326 then (false, 1326 - w, 1) else (true, w - 1326, 1)

/-- The significand of `Fma.roundPack` for a plan. -/
def sig (h l : UInt64) (left : Bool) (r : UInt64) : UInt64 :=
  if left then (Fma.shl128 h l r).2
  else if r ≥ 128 then 0
  else
    let q := (Fma.shr128 h l r).2
    if r ≥ 1 && Fma.bit128 h l (r - 1) && (Fma.lowBits128 h l (r - 1) || q &&& 1 == 1) then q + 1
    else q

/-- The last step of `Fma.roundPack`. -/
def assemble (s e q : UInt64) : UInt64 :=
  let inf := (s <<< 63) ||| 0x7FF0000000000000
  if e ≥ 2047 then inf
  else
    let out := ((e - 1) <<< 52) + q
    if out ≥ 0x7FF0000000000000 then inf else (s <<< 63) ||| out

theorem roundPack_eq (s w h l : UInt64) : Fma.roundPack s w h l =
    assemble s (plan w (Fma.msb128 h l)).2.2
      (sig h l (plan w (Fma.msb128 h l)).1 (plan w (Fma.msb128 h l)).2.1) := by
  unfold Fma.roundPack plan sig assemble
  rfl

/-- A comparison of a word with a literal, by its value. -/
theorem lit_le (a : UInt64) (k : UInt64) : k ≤ a ↔ k.toNat ≤ a.toNat := UInt64.le_iff_toNat_le

theorem assemble_spec (s e q : UInt64) (he1 : 1 ≤ e.toNat) (hq : q.toNat ≤ 2 ^ 53) :
    assemble s e q = packWord s e.toNat q.toNat := by
  unfold assemble packWord
  dsimp only
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have h53 : (2 : ℕ) ^ 53 = 9007199254740992 := by norm_num
  have h52 : (2 : ℕ) ^ 52 = 4503599627370496 := by norm_num
  by_cases hE : 2047 ≤ e.toNat
  · rw [ite_eq_left (show e ≥ 2047 from (lit_le e 2047).mpr hE), ite_eq_left hE]
  rw [ite_eq_right (fun h => hE ((lit_le e 2047).mp h)), ite_eq_right hE]
  have hsub : (e - 1).toNat = e.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le e 1).mpr he1)]
    rfl
  have hshl : ((e - 1) <<< 52).toNat = (e.toNat - 1) * 2 ^ 52 := by
    rw [shl_toNat, hsub]
    have : (52 : UInt64).toNat % 64 = 52 := rfl
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : (e.toNat - 1) * 2 ^ 52 + q.toNat < 2 ^ 64 := by omega
  have hout : ((e - 1) <<< 52) + q = UInt64.ofNat ((e.toNat - 1) * 2 ^ 52 + q.toNat) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, hshl, UInt64.toNat_ofNat_of_lt' hlt]
    exact Nat.mod_eq_of_lt hlt
  have hval : (UInt64.ofNat ((e.toNat - 1) * 2 ^ 52 + q.toNat)).toNat =
      (e.toNat - 1) * 2 ^ 52 + q.toNat := UInt64.toNat_ofNat_of_lt' hlt
  rw [hout]
  by_cases hW : 0x7FF0000000000000 ≤ (e.toNat - 1) * 2 ^ 52 + q.toNat
  · rw [ite_eq_left (show UInt64.ofNat ((e.toNat - 1) * 2 ^ 52 + q.toNat) ≥ 0x7FF0000000000000 from
      (lit_le _ _).mpr (by rw [hval]; exact hW)), ite_eq_left hW]
  · rw [ite_eq_right (fun h => hW (by
        have := (lit_le _ _).mp h
        rwa [hval] at this)), ite_eq_right hW]

/-- The packed word from a rounding. -/
theorem assemble_round (s e q : UInt64) (Y E Q : ℕ) (he : e.toNat = E) (hq : q.toNat = Q)
    (hR : RoundsTo Y E Q) : assemble s e q = packWord s E Q := by
  rw [← he, ← hq]
  exact assemble_spec s e q (by rw [he]; exact hR.1)
    (by rw [hq]; exact (significand_bounds _ _ _ hR).1)

theorem sig_far (h l r : UInt64) (hr : 128 ≤ r.toNat) : sig h l false r = 0 := by
  unfold sig
  rw [ite_eq_right Bool.false_ne_true, ite_eq_left (show r ≥ 128 from (lit_le r 128).mpr hr)]

theorem sig_left (h l r : UInt64) (hr : r.toNat < 128) (hfit : pair h l * 2 ^ r.toNat < 2 ^ 64) :
    (sig h l true r).toNat = pair h l * 2 ^ r.toNat := by
  unfold sig
  rw [ite_eq_left rfl]
  have hs := shl128_spec h l r hr (lt_trans hfit (by norm_num))
  generalize Fma.shl128 h l r = p at hs ⊢
  obtain ⟨a, b⟩ := p
  dsimp only at hs ⊢
  generalize pair h l * 2 ^ r.toNat = X at hs hfit ⊢
  unfold pair at hs
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have := b.toNat_lt
  omega

theorem and_one_beq (x : UInt64) : (x &&& 1 == 1) = decide (x.toNat % 2 = 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_one,
    Nat.and_one_is_mod, decide_eq_true_iff]

theorem sig_exact (h l : UInt64) (hN : pair h l < 2 ^ 63) :
    (sig h l false 0).toNat = pair h l := by
  have hs := shr128_spec h l 0
  unfold sig
  rw [ite_eq_right Bool.false_ne_true, ite_eq_right (by decide)]
  dsimp only
  rw [ite_eq_right (by simp)]
  generalize Fma.shr128 h l 0 = p at hs ⊢
  obtain ⟨a, b⟩ := p
  dsimp only at hs ⊢
  rw [UInt64.toNat_zero, pow_zero, Nat.div_one] at hs
  generalize pair h l = X at hs hN ⊢
  unfold pair at hs
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have := b.toNat_lt
  omega

/-- The rounding condition for a right shift by `r`: bit `r - 1` is set, and a lower bit or
bit `r` is set. -/
def RoundUp (N r : ℕ) : Prop :=
  N / 2 ^ (r - 1) % 2 = 1 ∧ (N % 2 ^ (r - 1) ≠ 0 ∨ N / 2 ^ r % 2 = 1)

theorem sig_round (h l r : UInt64) (hr1 : 1 ≤ r.toNat) (hr : r.toNat < 128)
    (hq : pair h l / 2 ^ r.toNat < 2 ^ 63) :
    (RoundUp (pair h l) r.toNat → (sig h l false r).toNat = pair h l / 2 ^ r.toNat + 1) ∧
      (¬ RoundUp (pair h l) r.toNat → (sig h l false r).toNat = pair h l / 2 ^ r.toNat) := by
  have hr1' : r ≥ 1 := (lit_le r 1).mpr hr1
  have hsub : (r - 1).toNat = r.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ hr1']
    rfl
  have hb := bit128_spec h l (r - 1) (by omega)
  have hlb := lowBits128_spec h l (r - 1)
  rw [hsub] at hb hlb
  have hs := shr128_spec h l r
  unfold sig
  rw [ite_eq_right Bool.false_ne_true,
    ite_eq_right (fun h' => absurd ((lit_le r 128).mp h') (by
      have : (128 : UInt64).toNat = 128 := rfl
      omega))]
  dsimp only
  rw [hb, hlb]
  generalize Fma.shr128 h l r = p at hs ⊢
  obtain ⟨a, q0⟩ := p
  dsimp only at hs ⊢
  rw [and_one_beq]
  generalize hX : pair h l / 2 ^ r.toNat = X at hs hq
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have hq0 : q0.toNat = X := by
    unfold pair at hs
    have := q0.toNat_lt
    omega
  have hadd : (q0 + 1).toNat = X + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, hq0]
    omega
  unfold RoundUp
  rw [hX]
  constructor
  · intro hup
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff, hq0]
      exact ⟨⟨hr1', hup.1⟩, hup.2⟩), hadd]
  · intro hnup
    rw [ite_eq_right (by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff, hq0, not_and]
      intro hb12 hb3
      exact hnup ⟨hb12.2, hb3⟩), hq0]

/-- Rounding `N / 2 ^ r` to nearest, ties to even, from bit `r - 1`, the bits below it, and
bit `r`. -/
theorem round_right (N r Q : ℕ) (hr : 1 ≤ r)
    (h1 : RoundUp N r → Q = N / 2 ^ r + 1) (h2 : ¬ RoundUp N r → Q = N / 2 ^ r) :
    2 * N ≤ (2 * Q + 1) * 2 ^ r ∧ 2 * Q * 2 ^ r ≤ 2 * N + 2 ^ r ∧
      (2 * N = (2 * Q + 1) * 2 ^ r ∨ 2 * N + 2 ^ r = 2 * Q * 2 ^ r → Q % 2 = 0) := by
  unfold RoundUp at h1 h2
  have hR : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ', show r - 1 + 1 = r by omega]
  have hdm := Nat.div_add_mod N (2 ^ r)
  have hml := Nat.mod_lt N (show 0 < 2 ^ r by positivity)
  have hHp : 0 < 2 ^ (r - 1) := by positivity
  generalize N / 2 ^ r = Q0 at hdm h1 h2
  generalize N % 2 ^ r = rem at hdm hml
  rw [hR] at hdm hml ⊢
  generalize 2 ^ (r - 1) = H at hdm hml h1 h2 hHp ⊢
  have hdivH : N / H = 2 * Q0 + rem / H := by
    rw [← hdm, show 2 * H * Q0 = H * (2 * Q0) by ring, Nat.mul_add_div hHp]
  have hmodH : N % H = rem % H := by
    rw [← hdm, show 2 * H * Q0 = H * (2 * Q0) by ring, Nat.mul_add_mod]
  have ht : rem / H < 2 := by rw [Nat.div_lt_iff_lt_mul hHp]; omega
  have hu : rem % H < H := Nat.mod_lt rem hHp
  have hmd := Nat.mod_add_div rem H
  have hNA : N = 2 * (Q0 * H) + rem := by rw [← hdm]; ring
  have e1 : (2 * (Q0 + 1) + 1) * (2 * H) = 4 * (Q0 * H) + 6 * H := by ring
  have e2 : 2 * (Q0 + 1) * (2 * H) = 4 * (Q0 * H) + 4 * H := by ring
  have e3 : (2 * Q0 + 1) * (2 * H) = 4 * (Q0 * H) + 2 * H := by ring
  have e4 : 2 * Q0 * (2 * H) = 4 * (Q0 * H) := by ring
  rw [hdivH, hmodH] at h1 h2
  generalize rem / H = t at ht hmd h1 h2
  generalize rem % H = u at hu hmd h1 h2
  have hodd : (2 * Q0 + 1) % 2 = 1 := by rw [Nat.mul_add_mod]
  have heven : (2 * Q0 + 0) % 2 = 0 := by rw [add_zero, Nat.mul_mod_right]
  obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
  · rw [mul_zero, add_zero] at hmd
    have hc : ¬ ((2 * Q0 + 0) % 2 = 1 ∧ (u ≠ 0 ∨ Q0 % 2 = 1)) := by
      rintro ⟨h, _⟩
      rw [heven] at h
      exact absurd h (by decide)
    rw [h2 hc, e3, e4]
    generalize Q0 * H = A at hNA ⊢
    omega
  · rw [mul_one] at hmd
    by_cases hup : (2 * Q0 + 1) % 2 = 1 ∧ (u ≠ 0 ∨ Q0 % 2 = 1)
    · have h3 := hup.2
      rw [h1 hup, e1, e2]
      generalize Q0 * H = A at hNA ⊢
      omega
    · have h3 : ¬ (u ≠ 0 ∨ Q0 % 2 = 1) := fun h => hup ⟨hodd, h⟩
      rw [h2 hup, e3, e4]
      generalize Q0 * H = A at hNA ⊢
      omega

/-- `RoundsTo` from a rounding at shift `R` scaled by `2 ^ W`. -/
theorem roundsTo_of (N W E Q R : ℕ) (hE : 1 ≤ E) (hS : E + 1325 = W + R)
    (hhi : N * 2 ^ W < 2 ^ 53 * spacing E) (hlo : E = 1 ∨ 2 ^ 52 * spacing E ≤ N * 2 ^ W)
    (h1 : 2 * N ≤ (2 * Q + 1) * 2 ^ R) (h2 : 2 * Q * 2 ^ R ≤ 2 * N + 2 ^ R)
    (h3 : 2 * N = (2 * Q + 1) * 2 ^ R ∨ 2 * N + 2 ^ R = 2 * Q * 2 ^ R → Q % 2 = 0) :
    RoundsTo (N * 2 ^ W) E Q := by
  have hsp : spacing E = 2 ^ R * 2 ^ W := by unfold spacing; rw [hS, pow_add, mul_comm]
  have hP : 0 < 2 ^ W := by positivity
  unfold RoundsTo
  refine ⟨hE, hhi, hlo, ?_, ?_, ?_⟩
  · rw [hsp, show 2 * (N * 2 ^ W) = 2 * N * 2 ^ W by ring,
      show (2 * Q + 1) * (2 ^ R * 2 ^ W) = (2 * Q + 1) * 2 ^ R * 2 ^ W by ring]
    exact Nat.mul_le_mul_right _ h1
  · rw [hsp, show 2 * Q * (2 ^ R * 2 ^ W) = 2 * Q * 2 ^ R * 2 ^ W by ring,
      show 2 * (N * 2 ^ W) + 2 ^ R * 2 ^ W = (2 * N + 2 ^ R) * 2 ^ W by ring]
    exact Nat.mul_le_mul_right _ h2
  · intro ht
    apply h3
    rw [hsp] at ht
    rcases ht with ht | ht
    · left
      apply Nat.eq_of_mul_eq_mul_right hP
      rw [show 2 * N * 2 ^ W = 2 * (N * 2 ^ W) by ring, ht]
      ring
    · right
      apply Nat.eq_of_mul_eq_mul_right hP
      rw [show (2 * N + 2 ^ R) * 2 ^ W = 2 * (N * 2 ^ W) + 2 ^ R * 2 ^ W by ring, ht]
      ring

/-- `RoundsTo` for an exact multiple of the spacing. -/
theorem roundsTo_exact (Y E Q : ℕ) (hE : 1 ≤ E) (hY : Y = Q * spacing E)
    (hhi : Y < 2 ^ 53 * spacing E) (hlo : E = 1 ∨ 2 ^ 52 * spacing E ≤ Y) :
    RoundsTo Y E Q := by
  have hS := spacing_pos E
  have e1 : (2 * Q + 1) * spacing E = 2 * (Q * spacing E) + spacing E := by ring
  have e2 : 2 * Q * spacing E = 2 * (Q * spacing E) := by ring
  unfold RoundsTo
  refine ⟨hE, hhi, hlo, ?_, ?_, ?_⟩
  · rw [e1, hY]; omega
  · rw [e2, hY]; omega
  · rw [e1, e2, hY]; omega

theorem binade_normal (N M W : ℕ) (hM1 : 2 ^ M ≤ N) (hM2 : N < 2 ^ (M + 1))
    (hA : 1378 ≤ W + M) :
    N * 2 ^ W < 2 ^ 53 * spacing (W + M - 1377) ∧ 2 ^ 52 * spacing (W + M - 1377) ≤ N * 2 ^ W := by
  have e1 : 2 ^ 53 * spacing (W + M - 1377) = 2 ^ (M + 1) * 2 ^ W := by
    unfold spacing
    rw [← pow_add, ← pow_add, show 53 + (W + M - 1377 + 1325) = M + 1 + W by omega]
  have e2 : 2 ^ 52 * spacing (W + M - 1377) = 2 ^ M * 2 ^ W := by
    unfold spacing
    rw [← pow_add, ← pow_add, show 52 + (W + M - 1377 + 1325) = M + W by omega]
  rw [e1, e2]
  exact ⟨Nat.mul_lt_mul_of_pos_right hM2 (by positivity), Nat.mul_le_mul_right _ hM1⟩

theorem binade_sub (N M W : ℕ) (hM2 : N < 2 ^ (M + 1)) (hA : W + M < 1378) :
    N * 2 ^ W < 2 ^ 53 * spacing 1 := by
  unfold spacing
  calc N * 2 ^ W < 2 ^ (M + 1) * 2 ^ W := Nat.mul_lt_mul_of_pos_right hM2 (by positivity)
    _ = 2 ^ (M + 1 + W) := (pow_add 2 (M + 1) W).symm
    _ ≤ 2 ^ (53 + (1 + 1325)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ 53 * 2 ^ (1 + 1325) := by rw [pow_add]

/-- The quotient by `2 ^ r` of a number below `2 ^ (M + 1)` lies below `2 ^ (M + 1 - r)`. -/
theorem div_small (N M r : ℕ) (hM2 : N < 2 ^ (M + 1)) (hr : r ≤ M + 1) :
    N / 2 ^ r < 2 ^ (M + 1 - r) := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hr]
  exact hM2

#print axioms assemble_spec
#print axioms sig_round
#print axioms round_right
#print axioms roundsTo_of
#print axioms roundsTo_exact

end Library.Numerics.Arithmetic.Fma.FmaRound
