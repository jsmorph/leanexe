module

public import Library.Numerics.Bignum.Second.Base

@[expose] public section

/-!
Karatsuba's product in place.  `kara t W ap bp rp tp n` writes the product of the `n` limbs from
`ap` and the `n` limbs from `bp` over the `2 n` words from `rp`, and it uses the `6 n` words from
`tp` as scratch.  Below the threshold, `max t 16`, it is Algorithm M in place.  Above it, with
`h = ⌈n / 2⌉` and `l = ⌊n / 2⌋`, `A = A0 + 2^(32 h) A1` and `B = B0 + 2^(32 h) B1`, it writes
`A0 B0` and `A1 B1` into the two halves of the result, the sums `A0 + A1` and `B0 + B1` of
`h + 1` limbs into the scratch, their product of `2 h + 2` limbs after them, subtracts `A0 B0`
and `A1 B1` from that product, which leaves `A0 B1 + A1 B0`, and adds it to the result from limb
`h` on.  The third product's scratch starts at `4 h + 4` and needs `6 (h + 1)` words, which fit in
`6 n` when `n ≥ 15`.

`kara_spec` states the result for any threshold, by strong induction on `n`, for operands below
the result and a result below the scratch, the order of every call in the library.  The operands
may overlap, as in a square.  The words outside the result and the scratch keep their values.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The ranges `[a, a + la)` and `[b, b + lb)` do not meet. -/
def Apart (a la b lb : ℕ) : Prop := a + la ≤ b ∨ b + lb ≤ a

/-- The facts that `kara_spec` states of the result `R` of a call on operands of `n` limbs from
`ap` and `bp`, with the result from `rp` and the scratch from `tp`. -/
def KaraPost (n : ℕ) (W : Array UInt64) (ap bp rp tp : ℕ) (R : Array UInt64) : Prop :=
  R.size = W.size ∧
  (∀ q, ¬ (rp ≤ q ∧ q < rp + 2 * n) → ¬ (tp ≤ q ∧ q < tp + 6 * n) → R[q]! = W[q]!) ∧
  SegDigits R rp (2 * n) ∧ segVal R rp (2 * n) = segVal W ap n * segVal W bp n

/-- A product is at least either factor's product with a smaller cofactor. -/
theorem carry_zero {X Y c P : ℕ} (hX : X < P) (hY : Y ≤ Z) (h : X + Y = Z + c * P) : c = 0 := by
  by_contra hne
  have : 1 * P ≤ c * P := Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hne)
  omega

set_option maxHeartbeats 2000000 in
/-- `kara` writes the product of two segments of `n` limbs over the `2 n` words from `rp`, and it
changes no word outside those and the `6 n` words of scratch from `tp`. -/
theorem kara_spec (t : UInt64) : ∀ (n : ℕ) (W : Array UInt64) (ap bp rp tp nn : UInt64),
    nn.toNat = n → W.size < 2 ^ 64 →
    ap.toNat + n ≤ rp.toNat → bp.toNat + n ≤ rp.toNat → rp.toNat + 2 * n ≤ tp.toNat →
    tp.toNat + 6 * n ≤ W.size →
    SegDigits W ap.toNat n → SegDigits W bp.toNat n →
    KaraPost n W ap.toNat bp.toNat rp.toNat tp.toNat (kara t W ap bp rp tp nn) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W ap bp rp tp nn hn hW ha hb hr ht hda hdb
  rw [kara]
  by_cases hc : nn < t ∨ nn < 16
  · rw [dif_pos hc]
    have hnn : nn.toNat + nn.toNat = 2 * n := by omega
    obtain ⟨h1, h2, h3, h4⟩ := baseMul_spec W ap nn bp nn rp hW (by omega) (by omega)
      (by omega) (by omega) (by omega) (hn ▸ hda) (hn ▸ hdb)
    rw [hnn] at h2 h3 h4
    rw [hn] at h4
    exact ⟨h1, fun q hq _ => h2 q (by omega), h3, h4⟩
  rw [dif_neg hc]
  have h16 : 16 ≤ n := by
    have h2 := (not_or.mp hc).2
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at h2
    simp only [UInt64.reduceToNat] at h2
    omega
  lift_lets
  intro h l W1 W2 s3 W3 s4 W4 W5 W6 W7
  have hnlt := UInt64.toNat_lt nn
  have hH : h.toNat = n - n / 2 := by
    show (nn - nn / 2).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]; simp only [UInt64.reduceToNat]; omega),
      UInt64.toNat_div, hn]; rfl
  have hL : l.toNat = n / 2 := by
    show (nn / 2).toNat = _
    rw [UInt64.toNat_div, hn]; rfl
  have e1 : W1 = kara t W ap bp rp tp h := rfl
  have e2 : W2 = kara t W1 (ap + h) (bp + h) (rp + 2 * h) tp l := rfl
  have e3 : s3 = addGen W2 ap (ap + h) l tp h := rfl
  have e3' : W3 = s3.2.set! (tp + h).toNat s3.1 := rfl
  have e4 : s4 = addGen W3 bp (bp + h) l (tp + h + 1) h := rfl
  have e4' : W4 = s4.2.set! (tp + 2 * h + 1).toNat s4.1 := rfl
  have e5 : W5 = kara t W4 tp (tp + h + 1) (tp + 2 * h + 2) (tp + 4 * h + 4) (h + 1) := rfl
  have e6 : W6 = (subGen W5 (tp + 2 * h + 2) rp (2 * h) (tp + 2 * h + 2) (2 * h + 2)).2 := rfl
  have e7 : W7 =
      (subGen W6 (tp + 2 * h + 2) (rp + 2 * h) (2 * l) (tp + 2 * h + 2) (2 * h + 2)).2 := rfl
  clear_value h l W1 W2 s3 W3 s4 W4 W5 W6 W7
  obtain ⟨H, hHdef⟩ : ∃ H, H = n - n / 2 := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = n / 2 := ⟨_, rfl⟩
  rw [← hHdef] at hH
  rw [← hLdef] at hL
  have hHL : H + L = n := by omega
  have hLH : L ≤ H := by omega
  have hHL1 : H ≤ L + 1 := by omega
  have h10 : 10 * H + 10 ≤ 6 * n := by omega
  have h8 : 8 ≤ L := by omega
  -- positions as words
  have pa : (ap + h).toNat = ap.toNat + H := by
    simp only [UInt64.toNat_add, hH]; omega
  have pb : (bp + h).toNat = bp.toNat + H := by
    simp only [UInt64.toNat_add, hH]; omega
  have p2h : (2 * h).toNat = 2 * H := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat, hH]; omega
  have p2l : (2 * l).toNat = 2 * L := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat, hL]; omega
  have pr2h : (rp + 2 * h).toNat = rp.toNat + 2 * H := by
    simp only [UInt64.toNat_add, p2h]; omega
  have pth : (tp + h).toNat = tp.toNat + H := by
    simp only [UInt64.toNat_add, hH]; omega
  have pth1 : (tp + h + 1).toNat = tp.toNat + H + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat, hH]; omega
  have pt2h1 : (tp + 2 * h + 1).toNat = tp.toNat + 2 * H + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat, p2h]; omega
  have pt2h2 : (tp + 2 * h + 2).toNat = tp.toNat + 2 * H + 2 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat, p2h]; omega
  have pt4h4 : (tp + 4 * h + 4).toNat = tp.toNat + 4 * H + 4 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, hH]; omega
  have ph1 : (h + 1).toNat = H + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat, hH]; omega
  have p2h2 : (2 * h + 2).toNat = 2 * H + 2 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat, p2h]; omega
  have prh : (rp + h).toNat = rp.toNat + H := by
    simp only [UInt64.toNat_add, hH]; omega
  have p2nh : (2 * nn - h).toNat = 2 * n - H := by
    have p2n : (2 * nn).toNat = 2 * n := by
      simp only [UInt64.toNat_mul, UInt64.reduceToNat, hn]; omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, p2n, hH]; omega), p2n, hH]
  -- the halves of the operands
  obtain ⟨A0, hA0⟩ : ∃ x, x = segVal W ap.toNat H := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ x, x = segVal W (ap.toNat + H) L := ⟨_, rfl⟩
  obtain ⟨B0, hB0⟩ : ∃ x, x = segVal W bp.toNat H := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ x, x = segVal W (bp.toNat + H) L := ⟨_, rfl⟩
  have hdA0 : SegDigits W ap.toNat H := hda.mono (by omega)
  have hdB0 : SegDigits W bp.toNat H := hdb.mono (by omega)
  have hdA1 : SegDigits W (ap.toNat + H) L := fun i hi => by
    rw [Nat.add_assoc]; exact hda (H + i) (by omega)
  have hdB1 : SegDigits W (bp.toNat + H) L := fun i hi => by
    rw [Nat.add_assoc]; exact hdb (H + i) (by omega)
  /- Step 1: `A0 B0` over the first `2 h` words of the result. -/
  have k1 : KaraPost H W ap.toNat bp.toNat rp.toNat tp.toNat W1 := by
    rw [e1]
    exact ih H (by omega) W ap bp rp tp h hH hW (by omega) (by omega) (by omega) (by omega)
      hdA0 hdB0
  obtain ⟨s1, f1, d1, v1⟩ := k1
  rw [← hA0, ← hB0] at v1
  have rA1 : ∀ i, i < n → W1[ap.toNat + i]! = W[ap.toNat + i]! :=
    fun i hi => f1 _ (by omega) (by omega)
  have rB1 : ∀ i, i < n → W1[bp.toNat + i]! = W[bp.toNat + i]! :=
    fun i hi => f1 _ (by omega) (by omega)
  /- Step 2: `A1 B1` over the next `2 l` words. -/
  have k2 : KaraPost L W1 (ap.toNat + H) (bp.toNat + H) (rp.toNat + 2 * H) tp.toNat W2 := by
    rw [e2, ← pa, ← pb, ← pr2h]
    exact ih L (by omega) W1 (ap + h) (bp + h) (rp + 2 * h) tp l hL (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by rw [pa]; exact hdA1.congr fun i hi => by rw [Nat.add_assoc, rA1 _ (by omega)])
      (by rw [pb]; exact hdB1.congr fun i hi => by rw [Nat.add_assoc, rB1 _ (by omega)])
  obtain ⟨s2, f2, d2, v2⟩ := k2
  have vA1 : segVal W1 (ap.toNat + H) L = A1 := by
    rw [hA1]; exact segVal_congr fun i hi => by rw [Nat.add_assoc, rA1 _ (by omega)]
  have vB1 : segVal W1 (bp.toNat + H) L = B1 := by
    rw [hB1]; exact segVal_congr fun i hi => by rw [Nat.add_assoc, rB1 _ (by omega)]
  rw [vA1, vB1] at v2
  have rA2 : ∀ i, i < n → W2[ap.toNat + i]! = W[ap.toNat + i]! :=
    fun i hi => by rw [f2 _ (by omega) (by omega)]; exact rA1 i hi
  have rB2 : ∀ i, i < n → W2[bp.toNat + i]! = W[bp.toNat + i]! :=
    fun i hi => by rw [f2 _ (by omega) (by omega)]; exact rB1 i hi
  have e2W : ∀ q, (q < rp.toNat ∨ rp.toNat + 2 * n ≤ q) → (q < tp.toNat ∨ tp.toNat + 6 * n ≤ q) →
      W2[q]! = W[q]! := fun q h1 h2 => by
    rw [f2 q (by omega) (by omega)]; exact f1 q (by omega) (by omega)
  have dR2 : SegDigits W2 rp.toNat (2 * n) := by
    have h1 : SegDigits W2 rp.toNat (2 * H) := d1.congr fun i hi => f2 _ (by omega) (by omega)
    have := h1.join d2
    rwa [show 2 * H + 2 * L = 2 * n by omega] at this
  have vR2 : segVal W2 rp.toNat (2 * n) = A0 * B0 + base ^ (2 * H) * (A1 * B1) := by
    have h1 : segVal W2 rp.toNat (2 * H) = A0 * B0 := by
      rw [← v1]; exact segVal_congr fun i hi => f2 _ (by omega) (by omega)
    rw [show 2 * n = 2 * H + 2 * L by omega, segVal_add, h1, v2]
  have v1R : segVal W2 rp.toNat (2 * H) = A0 * B0 := by
    rw [← v1]; exact segVal_congr fun i hi => f2 _ (by omega) (by omega)
  clear f1 f2 rA1 rB1 vA1 vB1 d1 v1 d2
  have s2' : W2.size = W.size := by rw [s2, s1]
  /- Step 3: `A0 + A1` over `h + 1` words of the scratch. -/
  have k3 := addGen_spec W2 ap (ap + h) l tp h (by omega) (by omega)
    (by rw [pa, hL, hH]; omega) (by omega)
    (fun i hi => by rw [rA2 i (by omega)]; exact hdA0 i (by omega))
    (fun i hi => by
      rw [pa, Nat.add_assoc, rA2 (H + i) (by omega), ← Nat.add_assoc]; exact hdA1 i (by omega))
    (fun i j _ hj => by omega) (fun i j _ hj => by rw [pa]; omega)
  rw [← e3, pa, hH, hL, show min L H = L by omega] at k3
  obtain ⟨s3s, f3, d3, c3, v3⟩ := k3
  have vA0 : segVal W2 ap.toNat H = A0 := by
    rw [hA0]; exact segVal_congr fun i hi => rA2 i (by omega)
  have vA1 : segVal W2 (ap.toNat + H) L = A1 := by
    rw [hA1]; exact segVal_congr fun i hi => by rw [Nat.add_assoc, rA2 _ (by omega)]
  rw [vA0, vA1] at v3
  rw [pth] at e3'
  have g3 := fun q => get_set s3.2 (tp.toNat + H) s3.1 q (by omega)
  rw [← e3'] at g3
  have f3' : ∀ q, (q < tp.toNat ∨ tp.toNat + H + 1 ≤ q) → W3[q]! = W2[q]! :=
    fun q hq => by rw [g3, if_neg (by omega)]; exact f3 q (by omega)
  have d3' : SegDigits W3 tp.toNat (H + 1) := fun i hi => by
    rw [g3]; split
    · rw [base_eq]; omega
    · exact d3 i (by omega)
  have v3' : segVal W3 tp.toNat (H + 1) = A0 + A1 := by
    rw [segVal_succ, g3, if_pos rfl, ← v3]
    congr 1
    exact segVal_congr fun i hi => by rw [g3, if_neg (by omega)]
  have s3' : W3.size = W.size := by rw [e3']; simp [s3s, s2']
  clear g3 f3 d3 v3 c3 s3s
  /- Step 4: `B0 + B1` over the next `h + 1` words. -/
  have rB3 : ∀ i, i < n → W3[bp.toNat + i]! = W[bp.toNat + i]! :=
    fun i hi => by rw [f3' _ (by omega)]; exact rB2 i hi
  have k4 := addGen_spec W3 bp (bp + h) l (tp + h + 1) h (by omega) (by omega)
    (by rw [pb, hL, hH]; omega) (by rw [pth1, hH]; omega)
    (fun i hi => by rw [rB3 i (by omega)]; exact hdB0 i (by omega))
    (fun i hi => by
      rw [pb, Nat.add_assoc, rB3 (H + i) (by omega), ← Nat.add_assoc]; exact hdB1 i (by omega))
    (fun i j _ hj => by rw [pth1]; omega) (fun i j _ hj => by rw [pb, pth1]; omega)
  rw [← e4, pb, pth1, hH, hL, show min L H = L by omega] at k4
  obtain ⟨s4s, f4, d4, c4, v4⟩ := k4
  have vB0 : segVal W3 bp.toNat H = B0 := by
    rw [hB0]; exact segVal_congr fun i hi => rB3 i (by omega)
  have vB1 : segVal W3 (bp.toNat + H) L = B1 := by
    rw [hB1]; exact segVal_congr fun i hi => by rw [Nat.add_assoc, rB3 _ (by omega)]
  rw [vB0, vB1] at v4
  rw [pt2h1] at e4'
  have g4 := fun q => get_set s4.2 (tp.toNat + 2 * H + 1) s4.1 q (by omega)
  rw [← e4'] at g4
  have f4' : ∀ q, (q < tp.toNat + H + 1 ∨ tp.toNat + 2 * H + 2 ≤ q) → W4[q]! = W3[q]! :=
    fun q hq => by rw [g4, if_neg (by omega)]; exact f4 q (by omega)
  have d4' : SegDigits W4 (tp.toNat + H + 1) (H + 1) := fun i hi => by
    rw [g4]; split
    · rw [base_eq]; omega
    · exact d4 i (by omega)
  have v4' : segVal W4 (tp.toNat + H + 1) (H + 1) = B0 + B1 := by
    rw [segVal_succ, g4, if_pos (by omega), ← v4]
    congr 1
    exact segVal_congr fun i hi => by rw [g4, if_neg (by omega)]
  have s4' : W4.size = W.size := by rw [e4']; simp [s4s, s3']
  clear g4 f4 d4 v4 c4 s4s rB3
  /- Step 5: `(A0 + A1) (B0 + B1)` over `2 h + 2` words after the sums. -/
  have d3'' : SegDigits W4 tp.toNat (H + 1) := d3'.congr fun i hi => f4' _ (by omega)
  have v3'' : segVal W4 tp.toNat (H + 1) = A0 + A1 := by
    rw [← v3']; exact segVal_congr fun i hi => f4' _ (by omega)
  have k5 : KaraPost (H + 1) W4 tp.toNat (tp.toNat + H + 1) (tp.toNat + 2 * H + 2)
      (tp.toNat + 4 * H + 4) W5 := by
    rw [e5, ← pth1, ← pt2h2, ← pt4h4]
    exact ih (H + 1) (by omega) W4 tp (tp + h + 1) (tp + 2 * h + 2) (tp + 4 * h + 4) (h + 1)
      ph1 (by omega) (by omega) (by rw [pth1, pt2h2]; omega) (by rw [pt2h2, pt4h4]; omega)
      (by rw [pt4h4]; omega) d3'' (by rw [pth1]; exact d4')
  obtain ⟨s5, f5, d5, v5⟩ := k5
  rw [v3'', v4'] at v5
  rw [show 2 * (H + 1) = 2 * H + 2 by omega] at d5 v5 f5
  -- the result's words through steps 3 to 5
  have rR5 : ∀ q, rp.toNat ≤ q → q < rp.toNat + 2 * n → W5[q]! = W2[q]! := fun q h1 h2 => by
    rw [f5 q (by omega) (by omega), f4' q (by omega), f3' q (by omega)]
  have e5W : ∀ q, (q < rp.toNat ∨ rp.toNat + 2 * n ≤ q) → (q < tp.toNat ∨ tp.toNat + 6 * n ≤ q) →
      W5[q]! = W[q]! := fun q h1 h2 => by
    rw [f5 q (by omega) (by omega), f4' q (by omega), f3' q (by omega)]; exact e2W q h1 h2
  have s5' : W5.size = W.size := by rw [s5, s4']
  clear f4' d3'' v3'' d4' v4' d3' v3' s5
  /- Step 6: subtract `A0 B0`. -/
  have k6 := subGen_spec W5 (tp + 2 * h + 2) rp (2 * h) (tp + 2 * h + 2) (2 * h + 2) (by omega)
    (by rw [pt2h2, p2h2]; omega) (by rw [p2h, p2h2]; omega) (by rw [pt2h2, p2h2]; omega)
    (by rw [pt2h2, p2h2]; exact d5)
    (by rw [p2h, p2h2, show min (2 * H) (2 * H + 2) = 2 * H by omega]
        exact fun i hi => by rw [rR5 _ (by omega) (by omega)]; exact dR2 i (by omega))
    (fun i j h1 _ => by omega)
    (fun i j _ hj => by rw [pt2h2, p2h, p2h2] at *; omega)
  rw [← e6, pt2h2, p2h, p2h2, show min (2 * H) (2 * H + 2) = 2 * H by omega] at k6
  obtain ⟨s6, f6, d6, c6, v6⟩ := k6
  have vP0 : segVal W5 rp.toNat (2 * H) = A0 * B0 := by
    rw [← v1R]; exact segVal_congr fun i hi => rR5 _ (by omega) (by omega)
  rw [vP0, v5] at v6
  have hle6 : A0 * B0 ≤ (A0 + A1) * (B0 + B1) :=
    Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  rw [carry_zero (segVal_lt d6) hle6 v6, Nat.zero_mul, Nat.add_zero] at v6
  have rR6 : ∀ q, rp.toNat ≤ q → q < rp.toNat + 2 * n → W6[q]! = W2[q]! := fun q h1 h2 => by
    rw [f6 q (by omega)]; exact rR5 q h1 h2
  have e6W : ∀ q, (q < rp.toNat ∨ rp.toNat + 2 * n ≤ q) → (q < tp.toNat ∨ tp.toNat + 6 * n ≤ q) →
      W6[q]! = W[q]! := fun q h1 h2 => by
    rw [f6 q (by omega)]; exact e5W q h1 h2
  have s6' : W6.size = W.size := by rw [s6, s5']
  clear f5 d5 v5 rR5 e5W s6 f6 hle6 vP0
  /- Step 7: subtract `A1 B1`, which leaves `A0 B1 + A1 B0`. -/
  have k7 := subGen_spec W6 (tp + 2 * h + 2) (rp + 2 * h) (2 * l) (tp + 2 * h + 2) (2 * h + 2)
    (by omega) (by rw [pt2h2, p2h2]; omega) (by rw [pr2h, p2l, p2h2]; omega)
    (by rw [pt2h2, p2h2]; omega)
    (by rw [pt2h2, p2h2]; exact d6)
    (by rw [pr2h, p2l, p2h2, show min (2 * L) (2 * H + 2) = 2 * L by omega]
        exact fun i hi => by
          rw [Nat.add_assoc, rR6 _ (by omega) (by omega)]; exact dR2 (2 * H + i) (by omega))
    (fun i j h1 _ => by omega)
    (fun i j _ hj => by rw [pt2h2, pr2h, p2l, p2h2] at *; omega)
  rw [← e7, pt2h2, pr2h, p2l, p2h2, show min (2 * L) (2 * H + 2) = 2 * L by omega] at k7
  obtain ⟨s7, f7, d7, c7, v7⟩ := k7
  have vP2 : segVal W6 (rp.toNat + 2 * H) (2 * L) = A1 * B1 := by
    rw [← v2]; exact segVal_congr fun i hi => by rw [Nat.add_assoc, rR6 _ (by omega) (by omega)]
  rw [vP2] at v7
  have hm6 : segVal W6 (tp.toNat + 2 * H + 2) (2 * H + 2) = A0 * B1 + A1 * B0 + A1 * B1 := by
    linarith [v6]
  have hle7 : A1 * B1 ≤ segVal W6 (tp.toNat + 2 * H + 2) (2 * H + 2) := by rw [hm6]; omega
  rw [carry_zero (segVal_lt d7) hle7 v7, Nat.zero_mul, Nat.add_zero, hm6] at v7
  have hM : segVal W7 (tp.toNat + 2 * H + 2) (2 * H + 2) = A0 * B1 + A1 * B0 := by omega
  have rR7 : ∀ q, rp.toNat ≤ q → q < rp.toNat + 2 * n → W7[q]! = W2[q]! := fun q h1 h2 => by
    rw [f7 q (by omega)]; exact rR6 q h1 h2
  have e7W : ∀ q, (q < rp.toNat ∨ rp.toNat + 2 * n ≤ q) → (q < tp.toNat ∨ tp.toNat + 6 * n ≤ q) →
      W7[q]! = W[q]! := fun q h1 h2 => by
    rw [f7 q (by omega)]; exact e6W q h1 h2
  have s7' : W7.size = W.size := by rw [s7, s6']
  clear rR6 e6W f7 v7 c7 s7 hle7 hm6 vP2 v6 d6
  /- Step 8: add `A0 B1 + A1 B0` from limb `h` of the result on. -/
  have hmin : min (2 * H + 2) (2 * n - H) = 2 * H + 2 := by omega
  have k8 := addGen_spec W7 (rp + h) (tp + 2 * h + 2) (2 * h + 2) (rp + h) (2 * nn - h) (by omega)
    (by rw [prh, p2nh]; omega) (by rw [pt2h2, p2h2, p2nh, hmin]; omega)
    (by rw [prh, p2nh]; omega)
    (by rw [prh, p2nh]
        exact fun i hi => by
          rw [Nat.add_assoc, rR7 _ (by omega) (by omega)]; exact dR2 (H + i) (by omega))
    (by rw [pt2h2, p2h2, p2nh, hmin]; exact d7)
    (fun i j _ _ => by omega)
    (fun i j _ hj => by rw [prh, pt2h2, p2h2, p2nh, hmin] at *; omega)
  rw [prh, pt2h2, p2h2, p2nh, hmin, hM] at k8
  generalize addGen W7 (rp + h) (tp + 2 * h + 2) (2 * h + 2) (rp + h) (2 * nn - h) = S8 at k8 ⊢
  obtain ⟨s8, f8, d8, c8, v8⟩ := k8
  -- the value
  have hT : segVal W7 (rp.toNat + H) (2 * n - H) = segVal W2 (rp.toNat + H) (2 * n - H) :=
    segVal_congr fun i hi => by rw [Nat.add_assoc, rR7 _ (by omega) (by omega)]
  have hlow : segVal S8.2 rp.toNat H = segVal W2 rp.toNat H :=
    segVal_congr fun i hi => by rw [f8 _ (by omega), rR7 _ (by omega) (by omega)]
  have hsplitW := segVal_add W2 rp.toNat H (2 * n - H)
  rw [show H + (2 * n - H) = 2 * n by omega, vR2] at hsplitW
  have hsplitS := segVal_add S8.2 rp.toNat H (2 * n - H)
  rw [show H + (2 * n - H) = 2 * n by omega, hlow] at hsplitS
  have hA := segVal_add W ap.toNat H L
  have hB := segVal_add W bp.toNat H L
  rw [hHL, ← hA0, ← hA1] at hA
  rw [hHL, ← hB0, ← hB1] at hB
  have hprod : segVal W ap.toNat n * segVal W bp.toNat n =
      A0 * B0 + base ^ (2 * H) * (A1 * B1) + base ^ H * (A0 * B1 + A1 * B0) := by
    rw [hA, hB, show 2 * H = H + H by omega, pow_add]; ring
  have hABlt : segVal W ap.toNat n * segVal W bp.toNat n < base ^ (2 * n) := by
    rw [show 2 * n = n + n by omega, pow_add]
    exact Nat.mul_lt_mul'' (segVal_lt hda) (segVal_lt hdb)
  have hpow : base ^ (2 * n) = base ^ H * base ^ (2 * n - H) := by
    rw [← pow_add]; congr 1; omega
  have hsum : segVal W ap.toNat n * segVal W bp.toNat n = segVal W2 rp.toNat H +
      base ^ H * (segVal W2 (rp.toNat + H) (2 * n - H) + (A0 * B1 + A1 * B0)) := by
    rw [hprod, hsplitW]; ring
  have hTM : segVal W2 (rp.toNat + H) (2 * n - H) + (A0 * B1 + A1 * B0) < base ^ (2 * n - H) := by
    have h1 : base ^ H * (segVal W2 (rp.toNat + H) (2 * n - H) + (A0 * B1 + A1 * B0)) <
        base ^ H * base ^ (2 * n - H) := by
      rw [← hpow]
      exact lt_of_le_of_lt (Nat.le_add_left _ _) (hsum ▸ hABlt)
    exact Nat.lt_of_mul_lt_mul_left h1
  rw [hT] at v8
  have hc8 : S8.1.toNat = 0 := by
    by_contra hne
    have : 1 * base ^ (2 * n - H) ≤ S8.1.toNat * base ^ (2 * n - H) :=
      Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  rw [hc8, Nat.zero_mul, Nat.add_zero] at v8
  refine ⟨by rw [s8, s7'], fun q hq1 hq2 => ?_, fun i hi => ?_, ?_⟩
  · rw [f8 q (by omega)]; exact e7W q (by omega) (by omega)
  · by_cases hiH : i < H
    · rw [f8 _ (by omega), rR7 _ (by omega) (by omega)]; exact dR2 i hi
    · have := d8 (i - H) (by omega)
      rwa [show rp.toNat + H + (i - H) = rp.toNat + i by omega] at this
  · rw [hsplitS, v8, hsum]

end Library.Numerics.Bignum
