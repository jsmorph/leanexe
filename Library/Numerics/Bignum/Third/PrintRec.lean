module

public import Library.Numerics.Bignum.Third.PrintLeaf

@[expose] public section

/-!
Algorithm 1.26 in place: `toChunks_spec` states that `toChunks` at level `i` writes the `2^(i+1)`
chunks of nine digits of a number below `P_i² = 10^(9·2^(i+1))`, by induction on the level.  A
number below `β^(n_i)` is converted at level `i - 1` with zero chunks above, and any other number
is divided by `P_i` with `divSeg`, its quotient converted at level `i - 1` from the next free words
and its remainder in place.  `chunk_split` is the arithmetic of the split: the chunks of
`Q 10^(9 h) + R` below `h` are those of `R`, and the chunks from `h` on are those of `Q`.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The chunks of `Q B^h + R`, `R < B^h`: those of `R` below `h` and those of `Q` from `h` on. -/
theorem chunk_split {B Q R h j : ℕ} (hB : 0 < B) (hR : R < B ^ h) :
    (j < h → (Q * B ^ h + R) / B ^ j % B = R / B ^ j % B) ∧
      (h ≤ j → (Q * B ^ h + R) / B ^ j % B = Q / B ^ (j - h) % B) := by
  constructor
  · intro hj
    obtain ⟨d, hd⟩ : ∃ d, h = j + 1 + d := ⟨h - j - 1, by omega⟩
    have e : Q * B ^ h + R = R + (Q * B ^ d * B) * B ^ j := by rw [hd]; ring
    rw [e, Nat.add_mul_div_right _ _ (pow_pos hB _), Nat.add_mul_mod_self_right]
  · intro hj
    have hRj : R / B ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hR (Nat.pow_le_pow_right hB hj))
    rw [show B ^ j = B ^ h * B ^ (j - h) by rw [← pow_add]; congr 1; omega,
      ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos hB _),
      Nat.div_eq_of_lt hR, Nat.zero_add]

/-- The bounds of a power from its entry in the table. -/
theorem PowOK.bounds {W : Array UInt64} {tb pb j : ℕ} (h : PowOK W tb pb j) :
    base ^ (W[tb + 2 * j + 1]!.toNat - 1) ≤ 10 ^ (9 * 2 ^ j) ∧
      10 ^ (9 * 2 ^ j) < base ^ W[tb + 2 * j + 1]!.toNat := by
  obtain ⟨-, -, a3, -, a5, a6, a7⟩ := h
  exact ⟨a6 ▸ segVal_ge_top a3 a7, a6 ▸ segVal_lt a5⟩

/-- The lengths of consecutive powers: `2 n_(i-1) - 1 ≤ n_i ≤ 2 n_(i-1)`, and `n_i ≥ 2` for
`i ≥ 1`. -/
theorem pow_lengths {a b i : ℕ} (ha : base ^ (a - 1) ≤ 10 ^ (9 * 2 ^ i))
    (ha' : 10 ^ (9 * 2 ^ i) < base ^ a) (hb : base ^ (b - 1) ≤ 10 ^ (9 * 2 ^ (i + 1)))
    (hb' : 10 ^ (9 * 2 ^ (i + 1)) < base ^ b) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) :
    2 * a - 1 ≤ b ∧ b ≤ 2 * a ∧ 2 ≤ b := by
  have hsq : 10 ^ (9 * 2 ^ (i + 1)) = 10 ^ (9 * 2 ^ i) * 10 ^ (9 * 2 ^ i) := by
    rw [← pow_add]; ring_nf
  have h1 : base < base ^ b := by
    calc base = 4294967296 := base_eq
      _ < 10 ^ 18 := by norm_num
      _ ≤ 10 ^ (9 * 2 ^ (i + 1)) := Nat.pow_le_pow_right (by norm_num) (by
          have : 2 ≤ 2 ^ (i + 1) := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
      _ < base ^ b := hb'
  have hbase : 1 < base := by rw [base_eq]; norm_num
  have hb2 : 2 ≤ b := by
    by_contra hc
    have : b ≤ 1 := by omega
    have := Nat.pow_le_pow_right base_pos this
    rw [pow_one] at this; omega
  refine ⟨?_, ?_, hb2⟩
  · by_contra hc
    have hlt : b < 2 * a - 1 := by omega
    have h2 : base ^ b ≤ base ^ (2 * a - 2) := Nat.pow_le_pow_right base_pos (by omega)
    have h3 : base ^ (2 * a - 2) ≤ 10 ^ (9 * 2 ^ (i + 1)) := by
      rw [hsq, show 2 * a - 2 = (a - 1) + (a - 1) by omega, pow_add]; exact Nat.mul_le_mul ha ha
    omega
  · by_contra hc
    have h2 : base ^ (2 * a) ≤ base ^ (b - 1) := Nat.pow_le_pow_right base_pos (by omega)
    have h3 : 10 ^ (9 * 2 ^ (i + 1)) < base ^ (2 * a) := by
      rw [hsq, two_mul, pow_add]
      exact Nat.mul_lt_mul'' ha' ha'
    omega

theorem shl_two (i : UInt64) (hi : i.toNat < 63) : ((2 : UInt64) <<< i).toNat = 2 ^ (i.toNat + 1) := by
  have := UInt64.toNat_shiftLeft (2 : UInt64) i
  rw [this, show i.toNat % 64 = i.toNat by omega]
  simp only [UInt64.reduceToNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by
    have : 2 * 2 ^ i.toNat < 2 ^ 64 := by
      calc 2 * 2 ^ i.toNat = 2 ^ (i.toNat + 1) := by ring
        _ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega), pow_succ]
  ring

theorem shl_one' (i : UInt64) (hi : i.toNat < 63) : ((1 : UInt64) <<< i).toNat = 2 ^ i.toNat := by
  have := UInt64.toNat_shiftLeft (1 : UInt64) i
  rw [this, show i.toNat % 64 = i.toNat by omega]
  simp only [UInt64.reduceToNat, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- What `toChunks` at level `i` leaves: the `2^(i+1)` chunks of `X` at `cp`, and every word
outside the number's `2 N` limbs at `p`, the chunks, and the `16 N + 11` words from `fp` kept. -/
def ChunksPost (W : Array UInt64) (p cp fp N X i : ℕ) (R : Array UInt64) : Prop :=
  R.size = W.size ∧
  (∀ q, ¬ (p ≤ q ∧ q < p + 2 * N) → ¬ (cp ≤ q ∧ q < cp + 2 ^ (i + 1)) →
    ¬ (fp ≤ q ∧ q < fp + 16 * N + 11) → R[q]! = W[q]!) ∧
  ∀ j, j < 2 ^ (i + 1) → R[cp + j]!.toNat = X / 10 ^ (9 * j) % 10 ^ 9

set_option maxHeartbeats 8000000 in
/-- Algorithm 1.26 at level `i`: `toChunks` writes the chunks of nine digits of the `2 n_i` limbs
at `p`, below `P_i²`, for the table of the powers below `p` and the chunks below the powers. -/
theorem toChunks_spec (t T L : UInt64) : ∀ (i : ℕ) (W : Array UInt64) (tb ii p cp fp : UInt64)
    (pb : ℕ), ii.toNat = i → i < 40 → W.size < 2 ^ 62 →
    (∀ j, j ≤ i → PowOK W tb.toNat pb j) →
    tb.toNat + 2 * i + 2 ≤ cp.toNat → cp.toNat + 2 ^ (i + 1) ≤ pb →
    (∀ j, j ≤ i → W[tb.toNat + 2 * j]!.toNat + W[tb.toNat + 2 * j + 1]!.toNat ≤ p.toNat) →
    p.toNat + 2 * W[tb.toNat + 2 * i + 1]!.toNat ≤ fp.toNat →
    fp.toNat + 16 * W[tb.toNat + 2 * i + 1]!.toNat + 11 ≤ W.size →
    SegDigits W p.toNat (2 * W[tb.toNat + 2 * i + 1]!.toNat) →
    segVal W p.toNat (2 * W[tb.toNat + 2 * i + 1]!.toNat) < 10 ^ (9 * 2 ^ (i + 1)) →
    ChunksPost W p.toNat cp.toNat fp.toNat W[tb.toNat + 2 * i + 1]!.toNat
      (segVal W p.toNat (2 * W[tb.toNat + 2 * i + 1]!.toNat)) i (toChunks t T L W tb ii p cp fp) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro W tb ii p cp fp pb hii hi40 hW hpow htc hcp hpe hpf hfs hdx hX
  rw [toChunks]
  have hpb0 := (hpow 0 (Nat.zero_le _)).1
  have hpe0 := hpe 0 (Nat.zero_le _)
  have h2pos : 0 < 2 ^ (i + 1) := pow_pos (by norm_num) _
  have hcpp : cp.toNat + 2 ^ (i + 1) ≤ p.toNat := by omega
  have h2i : (tb + 2 * ii).toNat = tb.toNat + 2 * i := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hii, UInt64.reduceToNat]; omega
  have h2i1 : (tb + 2 * ii + 1).toNat = tb.toNat + 2 * i + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hii, UInt64.reduceToNat]; omega
  rw [h2i, h2i1]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hpow i le_rfl
  generalize hnw : W[tb.toNat + 2 * i + 1]! = nw at a1 a2 a3 a4 a5 a6 a7 hpf hfs hdx hX ⊢
  generalize hdw : W[tb.toNat + 2 * i]! = dw at a1 a2 a3 a4 a5 a6 a7 ⊢
  generalize hN : nw.toNat = N at a1 a2 a3 a4 a5 a6 a7 hpf hfs hdx hX ⊢
  have h2n : (2 * nw).toNat = 2 * N := by
    simp only [UInt64.toNat_mul, hN, UInt64.reduceToNat]; omega
  -- the significant limbs
  obtain ⟨g1, g2, g3⟩ := sigSeg_spec W p (2 * nw) (by rw [h2n]; omega)
  rw [h2n] at g1 g2
  generalize hsl : (LeanExe.loop (2 * nw) (0 : UInt64) fun j k =>
    if W[(p + j).toNat]! = 0 then k else j + 1) = sl at g1 g2 g3 ⊢
  have hXs : segVal W p.toNat (2 * N) = segVal W p.toNat sl.toNat := by
    rw [show 2 * N = sl.toNat + (2 * N - sl.toNat) by omega, segVal_add,
      segVal_zeros (W := W) (p := p.toNat + sl.toNat) (k := 2 * N - sl.toNat) fun i' hi' => by
        rw [Nat.add_assoc]; exact g2 _ (by omega) (by omega), Nat.mul_zero, Nat.add_zero]
  generalize hXv : segVal W p.toNat (2 * N) = X at hX hXs ⊢
  by_cases hc : ii ≤ L ∨ ii = 0
  · -- a leaf: the first iteration's quadratic printer
    rw [dif_pos hc]
    have hsh := shl_two ii (by omega)
    rw [hii] at hsh
    obtain ⟨l1, l2, l3⟩ := leafChunks_spec W p sl cp ((2 : UInt64) <<< ii) hW (by omega)
      (by rw [hsh]; omega) (by rw [hsh]; omega) (hdx.mono g1)
    rw [hsh] at l2 l3
    refine ⟨l1, fun q h1 h2 h3 => l2 q (by omega) (by omega), fun j hj => by
      rw [l3 j hj, ← hXs]⟩
  rw [dif_neg hc]
  have hi1 : 1 ≤ i := by
    simp only [not_or] at hc
    exact Nat.one_le_iff_ne_zero.mpr fun h => hc.2 (UInt64.toNat_inj.mp (by rw [hii, h]; rfl))
  have hii1 : (ii - 1).toNat = i - 1 := by rw [toNat_sub_le' (by simp; omega), hii]; simp
  have hsh1 := shl_one' ii (by omega)
  rw [hii] at hsh1
  -- the previous level's power
  have hprev := hpow (i - 1) (by omega)
  obtain ⟨b1, b2⟩ := hprev.bounds
  obtain ⟨c1, c2⟩ := (hpow i le_rfl).bounds
  rw [hnw, hN] at c1 c2
  generalize hN' : W[tb.toNat + 2 * (i - 1) + 1]!.toNat = N' at b1 b2 hprev
  have hN'1 : 1 ≤ N' := by rw [← hN']; exact hprev.2.2.1
  obtain ⟨e1, e2, e3⟩ := pow_lengths (a := N') (b := N) (i := i - 1) b1 b2
    (by rw [show i - 1 + 1 = i by omega]; exact c1) (by rw [show i - 1 + 1 = i by omega]; exact c2)
    hN'1 a3
  have hidx : tb.toNat + 2 * (i - 1) + 1 = tb.toNat + 2 * (i - 1) + 1 := rfl
  have hPi : base ^ (N - 1) ≤ 10 ^ (9 * 2 ^ i) := c1
  by_cases hsl2 : sl < nw
  · -- the quotient is 0
    rw [if_pos hsl2]
    have hslN : sl.toNat < N := by rw [← hN]; exact UInt64.lt_iff_toNat_lt.mp hsl2
    have hcps : (cp + (1 : UInt64) <<< ii).toNat = cp.toNat + 2 ^ i := by
      rw [toNat_add_lt (by rw [hsh1]; omega), hsh1]
    obtain ⟨z1, z2, z3⟩ := clear_spec W (cp + (1 : UInt64) <<< ii) ((1 : UInt64) <<< ii) (by omega)
      (by rw [hcps, hsh1]; omega)
    rw [hcps, hsh1] at z2 z3
    generalize hW1 : (LeanExe.loop ((1 : UInt64) <<< ii) W fun j W =>
      W.set! (cp + (1 : UInt64) <<< ii + j).toNat 0) = W1 at z1 z2 z3
    have hW1 : ∀ q, (q < cp.toNat + 2 ^ i ∨ cp.toNat + 2 ^ i + 2 ^ i ≤ q) → W1[q]! = W[q]! := z2
    have hX1 : X < 10 ^ (9 * 2 ^ i) := by
      rw [hXs]
      calc segVal W p.toNat sl.toNat < base ^ sl.toNat := segVal_lt (hdx.mono g1)
        _ ≤ base ^ (N - 1) := Nat.pow_le_pow_right base_pos (by omega)
        _ ≤ 10 ^ (9 * 2 ^ i) := hPi
    have hW1n : W1[tb.toNat + 2 * (i - 1) + 1]! = W[tb.toNat + 2 * (i - 1) + 1]! :=
      hW1 _ (by omega)
    have hX1' : segVal W1 p.toNat (2 * N') = X := by
      rw [← hXv, segVal_congr (W := W1) (W' := W) (p := p.toNat) (p' := p.toNat)
        fun i' hi' => hW1 _ (by omega)]
      rw [show 2 * N = 2 * N' + (2 * N - 2 * N') by omega, segVal_add,
        segVal_zeros (W := W) (p := p.toNat + 2 * N') (k := 2 * N - 2 * N') fun i' hi' => by
          rw [Nat.add_assoc]; exact g2 _ (by omega) (by omega), Nat.mul_zero, Nat.add_zero]
    have r := ih (i - 1) (by omega) W1 tb (ii - 1) p cp fp pb hii1 (by omega) (by omega)
      (fun j hj => (hpow j (by omega)).congr (hW1 _ (by omega)) (hW1 _ (by omega))
        fun q h1 h2 => hW1 q (by have := (hpow j (by omega)).1; omega))
      (by omega) (by rw [show i - 1 + 1 = i by omega]; omega)
      (fun j hj => by rw [hW1 _ (by omega), hW1 _ (by omega)]; exact hpe j (by omega))
      (by rw [hW1n, hN']; omega) (by rw [hW1n, hN', z1]; omega)
      (by rw [hW1n, hN']; exact (hdx.mono (by omega)).congr fun i' hi' => hW1 _ (by omega))
      (by rw [hW1n, hN', hX1', show i - 1 + 1 = i by omega]; exact hX1)
    rw [hW1n, hN', hX1'] at r
    obtain ⟨r1, r2, r3⟩ := r
    rw [show i - 1 + 1 = i by omega] at r2 r3
    refine ⟨by rw [r1, z1], fun q h1 h2 h3 => ?_, fun j hj => ?_⟩
    · rw [r2 q (by omega) (by omega) (by omega), hW1 q (by omega)]
    · rcases Nat.lt_or_ge j (2 ^ i) with hj' | hj'
      · exact r3 j hj'
      · rw [r2 _ (by omega) (by omega) (by omega)]
        have := z3 (j - 2 ^ i) (by rw [pow_succ] at hj; omega)
        rw [show cp.toNat + 2 ^ i + (j - 2 ^ i) = cp.toNat + j by omega] at this
        rw [this, Nat.div_eq_of_lt (lt_of_lt_of_le hX1 (Nat.pow_le_pow_right (by norm_num)
          (by omega)))]
        rfl
  · -- the division by `P_i`
    rw [if_neg hsl2]
    dsimp only
    have hNsl : N ≤ sl.toNat := by
      rw [← hN]; exact UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hsl2)
    have hpei := hpe i le_rfl
    rw [hdw, hnw, hN] at hpei
    have hfn1 : (fp + nw + 1).toNat = fp.toNat + N + 1 := by
      rw [toNat_add_lt (by rw [toNat_add_lt (by omega), hN]; simp; omega), toNat_add_lt (by omega),
        hN]; simp
    have hP : segVal W dw.toNat N = 10 ^ (9 * 2 ^ i) := a6
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := divSeg_spec t T W p sl dw nw fp (fp + nw + 1) N sl.toNat hN
      rfl hW e3 hNsl (by omega) (by omega) (by rw [hfn1]; omega) (by rw [hfn1]; omega)
      (hdx.mono g1) a5 a7
    rw [hfn1] at d2
    rw [← hXs, hP] at d5 d6
    generalize hW1 : divSeg t T W p sl dw nw fp (fp + nw + 1) = W1 at d1 d2 d3 d4 d5 d6
    -- the zeros above the quotient
    have hsn : (sl - nw + 1).toNat = sl.toNat - N + 1 := by
      rw [toNat_add_lt (by rw [toNat_sub_le' (by rw [hN]; omega), hN]; simp; omega),
        toNat_sub_le' (by rw [hN]; omega), hN]; simp
    have hfs' : (fp + (sl - nw + 1)).toNat = fp.toNat + (sl.toNat - N + 1) := by
      rw [toNat_add_lt (by rw [hsn]; omega), hsn]
    have h2ns : (2 * nw - sl).toNat = 2 * N - sl.toNat := by
      rw [toNat_sub_le' (by rw [h2n]; omega), h2n]
    obtain ⟨z1, z2, z3⟩ := clear_spec W1 (fp + (sl - nw + 1)) (2 * nw - sl) (by omega)
      (by rw [hfs', h2ns, d1]; omega)
    rw [hfs', h2ns] at z2 z3
    generalize hW2 : (LeanExe.loop (2 * nw - sl) W1 fun j W =>
      W.set! (fp + (sl - nw + 1) + j).toNat 0) = W2 at z1 z2 z3
    have hXP : X < 10 ^ (9 * 2 ^ i) * 10 ^ (9 * 2 ^ i) := by
      rw [← pow_add]; rw [show 9 * 2 ^ (i + 1) = 9 * 2 ^ i + 9 * 2 ^ i by ring] at hX; exact hX
    have hPpos : 0 < 10 ^ (9 * 2 ^ i) := pow_pos (by norm_num) _
    have hQlt : X / 10 ^ (9 * 2 ^ i) < 10 ^ (9 * 2 ^ i) := (Nat.div_lt_iff_lt_mul hPpos).mpr hXP
    have hRlt : X % 10 ^ (9 * 2 ^ i) < 10 ^ (9 * 2 ^ i) := Nat.mod_lt _ hPpos
    have hPN' : 10 ^ (9 * 2 ^ i) ≤ base ^ (2 * N') :=
      le_of_lt (lt_of_lt_of_le c2 (Nat.pow_le_pow_right base_pos e2))
    -- the quotient's region
    have hQ1 : segVal W2 fp.toNat (N + 1) = X / 10 ^ (9 * 2 ^ i) := by
      rw [show N + 1 = (sl.toNat + 1 - N) + (2 * N - sl.toNat) by omega, segVal_add,
        segVal_zeros (W := W2) (p := fp.toNat + (sl.toNat + 1 - N)) (k := 2 * N - sl.toNat)
          fun i' hi' => by
            have := z3 i' hi'; rwa [show fp.toNat + (sl.toNat - N + 1) + i' =
              fp.toNat + (sl.toNat + 1 - N) + i' by omega] at this,
        Nat.mul_zero, Nat.add_zero, ← d6]
      exact segVal_congr fun i' hi' => z2 _ (by omega)
    have hdQ : SegDigits W2 fp.toNat (N + 1) := fun i' hi' => by
      by_cases h : i' < sl.toNat + 1 - N
      · rw [z2 _ (by omega)]; exact d4 i' h
      · have := z3 (i' - (sl.toNat + 1 - N)) (by omega)
        rw [show fp.toNat + (sl.toNat - N + 1) + (i' - (sl.toNat + 1 - N)) = fp.toNat + i' by
          omega] at this
        rw [this]; exact base_pos
    have hQ2 : segVal W2 fp.toNat (2 * N') = X / 10 ^ (9 * 2 ^ i) := by
      have hz := segVal_high_zero (W := W2) (p := fp.toNat) (a := 2 * N') (k := N + 1 - 2 * N')
        (by rw [show 2 * N' + (N + 1 - 2 * N') = N + 1 by omega]; exact hdQ)
        (by rw [show 2 * N' + (N + 1 - 2 * N') = N + 1 by omega, hQ1]
            exact lt_of_lt_of_le hQlt hPN')
      rw [← hQ1, show N + 1 = 2 * N' + (N + 1 - 2 * N') by omega, segVal_add W2 fp.toNat (2 * N'),
        hz, Nat.mul_zero, Nat.add_zero]
    -- the words that the division and the zeros keep
    have hW2W : ∀ q, (q < p.toNat ∨ p.toNat + sl.toNat ≤ q) → (q < fp.toNat ∨
        fp.toNat + (16 * N + 11) ≤ q) → W2[q]! = W[q]! := fun q h1 h2 => by
      rw [z2 q (by omega), d2 q (by omega) (by omega) (by omega)]
    have hcps : (cp + (1 : UInt64) <<< ii).toNat = cp.toNat + 2 ^ i := by
      rw [toNat_add_lt (by rw [hsh1]; omega), hsh1]
    have hW2n : W2[tb.toNat + 2 * (i - 1) + 1]! = W[tb.toNat + 2 * (i - 1) + 1]! :=
      hW2W _ (by omega) (by omega)
    -- the quotient at level `i - 1`
    have rq := ih (i - 1) (by omega) W2 tb (ii - 1) fp (cp + (1 : UInt64) <<< ii) (fp + nw + 1) pb
      hii1 (by omega) (by omega)
      (fun j hj => (hpow j (by omega)).congr (hW2W _ (by omega) (by omega))
        (hW2W _ (by omega) (by omega))
        fun q h1 h2 => hW2W q (by have := hpe j (by omega); omega) (by
          have := hpe j (by omega); omega))
      (by rw [hcps]; omega) (by rw [hcps, show i - 1 + 1 = i by omega]; rw [pow_succ] at hcp; omega)
      (fun j hj => by
        rw [hW2W _ (by omega) (by omega), hW2W _ (by omega) (by omega)]
        have := hpe j (by omega); omega)
      (by rw [hW2n, hN', hfn1]; omega) (by rw [hW2n, hN', hfn1, z1, d1]; omega)
      (by rw [hW2n, hN']; exact hdQ.mono (by omega))
      (by rw [hW2n, hN', hQ2, show i - 1 + 1 = i by omega]; exact hQlt)
    rw [hW2n, hN', hQ2, hfn1, hcps] at rq
    obtain ⟨q1, q2, q3⟩ := rq
    rw [show i - 1 + 1 = i by omega] at q2 q3
    generalize hW3 : toChunks t T L W2 tb (ii - 1) fp (cp + (1 : UInt64) <<< ii) (fp + nw + 1) = W3
      at q1 q2 q3 ⊢
    -- the remainder at level `i - 1`
    have hW3W : ∀ q, (q < fp.toNat ∨ fp.toNat + (16 * N + 11) ≤ q) →
        (q < cp.toNat + 2 ^ i ∨ cp.toNat + 2 ^ (i + 1) ≤ q) → W3[q]! = W2[q]! :=
      fun q h1 h2 => q2 q (by omega) (by rw [pow_succ] at h2; omega) (by omega)
    have hR2 : segVal W3 p.toNat (2 * N) = X % 10 ^ (9 * 2 ^ i) := by
      rw [show 2 * N = sl.toNat + (2 * N - sl.toNat) by omega, segVal_add,
        segVal_zeros (W := W3) (p := p.toNat + sl.toNat) (k := 2 * N - sl.toNat) fun i' hi' => by
          rw [hW3W _ (by omega) (by omega), hW2W _ (by omega) (by omega), Nat.add_assoc]
          exact g2 _ (by omega) (by omega), Nat.mul_zero, Nat.add_zero, ← d5]
      exact segVal_congr fun i' hi' => by rw [hW3W _ (by omega) (by omega), z2 _ (by omega)]
    have hdR : SegDigits W3 p.toNat (2 * N) := fun i' hi' => by
      rw [hW3W _ (by omega) (by omega)]
      by_cases h : i' < sl.toNat
      · rw [z2 _ (by omega)]; exact d3 i' h
      · rw [hW2W _ (by omega) (by omega)]; exact hdx i' hi'
    have hR3 : segVal W3 p.toNat (2 * N') = X % 10 ^ (9 * 2 ^ i) := by
      have hz := segVal_high_zero (W := W3) (p := p.toNat) (a := 2 * N') (k := 2 * N - 2 * N')
        (by rw [show 2 * N' + (2 * N - 2 * N') = 2 * N by omega]; exact hdR)
        (by rw [show 2 * N' + (2 * N - 2 * N') = 2 * N by omega, hR2]
            exact lt_of_lt_of_le hRlt hPN')
      rw [← hR2, show 2 * N = 2 * N' + (2 * N - 2 * N') by omega, segVal_add W3 p.toNat (2 * N'),
        hz, Nat.mul_zero, Nat.add_zero]
    have hW3n : W3[tb.toNat + 2 * (i - 1) + 1]! = W[tb.toNat + 2 * (i - 1) + 1]! := by
      rw [hW3W _ (by omega) (by omega), hW2n]
    have rr := ih (i - 1) (by omega) W3 tb (ii - 1) p cp fp pb hii1 (by omega) (by omega)
      (fun j hj => (hpow j (by omega)).congr
        (by rw [hW3W _ (by omega) (by omega), hW2W _ (by omega) (by omega)])
        (by rw [hW3W _ (by omega) (by omega), hW2W _ (by omega) (by omega)])
        fun q h1 h2 => by
          have := hpe j (by omega)
          have := (hpow j (by omega)).1
          rw [hW3W q (by omega) (by omega), hW2W q (by omega) (by omega)])
      (by omega) (by rw [show i - 1 + 1 = i by omega]; rw [pow_succ] at hcp; omega)
      (fun j hj => by
        rw [hW3W _ (by omega) (by omega), hW2W _ (by omega) (by omega),
          hW3W _ (by omega) (by omega), hW2W _ (by omega) (by omega)]
        exact hpe j (by omega))
      (by rw [hW3n, hN']; omega) (by rw [hW3n, hN', q1, z1, d1]; omega)
      (by rw [hW3n, hN']; exact hdR.mono (by omega))
      (by rw [hW3n, hN', hR3, show i - 1 + 1 = i by omega]; exact hRlt)
    rw [hW3n, hN', hR3] at rr
    obtain ⟨s1, s2, s3⟩ := rr
    rw [show i - 1 + 1 = i by omega] at s2 s3
    -- the chunks of `X = Q P_i + R`
    have hsplit : X / 10 ^ (9 * 2 ^ i) * 10 ^ (9 * 2 ^ i) + X % 10 ^ (9 * 2 ^ i) = X :=
      Nat.div_add_mod' X _
    have hRlt' : X % 10 ^ (9 * 2 ^ i) < (10 ^ 9) ^ (2 ^ i) := by rw [← pow_mul]; exact hRlt
    refine ⟨by rw [s1, q1, z1, d1], fun q h1 h2 h3 => ?_, fun j hj => ?_⟩
    · rw [s2 q (by omega) (by rw [pow_succ] at h2; omega) (by omega),
        hW3W q (by omega) (by omega), hW2W q (by omega) (by omega)]
    · obtain ⟨cs1, cs2⟩ := chunk_split (B := 10 ^ 9) (Q := X / 10 ^ (9 * 2 ^ i))
        (R := X % 10 ^ (9 * 2 ^ i)) (h := 2 ^ i) (j := j) (by norm_num) hRlt'
      simp only [← pow_mul] at cs1 cs2
      rw [hsplit] at cs1 cs2
      rcases Nat.lt_or_ge j (2 ^ i) with hj' | hj'
      · rw [s3 j hj', cs1 hj']
      · rw [s2 _ (by omega) (by omega) (by omega)]
        have := q3 (j - 2 ^ i) (by rw [pow_succ] at hj; omega)
        rw [show cp.toNat + 2 ^ i + (j - 2 ^ i) = cp.toNat + j by omega] at this
        rw [this, cs2 hj']

end Library.Numerics.Bignum
