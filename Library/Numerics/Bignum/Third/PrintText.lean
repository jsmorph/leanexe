module

public import Library.Numerics.Bignum.Third.PrintRec

@[expose] public section

/-!
The text of the chunks.  `text_of_chunks` is the second half of the first iteration's proof of
`intToText_eq`, stated for any array of `K` chunks of nine digits of `|z|` with `|z| < 10^(9 K)`:
the build of the first iteration's printer over such an array is `printSpec z`.  `textOfChunks_eq`
carries it to `textOfChunks`, which reads the chunks from a workspace.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Decimal.Int64Text (digitWords digitWords_getElem? digitCount_toNat
  digitByte_eq digitWords_length_le_iff digitWords_length_pos build_getElem? digitCount digitByte)
open LeanExe.Dialect

/-- The first iteration's printer over any array of `K` chunks of nine digits of `|z|`. -/
theorem text_of_chunks {z : ℤ} {c : Array UInt64} {K : ℕ} (hK : K < 2 ^ 60) (hK1 : 1 ≤ K)
    (hcs : c.size = K)
    (hcj : ∀ j, j < K → c[j]!.toNat = z.natAbs / 10 ^ (9 * j) % 10 ^ 9)
    (hAK : z.natAbs < (10 ^ 9) ^ K) :
    (let sc := significant c
     let t := if sc == 0 then 0 else sc - 1
     let sign : UInt64 := if decide (z < 0) then 1 else 0
     let len := sign + digitCount c[t.toNat]! + 9 * t
     LeanExe.build len fun i =>
       if i < sign then 45 else digitByte c[((len - 1 - i) / 9).toNat]! ((len - 1 - i) % 9)) =
      printSpec z := by
  dsimp only
  obtain ⟨hts, hz, htop⟩ := significant_spec c (by omega)
  generalize hsc : significant c = sc at hts hz htop ⊢
  have hAs : z.natAbs < (10 ^ 9) ^ sc.toNat := by
    refine lt_of_digits_zero (by positivity) hAK (fun j h1 h2 => ?_) (by omega)
    have := hcj j (by omega)
    rw [hz j h1] at this
    rw [← pow_mul]
    exact this.symm
  have hTn : (if (sc == 0) = true then (0 : UInt64) else sc - 1).toNat = sc.toNat - 1 := by
    by_cases h0 : sc = 0
    · rw [ite_eq_left (by simp [h0]), h0]; rfl
    · rw [ite_eq_right (by simpa using h0), UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]
        have : sc.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        simp; omega)]
      rfl
  generalize hTd : (if (sc == 0) = true then (0 : UInt64) else sc - 1) = T at hTn ⊢
  have hTK : T.toNat < K := by omega
  have hAT : z.natAbs < 10 ^ (9 * (T.toNat + 1)) := by
    rw [pow_mul]
    exact lt_of_lt_of_le hAs (Nat.pow_le_pow_right (by positivity) (by omega))
  have hcT : c[T.toNat]!.toNat = z.natAbs / 10 ^ (9 * T.toNat) := by
    rw [hcj _ hTK, Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le hAT (by rw [show 9 * (T.toNat + 1) = 9 + 9 * T.toNat by ring])
  have htpos : 0 < T.toNat → 0 < c[T.toNat]!.toNat := by
    intro hT0
    have hne := htop (by omega)
    rw [show sc.toNat - 1 = T.toNat by omega] at hne
    rcases Nat.eq_zero_or_pos c[T.toNat]!.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by rw [h0]; rfl)) hne
    · exact h0
  have hsplit := digits_length_split hcT hAT htpos
  have hcTlt : c[T.toNat]!.toNat < 10 ^ 9 := by
    rw [hcj _ hTK]; exact Nat.mod_lt _ (by positivity)
  have hDc : (digitWords c[T.toNat]!.toNat).length ≤ 9 :=
    (digitWords_length_le_iff _ 9 (by norm_num)).mpr hcTlt
  have hDc1 := digitWords_length_pos c[T.toNat]!.toNat
  have hdc := digitCount_toNat c[T.toNat]!
  generalize hLd : (digitWords z.natAbs).length = L at hsplit
  have hsign : (if decide (z < 0) = true then (1 : UInt64) else 0).toNat =
      if z < 0 then 1 else 0 := by
    by_cases hz0 : z < 0
    · rw [ite_eq_left (by simpa using hz0), ite_eq_left hz0]; rfl
    · rw [ite_eq_right (by simpa using hz0), ite_eq_right hz0]; rfl
  generalize hSd : (if decide (z < 0) = true then (1 : UInt64) else 0) = S at hsign ⊢
  have hlen : (S + digitCount c[T.toNat]! + 9 * T).toNat = (if z < 0 then 1 else 0) + L := by
    have hT9 : (9 * T).toNat = 9 * T.toNat := by
      rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, hsign, hdc, hT9]
    split <;> omega
  apply Array.ext_getElem?
  intro i
  rw [← Array.getElem?_toList (xs := printSpec z), printSpec_toList, build_getElem?, hlen]
  have hget := digitWords_getElem? z.natAbs
  rw [hLd] at hget
  have hdigit : ∀ j, j < L → digitByte c[((S + digitCount c[T.toNat]! + 9 * T - 1 -
      UInt64.ofNat (j + (if z < 0 then 1 else 0))) / 9).toNat]!
      ((S + digitCount c[T.toNat]! + 9 * T - 1 -
        UInt64.ofNat (j + (if z < 0 then 1 else 0))) % 9) =
      UInt64.ofNat (z.natAbs / 10 ^ (L - 1 - j) % 10 + 48) := by
    intro j hj
    have hk : (S + digitCount c[T.toNat]! + 9 * T - 1 -
        UInt64.ofNat (j + (if z < 0 then 1 else 0))).toNat = L - 1 - j := by
      have hj' : (UInt64.ofNat (j + (if z < 0 then 1 else 0))).toNat =
          j + (if z < 0 then 1 else 0) :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; split <;> omega)
      rw [UInt64.toNat_sub, UInt64.toNat_sub, hlen, hj']
      simp only [UInt64.reduceToNat]
      split <;> omega
    rw [digitByte_eq, UInt64.toNat_div, UInt64.toNat_mod, hk]
    simp only [UInt64.reduceToNat]
    rw [hcj _ (by omega), chunk_digit _ _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod]
  by_cases hneg : z < 0
  · simp only [hneg, ↓reduceIte] at hsign hdigit ⊢
    rcases i with _ | i
    · have hs : UInt64.ofNat 0 < S := by
        rw [UInt64.lt_iff_toNat_lt, hsign]; decide
      rw [ite_eq_left (by omega), ite_eq_left hs]
      rfl
    · rw [List.singleton_append, List.getElem?_cons_succ, hget]
      by_cases hi : i < L
      · rw [ite_eq_left (by omega), ite_eq_left hi]
        have hnot : ¬ UInt64.ofNat (i + 1) < S := by
          rw [UInt64.lt_iff_toNat_lt, hsign, UInt64.toNat_ofNat_of_lt' (by
            simp only [UInt64.size]; omega)]
          omega
        rw [ite_eq_right hnot, hdigit i hi]
      · rw [ite_eq_right (by omega), ite_eq_right hi]
  · simp only [hneg, ↓reduceIte, List.nil_append] at hsign hdigit ⊢
    rw [hget]
    by_cases hi : i < L
    · rw [ite_eq_left (by omega), ite_eq_left hi]
      have hnot : ¬ UInt64.ofNat i < S := by
        rw [UInt64.lt_iff_toNat_lt, hsign]; omega
      rw [ite_eq_right hnot, ← hdigit i hi, Nat.add_zero]
    · rw [ite_eq_right (by omega), ite_eq_right hi]

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The text of the chunks in a workspace. -/
theorem textOfChunks_eq {z : ℤ} (W : Array UInt64) (cp K : UInt64)
    (hc : cp.toNat + K.toNat < 2 ^ 64) (hK : K.toNat < 2 ^ 60) (hK1 : 1 ≤ K.toNat)
    (hcj : ∀ j, j < K.toNat → W[cp.toNat + j]!.toNat = z.natAbs / 10 ^ (9 * j) % 10 ^ 9)
    (hAK : z.natAbs < (10 ^ 9) ^ K.toNat) :
    textOfChunks (decide (z < 0)) W cp K = printSpec z := by
  unfold textOfChunks
  exact text_of_chunks hK hK1 (build_size _ _) (fun j hj => by
    rw [build_get hj, toNat_add_lt (by rw [toNat_ofNat_lt (by omega)]; omega),
      toNat_ofNat_lt (by omega)]
    exact hcj j hj) hAK

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- `levelsFor c` is the least `K` with `2^(K+1) ≥ c`, for `2 ≤ c ≤ 2^40`. -/
theorem levelsFor_spec (c : UInt64) (hc2 : 2 ≤ c.toNat) (hc : c.toNat ≤ 2 ^ 40) :
    (levelsFor c).toNat < 40 ∧ c.toNat ≤ 2 ^ ((levelsFor c).toNat + 1) ∧
      ((levelsFor c).toNat = 0 ∨ 2 ^ (levelsFor c).toNat < c.toNat) := by
  unfold levelsFor
  obtain ⟨j, hj, hI, hcond⟩ := repeatWhile_count 40 (0 : UInt64)
    (fun k => (2 : UInt64) <<< k < c) (fun k => k + 1)
    (fun j (k : UInt64) => k.toNat = j ∧ (j = 0 ∨ 2 ^ j < c.toNat)) ⟨rfl, Or.inl rfl⟩
    (fun j k hj ⟨h1, h2⟩ hcnd => by
      have hsh := shl_two k (by simp at hj; omega)
      simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hsh, h1] at hcnd
      refine ⟨by rw [toNat_add_lt (by simp at hj; simp; omega), h1]; simp, Or.inr hcnd⟩)
    (fun k ⟨h1, h2⟩ => by
      have hsh := shl_two k (by simp at h1; omega)
      simp only [decide_eq_false_iff_not, UInt64.not_lt, UInt64.le_iff_toNat_le, hsh, h1]
      simp only [UInt64.reduceToNat] at h1 ⊢
      calc c.toNat ≤ 2 ^ 40 := hc
        _ ≤ 2 ^ (40 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨h1, h2⟩ := hI
  simp only [UInt64.reduceToNat] at hj
  generalize hK : LeanExe.repeatWhile 40 (0 : UInt64) (fun k => (2 : UInt64) <<< k < c)
    (fun k => k + 1) = K at h1 hcond ⊢
  have hsh := shl_two K (by omega)
  simp only [decide_eq_false_iff_not, UInt64.not_lt, UInt64.le_iff_toNat_le, hsh] at hcond
  refine ⟨?_, hcond, by rw [h1]; exact h2⟩
  by_contra hge
  have : j = 40 := by omega
  rw [this] at h2
  rcases h2 with h | h
  · omega
  · omega

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

set_option maxHeartbeats 4000000 in
/-- `chunksDC` writes the `2^(K+1)` chunks of nine digits of `u` from position `2 K + 2`. -/
theorem chunksDC_spec (t T L : UInt64) (u : Array UInt64) (hu : Digits u) (hs : u.size < 2 ^ 32)
    (j : ℕ) (hj : j < 2 ^ ((levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)).toNat + 1)) :
    (chunksDC t T L u)[2 * (levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)).toNat + 2 +
      j]!.toNat = value u / 10 ^ (9 * j) % 10 ^ 9 := by
  have hn := size_toNat64 (u := u) (by omega)
  have hc : (u.size.toUInt64 + u.size.toUInt64 / 14 + 2).toNat = u.size + u.size / 14 + 2 := by
    simp only [UInt64.toNat_add, UInt64.toNat_div, hn, UInt64.reduceToNat]; omega
  obtain ⟨hK40, hKc, hKmin⟩ := levelsFor_spec _ (by rw [hc]; omega) (by rw [hc]; omega)
  rw [hc] at hKc hKmin
  unfold chunksDC
  dsimp only
  generalize hKd : levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2) = K at hK40 hKc hKmin hj ⊢
  have h2K : (2 : UInt64) <<< K = (2 : UInt64) <<< K := rfl
  have hsh2 := shl_two K (by omega)
  have hsh1 := shl_one' K (by omega)
  have hpK : 2 ^ K.toNat < 2 ^ 34 := by
    rcases hKmin with h0 | h0
    · rw [h0]; norm_num
    · calc 2 ^ K.toNat < u.size + u.size / 14 + 2 := h0
        _ < 2 ^ 34 := by omega
  have h2pos : 0 < 2 ^ K.toNat := pow_pos (by norm_num) _
  have hpw : 2 ^ (K.toNat + 1) = 2 * 2 ^ K.toNat := by ring
  have hcp : (2 * K + 2).toNat = 2 * K.toNat + 2 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  have hpb : (2 * K + 2 + (2 : UInt64) <<< K).toNat = 2 * K.toNat + 2 + 2 * 2 ^ K.toNat := by
    rw [toNat_add_lt (by rw [hcp, hsh2]; omega), hcp, hsh2, hpw]
  have hxp : (2 * K + 2 + (2 : UInt64) <<< K + 7 * (1 : UInt64) <<< K).toNat =
      2 * K.toNat + 2 + 9 * 2 ^ K.toNat := by
    have : (7 * (1 : UInt64) <<< K).toNat = 7 * 2 ^ K.toNat := by
      rw [toNat_mul_lt' (by rw [hsh1]; simp; omega), hsh1]; simp
    rw [toNat_add_lt (by rw [hpb, this]; omega), hpb, this]; ring
  have hsz : (2 * K + 2 + (2 : UInt64) <<< K + 7 * (1 : UInt64) <<< K +
      22 * (1 : UInt64) <<< K + 20).toNat = 2 * K.toNat + 2 + 31 * 2 ^ K.toNat + 20 := by
    have : (22 * (1 : UInt64) <<< K).toNat = 22 * 2 ^ K.toNat := by
      rw [toNat_mul_lt' (by rw [hsh1]; simp; omega), hsh1]; simp
    rw [toNat_add_lt (by rw [toNat_add_lt (by rw [hxp, this]; omega), hxp, this]; simp; omega),
      toNat_add_lt (by rw [hxp, this]; omega), hxp, this]; simp; ring
  generalize hcpw : 2 * K + 2 = cp at hcp hpb hxp hsz ⊢
  generalize hpbw : cp + (2 : UInt64) <<< K = pb at hpb hxp hsz ⊢
  generalize hxpw : pb + 7 * (1 : UInt64) <<< K = xp at hxp hsz ⊢
  -- the workspace
  generalize hWd : LeanExe.build (xp + 22 * (1 : UInt64) <<< K + 20) (fun i =>
    if xp ≤ i ∧ i < xp + u.size.toUInt64 then u[(i - xp).toNat]! else 0) = W
  have hWs : W.size = 2 * K.toNat + 2 + 31 * 2 ^ K.toNat + 20 := by rw [← hWd, build_size, hsz]
  have hWq : ∀ q, q < W.size → W[q]! = if xp.toNat ≤ q ∧ q < xp.toNat + u.size then
      u[q - xp.toNat]! else 0 := fun q hq => by
    rw [hWs] at hq
    have hq' : (UInt64.ofNat q).toNat = q := toNat_ofNat_lt (by omega)
    rw [← hWd, build_get (by rw [hsz]; omega)]
    by_cases h : xp.toNat ≤ q ∧ q < xp.toNat + u.size
    · rw [if_pos (by
        rw [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hq', toNat_add_lt (by omega), hn]
        exact h), if_pos h, toNat_sub_le' (by rw [hq']; omega), hq']
    · rw [if_neg (by
        rw [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hq', toNat_add_lt (by omega), hn]
        exact h), if_neg h]
  -- the powers
  obtain ⟨w1, w2, w3⟩ := powInit_spec t W 0 pb K (by omega) hK40 (by simp; omega)
    (by rw [hWs]; omega)
  simp only [UInt64.toNat_zero, Nat.zero_add] at w2 w3
  generalize hW1 : powInit t W 0 pb K = W1 at w1 w2 w3
  have hk1 : (2 * K + 1).toNat = 2 * K.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  rw [hk1]
  obtain ⟨-, -, a3, a4, -, -, -⟩ := w3 K.toNat le_rfl
  simp only [Nat.zero_add] at a3 a4
  generalize hnK : W1[2 * K.toNat + 1]! = nw at a3 a4 ⊢
  have hfp : (xp + 2 * nw).toNat = xp.toNat + 2 * nw.toNat := by
    rw [toNat_add_lt (by rw [toNat_mul_lt' (by simp; omega)]; simp; omega),
      toNat_mul_lt' (by simp; omega)]; simp
  have hW1x : ∀ q, xp.toNat ≤ q → W1[q]! = W[q]! := fun q hq => w2 q (by omega) (by omega)
  -- the number fits the region of level `K`
  have hval : value u < base ^ u.size := value_lt hu
  have hPK := (w3 K.toNat le_rfl).bounds
  simp only [Nat.zero_add, hnK] at hPK
  have hu2 : value u < 10 ^ (9 * 2 ^ (K.toNat + 1)) :=
    lt_of_lt_of_le hval (le_trans (pow_chunks _) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hn2 : u.size ≤ 2 * nw.toNat := by
    by_contra hcon
    have h1 : 10 ^ (9 * 2 ^ (K.toNat + 1)) < base ^ (2 * nw.toNat) := by
      rw [show 9 * 2 ^ (K.toNat + 1) = 9 * 2 ^ K.toNat + 9 * 2 ^ K.toNat by ring, pow_add,
        two_mul, pow_add]
      exact Nat.mul_lt_mul'' hPK.2 hPK.2
    have h2 : base ^ (2 * nw.toNat) ≤ base ^ u.size := Nat.pow_le_pow_right base_pos (by omega)
    have h3 : base ^ u.size ≤ 10 ^ (9 * 2 ^ (K.toNat + 1)) :=
      le_trans (pow_chunks _) (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hX : segVal W1 xp.toNat (2 * nw.toNat) = value u := by
    rw [← segVal_value, show 2 * nw.toNat = u.size + (2 * nw.toNat - u.size) by omega, segVal_add,
      segVal_zeros (W := W1) (p := xp.toNat + u.size) (k := 2 * nw.toNat - u.size) fun i hi => by
        rw [hW1x _ (by omega), hWq _ (by rw [hWs]; omega), if_neg (by omega)],
      Nat.mul_zero, Nat.add_zero]
    exact segVal_congr fun i hi => by
      rw [hW1x _ (by omega), hWq _ (by rw [hWs]; omega), if_pos (by omega), Nat.zero_add]
      congr 1; omega
  have hdX : SegDigits W1 xp.toNat (2 * nw.toNat) := fun i hi => by
    rw [hW1x _ (by omega), hWq _ (by rw [hWs]; omega)]
    split
    · exact hu _ (by omega)
    · exact base_pos
  have r := toChunks_spec t T L K.toNat W1 0 K xp cp (xp + 2 * nw) pb.toNat rfl hK40 (by omega)
    (by simpa using w3) (by simp; omega) (by rw [hpb]; omega)
    (fun j hj => by
      obtain ⟨-, b2, -, b4, -, -, -⟩ := w3 j hj
      simp only [UInt64.toNat_zero, Nat.zero_add] at b2 b4 ⊢
      have : 2 ^ (j + 1) ≤ 2 ^ (K.toNat + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
    (by simp only [UInt64.toNat_zero, Nat.zero_add, hnK, hfp]; omega)
    (by simp only [UInt64.toNat_zero, Nat.zero_add, hnK, hfp, w1, hWs]; omega)
    (by simpa [hnK] using hdX) (by simpa [hnK, hX] using hu2)
  simp only [UInt64.toNat_zero, Nat.zero_add, hnK, hX, hcp] at r
  exact r.2.2 j hj

/-- The natural printer of the third iteration writes Lean's decimal text of the value, at every
threshold. -/
theorem natToTextDCWith_eq (t T L P : UInt64) {u : Array UInt64} (hu : Canonical u)
    (hs : u.size < 2 ^ 32) : natToTextDCWith t T L P u = printSpec (value u : ℤ) := by
  unfold natToTextDCWith
  have hu' : (⟨false, u⟩ : BigInt) = BigInt.ofInt (value u : ℤ) := by
    unfold BigInt.ofInt
    rw [Int.natAbs_natCast, ← (canonical_iff u).mp hu]
    simp
  split
  · rw [hu', intToText_eq (by rw [← hu']; exact hs)]
  · have hn := size_toNat64 (u := u) (by omega)
    have hc : (u.size.toUInt64 + u.size.toUInt64 / 14 + 2).toNat = u.size + u.size / 14 + 2 := by
      simp only [UInt64.toNat_add, UInt64.toNat_div, hn, UInt64.reduceToNat]; omega
    obtain ⟨hK40, hKc, hKmin⟩ := levelsFor_spec _ (by rw [hc]; omega) (by rw [hc]; omega)
    rw [hc] at hKc
    generalize hKd : levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2) = K at hK40 hKc hKmin
    have hsh2 := shl_two K (by omega)
    have hcp : (2 * K + 2).toNat = 2 * K.toNat + 2 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
    have hdec : decide ((value u : ℤ) < 0) = false := by simp
    rw [← hdec]
    have hpK : 2 ^ (K.toNat + 1) < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    apply textOfChunks_eq (z := (value u : ℤ)) _ _ _ (by rw [hcp, hsh2]; omega) (by rw [hsh2]; omega)
      (by rw [hsh2]; exact Nat.one_le_two_pow) (fun j hj => by
        rw [hcp, Int.natAbs_natCast, ← hKd]
        rw [hsh2, ← hKd] at hj
        exact chunksDC_spec t T L u hu.1 hs j hj)
      (by
        rw [Int.natAbs_natCast, hsh2, ← pow_mul]
        exact lt_of_lt_of_le (value_lt hu.1) (le_trans (pow_chunks _)
          (Nat.pow_le_pow_right (by norm_num) (by omega))))

theorem natToTextDC_eq {u : Array UInt64} (hu : Canonical u) (hs : u.size < 2 ^ 32) :
    natToTextDC u = printSpec (value u : ℤ) :=
  natToTextDCWith_eq _ _ _ _ hu hs

/-- The natural printer writes the first iteration's text of the natural as an integer. -/
theorem natToTextDC_eq_intToText {u : Array UInt64} (hu : Canonical u) (hs : u.size < 2 ^ 32) :
    natToTextDC u = intToText ⟨false, u⟩ := by
  have hu' : (⟨false, u⟩ : BigInt) = BigInt.ofInt (value u : ℤ) := by
    unfold BigInt.ofInt
    rw [Int.natAbs_natCast, ← (canonical_iff u).mp hu]
    simp
  rw [natToTextDC_eq hu hs, hu', intToText_eq (by rw [← hu']; exact hs)]

/-- The integer printer of the third iteration writes Lean's decimal text of the integer. -/
theorem intToTextDC_eq {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToTextDC (.ofInt z) = printSpec z := by
  unfold intToTextDC
  split
  · exact intToText_eq h
  · have hs := h
    simp only [BigInt.ofInt] at hs ⊢
    have hn := size_toNat64 (u := limbsOf z.natAbs) (by omega)
    have hc : ((limbsOf z.natAbs).size.toUInt64 + (limbsOf z.natAbs).size.toUInt64 / 14 +
        2).toNat = (limbsOf z.natAbs).size + (limbsOf z.natAbs).size / 14 + 2 := by
      simp only [UInt64.toNat_add, UInt64.toNat_div, hn, UInt64.reduceToNat]; omega
    obtain ⟨hK40, hKc, hKmin⟩ := levelsFor_spec _ (by rw [hc]; omega) (by rw [hc]; omega)
    rw [hc] at hKc
    generalize hKd : levelsFor ((limbsOf z.natAbs).size.toUInt64 +
      (limbsOf z.natAbs).size.toUInt64 / 14 + 2) = K at hK40 hKc hKmin
    have hsh2 := shl_two K (by omega)
    have hcp : (2 * K + 2).toNat = 2 * K.toNat + 2 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
    have hpK : 2 ^ (K.toNat + 1) < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hv := value_limbsOf z.natAbs
    apply textOfChunks_eq (z := z) _ _ _ (by rw [hcp, hsh2]; omega) (by rw [hsh2]; omega)
      (by rw [hsh2]; exact Nat.one_le_two_pow) (fun j hj => by
        rw [hsh2] at hj
        have := chunksDC_spec karaThreshold divBase printLeaf (limbsOf z.natAbs)
          (canonical_limbsOf _).1 hs j (by rw [hKd]; exact hj)
        rw [hv, hKd] at this
        rw [hcp]; exact this)
      (by
        rw [hsh2, ← pow_mul]
        calc z.natAbs = value (limbsOf z.natAbs) := hv.symm
          _ < base ^ (limbsOf z.natAbs).size := value_lt (canonical_limbsOf _).1
          _ ≤ _ := le_trans (pow_chunks _) (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The integer printer writes the first iteration's text. -/
theorem intToTextDC_eq_intToText {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToTextDC (.ofInt z) = intToText (.ofInt z) := by
  rw [intToTextDC_eq h, intToText_eq h]

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

/-- The integer printer writes the bytes of Lean's `toString`, one to a word. -/
theorem intToTextDC_toString {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    intToTextDC (.ofInt z) = Library.Numerics.Decimal.Shared.StrconvGrammar.words
      (Library.Numerics.Decimal.Shared.StrconvGrammar.ascii (toString z)) :=
  intToTextDC_eq h

/-- Reading the printer's text gives the integer back. -/
theorem readSpec_intToTextDC {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32) :
    readSpec (intToTextDC (.ofInt z)) = (true, .ofInt z) := by
  rw [intToTextDC_eq h, readSpec_print]

/-- The first iteration's reader reads the printer's text back. -/
theorem intOfText_intToTextDC {z : ℤ} (h : (BigInt.ofInt z).mag.size < 2 ^ 32)
    (hp : (printSpec z).size < 2 ^ 32) : intOfText (intToTextDC (.ofInt z)) = (true, .ofInt z) := by
  rw [intToTextDC_eq h, read_print z hp]

end Library.Numerics.Bignum
