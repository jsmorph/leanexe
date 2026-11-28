module

public import Library.Numerics.Bignum.Second.Kara
public import Library.Numerics.Bignum.IntProof

@[expose] public section

/-!
The product of the second iteration equals the first iteration's specification: `natMulKara u v`
is `limbsOf (value u * value v)` for arrays of limbs, and `intMulKara` of two canonical integers is
the canonical integer of the product.

`mulLong t u v`, for `u` at least as long as `v`, copies both operands into one workspace.  When
`v` is shorter than the threshold, Algorithm M in place writes the product after them.  Otherwise
`u` is padded with zeros to `q` chunks of `n = v.size` limbs, and the loop multiplies chunk `c` by
`v` into a buffer of `2 n` limbs, by `kara`, or by Algorithm M when the last chunk is shorter than
the threshold, and adds the buffer to the result from limb `c n` on.  `chunks_inv` keeps the
invariant of that loop: the result holds the product of `v` and the first `c n` limbs of the padded
`u`, every limb from `c n + n` on is still 0, and the words below the result are the operands.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The value of a segment of limbs that is below `base ^ a` is the value of its first `a`
limbs. -/
theorem segVal_trunc {W : Array UInt64} {p a k : ℕ} (hd : SegDigits W p (a + k))
    (hlt : segVal W p (a + k) < base ^ a) : segVal W p (a + k) = segVal W p a := by
  have hz := segVal_high_zero hd hlt
  rw [segVal_add, hz, Nat.mul_zero, Nat.add_zero]

/-- The invariant of the loop over the chunks of `u`: the size, the operands below the result,
the limbs of the result, the zeros above the partial product, and its value. -/
def ChunkInv (W0 : Array UInt64) (R K N : ℕ) (V : ℕ) (c : ℕ) (W : Array UInt64) : Prop :=
  W.size = W0.size ∧ (∀ i, i < R → W[i]! = W0[i]!) ∧ SegDigits W R K ∧
  (∀ i, c * N + N ≤ i → i < K → W[R + i]! = 0) ∧ segVal W R K = segVal W0 0 (c * N) * V

/-- The step of the chunk loop: the buffer of `P` limbs from `Tb` holds the product `CV · V` of
chunk `c` and `v`, and its sum with the result from limb `c N` on keeps the invariant. -/
theorem chunk_add {W0 W' W'' : Array UInt64} {R K N V c P Tb CV : ℕ}
    (hinv : ChunkInv W0 R K N V c W') (hP1 : N ≤ P) (hP2 : P ≤ 2 * N) (hK : c * N + P ≤ K)
    (hRT : R + K ≤ Tb) (hTsz : Tb + P ≤ W0.size) (hW : W0.size < 2 ^ 64)
    (s'' : W''.size = W0.size) (f'' : ∀ q, q < Tb → W''[q]! = W'[q]!)
    (d'' : SegDigits W'' Tb P) (vb : segVal W'' Tb P = CV * V)
    (hS : segVal W0 0 (c * N) + base ^ (c * N) * CV = segVal W0 0 ((c + 1) * N))
    (hlt : segVal W0 0 ((c + 1) * N) * V < base ^ (c * N + P))
    (dp cp np : UInt64) (hdp : dp.toNat = R + c * N) (hcp : cp.toNat = Tb)
    (hnp : np.toNat = P) :
    ChunkInv W0 R K N V (c + 1) (addGen W'' dp cp np dp np).2 := by
  obtain ⟨s', f', dg', z', v'⟩ := hinv
  have hc1 : (c + 1) * N = c * N + N := by ring
  have hRk : ∀ i, i < K → W''[R + i]! = W'[R + i]! := fun i hi => f'' _ (by omega)
  have kA := addGen_spec W'' dp cp np dp np (by omega) (by omega) (by rw [hcp, hnp]; omega)
    (by omega)
    (fun i hi => by
      rw [hdp, hnp] at *
      rw [Nat.add_assoc, hRk _ (by omega)]; exact dg' (c * N + i) (by omega))
    (by rw [hcp, hnp, Nat.min_self]; exact d'')
    (fun i j _ _ => by omega) (fun i j _ hj => by rw [hcp, hdp, hnp] at *; omega)
  rw [hdp, hcp, hnp, Nat.min_self] at kA
  obtain ⟨sA, fA, dA, cA, vA⟩ := kA
  generalize addGen W'' dp cp np dp np = SA at sA fA dA cA vA ⊢
  rw [vb] at vA
  have hseg : segVal W'' (R + c * N) P = segVal W' (R + c * N) P :=
    segVal_congr fun i hi => by rw [Nat.add_assoc, hRk _ (by omega), ← Nat.add_assoc]
  rw [hseg] at vA
  -- the old and the new value split at limbs `c N` and `c N + P`
  have hold : segVal W0 0 (c * N) * V =
      segVal W' R (c * N) + base ^ (c * N) * segVal W' (R + c * N) P := by
    have h1 := segVal_add W' R (c * N) (P + (K - (c * N + P)))
    have h2 := segVal_add W' (R + c * N) P (K - (c * N + P))
    have h3 : segVal W' (R + c * N + P) (K - (c * N + P)) = 0 := segVal_zeros fun i hi => by
      rw [Nat.add_assoc, Nat.add_assoc]; exact z' _ (by omega) (by omega)
    rw [show c * N + (P + (K - (c * N + P))) = K by omega, v', h2, h3] at h1
    simpa using h1
  have hnew : segVal SA.2 R K =
      segVal W' R (c * N) + base ^ (c * N) * segVal SA.2 (R + c * N) P := by
    have h1 := segVal_add SA.2 R (c * N) (P + (K - (c * N + P)))
    have h2 := segVal_add SA.2 (R + c * N) P (K - (c * N + P))
    have h3 : segVal SA.2 (R + c * N + P) (K - (c * N + P)) = 0 := segVal_zeros fun i hi => by
      rw [Nat.add_assoc, Nat.add_assoc, fA _ (by omega), hRk _ (by omega)]
      exact z' _ (by omega) (by omega)
    have hlowk : segVal SA.2 R (c * N) = segVal W' R (c * N) :=
      segVal_congr fun i hi => by rw [fA _ (by omega), hRk _ (by omega)]
    rw [show c * N + (P + (K - (c * N + P))) = K by omega, h2, h3, hlowk] at h1
    simpa using h1
  -- the carry is 0 because the new value fits
  have hval : segVal SA.2 R K + SA.1.toNat * base ^ (c * N + P) =
      segVal W0 0 ((c + 1) * N) * V := by
    rw [hnew, ← hS, pow_add]
    have : segVal W' R (c * N) + base ^ (c * N) * segVal W' (R + c * N) P =
        segVal W0 0 (c * N) * V := hold.symm
    calc segVal W' R (c * N) + base ^ (c * N) * segVal SA.2 (R + c * N) P +
          SA.1.toNat * (base ^ (c * N) * base ^ P)
        = segVal W' R (c * N) + base ^ (c * N) *
          (segVal SA.2 (R + c * N) P + SA.1.toNat * base ^ P) := by ring
      _ = segVal W' R (c * N) + base ^ (c * N) * (segVal W' (R + c * N) P + CV * V) := by
          rw [vA]
      _ = (segVal W0 0 (c * N) + base ^ (c * N) * CV) * V := by
          zify at this ⊢; linear_combination this
  have hc0 : SA.1.toNat = 0 := by
    by_contra hne
    have : 1 * base ^ (c * N + P) ≤ SA.1.toNat * base ^ (c * N + P) :=
      Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  rw [hc0, Nat.zero_mul, Nat.add_zero] at hval
  refine ⟨by rw [sA, s''], fun i hi => ?_, fun i hi => ?_, fun i hi1 hi2 => ?_, hval⟩
  · rw [fA _ (by omega), f'' _ (by omega)]; exact f' i hi
  · by_cases hin : c * N ≤ i ∧ i < c * N + P
    · have := dA (i - c * N) (by omega)
      rwa [show R + c * N + (i - c * N) = R + i by omega] at this
    · rw [fA _ (by omega), hRk _ hi]; exact dg' i hi
  · rw [fA _ (by omega), hRk _ hi2]; exact z' i (by omega) hi2

/-- The words of an array of limbs and zeros are limbs. -/
theorem digit_or_zero {x : UInt64} {u : Array UInt64} (hu : Digits u) {j : ℕ}
    (h : x = u[j]! ∨ x = 0) : x.toNat < base := by
  rcases h with h | h
  · rw [h]; exact digit_all hu j
  · rw [h]; exact base_pos

set_option maxHeartbeats 2000000 in
/-- The product of `u` and `v` when `u` is at least as long as `v`. -/
theorem mulLong_eq (t : UInt64) {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) (hvu : v.size ≤ u.size) :
    mulLong t u v = limbsOf (value u * value v) := by
  unfold mulLong
  lift_lets
  intro m n W q B R T S W0 W1
  have hm : m.toNat = u.size := size_toNat (u := u) (by omega)
  have hn : n.toNat = v.size := size_toNat (u := v) (by omega)
  have hmn : (m + n).toNat = u.size + v.size := by rw [toNat_add_lt] <;> omega
  have hval : value u * value v < base ^ (u.size + v.size) := by
    rw [pow_add]; exact Nat.mul_lt_mul'' (value_lt hu) (value_lt hv)
  by_cases hs : n < t ∨ n < 16
  · rw [if_pos hs]
    have hsz : (2 * (m + n)).toNat = 2 * (u.size + v.size) := by
      rw [UInt64.toNat_mul, hmn]; simp only [UInt64.reduceToNat]; omega
    have hWs : W.size = 2 * (u.size + v.size) := by
      show (LeanExe.build _ _).size = _; rw [build_size, hsz]
    have hget : ∀ i, i < 2 * (u.size + v.size) →
        W[i]! = if i < u.size then u[i]! else if i < u.size + v.size then v[i - u.size]! else 0 := by
      intro i hi
      show (LeanExe.build _ _)[i]! = _
      rw [build_get (by rw [hsz]; exact hi)]
      have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
      simp only [UInt64.lt_iff_toNat_lt, hii, hm, hmn]
      split
      · rfl
      · split
        · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hii, hm]; omega), hii, hm]
        · rfl
    have hda : SegDigits W 0 u.size := fun i hi => by
      rw [hget _ (by omega), if_pos (by omega)]; exact digit_all hu _
    have hdb : SegDigits W u.size v.size := fun i hi => by
      rw [hget _ (by omega), if_neg (by omega), if_pos (by omega), show u.size + i - u.size = i by omega]
      exact digit_all hv _
    obtain ⟨s1, -, d1, v1⟩ := baseMul_spec W 0 m m n (m + n) (by omega)
      (by simp only [UInt64.reduceToNat, hm]; omega) (by rw [hm, hn]; omega)
      (by rw [hmn, hm, hn]; omega) (by simp only [UInt64.reduceToNat, hmn, hm]; omega)
      (by rw [hmn, hm, hn]; omega) (by simp only [UInt64.reduceToNat, hm]; exact hda)
      (by rw [hm, hn]; exact hdb)
    rw [hm, hn, hmn] at d1 v1
    have hu' : segVal W 0 u.size = value u := by
      rw [← segVal_value]
      exact segVal_congr fun i hi => by rw [hget _ (by omega), if_pos (by omega)]
    have hv' : segVal W u.size v.size = value v := by
      rw [← segVal_value]
      exact segVal_congr fun i hi => by
        rw [hget _ (by omega), if_neg (by omega), if_pos (by omega),
          show u.size + i - u.size = 0 + i by omega]
    rw [UInt64.toNat_ofNat, Nat.zero_mod] at v1
    rw [trimSeg_eq _ _ _ (by omega) (by rw [s1, hmn]; omega) (by rw [hmn]; exact d1), hmn, v1,
      ← hu', ← hv']
  rw [if_neg hs]
  have hN16 : 16 ≤ v.size := by
    have h2 := (not_or.mp hs).2
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le, hn] at h2
    simpa using h2
  -- the layout: `u` padded to `Q` chunks, `v`, the result, the buffer, the scratch
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = (u.size + v.size - 1) / v.size := ⟨_, rfl⟩
  have hQ1 : Q * v.size ≤ u.size + v.size - 1 := hQd ▸ Nat.div_mul_le_self _ _
  have hQ2 : u.size + v.size - 1 < Q * v.size + v.size := hQd ▸ Nat.lt_div_mul_add (by omega)
  have hQle : Q ≤ u.size + v.size := hQd ▸ (Nat.div_le_self _ _).trans (by omega)
  have hq : q.toNat = Q := by
    show ((m + n - 1) / n).toNat = Q
    rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, hmn]; simp only [UInt64.reduceToNat]; omega), hmn, hn, hQd]
    simp only [UInt64.reduceToNat]
  have hB : B.toNat = Q * v.size := by
    show (q * n).toNat = _; rw [UInt64.toNat_mul, hq, hn]; omega
  have hR : R.toNat = Q * v.size + v.size := by
    show (B + n).toNat = _; rw [toNat_add_lt] <;> rw [hB, hn] <;> omega
  have hRB : (R + B).toNat = 2 * (Q * v.size) + v.size := by
    rw [toNat_add_lt] <;> rw [hR, hB] <;> omega
  have hT : T.toNat = 2 * (Q * v.size) + 2 * v.size := by
    show (R + B + n).toNat = _; rw [toNat_add_lt] <;> rw [hRB, hn] <;> omega
  have h2n : (2 * n).toNat = 2 * v.size := by
    rw [UInt64.toNat_mul, hn]; simp only [UInt64.reduceToNat]; omega
  have hS : S.toNat = 2 * (Q * v.size) + 4 * v.size := by
    show (T + 2 * n).toNat = _; rw [toNat_add_lt] <;> rw [hT, h2n] <;> omega
  have h6n : (6 * n).toNat = 6 * v.size := by
    rw [UInt64.toNat_mul, hn]; simp only [UInt64.reduceToNat]; omega
  have hsz : (S + 6 * n).toNat = 2 * (Q * v.size) + 10 * v.size := by
    rw [toNat_add_lt] <;> rw [hS, h6n] <;> omega
  have hW0s : W0.size = 2 * (Q * v.size) + 10 * v.size := by
    show (LeanExe.build _ _).size = _; rw [build_size, hsz]
  have hget : ∀ i, i < W0.size → W0[i]! = if i < u.size then u[i]!
      else if Q * v.size ≤ i ∧ i < Q * v.size + v.size then v[i - Q * v.size]! else 0 := by
    intro i hi
    show (LeanExe.build _ _)[i]! = _
    rw [build_get (by rw [hsz]; omega)]
    have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, hii, hm, hB, hR]
    split
    · rfl
    · split
      · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hii, hB]; omega), hii, hB]
      · rfl
  have hdW0 : ∀ i, i < W0.size → W0[i]!.toNat < base := fun i hi => by
    rw [hget i hi]
    split
    · exact digit_all hu _
    · split
      · exact digit_all hv _
      · exact base_pos
  have hvW0 : segVal W0 (Q * v.size) v.size = value v := by
    rw [← segVal_value]
    exact segVal_congr fun i hi => by
      rw [hget _ (by omega), if_neg (by omega), if_pos (by omega),
        show Q * v.size + i - Q * v.size = 0 + i by omega]
  have huW0 : segVal W0 0 (Q * v.size) = value u := by
    have h1 := segVal_add W0 0 u.size (Q * v.size - u.size)
    rw [show u.size + (Q * v.size - u.size) = Q * v.size by omega,
      segVal_zeros (W := W0) (p := 0 + u.size) (k := Q * v.size - u.size) (fun i hi => by
        rw [hget _ (by omega), if_neg (by omega), if_neg (by omega)]),
      Nat.mul_zero, Nat.add_zero] at h1
    rw [h1, ← segVal_value]
    exact segVal_congr fun i hi => by rw [hget _ (by omega), if_pos (by omega)]
  have hW0lt : W0.size < 2 ^ 64 := by omega
  -- the loop over the chunks
  have key : ChunkInv W0 (Q * v.size + v.size) (Q * v.size + v.size) v.size (value v)
      q.toNat W1 := by
    refine loop_induction (P := fun c W => ChunkInv W0 (Q * v.size + v.size)
      (Q * v.size + v.size) v.size (value v) c W) ?_ ?_
    · refine ⟨rfl, fun _ _ => rfl, fun i hi => hdW0 _ (by omega), fun i _ hi => ?_, ?_⟩
      · rw [hget _ (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [segVal_zeros (fun i hi => by rw [hget _ (by omega), if_neg (by omega), if_neg (by omega)]),
          Nat.zero_mul, segVal_zero, Nat.zero_mul]
    intro c W' hc hinv
    rw [hq] at hc
    have hcc : (UInt64.ofNat c).toNat = c := toNat_ofNat_lt (by omega)
    have hcn : (UInt64.ofNat c * n).toNat = c * v.size := by
      rw [UInt64.toNat_mul, hcc, hn]
      exact Nat.mod_eq_of_lt (by nlinarith)
    have hRc : (R + UInt64.ofNat c * n).toNat = Q * v.size + v.size + c * v.size := by
      rw [toNat_add_lt] <;> rw [hR, hcn]; nlinarith
    have hc1n : c * v.size + v.size ≤ Q * v.size := by nlinarith
    have hcN : (c + 1) * v.size = c * v.size + v.size := by ring
    obtain ⟨L, hLd, hLlo, hLhi, hLsum⟩ : ∃ L, (if UInt64.ofNat c + 1 < q then n else
        m - UInt64.ofNat c * n).toNat = L ∧ 1 ≤ L ∧ L ≤ v.size ∧
        (c * v.size + L = c * v.size + v.size ∨ c * v.size + L = u.size) := by
      by_cases hlast : c + 1 < Q
      · refine ⟨v.size, ?_, by omega, le_rfl, Or.inl rfl⟩
        rw [if_pos (by
          rw [UInt64.lt_iff_toNat_lt, hq, toNat_add_lt (by simp only [UInt64.reduceToNat]; omega),
            hcc]; simpa using hlast), hn]
      · have hcQ : c + 1 = Q := by omega
        have : c * v.size < u.size := by
          have : (c + 1) * v.size = Q * v.size := by rw [hcQ]
          omega
        refine ⟨u.size - c * v.size, ?_, by omega, ?_, Or.inr (by omega)⟩
        · rw [if_neg (by
            rw [UInt64.lt_iff_toNat_lt, hq, toNat_add_lt (by simp only [UInt64.reduceToNat]; omega),
              hcc]; simpa using hlast),
            UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hcn, hm]; omega), hcn, hm]
        · have : (c + 1) * v.size = Q * v.size := by rw [hcQ]
          omega
    -- the chunk's value and the partial sums of the padded `u`
    have hCV : segVal W0 (c * v.size) v.size = segVal W0 (c * v.size) L := by
      rcases hLsum with h | h
      · rw [show L = v.size by omega]
      · have h1 := segVal_add W0 (c * v.size) L (v.size - L)
        rw [show L + (v.size - L) = v.size by omega,
          segVal_zeros (W := W0) (p := c * v.size + L) (k := v.size - L) (fun i hi => by
            rw [hget _ (by omega), if_neg (by omega), if_neg (by omega)]),
          Nat.mul_zero, Nat.add_zero] at h1
        exact h1
    have hSc : segVal W0 0 (c * v.size) + base ^ (c * v.size) * segVal W0 (c * v.size) v.size =
        segVal W0 0 ((c + 1) * v.size) := by
      rw [hcN, segVal_add, Nat.zero_add]
    have hSlt : segVal W0 0 ((c + 1) * v.size) < base ^ (c * v.size + L) := by
      have h1 := segVal_add W0 0 (c * v.size + L) ((c + 1) * v.size - (c * v.size + L))
      rcases hLsum with h | h
      · rw [hcN, ← h]; exact segVal_lt fun i hi => hdW0 _ (by omega)
      · rw [show c * v.size + L + ((c + 1) * v.size - (c * v.size + L)) = (c + 1) * v.size by
          omega, segVal_zeros (W := W0) (p := 0 + (c * v.size + L))
            (k := (c + 1) * v.size - (c * v.size + L)) (fun i hi => by
            rw [hget _ (by omega), if_neg (by omega), if_neg (by omega)]),
          Nat.mul_zero, Nat.add_zero] at h1
        rw [h1]; exact segVal_lt fun i hi => hdW0 _ (by omega)
    have hvlt := value_lt hv
    obtain ⟨s', f', dg', z', v'⟩ := hinv
    have rW' : ∀ i, i < Q * v.size + v.size → W'[i]! = W0[i]! := f'
    dsimp only
    generalize (if UInt64.ofNat c + 1 < q then n else m - UInt64.ofNat c * n) = len at hLd ⊢
    split
    · -- the last chunk is short: Algorithm M in place into the buffer
      have kM := baseMul_spec W' (UInt64.ofNat c * n) len B n T (by omega)
        (by rw [hcn, hLd]; omega) (by rw [hB, hn]; omega) (by rw [hT, hLd, hn]; omega)
        (by rw [hT, hcn, hLd]; omega) (by rw [hT, hB, hn]; omega)
        (by rw [hcn, hLd]; exact fun i hi => by rw [rW' _ (by omega)]; exact hdW0 _ (by omega))
        (by rw [hB, hn]; exact fun i hi => by rw [rW' _ (by omega)]; exact hdW0 _ (by omega))
      rw [hcn, hLd, hB, hn, hT] at kM
      obtain ⟨sM, fM, dM, vM⟩ := kM
      have hcv : segVal W' (c * v.size) L = segVal W0 (c * v.size) v.size := by
        rw [hCV]; exact segVal_congr fun i hi => rW' _ (by omega)
      have hvv : segVal W' (Q * v.size) v.size = value v := by
        rw [← hvW0]; exact segVal_congr fun i hi => rW' _ (by omega)
      rw [hcv, hvv] at vM
      exact chunk_add ⟨s', f', dg', z', v'⟩ (by omega) (by omega) (by omega) (by omega)
        (by omega) hW0lt (by rw [sM, s']) (fun q hq => fM q (by omega)) dM vM hSc
        (by
          calc segVal W0 0 ((c + 1) * v.size) * value v
              < base ^ (c * v.size + L) * base ^ v.size :=
                Nat.mul_lt_mul'' hSlt hvlt
            _ = base ^ (c * v.size + (L + v.size)) := by rw [← pow_add]; ring_nf)
        _ _ _ hRc hT (by rw [toNat_add_lt] <;> rw [hLd, hn] <;> omega)
    · -- a full chunk: Karatsuba's product into the buffer
      have kK := kara_spec t v.size W' (UInt64.ofNat c * n) B T S n hn (by omega)
        (by rw [hcn, hT]; omega) (by rw [hB, hT]; omega) (by rw [hT, hS]; omega)
        (by rw [hS]; omega)
        (by rw [hcn]; exact fun i hi => by rw [rW' _ (by omega)]; exact hdW0 _ (by omega))
        (by rw [hB]; exact fun i hi => by rw [rW' _ (by omega)]; exact hdW0 _ (by omega))
      rw [hcn, hB, hT, hS] at kK
      obtain ⟨sK, fK, dK, vK⟩ := kK
      have hcv : segVal W' (c * v.size) v.size = segVal W0 (c * v.size) v.size :=
        segVal_congr fun i hi => rW' _ (by omega)
      have hvv : segVal W' (Q * v.size) v.size = value v := by
        rw [← hvW0]; exact segVal_congr fun i hi => rW' _ (by omega)
      rw [hcv, hvv] at vK
      exact chunk_add ⟨s', f', dg', z', v'⟩ (by omega) (by omega) (by omega) (by omega)
        (by omega) hW0lt (by rw [sK, s']) (fun q hq => fK q (by omega) (by omega)) dK vK hSc
        (by
          calc segVal W0 0 ((c + 1) * v.size) * value v
              < base ^ ((c + 1) * v.size) * base ^ v.size :=
                Nat.mul_lt_mul'' (segVal_lt fun i hi => hdW0 _ (by omega)) hvlt
            _ = base ^ (c * v.size + 2 * v.size) := by rw [← pow_add, hcN]; ring_nf)
        _ _ _ hRc hT h2n
  -- the trimmed result
  rw [hq] at key
  obtain ⟨s1, -, d1, -, v1⟩ := key
  rw [huW0] at v1
  rw [trimSeg_eq W1 R (m + n) (by omega) (by rw [s1, hR, hmn]; omega)
    (by rw [hR, hmn]; exact d1.mono (by omega)), hR, hmn]
  congr 1
  have := segVal_trunc (W := W1) (p := Q * v.size + v.size) (a := u.size + v.size)
    (k := Q * v.size - u.size) (by rw [show u.size + v.size + (Q * v.size - u.size) =
      Q * v.size + v.size by omega]; exact d1)
    (by rw [show u.size + v.size + (Q * v.size - u.size) = Q * v.size + v.size by omega, v1]
        exact hval)
  rw [show u.size + v.size + (Q * v.size - u.size) = Q * v.size + v.size by omega, v1] at this
  exact this.symm

/-- The product of the second iteration, at any threshold, is the canonical form of the product
of the values. -/
theorem natMulKaraWith_eq (t : UInt64) {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natMulKaraWith t u v = limbsOf (value u * value v) := by
  unfold natMulKaraWith
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, size_toNat (by omega), size_toNat (by omega)] at h
    rw [mulLong_eq t hv hu hsv hsu (by omega), Nat.mul_comm]
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, size_toNat (by omega), size_toNat (by omega)] at h
    exact mulLong_eq t hu hv hsu hsv (by omega)

/-- `natMulKara` returns the canonical limbs of the product. -/
theorem natMulKara_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natMulKara u v = limbsOf (value u * value v) :=
  natMulKaraWith_eq _ hu hv hsu hsv

/-- `natMulKara` returns what the first iteration's `natMul` returns. -/
theorem natMulKara_eq_natMul {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) : natMulKara u v = natMul u v := by
  rw [natMulKara_eq hu hv hsu hsv, natMul_eq hu hv hsu hsv]

/-- `intMulKara` returns what the first iteration's `intMul` returns, on arrays of limbs. -/
theorem intMulKara_eq_intMul {x y : BigInt} (hx : Digits x.mag) (hy : Digits y.mag)
    (hsx : x.mag.size < 2 ^ 32) (hsy : y.mag.size < 2 ^ 32) : intMulKara x y = intMul x y := by
  unfold intMulKara intMul
  rw [natMulKara_eq_natMul hx hy hsx hsy]

/-- `intMulKara` of two canonical integers is the canonical integer of the product. -/
theorem intMulKara_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intMulKara (.ofInt a) (.ofInt b) = .ofInt (a * b) := by
  rw [intMulKara_eq_intMul (canonical_limbsOf _).1 (canonical_limbsOf _).1 ha hb, intMul_eq ha hb]

/-- The result of `natMulKara` is canonical. -/
theorem natMulKara_canonical {u v : Array UInt64} (hu : Digits u) (hv : Digits v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) : Canonical (natMulKara u v) := by
  rw [natMulKara_eq hu hv hsu hsv]; exact canonical_limbsOf _

/-- The result of `intMulKara` on canonical integers is canonical. -/
theorem intMulKara_canonical {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) : (intMulKara (.ofInt a) (.ofInt b)).Canonical := by
  rw [intMulKara_eq ha hb]; exact canonical_ofInt _

end Library.Numerics.Bignum