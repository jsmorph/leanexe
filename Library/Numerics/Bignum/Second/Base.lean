module

public import Library.Numerics.Bignum.Second.Seg

@[expose] public section

/-!
Algorithm M in place and the trimmed copy of a segment.  `baseMul_spec` follows MultiPrecision's
`mul_eq`: after `j` rows the `j + ma` words of the result hold the product of the first operand
and the first `j` limbs of the second, and the words above them are still the zeros of the
first loop.  `trimSeg_eq` reduces the trimmed copy of a segment to `natTrim` of a slice, whose
canonical form `natTrim_eq` gives.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The loop that clears the `L` words from `rp`. -/
theorem clear_spec (W : Array UInt64) (rp L : UInt64) (hW : W.size < 2 ^ 64)
    (hr : rp.toNat + L.toNat ≤ W.size) :
    (LeanExe.loop L W fun i W => W.set! (rp + i).toNat 0).size = W.size ∧
    (∀ q, (q < rp.toNat ∨ rp.toNat + L.toNat ≤ q) →
      (LeanExe.loop L W fun i W => W.set! (rp + i).toNat 0)[q]! = W[q]!) ∧
    (∀ i, i < L.toNat → (LeanExe.loop L W fun i W => W.set! (rp + i).toNat 0)[rp.toNat + i]! = 0) := by
  refine loop_induction (P := fun i (V : Array UInt64) => V.size = W.size ∧
      (∀ q, (q < rp.toNat ∨ rp.toNat + i ≤ q) → V[q]! = W[q]!) ∧
      (∀ i', i' < i → V[rp.toNat + i']! = 0))
    ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ ?_
  intro i V hi ⟨hs, hfr, hz⟩
  have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
  have hri : (rp + UInt64.ofNat i).toNat = rp.toNat + i := by rw [toNat_add_lt] <;> omega
  rw [hri]
  have hget := fun q => get_set V (rp.toNat + i) 0 q (by omega)
  refine ⟨by simp [hs], fun q hq => ?_, fun i' hi' => ?_⟩
  · rw [hget, if_neg (by omega)]; exact hfr q (by omega)
  · rw [hget]
    split
    · rfl
    · exact hz i' (by omega)

/-- One row of Algorithm M in place: the `ma` words from `rp + j` plus the first operand times
`y`, with the final carry. -/
theorem row_spec (V : Array UInt64) (ap ma rp j y : UInt64) (hW : V.size < 2 ^ 64)
    (ha : ap.toNat + ma.toNat ≤ V.size) (hr : rp.toNat + j.toNat + ma.toNat ≤ V.size)
    (hra : rp.toNat + j.toNat + ma.toNat ≤ ap.toNat ∨ ap.toNat + ma.toNat ≤ rp.toNat + j.toNat)
    (hda : SegDigits V ap.toNat ma.toNat) (hdr : SegDigits V (rp.toNat + j.toNat) ma.toNat)
    (hy : y.toNat < base) :
    let s := LeanExe.loop ma ((0 : UInt64), V) fun i s =>
      let t := s.2[(ap + i).toNat]! * y + s.2[(rp + i + j).toNat]! + s.1
      (t >>> 32, s.2.set! (rp + i + j).toNat (t &&& 0xFFFFFFFF))
    s.2.size = V.size ∧
    (∀ q, (q < rp.toNat + j.toNat ∨ rp.toNat + j.toNat + ma.toNat ≤ q) → s.2[q]! = V[q]!) ∧
    SegDigits s.2 (rp.toNat + j.toNat) ma.toNat ∧ s.1.toNat < base ∧
    segVal s.2 (rp.toNat + j.toNat) ma.toNat + s.1.toNat * base ^ ma.toNat =
      segVal V (rp.toNat + j.toNat) ma.toNat + segVal V ap.toNat ma.toNat * y.toNat := by
  intro s
  refine loop_induction (P := fun i (s : UInt64 × Array UInt64) => s.2.size = V.size ∧
      (∀ q, (q < rp.toNat + j.toNat ∨ rp.toNat + j.toNat + i ≤ q) → s.2[q]! = V[q]!) ∧
      SegDigits s.2 (rp.toNat + j.toNat) i ∧ s.1.toNat < base ∧
      segVal s.2 (rp.toNat + j.toNat) i + s.1.toNat * base ^ i =
        segVal V (rp.toNat + j.toNat) i + segVal V ap.toNat i * y.toNat)
    ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), base_pos, by simp [segVal]⟩ ?_
  intro i s hi ⟨hs, hfr, hdg, hc, hv⟩
  have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
  have hai : (ap + UInt64.ofNat i).toNat = ap.toNat + i := by rw [toNat_add_lt] <;> omega
  have hri1 : (rp + UInt64.ofNat i).toNat = rp.toNat + i := by rw [toNat_add_lt] <;> omega
  have hri : (rp + UInt64.ofNat i + j).toNat = rp.toNat + j.toNat + i := by
    rw [toNat_add_lt] <;> rw [hri1] <;> omega
  have hA : s.2[ap.toNat + i]! = V[ap.toNat + i]! := hfr _ (by omega)
  have hR : s.2[rp.toNat + j.toNat + i]! = V[rp.toNat + j.toNat + i]! :=
    read_kept (x := rp.toNat + j.toNat) hfr fun i' hi' => by omega
  have hAd := hda i hi
  have hRd := hdr i hi
  dsimp only
  rw [hai, hri, hA, hR]
  have hprod : V[ap.toNat + i]!.toNat * y.toNat ≤ 4294967295 * 4294967295 := by
    rw [base_eq] at hAd hy; exact Nat.mul_le_mul (by omega) (by omega)
  have ht : (V[ap.toNat + i]! * y + V[rp.toNat + j.toNat + i]! + s.1).toNat =
      V[ap.toNat + i]!.toNat * y.toNat + V[rp.toNat + j.toNat + i]!.toNat + s.1.toNat := by
    rw [base_eq] at hRd hc
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul,
      Nat.mod_eq_of_lt (by omega : V[ap.toNat + i]!.toNat * y.toNat < 2 ^ 64)]
    omega
  generalize V[ap.toNat + i]! * y + V[rp.toNat + j.toNat + i]! + s.1 = t at ht
  have hdin : rp.toNat + j.toNat + i < s.2.size := by omega
  have hget := fun q => get_set s.2 (rp.toNat + j.toNat + i) (t &&& 0xFFFFFFFF) q hdin
  refine ⟨by simp [hs], fun q hq => ?_, fun i' hi' => ?_, ?_, ?_⟩
  · rw [hget, if_neg (by omega)]; exact hfr q (by omega)
  · rw [hget]
    split
    · rw [and_mask]; exact Nat.mod_lt _ base_pos
    · exact hdg i' (by omega)
  · rw [shr32, ht]
    rw [base_eq] at hRd hc ⊢
    omega
  · have hcongr : segVal (s.2.set! (rp.toNat + j.toNat + i) (t &&& 0xFFFFFFFF))
        (rp.toNat + j.toNat) i = segVal s.2 (rp.toNat + j.toNat) i :=
      segVal_congr fun i' hi' => by rw [hget, if_neg (by omega)]
    rw [segVal_succ, hcongr, hget, if_pos rfl, and_mask, shr32, segVal_succ, segVal_succ, ht,
      pow_succ]
    have hdm := Nat.mod_add_div
      (V[ap.toNat + i]!.toNat * y.toNat + V[rp.toNat + j.toNat + i]!.toNat + s.1.toNat) base
    zify at hv hdm ⊢
    linear_combination hv + (base : ℤ) ^ i * hdm

/-- `baseMul` writes over the `ma + nb` words from `rp` the product of the `ma` words from `ap`
and the `nb` words from `bp`, when the result's range is apart from both operands. -/
theorem baseMul_spec (W : Array UInt64) (ap ma bp nb rp : UInt64) (hW : W.size < 2 ^ 64)
    (ha : ap.toNat + ma.toNat ≤ W.size) (hb : bp.toNat + nb.toNat ≤ W.size)
    (hr : rp.toNat + (ma.toNat + nb.toNat) ≤ W.size)
    (hra : rp.toNat + (ma.toNat + nb.toNat) ≤ ap.toNat ∨ ap.toNat + ma.toNat ≤ rp.toNat)
    (hrb : rp.toNat + (ma.toNat + nb.toNat) ≤ bp.toNat ∨ bp.toNat + nb.toNat ≤ rp.toNat)
    (hda : SegDigits W ap.toNat ma.toNat) (hdb : SegDigits W bp.toNat nb.toNat) :
    (baseMul W ap ma bp nb rp).size = W.size ∧
    (∀ q, (q < rp.toNat ∨ rp.toNat + (ma.toNat + nb.toNat) ≤ q) →
      (baseMul W ap ma bp nb rp)[q]! = W[q]!) ∧
    SegDigits (baseMul W ap ma bp nb rp) rp.toNat (ma.toNat + nb.toNat) ∧
    segVal (baseMul W ap ma bp nb rp) rp.toNat (ma.toNat + nb.toNat) =
      segVal W ap.toNat ma.toNat * segVal W bp.toNat nb.toNat := by
  have hL : (ma + nb).toNat = ma.toNat + nb.toNat := toNat_add_lt (by omega)
  obtain ⟨hzs, hzf, hzz⟩ := clear_spec W rp (ma + nb) hW (by omega)
  rw [hL] at hzf hzz
  unfold baseMul
  generalize (LeanExe.loop (ma + nb) W fun i W => W.set! (rp + i).toNat 0) = Z at hzs hzf hzz
  have key := loop_induction (n := nb) (init := Z)
    (f := fun j W =>
      let y := W[(bp + j).toNat]!
      let s := LeanExe.loop ma ((0 : UInt64), W) fun i s =>
        let t := s.2[(ap + i).toNat]! * y + s.2[(rp + i + j).toNat]! + s.1
        (t >>> 32, s.2.set! (rp + i + j).toNat (t &&& 0xFFFFFFFF))
      s.2.set! (rp + j + ma).toNat s.1)
    (P := fun j (V : Array UInt64) => V.size = W.size ∧
      (∀ q, (q < rp.toNat ∨ rp.toNat + (ma.toNat + nb.toNat) ≤ q) → V[q]! = W[q]!) ∧
      SegDigits V rp.toNat (ma.toNat + nb.toNat) ∧
      (∀ i, j + ma.toNat ≤ i → i < ma.toNat + nb.toNat → V[rp.toNat + i]! = 0) ∧
      segVal V rp.toNat (j + ma.toNat) = segVal W ap.toNat ma.toNat * segVal W bp.toNat j)
    ⟨hzs, hzf, fun i hi => by rw [hzz i hi]; exact base_pos, fun i _ hi => hzz i hi,
      by rw [segVal_zeros fun i hi => hzz i (by omega)]; simp [segVal]⟩
    (by
      intro j V hj ⟨hs, hfr, hdg, hz, hv⟩
      have hjj : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (by omega)
      have hbj : (bp + UInt64.ofNat j).toNat = bp.toNat + j := by rw [toNat_add_lt] <;> omega
      have hY : V[bp.toNat + j]! = W[bp.toNat + j]! := hfr _ (by omega)
      have hYd := hdb j hj
      have hapV : SegDigits V ap.toNat ma.toNat :=
        hda.congr fun i hi => hfr _ (by omega)
      have hrow := row_spec V ap ma rp (UInt64.ofNat j) W[bp.toNat + j]! (by omega) (by omega)
        (by rw [hjj]; omega) (by rw [hjj]; omega) hapV
        (by rw [hjj]; exact fun i hi => by rw [Nat.add_assoc]; exact hdg (j + i) (by omega)) hYd
      dsimp only
      rw [hbj, hY]
      generalize (LeanExe.loop ma ((0 : UInt64), V) fun i s =>
        let t := s.2[(ap + i).toNat]! * W[bp.toNat + j]! + s.2[(rp + i + UInt64.ofNat j).toNat]! + s.1
        (t >>> 32, s.2.set! (rp + i + UInt64.ofNat j).toNat (t &&& 0xFFFFFFFF))) = s at hrow
      rw [hjj] at hrow
      obtain ⟨hs2, hfr2, hdg2, hc2, hv2⟩ := hrow
      have hpos1 : (rp + UInt64.ofNat j).toNat = rp.toNat + j := by rw [toNat_add_lt] <;> omega
      have hpos : (rp + UInt64.ofNat j + ma).toNat = rp.toNat + j + ma.toNat := by
        rw [toNat_add_lt] <;> rw [hpos1] <;> omega
      rw [hpos]
      have hget := fun q => get_set s.2 (rp.toNat + j + ma.toNat) s.1 q (by omega)
      have hav : segVal V ap.toNat ma.toNat = segVal W ap.toNat ma.toNat :=
        segVal_congr fun i hi => hfr _ (by omega)
      refine ⟨by simp [hs2, hs], fun q hq => ?_, fun i hi => ?_, fun i hi1 hi2 => ?_, ?_⟩
      · rw [hget, if_neg (by omega), hfr2 q (by omega)]; exact hfr q hq
      · rw [hget]
        split
        · exact hc2
        · by_cases hin : j ≤ i ∧ i < j + ma.toNat
          · have := hdg2 (i - j) (by omega)
            rwa [show rp.toNat + j + (i - j) = rp.toNat + i by omega] at this
          · rw [hfr2 _ (by omega)]; exact hdg i hi
      · rw [hget, if_neg (by omega), hfr2 _ (by omega)]; exact hz i (by omega) hi2
      · -- the value of the first `j + 1 + ma` words
        have hsplit := segVal_add (s.2.set! (rp.toNat + j + ma.toNat) s.1) rp.toNat j (ma.toNat + 1)
        rw [show j + (ma.toNat + 1) = j + 1 + ma.toNat by omega] at hsplit
        rw [hsplit]
        have hlow : segVal (s.2.set! (rp.toNat + j + ma.toNat) s.1) rp.toNat j =
            segVal V rp.toNat j :=
          segVal_congr fun i hi => by rw [hget, if_neg (by omega), hfr2 _ (by omega)]
        have hhigh : segVal (s.2.set! (rp.toNat + j + ma.toNat) s.1) (rp.toNat + j) (ma.toNat + 1) =
            segVal s.2 (rp.toNat + j) ma.toNat + s.1.toNat * base ^ ma.toNat := by
          rw [segVal_succ, hget, if_pos rfl]
          congr 1
          exact segVal_congr fun i hi => by rw [hget, if_neg (by omega)]
        rw [hlow, hhigh, hv2, hav, segVal_succ]
        rw [segVal_add] at hv
        zify at hv ⊢
        linear_combination hv)
  obtain ⟨h1, h2, h3, -, h5⟩ := key
  refine ⟨h1, h2, h3, ?_⟩
  rw [show ma.toNat + nb.toNat = nb.toNat + ma.toNat by omega]
  exact h5

/-- The trimmed copy of a segment of limbs is the canonical form of its value. -/
theorem trimSeg_eq (W : Array UInt64) (p len : UInt64) (hW : W.size < 2 ^ 64)
    (hp : p.toNat + len.toNat ≤ W.size) (hd : SegDigits W p.toNat len.toNat) :
    trimSeg W p len = limbsOf (segVal W p.toNat len.toNat) := by
  have hsz : (slice W p len).size = len.toNat := build_size _ _
  have hidx : ∀ i : ℕ, i < len.toNat → (p + UInt64.ofNat i).toNat = p.toNat + i := fun i hi => by
    rw [toNat_add_lt] <;> rw [toNat_ofNat_lt (by omega)] <;> omega
  have hget : ∀ i : ℕ, i < len.toNat → (slice W p len)[i]! = W[p.toNat + i]! := fun i hi => by
    rw [slice, build_get hi, hidx i hi]
  have hsig : significant (slice W p len) =
      LeanExe.loop len (0 : UInt64) fun i k => if W[(p + i).toNat]! = 0 then k else i + 1 := by
    unfold significant
    rw [hsz, show len.toNat.toUInt64 = len from UInt64.ofNat_toNat]
    apply loop_congr
    intro k hk s
    rw [toNat_ofNat_lt (by omega), hget k hk, hidx k hk]
  have hle := (significant_spec (slice W p len) (by omega)).1
  have htrim : trimSeg W p len = natTrim (slice W p len) := by
    unfold trimSeg natTrim
    rw [hsig]
    apply build_congr
    intro i hi
    rw [← hsig] at hi
    have hi' : i.toNat < len.toNat := by omega
    rw [hget _ hi', ← hidx _ hi', UInt64.ofNat_toNat]
  have hdig : Digits (slice W p len) := fun i hi => by
    rw [hget i (by omega)]; exact hd i (by omega)
  rw [htrim, natTrim_eq hdig (by omega), ← segVal_value, hsz]
  congr 1
  exact segVal_congr fun i hi => by rw [Nat.zero_add, hget i hi]

end Library.Numerics.Bignum
