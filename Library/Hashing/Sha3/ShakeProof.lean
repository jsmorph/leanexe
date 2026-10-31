import Library.Hashing.Sha3.Proof

/-! The SHAKE programs compute SHAKE128 and SHAKE256 of the transcription.  The squeeze of
Algorithm 8, steps 7 to 10, is the first `d` bits of the first `r` bits of the states
`f^[i](S)`, concatenated, and the program writes lane `w % rw` of `keccakF^[w / rw]` of its state
to word `w` of its output.  For a message of fewer than `2^61` bytes and an output of `d < 2^61`
bytes, `shake128_spec` and `shake256_spec` state that the bits of the first `d` output bytes are
the transcription's output of `8 d` bits, and the output holds `⌈d / 8⌉` words whose bytes past
`d` are zero. -/

namespace Library.Hashing.Sha3.ShakeProof

open Library.Hashing.Sha3 Library.Hashing.Sha3.Spec Library.Hashing.Sha3.RoundProof
  Library.Hashing.Sha3.SpongeProof Library.Hashing.Sha3.Proof Library.Bytes

/-- The squeeze of Algorithm 8 from the output `Z` with `m` passes left is the first `d` bits of
`Z` followed by the first `r` bits of each state `f^[i](S)` for `i < m`, when each state has at
least `r` bits and the passes reach `d` bits. -/
theorem squeeze_stream (f : Bits → Bits) (r d : Nat) :
    ∀ (m : Nat) (S Z : Bits), (∀ i, r ≤ (f^[i] S).length) → d ≤ Z.length + m * r →
      squeeze f r d m S Z = trunc d (Z ++ (List.range m).flatMap fun i => trunc r (f^[i] S))
  | 0, S, Z, _, _ => by simp [squeeze]
  | m + 1, S, Z, hlen, hd => by
    have h0 : r ≤ S.length := hlen 0
    have hZ : (Z ++ trunc r S).length = Z.length + r := by
      simp [trunc, Nat.min_eq_left h0]
    have hsplit : (List.range (m + 1)).flatMap (fun i => trunc r (f^[i] S)) =
        trunc r S ++ (List.range m).flatMap fun i => trunc r (f^[i] (f S)) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      rfl
    rw [squeeze, hsplit, ← List.append_assoc]
    split
    · rename_i h
      unfold trunc at h ⊢
      rw [List.take_append_of_le_length h]
    · rw [squeeze_stream f r d m (f S) (Z ++ trunc r S)
        (fun i => by rw [← Function.iterate_succ_apply]; exact hlen (i + 1))
        (by rw [hZ]; rw [Nat.add_mul, Nat.one_mul] at hd; omega)]

/-- Iterated KECCAK-p[1600, 24] on the string of the lanes is the string of iterated `keccakF`. -/
theorem iterate_lanes (k : Nat) : ∀ s : Lanes,
    (keccakP 6 24)^[k] (toBits (toState s)) = toBits (toState (keccakF^[k] s)) := by
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    rw [Function.iterate_succ_apply, keccakP_lanes, ih, Function.iterate_succ_apply]

theorem laneAt_eq (s : Lanes) {i : Nat} (hi : i < 25) :
    laneAt s (UInt64.ofNat i) = (laneList s).getD i 0 := by
  interval_cases i <;> rfl

theorem get!_set! (xs : Array UInt64) (i : Nat) (v : UInt64) (j : Nat) :
    (xs.set! i v)[j]! = if i = j ∧ i < xs.size then v else xs[j]! := by
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < xs.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

/-- `squeezeBlock` sets words `base` to `base + rw - 1` below `words` to the state's first lanes. -/
theorem squeezeBlock_spec (out : Array UInt64) (s : Lanes) (rw words base : UInt64)
    (hb : base.toNat + rw.toNat < 2 ^ 64) (hrw : rw.toNat ≤ 25) :
    (squeezeBlock out s rw words base).size = out.size ∧
    ∀ w, (squeezeBlock out s rw words base)[w]! =
      if base.toNat ≤ w ∧ w < base.toNat + rw.toNat ∧ w < words.toNat ∧ w < out.size then
        (laneList s).getD (w - base.toNat) 0 else out[w]! := by
  unfold squeezeBlock
  refine LeanExe.Dialect.loop_induction
    (P := fun k (o : Array UInt64) => o.size = out.size ∧ ∀ w, o[w]! =
      if base.toNat ≤ w ∧ w < base.toNat + k ∧ w < words.toNat ∧ w < out.size then
        (laneList s).getD (w - base.toNat) 0 else out[w]!)
    ⟨rfl, fun w => by rw [ite_eq_right (by omega)]⟩ ?_
  intro k o hk ⟨hsize, hget⟩
  have hbk : (base + UInt64.ofNat k).toNat = base.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : (base + UInt64.ofNat k < words) ↔ base.toNat + k < words.toNat := by
    rw [UInt64.lt_iff_toNat_lt, hbk]
  by_cases hw : base + UInt64.ofNat k < words
  · rw [ite_eq_left hw]
    refine ⟨by simp [hsize], fun w => ?_⟩
    rw [get!_set!, hbk, hget, hsize]
    by_cases hwk : base.toNat + k = w
    · subst hwk
      by_cases hs : base.toNat + k < out.size
      · rw [ite_eq_left ⟨rfl, hs⟩, ite_eq_left ⟨by omega, by omega, hlt.mp hw, hs⟩,
          laneAt_eq _ (by omega)]
        congr 1; omega
      · rw [ite_eq_right (fun h => hs h.2), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (fun h => hwk h.1)]
      congr 1
      apply propext
      omega
  · rw [ite_eq_right hw]
    refine ⟨hsize, fun w => ?_⟩
    rw [hget]
    congr 1
    apply propext
    constructor
    · intro h; exact ⟨h.1, by omega, h.2.2⟩
    · intro h
      refine ⟨h.1, ?_, h.2.2⟩
      by_contra hc
      have : w = base.toNat + k := by omega
      exact hw (hlt.mpr (this ▸ h.2.2.1))

/-- The step of SHAKE's squeezing loop in `shakeWith`. -/
def squeezeStep (rw words blocks : UInt64) (k : UInt64) (st : Lanes × Array UInt64) :
    Lanes × Array UInt64 :=
  (if k + 1 < blocks then keccakF st.1 else st.1, squeezeBlock st.2 st.1 rw words (k * rw))

/-- The output mask of `shakeWith` for `d` bytes. -/
def finish (d words : UInt64) (out : Array UInt64) : Array UInt64 :=
  if d % 8 == 0 then out
  else out.set! (words - 1).toNat (out[(words - 1).toNat]! &&& ((1 <<< (8 * (d % 8))) - 1))

theorem shakeWith_eq (msg : Array UInt64) (n d rw : UInt64) :
    shakeWith msg n d rw = finish d ((d + 7) / 8)
      (LeanExe.loop (((d + 7) / 8 + rw - 1) / rw)
        (absorb msg n rw 0x1F, LeanExe.build ((d + 7) / 8) fun _ => 0)
        (squeezeStep rw ((d + 7) / 8) (((d + 7) / 8 + rw - 1) / rw))).2 := rfl

theorem build_get! (words : UInt64) (w : Nat) :
    (LeanExe.build words fun _ => (0 : UInt64))[w]! = 0 := by
  by_cases h : w < words.toNat
  · rw [LeanExe.Dialect.build_get h]
  · rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
      (by rw [LeanExe.Dialect.build_size]; omega)]
    rfl

/-- After the squeezing loop, word `w` below `words` of the output is lane `w % rw` of
`keccakF^[w / rw]` of the state, and the other words are zero. -/
theorem squeeze_loop (s : Lanes) (rw words blocks : UInt64) (hrw0 : 0 < rw.toNat)
    (hrw : rw.toNat ≤ 25) (hbw : blocks.toNat * rw.toNat < 2 ^ 63) :
    (LeanExe.loop blocks (s, LeanExe.build words fun _ => 0)
        (squeezeStep rw words blocks)).2.size = words.toNat ∧
      ∀ w, (LeanExe.loop blocks (s, LeanExe.build words fun _ => 0)
          (squeezeStep rw words blocks)).2[w]! =
        if w < min (blocks.toNat * rw.toNat) words.toNat then
          (laneList (keccakF^[w / rw.toNat] s)).getD (w % rw.toNat) 0 else 0 := by
  have key := LeanExe.Dialect.loop_induction
    (n := blocks) (init := (s, LeanExe.build words fun _ => (0 : UInt64)))
    (f := squeezeStep rw words blocks)
    (P := fun k (st : Lanes × Array UInt64) => st.2.size = words.toNat ∧
      (∀ w, st.2[w]! = if w < min (k * rw.toNat) words.toNat then
        (laneList (keccakF^[w / rw.toNat] s)).getD (w % rw.toNat) 0 else 0) ∧
      (k < blocks.toNat → st.1 = keccakF^[k] s))
    ⟨LeanExe.Dialect.build_size _ _, fun w => by rw [build_get!, ite_eq_right (by omega)],
      fun _ => rfl⟩
    (by
      intro k st hk ⟨hsize, hget, hstate⟩
      have hkrw : (UInt64.ofNat k * rw).toNat = k * rw.toNat := by
        have : k * rw.toNat < 2 ^ 63 :=
          Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hk)) hbw
        have hk0 : k ≤ k * rw.toNat := Nat.le_mul_of_pos_right _ hrw0
        rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have hk1 : (k + 1) * rw.toNat ≤ blocks.toNat * rw.toNat := Nat.mul_le_mul_right _ hk
      obtain ⟨hs', hg'⟩ := squeezeBlock_spec st.2 st.1 rw words (UInt64.ofNat k * rw)
        (by rw [hkrw]; rw [Nat.add_mul, Nat.one_mul] at hk1; omega) hrw
      refine ⟨by simp only [squeezeStep]; rw [hs', hsize], fun w => ?_, fun hk' => ?_⟩
      · simp only [squeezeStep]
        rw [hg', hkrw, hsize, hget, hstate hk]
        have hm : (k + 1) * rw.toNat = k * rw.toNat + rw.toNat := by ring
        by_cases h1 : w < k * rw.toNat
        · rw [ite_eq_right (by omega)]
          by_cases h2 : w < words.toNat
          · rw [ite_eq_left (by omega), ite_eq_left (by rw [hm]; omega)]
          · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        · by_cases h2 : w < k * rw.toNat + rw.toNat ∧ w < words.toNat
          · rw [ite_eq_left (by omega), ite_eq_left (by rw [hm]; omega)]
            have hq : w / rw.toNat = k := Nat.div_eq_of_lt_le (by omega) (by rw [hm]; omega)
            have hr : w % rw.toNat = w - k * rw.toNat := by
              rw [Nat.mod_def, hq, Nat.mul_comm]
            rw [hq, hr]
          · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [hm]; omega)]
      · simp only [squeezeStep]
        have hk2 : k + 1 ≤ (k + 1) * rw.toNat := Nat.le_mul_of_pos_right _ hrw0
        have hlt : UInt64.ofNat k + 1 < blocks := by
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
            UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)]
          simp only [UInt64.toNat_one]
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hk'
        rw [ite_eq_left hlt, hstate hk, Function.iterate_succ_apply'])
  exact ⟨key.1, key.2.1⟩

theorem sfx_shake :
    ∀ i, (0x1F : UInt64).toNat.testBit i = ([true, true, true, true] ++ [true]).getD i false :=
  sfx_bits 31 _ (by decide) (by decide) (by decide)

/-- The arithmetic of `d` output bytes: `⌈d / 8⌉` words and `⌈words / rw⌉` blocks. -/
theorem output_arith (d rw : UInt64) (hd : d.toNat < 2 ^ 61) (hrw0 : 0 < rw.toNat)
    (hrw : rw.toNat ≤ 25) :
    ((d + 7) / 8).toNat = (d.toNat + 7) / 8 ∧
    (((d + 7) / 8 + rw - 1) / rw).toNat = ((d.toNat + 7) / 8 + rw.toNat - 1) / rw.toNat ∧
    (d.toNat + 7) / 8 ≤ ((d.toNat + 7) / 8 + rw.toNat - 1) / rw.toNat * rw.toNat ∧
    ((d.toNat + 7) / 8 + rw.toNat - 1) / rw.toNat * rw.toNat < 2 ^ 63 := by
  have h7 : (d + 7).toNat = d.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have hw : ((d + 7) / 8).toNat = (d.toNat + 7) / 8 := by rw [UInt64.toNat_div, h7]; rfl
  have hwr : ((d + 7) / 8 + rw - 1).toNat = (d.toNat + 7) / 8 + rw.toNat - 1 := by
    have : ((d + 7) / 8 + rw).toNat = (d.toNat + 7) / 8 + rw.toNat := by
      rw [UInt64.toNat_add, hw]; omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, this]; simp; omega), this]
    simp
  refine ⟨hw, by rw [UInt64.toNat_div, hwr], ?_, ?_⟩
  · have h1 := Nat.div_add_mod ((d.toNat + 7) / 8 + rw.toNat - 1) rw.toNat
    have h2 := Nat.mod_lt ((d.toNat + 7) / 8 + rw.toNat - 1) hrw0
    have h3 : ((d.toNat + 7) / 8 + rw.toNat - 1) / rw.toNat * rw.toNat =
        rw.toNat * (((d.toNat + 7) / 8 + rw.toNat - 1) / rw.toNat) := Nat.mul_comm _ _
    omega
  · have := Nat.div_mul_le_self ((d.toNat + 7) / 8 + rw.toNat - 1) rw.toNat
    omega

/-- The last word's mask keeps the bits below `8 d`. -/
theorem finish_bit (d words : UInt64) (out : Array UInt64)
    (hw : words.toNat = (d.toNat + 7) / 8) {t : Nat} (ht : t < 8 * d.toNat) :
    bit (finish d words out)[t / 64]! (t % 64) = bit out[t / 64]! (t % 64) := by
  unfold finish
  by_cases h0 : d % 8 = 0
  · simp [h0]
  · have h0' : ¬ d.toNat % 8 = 0 := fun h =>
      h0 (UInt64.toNat_inj.mp (by rw [UInt64.toNat_mod]; exact h))
    have hb : (d % 8 == 0) = false := by simpa using h0
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have hw1 : (words - 1).toNat = words.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    rw [ShakeProof.get!_set!, hw1]
    by_cases h1 : words.toNat - 1 = t / 64 ∧ words.toNat - 1 < out.size
    · rw [ite_eq_left h1, h1.1, bit_and]
      have hm : (8 * (d % 8) : UInt64) = (8 * (d.toNat % 8)).toUInt64 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mul, UInt64.toNat_mod, Nat.toUInt64, UInt64.toNat_ofNat']
        simp only [show (8 : UInt64).toNat = 8 from rfl]
      rw [hm, bit_mask (by omega), decide_eq_true (by omega), Bool.and_true]
    · rw [ite_eq_right h1]

theorem getD_range {m i : Nat} (h : i < m) : (List.range m).getD i 0 = i := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The first `d` bytes of the SHAKE program's output, read least significant bit first, are
KECCAK[c] of the message and the suffix `1111`, to `8 d` bits. -/
theorem shakeWith_spec (msg : Array UInt64) (n d rw : UInt64) (c : Nat)
    (hn : n.toNat < 2 ^ 61) (hd : d.toNat < 2 ^ 61) (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25)
    (hc : 1600 - c = 64 * rw.toNat) :
    bitsOfBytes ((List.range d.toNat).map (byteAt (shakeWith msg n d rw))) =
      keccak c (messageBits msg n.toNat ++ [true, true, true, true]) (8 * d.toNat) := by
  obtain ⟨hw, hb, hbw1, hbw2⟩ := output_arith d rw hd hrw0 hrw
  rw [← hb, ← hw] at hbw1
  rw [← hb] at hbw2
  obtain ⟨hsize, hget⟩ := squeeze_loop (absorb msg n rw 0x1F) rw ((d + 7) / 8)
    (((d + 7) / 8 + rw - 1) / rw) hrw0 hrw hbw2
  rw [Nat.min_eq_right hbw1] at hget
  have hlen : ∀ i, 64 * rw.toNat ≤
      ((keccakP 6 24)^[i] (toBits (toState (absorb msg n rw 0x1F)))).length := by
    intro i; rw [iterate_lanes, length_toBits]; omega
  have hr : 0 < 64 * rw.toNat := by omega
  rw [keccak, hc, sponge_absorb msg n rw 0x1F _ hrw0 hrw hn (by decide) sfx_shake,
    squeeze_stream _ _ _ _ _ [] hlen (by
      simp only [List.length_nil, Nat.zero_add]
      have := Nat.lt_div_mul_add (a := 8 * d.toNat) hr
      rw [Nat.add_mul, Nat.one_mul]; omega)]
  have hseg : ∀ a ∈ List.range (8 * d.toNat / (64 * rw.toNat) + 1),
      (trunc (64 * rw.toNat)
        ((keccakP 6 24)^[a] (toBits (toState (absorb msg n rw 0x1F))))).length =
        64 * rw.toNat := by
    intro a _; simp [trunc, Nat.min_eq_left (hlen a)]
  have hflat := length_flatMap_of_length _ _ _ hseg
  apply ext_getD (by
    rw [length_bitsOfBytes, trunc, List.length_take, List.nil_append, hflat]
    simp only [List.length_map, List.length_range]
    have := Nat.lt_div_mul_add (a := 8 * d.toNat) hr
    rw [Nat.add_mul, Nat.one_mul]; omega)
  intro t ht
  rw [length_bitsOfBytes, List.length_map, List.length_range] at ht
  -- The program's bit.
  rw [getD_bitsOfBytes _ (by simp; omega)]
  have hbyte : ((List.range d.toNat).map (byteAt (shakeWith msg n d rw))).getD (t / 8) 0 =
      byteAt (shakeWith msg n d rw) (t / 8) := by
    simp [List.getD_eq_getElem?_getD, show t / 8 < d.toNat by omega]
  rw [hbyte, testBit_byteAt _ _ (by omega),
    show (t / 8) / 8 = t / 64 by omega, show 8 * (t / 8 % 8) + t % 8 = t % 64 by omega,
    shakeWith_eq, finish_bit _ _ _ hw ht, hget, ite_eq_left (by rw [hw]; omega)]
  -- The transcription's bit.
  have htr : (trunc (8 * d.toNat) ([] ++ (List.range (8 * d.toNat / (64 * rw.toNat) + 1)).flatMap
      fun i => trunc (64 * rw.toNat)
        ((keccakP 6 24)^[i] (toBits (toState (absorb msg n rw 0x1F)))))).getD t false =
      ((List.range (8 * d.toNat / (64 * rw.toNat) + 1)).flatMap fun i => trunc (64 * rw.toNat)
        ((keccakP 6 24)^[i] (toBits (toState (absorb msg n rw 0x1F))))).getD t false := by
    simp [trunc, List.getD_eq_getElem?_getD, ht]
  have hq : t / (64 * rw.toNat) < 8 * d.toNat / (64 * rw.toNat) + 1 :=
    Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  rw [htr, getD_flatMap _ (64 * rw.toNat) 0 false _ hseg t (by
      simp only [List.length_range]
      have := Nat.lt_div_mul_add (a := 8 * d.toNat) hr
      rw [Nat.add_mul, Nat.one_mul]; omega),
    getD_range hq]
  have htr2 : (trunc (64 * rw.toNat)
      ((keccakP 6 24)^[t / (64 * rw.toNat)] (toBits (toState (absorb msg n rw 0x1F))))).getD
        (t % (64 * rw.toNat)) false =
      ((keccakP 6 24)^[t / (64 * rw.toNat)] (toBits (toState (absorb msg n rw 0x1F)))).getD
        (t % (64 * rw.toNat)) false := by
    simp [trunc, List.getD_eq_getElem?_getD, Nat.mod_lt _ hr]
  rw [htr2, iterate_lanes, getD_lanes _ (by have := Nat.mod_lt t hr; omega),
    Nat.div_div_eq_div_mul, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

theorem shakeWith_size (msg : Array UInt64) (n d rw : UInt64) (hd : d.toNat < 2 ^ 61)
    (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25) :
    (shakeWith msg n d rw).size = (d.toNat + 7) / 8 := by
  obtain ⟨hw, hb, -, hbw2⟩ := output_arith d rw hd hrw0 hrw
  rw [← hb] at hbw2
  obtain ⟨hsize, -⟩ := squeeze_loop (absorb msg n rw 0x1F) rw ((d + 7) / 8)
    (((d + 7) / 8 + rw - 1) / rw) hrw0 hrw hbw2
  rw [shakeWith_eq, finish]
  split <;> simp [hsize, hw]

/-- The bytes of the SHAKE program's output past the first `d` are zero. -/
theorem shakeWith_tail (msg : Array UInt64) (n d rw : UInt64) (hd : d.toNat < 2 ^ 61)
    (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25) {i : Nat} (hi : d.toNat ≤ i) :
    byteAt (shakeWith msg n d rw) i = 0 := by
  obtain ⟨hw, hb, -, hbw2⟩ := output_arith d rw hd hrw0 hrw
  rw [← hb] at hbw2
  obtain ⟨hsize, hget⟩ := squeeze_loop (absorb msg n rw 0x1F) rw ((d + 7) / 8)
    (((d + 7) / 8 + rw - 1) / rw) hrw0 hrw hbw2
  have hzero : ∀ k, k < 8 → (byteAt (shakeWith msg n d rw) i).toNat.testBit k = false := by
    intro k hk
    rw [testBit_byteAt _ _ hk, shakeWith_eq]
    unfold finish
    by_cases hlt : i / 8 < (d.toNat + 7) / 8
    · have h0 : ¬ d.toNat % 8 = 0 := by omega
      have h0' : ¬ d % 8 = 0 := fun h => h0 (by
        have := congrArg UInt64.toNat h
        rw [UInt64.toNat_mod] at this
        simpa using this)
      have hbq : (d % 8 == 0) = false := by simpa using h0'
      have hw1 : ((d + 7) / 8 - 1).toNat = (d.toNat + 7) / 8 - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hw]; simp; omega), hw]
        simp
      simp only [hbq, Bool.false_eq_true, ↓reduceIte]
      rw [get!_set!, hw1, hsize, hw, ite_eq_left ⟨by omega, by omega⟩, bit_and]
      have hm : (8 * (d % 8) : UInt64) = (8 * (d.toNat % 8)).toUInt64 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mul, UInt64.toNat_mod, Nat.toUInt64, UInt64.toNat_ofNat']
        simp only [show (8 : UInt64).toNat = 8 from rfl]
      rw [hm, bit_mask (by omega), decide_eq_false (by omega), Bool.and_false]
    · have hout : ∀ (x : Array UInt64), x.size = (d.toNat + 7) / 8 → x[i / 8]! = 0 := by
        intro x hx
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (by omega)]
        rfl
      split
      · rw [hout _ (by rw [hsize, hw]), bit_zero]
      · rw [hout _ (by rw [Array.size_set!, hsize, hw]), bit_zero]
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [UInt8.toNat_zero, Nat.zero_testBit]
  by_cases hk : k < 8
  · exact hzero k hk
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt8.toNat_lt _)
      (Nat.pow_le_pow_right (by decide) (by omega)))

/-- SHAKE128 of the first `n` bytes of `msg` to `d` bytes is the transcription's SHAKE128 to
`8 d` bits. -/
theorem shake128_spec (msg : Array UInt64) (n d : UInt64) (hn : n.toNat < 2 ^ 61)
    (hd : d.toNat < 2 ^ 61) :
    bitsOfBytes ((List.range d.toNat).map (byteAt (shake128 msg n d))) =
      Spec.shake128 (messageBits msg n.toNat) (8 * d.toNat) :=
  shakeWith_spec msg n d 21 256 hn hd (by decide) (by decide) (by decide)

/-- SHAKE256 of the first `n` bytes of `msg` to `d` bytes is the transcription's SHAKE256 to
`8 d` bits. -/
theorem shake256_spec (msg : Array UInt64) (n d : UInt64) (hn : n.toNat < 2 ^ 61)
    (hd : d.toNat < 2 ^ 61) :
    bitsOfBytes ((List.range d.toNat).map (byteAt (shake256 msg n d))) =
      Spec.shake256 (messageBits msg n.toNat) (8 * d.toNat) :=
  shakeWith_spec msg n d 17 512 hn hd (by decide) (by decide) (by decide)

#print axioms shake128_spec
#print axioms shake256_spec
#print axioms shakeWith_tail
#print axioms shakeWith_size
#print axioms Library.Hashing.Sha3.Proof.sha3_224_spec
#print axioms Library.Hashing.Sha3.Proof.sha3_512_spec

end Library.Hashing.Sha3.ShakeProof
