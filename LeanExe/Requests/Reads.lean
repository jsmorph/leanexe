import LeanExe.Requests.Records

/-!
The rate of the framing's reads of the receive register, and the records that the bytes encode.
`frameTick` reads the receive register only in phase 0, after a status read that shows a byte, and
the window after that read reads the status again, so no two consecutive windows read a byte and
the first window reads none.  `frame_reads` states that the first `n` windows read at most `n / 2`
bytes, and `decode_lengths` that each record that bytes encode has `kin` words and takes `8 kin`
of the bytes, which together bound the records that a step with records receives in a number of
windows.

`decode_take` states that `recordBytes` inverts `decode` on bytes below 256, which every byte of
`dataIn` is by `dataIn_lt`: the bytes of the first `i` records that `decode` gives are the first
`8 kin i` bytes, and `decode_length` states that `decode` gives one record for each `8 kin` bytes.
`flatMap_recordBytes_inj` states that records of `kin` words are determined by their bytes, so
`decode_recs` characterizes the records.  A statement over the records that the bytes read encode
can therefore name prefixes of the bytes read in their place.
-/

namespace LeanExe.Requests

open LeanExe.Native (readReq writeReq)

variable {M α : Type} (B : Bus α) (u : Uart) {kin kout : Nat}
  {mach : M → List UInt64 → M × List UInt64} {m0 : M}

theorem ne_one_zero {x : UInt64} (h : x = 0) : x ≠ 1 := by rw [h]; decide
theorem ne_one_two {x : UInt64} (h : x = 2) : x ≠ 1 := by rw [h]; decide
theorem ne_one_three {x : UInt64} (h : x = 3) : x ≠ 1 := by rw [h]; decide

/-- A window's result `p` reads the receive register and enters phase 1, or reads the status or
writes the transmit register and does not enter phase 1. -/
def TickCase (p : Framing M × UInt64) : Prop :=
  (p.2 = readReq u.rx ∧ p.1.phase = 1) ∨
    ((p.2 = readReq u.status ∨ ∃ x, p.2 = writeReq u.tx x) ∧ p.1.phase ≠ 1)

/-- Every window of the framing has a result of `TickCase`. -/
theorem frameTick_cases (f : Framing M) (v : UInt64) :
    TickCase u (frameTick u kin kout mach f v) := by
  unfold frameTick
  split
  next h0 =>
    split
    next => exact Or.inl ⟨rfl, rfl⟩
    next => exact Or.inr ⟨Or.inl rfl, ne_one_zero (beq_iff_eq.mp h0)⟩
  next =>
    split
    next =>
      split
      next => exact Or.inr ⟨Or.inl rfl, ne_one_zero rfl⟩
      next =>
        split
        next => exact Or.inr ⟨Or.inl rfl, ne_one_zero rfl⟩
        next => exact Or.inr ⟨Or.inl rfl, ne_one_two rfl⟩
    next =>
      split
      next h2 =>
        split
        next => exact Or.inr ⟨Or.inr ⟨_, rfl⟩, ne_one_three rfl⟩
        next => exact Or.inr ⟨Or.inl rfl, ne_one_two (beq_iff_eq.mp h2)⟩
      next =>
        split
        next => exact Or.inr ⟨Or.inl rfl, ne_one_two rfl⟩
        next =>
          split
          next => exact Or.inr ⟨Or.inl rfl, ne_one_two rfl⟩
          next => exact Or.inr ⟨Or.inl rfl, ne_one_zero rfl⟩

/-- A window from phase 1 reads the status. -/
theorem frameTick_phase1 {f : Framing M} (h : f.phase = 1) (v : UInt64) :
    (frameTick u kin kout mach f v).2 = readReq u.status := by
  unfold frameTick
  split
  next h0 => exact absurd (h.symm.trans (beq_iff_eq.mp h0)) (by decide)
  next =>
    split
    next =>
      split
      next => rfl
      next =>
        split
        next => rfl
        next => rfl
    next h1 => exact absurd (beq_iff_eq.mpr h) h1

variable (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
  (hrs : u.rx ≠ u.status)

include hrx hs hrs in
theorem readReq_rx_ne : readReq u.rx ≠ readReq u.status := by
  intro e
  have := congrArg reqReg e
  rw [reqReg_readReq hs, reqReg_readReq hrx] at this
  exact hrs this

include hrx htx in
theorem readReq_rx_ne_write (x : UInt64) : writeReq u.tx x ≠ readReq u.rx := by
  intro e
  have := congrArg reqWrite e
  rw [reqWrite_writeReq x htx, reqWrite_readReq hrx] at this
  exact absurd this (by decide)

include hrx htx hs hrs in
/-- The bytes that the window from `r` reads: one when its request reads the receive register and
none otherwise. -/
theorem dataIn_window (σ : Nat → UInt32) (r : ReqState (Framing M)) :
    ((frameTick u kin kout mach r.state r.last).2 = readReq u.rx →
        (dataIn B u [reqEvent B (frameTick u kin kout mach) σ r]).length = 1) ∧
      ((frameTick u kin kout mach r.state r.last).2 ≠ readReq u.rx →
        (dataIn B u [reqEvent B (frameTick u kin kout mach) σ r]).length = 0) := by
  rcases frameTick_cases u r.state r.last (kin := kin) (kout := kout) (mach := mach) with
    ⟨hq, -⟩ | ⟨hq | ⟨x, hq⟩, -⟩
  · refine ⟨fun _ => ?_, fun h => absurd hq h⟩
    simp only [reqEvent, hq, reqWrite_readReq hrx, reqReg_readReq hrx, Bool.false_eq_true,
      ite_false, dataIn_data, List.length_singleton]
  · refine ⟨fun h => absurd (hq.symm.trans h) (readReq_rx_ne u hrx hs hrs).symm, fun _ => ?_⟩
    simp only [reqEvent, hq, reqWrite_readReq hs, reqReg_readReq hs, Bool.false_eq_true,
      ite_false, dataIn_status B u hrx hs hrs, List.length_nil]
  · refine ⟨fun h => absurd (hq.symm.trans h) (readReq_rx_ne_write u hrx htx x), fun _ => ?_⟩
    simp only [reqEvent, hq, reqWrite_writeReq x htx, ite_true, dataIn_write, List.length_nil]

theorem reqNext_state (tick : Framing M → UInt64 → Framing M × UInt64) (σ : Nat → UInt32)
    (r : ReqState (Framing M)) : (reqNext tick σ r).state = (tick r.state r.last).1 := by
  unfold reqNext; split <;> rfl

/-- The first window, from phase 0 with no value read, reads the status. -/
theorem frameTick_first {f : Framing M} (h : f.phase = 0) :
    frameTick u kin kout mach f 0 = (f, readReq u.status) := by
  have hz : (0 : UInt64) &&& u.rxFull = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and]
    exact Nat.zero_and _
  unfold frameTick
  rw [ite_eq_left (show (f.phase == 0) = true from beq_iff_eq.mpr h), hz]
  rfl

include hrx htx hs hrs in
/-- After window `n`, twice the bytes read are at most `n + 1`, and less than that unless the
framing is in phase 1. -/
theorem frame_reads_succ (σ : Nat → UInt32) (n : Nat) :
    ((reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).state.phase = 1 →
        2 * (dataIn B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0) σ)
          (n + 1))).length ≤ n + 1) ∧
      ((reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).state.phase ≠ 1 →
        2 * (dataIn B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0) σ)
          (n + 1))).length + 1 ≤ n + 1) := by
  induction n with
  | zero =>
      have hq : frameTick u kin kout mach
          (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0).state
          (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0).last =
            ((reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0).state,
              readReq u.status) := by
        rw [show (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0).last = 0 from rfl]
        exact frameTick_first u
          (show (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0).state.phase = 0
            from rfl)
      have hw := (dataIn_window B u hrx htx hs hrs (kin := kin) (kout := kout) (mach := mach) σ
        (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0)).2
          (by rw [hq]; exact (readReq_rx_ne u hrx hs hrs).symm)
      have hc : (dataIn B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0)
          σ) (0 + 1))).length = 0 := by
        rw [windows, windows, List.nil_append]
        exact hw
      have hph : (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ
          (0 + 1)).state.phase = 0 := by
        rw [show reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (0 + 1) =
            reqNext (frameTick u kin kout mach) σ
              (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ 0) from rfl,
          reqNext_state, hq]
        rfl
      rw [hc, hph]
      exact ⟨fun h => absurd h (by decide), fun _ => by omega⟩
  | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hst : (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1 + 1)).state =
          (frameTick u kin kout mach
            (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).state
            (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).last).1 := by
        rw [show reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1 + 1) =
            reqNext (frameTick u kin kout mach) σ
              (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)) from rfl,
          reqNext_state]
      have hcc : (dataIn B u (windows (reqTrace B (frameTick u kin kout mach)
          (frame0 kin kout m0) σ) (n + 1 + 1))).length =
            (dataIn B u (windows (reqTrace B (frameTick u kin kout mach)
              (frame0 kin kout m0) σ) (n + 1))).length +
            (dataIn B u [reqEvent B (frameTick u kin kout mach) σ
              (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1))]).length := by
        rw [windows, dataIn_append, List.length_append]
        try rfl
      have hw := dataIn_window B u hrx htx hs hrs (kin := kin) (kout := kout) (mach := mach) σ
        (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1))
      rw [hcc, hst]
      rcases frameTick_cases u
          (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).state
          (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).last
          (kin := kin) (kout := kout) (mach := mach) with
        ⟨hq, hph⟩ | ⟨hq, hph⟩
      · have hp0 : (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ
            (n + 1)).state.phase ≠ 1 := fun e =>
          readReq_rx_ne u hrx hs hrs (hq.symm.trans (frameTick_phase1 u e _))
        have h2 := ih2 hp0
        rw [hw.1 hq]
        exact ⟨fun _ => by omega, fun h => absurd hph h⟩
      · have hne : (frameTick u kin kout mach
            (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).state
            (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ (n + 1)).last).2 ≠
              readReq u.rx := by
          rcases hq with hq | ⟨x, hq⟩
          · rw [hq]; exact (readReq_rx_ne u hrx hs hrs).symm
          · rw [hq]; exact readReq_rx_ne_write u hrx htx x
        rw [hw.2 hne]
        refine ⟨fun h => absurd h hph, fun _ => ?_⟩
        by_cases h1 : (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ
            (n + 1)).state.phase = 1
        · have := ih1 h1; omega
        · have := ih2 h1; omega

include hrx htx hs hrs in
/-- The first `n` windows of the framing read at most `n / 2` bytes from the receive register. -/
theorem frame_reads (σ : Nat → UInt32) (n : Nat) :
    2 * (dataIn B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0) σ)
      n)).length ≤ n := by
  cases n with
  | zero => simp [windows, dataIn]
  | succ n =>
      obtain ⟨h1, h2⟩ := frame_reads_succ B u hrx htx hs hrs (kin := kin) (kout := kout)
        (mach := mach) (m0 := m0) σ n
      by_cases h : (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ
          (n + 1)).state.phase = 1
      · exact h1 h
      · have := h2 h; omega

/-- The lengths of the decoder's state after `n` bytes: each record has `kin` words, and the
records, the words of the current record, and the bytes of the current word take the `n` bytes. -/
def DecodeLengths (kin : Nat) (d : Decoded) (n : Nat) : Prop :=
  (∀ r ∈ d.recs, r.length = kin) ∧ d.words.length < kin ∧ d.nbyte ≤ 7 ∧
    d.recs.length * (8 * kin) + d.words.length * 8 + d.nbyte = n

theorem decodeByte_lengths {kin : Nat} {d : Decoded} {n : Nat} (h : DecodeLengths kin d n)
    (b : UInt64) : DecodeLengths kin (decodeByte kin d b) (n + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold decodeByte
  split
  · exact ⟨h1, h2, by simp only; omega, by simp only; omega⟩
  · split
    · exact ⟨h1, by simp only [List.length_append, List.length_singleton]; omega,
        by simp only; omega, by simp only [List.length_append, List.length_singleton]; omega⟩
    · refine ⟨fun r hr => ?_, by simp only [List.length_nil]; omega, by simp only; omega,
        by simp only [List.length_append, List.length_singleton, List.length_nil, Nat.add_mul,
          Nat.one_mul]; omega⟩
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h1 r hr
      · simp only [List.length_append, List.length_singleton]; omega

theorem foldl_decodeByte_lengths {kin : Nat} :
    ∀ (bs : List UInt64) (d : Decoded) (n : Nat), DecodeLengths kin d n →
      DecodeLengths kin (bs.foldl (decodeByte kin) d) (n + bs.length)
  | [], _, _, h => h
  | b :: bs, d, n, h => by
      rw [List.foldl_cons, List.length_cons, show n + (bs.length + 1) = n + 1 + bs.length by omega]
      exact foldl_decodeByte_lengths bs _ _ (decodeByte_lengths h b)

/-- Each record that the bytes `bs` encode has `kin` words, and the records, the words of the
current record, and the bytes of the current word take all of `bs`. -/
theorem decode_lengths {kin : Nat} (hkin : 0 < kin) (bs : List UInt64) :
    (∀ r ∈ (decode kin bs).recs, r.length = kin) ∧ (decode kin bs).words.length < kin ∧
      (decode kin bs).nbyte ≤ 7 ∧
      (decode kin bs).recs.length * (8 * kin) + (decode kin bs).words.length * 8 +
        (decode kin bs).nbyte = bs.length := by
  have h := foldl_decodeByte_lengths (kin := kin) bs ⟨[], [], 0, 0⟩ 0
    ⟨fun r hr => absurd hr (by simp), by simp only [List.length_nil]; omega, by simp only; omega,
      by simp only [List.length_nil]; omega⟩
  rw [Nat.zero_add] at h
  exact h

/-- The `k` low bytes of the word `a`, the most significant first. -/
def lowBytes (a : UInt64) : Nat → List UInt64
  | 0 => []
  | k + 1 => lowBytes (a / 256) k ++ [a % 256]

theorem lowBytes_push {a b : UInt64} {k : Nat} (ha : a.toNat < 256 ^ k) (hk : k ≤ 7)
    (hb : b.toNat < 256) : lowBytes (a * 256 + b) (k + 1) = lowBytes a k ++ [b] := by
  have hp : 256 ^ k ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) hk
  have e : (a * 256 + b).toNat = a.toNat * 256 + b.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat, Nat.reducePow] at *
    omega
  have e1 : (a * 256 + b) / 256 = a := UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_div, e]
    simp only [UInt64.reduceToNat]
    omega)
  have e2 : (a * 256 + b) % 256 = b := UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_mod, e]
    simp only [UInt64.reduceToNat]
    omega)
  rw [lowBytes, e1, e2]

theorem wordBytes_lowBytes (w : UInt64) : wordBytes w 8 = lowBytes w 8 := by
  have hw := w.toNat_lt
  simp only [wordBytes, lowBytes, List.nil_append, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt64.toNat_inj.mp <;>
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_div,
      UInt64.toNat_mod, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Nat.reducePow] at * <;> omega

theorem length_wordBytes (w : UInt64) (k : Nat) : (wordBytes w k).length = k := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => simp [wordBytes, ih]

theorem length_recordBytes (ws : List UInt64) : (recordBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [recordBytes_cons, List.length_append, length_wordBytes, ih, List.length_cons]
      omega

theorem length_flatMap_recordBytes {kin : Nat} :
    ∀ {recs : List (List UInt64)}, (∀ r ∈ recs, r.length = kin) →
      (recs.flatMap recordBytes).length = 8 * kin * recs.length
  | [], _ => rfl
  | r :: rs, h => by
      rw [List.flatMap_cons, List.length_append, length_recordBytes, h r (by simp),
        length_flatMap_recordBytes fun x hx => h x (by simp [hx]), List.length_cons]
      rw [Nat.mul_succ]
      omega

/-- The bytes that the decoder's state `d` holds after the bytes `bs`: those of the complete
records, of the words of the current record, and of the current word, each most significant
first. -/
def DecodeBytes (d : Decoded) (bs : List UInt64) : Prop :=
  d.nbyte ≤ 7 ∧ d.acc.toNat < 256 ^ d.nbyte ∧
    bs = d.recs.flatMap recordBytes ++ d.words.flatMap (fun w => wordBytes w 8) ++
      lowBytes d.acc d.nbyte

theorem decodeByte_bytes {kin : Nat} {d : Decoded} {bs : List UInt64} (h : DecodeBytes d bs)
    {b : UInt64} (hb : b.toNat < 256) : DecodeBytes (decodeByte kin d b) (bs ++ [b]) := by
  obtain ⟨h7, ha, e⟩ := h
  unfold decodeByte
  split
  · have hp : 256 ^ d.nbyte * 256 = 256 ^ (d.nbyte + 1) := (Nat.pow_succ ..).symm
    refine ⟨by simp only; omega, ?_, ?_⟩
    · have hp7 : 256 ^ d.nbyte ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) h7
      show (d.acc * 256 + b).toNat < 256 ^ (d.nbyte + 1)
      rw [UInt64.toNat_add, UInt64.toNat_mul]
      simp only [UInt64.reduceToNat, Nat.reducePow] at *
      omega
    · show bs ++ [b] = _ ++ _ ++ lowBytes (d.acc * 256 + b) (d.nbyte + 1)
      rw [lowBytes_push ha h7 hb, e, List.append_assoc _ (lowBytes d.acc d.nbyte)]
  · have h7' : d.nbyte = 7 := by omega
    rw [h7'] at ha
    have hw : wordBytes (d.acc * 256 + b) 8 = lowBytes d.acc 7 ++ [b] := by
      rw [wordBytes_lowBytes, lowBytes_push ha (Nat.le_refl _) hb]
    split
    · refine ⟨by simp only; omega, by simp only [UInt64.reduceToNat]; omega, ?_⟩
      show bs ++ [b] = _ ++ (d.words ++ [d.acc * 256 + b]).flatMap _ ++ lowBytes 0 0
      rw [e, h7', List.flatMap_append, List.flatMap_singleton, hw]
      simp only [lowBytes, List.append_nil, List.append_assoc]
    · refine ⟨by simp only; omega, by simp only [UInt64.reduceToNat]; omega, ?_⟩
      show bs ++ [b] = (d.recs ++ [d.words ++ [d.acc * 256 + b]]).flatMap recordBytes ++
        ([] : List UInt64).flatMap _ ++ lowBytes 0 0
      rw [e, h7', List.flatMap_append, List.flatMap_singleton, recordBytes, List.flatMap_append,
        List.flatMap_singleton, hw]
      simp only [lowBytes, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem foldl_decodeByte_bytes {kin : Nat} :
    ∀ (bs : List UInt64) (d : Decoded) (pre : List UInt64), DecodeBytes d pre →
      (∀ b ∈ bs, b.toNat < 256) → DecodeBytes (bs.foldl (decodeByte kin) d) (pre ++ bs)
  | [], _, pre, h, _ => by rw [List.append_nil]; exact h
  | b :: bs, d, pre, h, hb => by
      rw [List.foldl_cons, show pre ++ b :: bs = pre ++ [b] ++ bs by simp]
      exact foldl_decodeByte_bytes bs _ _ (decodeByte_bytes h (hb b (by simp)))
        fun x hx => hb x (by simp [hx])

theorem decode_bytes (kin : Nat) {bs : List UInt64} (hb : ∀ b ∈ bs, b.toNat < 256) :
    DecodeBytes (decode kin bs) bs := by
  have h := foldl_decodeByte_bytes (kin := kin) bs ⟨[], [], 0, 0⟩ [] ⟨by simp, by simp, rfl⟩ hb
  rw [List.nil_append] at h
  exact h

/-- The number of records that the bytes `bs` encode. -/
theorem decode_length {kin : Nat} (hkin : 0 < kin) (bs : List UInt64) :
    (decode kin bs).recs.length = bs.length / (8 * kin) := by
  obtain ⟨-, hw, hn, hlen⟩ := decode_lengths hkin bs
  have hr : (decode kin bs).words.length * 8 + (decode kin bs).nbyte < 8 * kin := by omega
  rw [← hlen, Nat.mul_comm _ (8 * kin), Nat.add_assoc, Nat.add_comm,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]

/-- The bytes of the first `i` records that the bytes `bs` encode are the first `8 kin i` bytes of
`bs`. -/
theorem decode_take {kin : Nat} (hkin : 0 < kin) {bs : List UInt64}
    (hb : ∀ b ∈ bs, b.toNat < 256) {i : Nat} (hi : i ≤ (decode kin bs).recs.length) :
    ((decode kin bs).recs.take i).flatMap recordBytes = bs.take (8 * kin * i) := by
  obtain ⟨-, -, e⟩ := decode_bytes kin hb
  obtain ⟨h8, -⟩ := decode_lengths hkin bs
  generalize decode kin bs = d at e h8 hi
  subst e
  have hl : ((d.recs.take i).flatMap recordBytes).length = 8 * kin * i := by
    rw [length_flatMap_recordBytes fun r hr => h8 r (List.mem_of_mem_take hr), List.length_take,
      Nat.min_eq_left hi]
  calc (d.recs.take i).flatMap recordBytes
      = ((d.recs.take i).flatMap recordBytes ++ ((d.recs.drop i).flatMap recordBytes ++
          d.words.flatMap (fun w => wordBytes w 8) ++ lowBytes d.acc d.nbyte)).take
          (8 * kin * i) := (List.take_left' hl).symm
    _ = _ := by
      rw [← List.append_assoc, ← List.append_assoc, ← List.flatMap_append, List.take_append_drop]

/-- The records that the bytes `bs` encode are records of `kin` words whose bytes are those of `bs`
up to its last complete record. -/
theorem decode_recs {kin : Nat} (hkin : 0 < kin) {bs : List UInt64}
    (hb : ∀ b ∈ bs, b.toNat < 256) :
    (∀ r ∈ (decode kin bs).recs, r.length = kin) ∧
      (decode kin bs).recs.flatMap recordBytes = bs.take (8 * kin * (bs.length / (8 * kin))) := by
  refine ⟨(decode_lengths hkin bs).1, ?_⟩
  have h := decode_take hkin hb (Nat.le_refl _)
  rwa [List.take_length, decode_length hkin] at h

/-- The value of the `k` low bytes of `a`, read most significant first. -/
theorem lowBytes_value (a : UInt64) (k : Nat) :
    (lowBytes a k).foldl (fun n b => n * 256 + b.toNat) 0 = a.toNat % 256 ^ k := by
  induction k generalizing a with
  | zero => simp [lowBytes, Nat.mod_one]
  | succ k ih =>
      rw [lowBytes, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, UInt64.toNat_div,
        UInt64.toNat_mod, Nat.pow_succ', Nat.mod_mul]
      simp only [UInt64.reduceToNat]
      omega

theorem wordBytes_inj {w w' : UInt64} (h : wordBytes w 8 = wordBytes w' 8) : w = w' := by
  rw [wordBytes_lowBytes, wordBytes_lowBytes] at h
  have e := congrArg (fun l => l.foldl (fun n b => n * 256 + b.toNat) 0) h
  simp only [lowBytes_value, Nat.reducePow] at e
  apply UInt64.toNat_inj.mp
  rwa [Nat.mod_eq_of_lt w.toNat_lt, Nat.mod_eq_of_lt w'.toNat_lt] at e

theorem recordBytes_inj : ∀ {ws ws' : List UInt64}, ws.length = ws'.length →
    recordBytes ws = recordBytes ws' → ws = ws'
  | [], [], _, _ => rfl
  | w :: ws, w' :: ws', hl, h => by
      rw [recordBytes_cons, recordBytes_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_wordBytes, length_wordBytes])
      rw [wordBytes_inj h1, recordBytes_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-- Records of `kin` words are determined by their bytes. -/
theorem flatMap_recordBytes_inj {kin : Nat} (hkin : 0 < kin) {recs recs' : List (List UInt64)}
    (h : ∀ r ∈ recs, r.length = kin) (h' : ∀ r ∈ recs', r.length = kin)
    (e : recs.flatMap recordBytes = recs'.flatMap recordBytes) : recs = recs' := by
  have hl : recs.length = recs'.length := by
    have := congrArg List.length e
    rw [length_flatMap_recordBytes h, length_flatMap_recordBytes h'] at this
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  induction recs generalizing recs' with
  | nil => exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons r rs ih =>
      obtain _ | ⟨r', rs'⟩ := recs'
      · simp at hl
      · rw [List.flatMap_cons, List.flatMap_cons] at e
        have hr := h r (by simp)
        have hr' := h' r' (by simp)
        obtain ⟨e1, e2⟩ := List.append_inj e
          (by rw [length_recordBytes, length_recordBytes, hr, hr'])
        rw [recordBytes_inj (hr.trans hr'.symm) e1, ih (fun x hx => h x (by simp [hx]))
          (fun x hx => h' x (by simp [hx])) e2 (by simpa using hl)]

/-- Every byte that a trace reads from the receive register is below 256. -/
theorem dataIn_lt {α : Type} (B : Bus α) (u : Uart) (tr : List α) :
    ∀ b ∈ dataIn B u tr, b.toNat < 256 := by
  intro b hb
  simp only [dataIn, List.mem_filterMap, dataInByte, Option.map_eq_some_iff] at hb
  obtain ⟨e, -, v, -, rfl⟩ := hb
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end LeanExe.Requests
