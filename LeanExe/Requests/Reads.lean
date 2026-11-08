import LeanExe.Requests.Records

/-!
The rate of the framing's reads of the receive register and the lengths of the records that the
bytes encode.  `frameTick` reads the receive register only in phase 0, after a status read that
shows a byte, and the window after that read reads the status again, so no two consecutive windows
read a byte and the first window reads none.  `frame_reads` states that the first `n` windows read
at most `n / 2` bytes, and `decode_lengths` that each record that bytes encode has `kin` words and
takes `8 kin` of the bytes, which together bound the records that a step with records receives in
a number of windows.
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

end LeanExe.Requests
