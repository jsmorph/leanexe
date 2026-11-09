import Demos.Bms.Spec
import Library.Hashing.Crc.Proof

/-!
Theorems M1 to M12 of the BMS requirements about the machine of `Demos/Bms/Spec.lean`, each for
every sequence `x` of segment results from the state after a board reset, or from every state
where the requirement says so.  `m1` is the main safety theorem: an answer with a nonzero permit
answers a record that passed every check, and the states before it followed the transitions from
the last reset acceptance through the last start, as `Permitted` states over the segments and the
answers alone.

The proofs relate the machine's state before segment `t` to the history terms of the
specification: `synced_eq`, `expected_eq`, `prevReset_eq`, `age_eq`, and `permitInForce_eq`, and
with them `failure_eq`, by which the machine's checks of segment `t` are the checks that the
history defines.  `resetAcceptance_iff` and `start_iff` identify a reset acceptance and a start
with the transitions from `RESET_REQUIRED` or `FAULT` to `STANDBY` and from `STANDBY` to
`PRECHARGE`.  `pc_run` counts the precharge records after a start.  M1 then follows from the
last segment up to `n` whose state is `RESET_REQUIRED` or `FAULT` and the last whose state is
`STANDBY`, which `exists_last` gives.
-/

namespace Demos.Bms.Spec

open Library.Hashing.Crc.Division (crc32Eval bitsValue)

/-! ## Bytes -/

theorem foldl_beValue (a : Nat) (bs : List UInt8) :
    bs.foldl (fun v b => 256 * v + b.toNat) a = a * 256 ^ bs.length + beValue bs := by
  induction bs generalizing a with
  | nil => simp [beValue]
  | cons b bs ih =>
    have e : beValue (b :: bs) = (256 * 0 + b.toNat) * 256 ^ bs.length + beValue bs := ih _
    rw [List.foldl_cons, ih, e, List.length_cons, pow_succ]
    ring

theorem beValue_append (A B : List UInt8) :
    beValue (A ++ B) = beValue A * 256 ^ B.length + beValue B := by
  rw [beValue, List.foldl_append, foldl_beValue]
  rfl

theorem beValue_lt (bs : List UInt8) : beValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [beValue]
  | cons b bs ih =>
    have e : beValue (b :: bs) = b.toNat * 256 ^ bs.length + beValue bs := by
      have h : beValue (b :: bs) = (256 * 0 + b.toNat) * 256 ^ bs.length + beValue bs :=
        foldl_beValue _ bs
      rw [h, Nat.mul_zero, Nat.zero_add]
    have hb := b.toNat_lt
    rw [e, List.length_cons, pow_succ]
    have : b.toNat * 256 ^ bs.length + 256 ^ bs.length ≤ 256 ^ bs.length * 256 := by
      have := Nat.mul_le_mul_right (256 ^ bs.length) (show b.toNat + 1 ≤ 256 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      linarith
    omega

@[simp] theorem length_beBytes (k n : Nat) : (beBytes k n).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [beBytes, ih]

theorem beValue_beBytes (k n : Nat) : beValue (beBytes k n) = n % 256 ^ k := by
  induction k with
  | zero => simp [beBytes, beValue, Nat.mod_one]
  | succ k ih =>
    rw [beBytes, show UInt8.ofNat (n / 256 ^ k) :: beBytes k n =
      [UInt8.ofNat (n / 256 ^ k)] ++ beBytes k n from rfl, beValue_append, ih, length_beBytes]
    have e : beValue [UInt8.ofNat (n / 256 ^ k)] = n / 256 ^ k % 256 := by
      simp [beValue]
    rw [e, pow_succ, Nat.mod_mul]
    ring

theorem field_lt (raw : List UInt8) (off len : Nat) : field raw off len < 256 ^ len :=
  lt_of_lt_of_le (beValue_lt _) (Nat.pow_le_pow_right (by decide) (by simp))

theorem field_append_of_le {A B : List UInt8} {off len : Nat} (h : A.length ≤ off) :
    field (A ++ B) off len = field B (off - A.length) len := by
  simp [field, List.drop_append, List.drop_eq_nil_of_le h]

theorem field_append_of_ge {A B : List UInt8} {off len : Nat} (h : off + len ≤ A.length) :
    field (A ++ B) off len = field A off len := by
  rw [field, field, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

theorem field_beBytes (k n : Nat) : field (beBytes k n) 0 k = n % 256 ^ k := by
  rw [field, List.drop_zero, List.take_of_length_le (by simp), beValue_beBytes]

/-! ## Checks -/

theorem firstFailure_eq_none {cs : List (Bool × Nat)} :
    firstFailure cs = none ↔ ∀ c ∈ cs, c.1 = false := by
  simp [firstFailure]

theorem firstFailure_mem {cs : List (Bool × Nat)} {c : Nat} (h : firstFailure cs = some c) :
    c ∈ cs.map (·.2) := by
  simp only [firstFailure, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact List.mem_map.mpr ⟨a, List.mem_of_find?_eq_some ha, rfl⟩

theorem checks_none_iff {synced : Bool} {expected permit : Nat} {age : List Nat} {x : Input} :
    firstFailure (checks synced expected permit age x) = none ↔
      good x = true ∧ seqFault synced expected (scanOf x) = false ∧
        firstFailure (contentChecks permit age (scanOf x)) = none := by
  simp only [checks, firstFailure_eq_none, List.mem_append, List.mem_cons, good, List.all_eq_true,
    Bool.not_eq_true']
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), h _ (Or.inr (Or.inl rfl)), fun c hc => h c (Or.inr (Or.inr hc))⟩
  · rintro ⟨h1, h2, h3⟩ c (hc | rfl | hc)
    · exact h1 c hc
    · exact h2
    · exact h3 c hc

theorem passesComm_eq (x : Nat → Input) (t : Nat) :
    passesComm x t = passesCommWith (syncedAt x t) (expectedAt x t) (x t) := by
  cases t with
  | zero => simp [passesComm, passesCommWith, syncedAt, seqFault]
  | succ t =>
    cases h : good (x t) <;> simp [passesComm, passesCommWith, syncedAt, expectedAt, seqFault, h, bne]

theorem passesComm_of_failureAt {x : Nat → Input} {t : Nat} (h : failureAt x t = none) :
    passesComm x t = true := by
  obtain ⟨h1, h2, -⟩ := checks_none_iff.mp h
  simp [passesComm_eq, passesCommWith, h1, h2]

theorem good_of_failureAt {x : Nat → Input} {t : Nat} (h : failureAt x t = none) :
    good (x t) = true :=
  (checks_none_iff.mp h).1

theorem contentFailureAt_of_failureAt {x : Nat → Input} {t : Nat} (h : failureAt x t = none) :
    contentFailureAt x t = none :=
  (checks_none_iff.mp h).2.2

theorem auxFault_true_of {permit : Nat} {age : List Nat} {sc : Scan}
    (h : auxFault permit age sc = true) {synced : Bool} {expected : Nat} {x : Input}
    (hx : scanOf x = sc) : firstFailure (checks synced expected permit age x) ≠ none := by
  intro h0
  have := (checks_none_iff.mp h0).2.2
  rw [firstFailure_eq_none] at this
  have := this (auxFault permit age (scanOf x), codeAux) (by simp [contentChecks])
  rw [hx, h] at this
  exact absurd this (by decide)

theorem checks_codes (synced : Bool) (expected permit : Nat) (age : List Nat) (x : Input) :
    (checks synced expected permit age x).map (·.2) =
      [codeDecode, codeOverflow, codeLength, codeCrc, codeTag, codeSeq, codeReserved, codeSensor,
        codeOverVoltage, codeUnderVoltage, codeOverTemp, codeUnderTemp, codeChargeCurrent,
        codeDischargeCurrent, codeChargeTemp, codeSum, codeAux] := rfl

theorem failure_lt {s : State} {x : Input} {c : Nat} (h : failure s x = some c) : c < 2 ^ 16 := by
  have := firstFailure_mem h
  rw [checks_codes] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (subst h; decide)

/-! ## One step -/

section Step

variable {s : State} {x : Input}

theorem next_failure {c : Nat} (h : failure s x = some c) :
    next s x = ⟨.fault, if s.mode = .fault then s.diag else c, s.pcCount⟩ := by
  simp [next, h]

theorem next_pass (h : failure s x = none) :
    next s x = if (scanOf x).stopOk then rule5 s (scanOf x) else rule4 s := by
  simp [next, h]

/-- A step whose next state is neither `RESET_REQUIRED` nor `FAULT` passes every check with
`STOP_OK` 1, from such a state or by a reset acceptance to `STANDBY`. -/
theorem next_active (h1 : (next s x).mode ≠ .resetRequired) (h2 : (next s x).mode ≠ .fault) :
    failure s x = none ∧ (scanOf x).stopOk = true ∧
      ((s.mode ≠ .resetRequired ∧ s.mode ≠ .fault) ∨
        (acceptanceWith s.synced s.prevReset (scanOf x) = true ∧
          (next s x).mode = .standby)) := by
  cases hf : failure s x with
  | some c => rw [next_failure hf] at h2; exact absurd rfl h2
  | none =>
    rw [next_pass hf] at h1 h2 ⊢
    cases hst : (scanOf x).stopOk
    · simp only [hst, Bool.false_eq_true, ↓reduceIte] at h1 h2
      cases hm : s.mode <;> simp [rule4, hm] at h1 h2
    · simp only [↓reduceIte, true_and]
      cases hm : s.mode <;> simp only [rule5, hm] at h1 h2 ⊢ <;> split_ifs at h1 h2 ⊢ <;> simp_all

/-- From `RESET_REQUIRED` or `FAULT`, the next state is `STANDBY` exactly for a record that passes
every check with `STOP_OK` 1 and meets the conditions of a reset acceptance, and it is never
`PRECHARGE` or `NORMAL`. -/
theorem next_inactive (hm : s.mode = .resetRequired ∨ s.mode = .fault) :
    ((next s x).mode = .standby ↔ failure s x = none ∧ (scanOf x).stopOk = true ∧
      acceptanceWith s.synced s.prevReset (scanOf x) = true) ∧
    (next s x).mode ≠ .precharge ∧ (next s x).mode ≠ .normal := by
  cases hf : failure s x with
  | some c => rw [next_failure hf]; simp
  | none =>
    rw [next_pass hf]
    cases hst : (scanOf x).stopOk
    · rcases hm with hm | hm <;> simp [rule4, hm]
    · simp only [↓reduceIte]
      rcases hm with hm | hm <;> simp only [rule5, hm] <;> split_ifs <;> simp_all

/-- From `STANDBY`, the next state is `PRECHARGE` exactly for a start, with the precharge count 0,
and it is never `NORMAL`. -/
theorem next_standby (hm : s.mode = .standby) :
    ((next s x).mode = .precharge ↔ failure s x = none ∧ (scanOf x).stopOk = true ∧
      startCondition (scanOf x) = true) ∧
    ((next s x).mode = .precharge → (next s x).pcCount = 0) ∧ (next s x).mode ≠ .normal := by
  cases hf : failure s x with
  | some c => rw [next_failure hf]; simp
  | none =>
    rw [next_pass hf]
    cases hst : (scanOf x).stopOk
    · simp [rule4, hm]
    · simp only [↓reduceIte, rule5, hm]
      split_ifs <;> simp_all

/-- From `PRECHARGE`, a next state of `PRECHARGE` needs `RUN` 1 and raises the precharge count,
which stays below `N_pc`, and a next state of `NORMAL` needs `RUN` 1 and the precharge
condition. -/
theorem next_precharge (hm : s.mode = .precharge) :
    ((next s x).mode = .precharge → (scanOf x).run = true ∧
      (next s x).pcCount = s.pcCount + 1 ∧ s.pcCount + 1 < nPc) ∧
    ((next s x).mode = .normal → (scanOf x).run = true ∧
      prechargeCondition (scanOf x) = true) := by
  cases hf : failure s x with
  | some c => rw [next_failure hf]; simp
  | none =>
    rw [next_pass hf]
    cases hst : (scanOf x).stopOk
    · simp [rule4, hm]
    · simp only [↓reduceIte, rule5, hm]
      split_ifs <;> simp_all

/-- From `NORMAL`, the next state is never `PRECHARGE`, and a next state of `NORMAL` needs
`RUN` 1. -/
theorem next_normal (hm : s.mode = .normal) :
    (next s x).mode ≠ .precharge ∧ ((next s x).mode = .normal → (scanOf x).run = true) := by
  cases hf : failure s x with
  | some c => rw [next_failure hf]; simp
  | none =>
    rw [next_pass hf]
    cases hst : (scanOf x).stopOk
    · simp [rule4, hm]
    · simp only [↓reduceIte, rule5, hm]
      split_ifs <;> simp_all

/-- From `FAULT`, the next state is `FAULT` with the same code, or `STANDBY`. -/
theorem next_fault (hm : s.mode = .fault) :
    ((next s x).mode = .fault ∧ (next s x).diag = s.diag) ∨ (next s x).mode = .standby := by
  cases hf : failure s x with
  | some c => rw [next_failure hf]; simp [hm]
  | none =>
    rw [next_pass hf]
    cases hst : (scanOf x).stopOk
    · simp [rule4, hm]
    · simp only [↓reduceIte, rule5, hm]
      split_ifs <;> simp_all

/-- A record that passes every check with `STOP_OK` 0 leads to `RESET_REQUIRED` or keeps
`FAULT`. -/
theorem next_stop (hf : failure s x = none) (hst : (scanOf x).stopOk = false) :
    (next s x).mode = .resetRequired ∨ (next s x).mode = .fault := by
  rw [next_pass hf, hst]
  cases hm : s.mode <;> simp [rule4, hm]

/-- A record that passes every check with `STOP_OK` 1 and `RUN` 0 leads from `PRECHARGE` or
`NORMAL` to `STANDBY`. -/
theorem next_standbyRequest (hf : failure s x = none) (hst : (scanOf x).stopOk = true)
    (hr : (scanOf x).run = false) (hm : s.mode = .precharge ∨ s.mode = .normal) :
    (next s x).mode = .standby := by
  rw [next_pass hf, hst]
  rcases hm with hm | hm <;> simp [rule5, hm, hr]

end Step

/-! ## Runs -/

theorem lastBefore_succ (p : Nat → Bool) (t : Nat) :
    lastBefore p (t + 1) = if p t then some t else lastBefore p t := rfl

/-- `lastBefore p t` is the last segment before `t` at which `p` holds. -/
theorem lastBefore_spec {p : Nat → Bool} {t u : Nat} (h : lastBefore p t = some u) :
    u < t ∧ p u = true ∧ ∀ v, u < v → v < t → p v = false := by
  induction t with
  | zero => simp [lastBefore] at h
  | succ t ih =>
    rw [lastBefore_succ] at h
    split at h
    · next hp =>
      cases h
      exact ⟨by omega, hp, fun v h1 h2 => by omega⟩
    · next hp =>
      obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨by omega, h2, fun v hv1 hv2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv2 with hv | hv
      · exact h3 v hv1 hv
      · subst hv
        simpa using hp

theorem lastBefore_some {p : Nat → Bool} (h0 : p 0 = true) :
    ∀ {t : Nat}, 0 < t → ∃ u, lastBefore p t = some u
  | t + 1, _ => by
    rw [lastBefore_succ]
    split
    · exact ⟨t, rfl⟩
    · next hp =>
      cases t with
      | zero => exact absurd h0 (by simpa using hp)
      | succ t => exact lastBefore_some h0 (Nat.succ_pos t)

/-- If `p` holds at `w`, a last segment from `w` to `n` at which `p` holds exists. -/
theorem exists_last (p : Nat → Prop) [DecidablePred p] {w n : Nat} (hw : p w) (hwn : w ≤ n) :
    ∃ i, w ≤ i ∧ i ≤ n ∧ p i ∧ ∀ t, i < t → t ≤ n → ¬p t := by
  induction n with
  | zero => exact ⟨w, le_refl _, hwn, hw, fun t h1 h2 => by omega⟩
  | succ n ih =>
    by_cases hp : p (n + 1)
    · exact ⟨n + 1, hwn, le_refl _, hp, fun t h1 h2 => by omega⟩
    · rcases Nat.lt_or_ge w (n + 1) with h | h
      · obtain ⟨i, h1, h2, h3, h4⟩ := ih (by omega)
        refine ⟨i, h1, by omega, h3, fun t ht1 ht2 => ?_⟩
        rcases Nat.lt_or_ge t (n + 1) with h' | h'
        · exact h4 t ht1 (by omega)
        · have : t = n + 1 := by omega
          subst this
          exact hp
      · have : w = n + 1 := by omega
        subst this
        exact absurd hw hp

/-- If `p` holds at `b ≥ a`, a first segment from `a` to `b` at which `p` holds exists. -/
theorem exists_first (p : Nat → Prop) [DecidablePred p] {a b : Nat} (hb : p b) (hab : a ≤ b) :
    ∃ k, a ≤ k ∧ k ≤ b ∧ p k ∧ ∀ t, a ≤ t → t < k → ¬p t := by
  have h : ∃ k, a ≤ k ∧ p k := ⟨b, hab, hb⟩
  exact ⟨Nat.find h, (Nat.find_spec h).1, Nat.find_min' h ⟨hab, hb⟩, (Nat.find_spec h).2,
    fun t h1 h2 hp => Nat.find_min h h2 ⟨h1, hp⟩⟩

section Run

variable (x : Nat → Input)

@[simp] theorem stateAt_zero : stateAt x 0 = init := rfl

theorem stateAt_succ (t : Nat) : stateAt x (t + 1) = (step (stateAt x t) (x t)).1 := rfl

theorem answerAt_eq (t : Nat) : answerAt x t = (step (stateAt x t) (x t)).2 := rfl

theorem mode_succ (t : Nat) : (stateAt x (t + 1)).mode = (next (stateAt x t) (x t)).mode := rfl

theorem answerAt_state (t : Nat) : (answerAt x t).state = (stateAt x (t + 1)).mode := rfl

theorem answerAt_permit (t : Nat) : (answerAt x t).permit = (stateAt x (t + 1)).mode.permit := rfl

theorem answerAt_code (t : Nat) : (answerAt x t).code = (stateAt x (t + 1)).diag := rfl

theorem stateBefore_eq (t : Nat) : stateBefore x t = (stateAt x t).mode := by
  cases t with
  | zero => rfl
  | succ t => simp [stateBefore, answerAt_state]

theorem permitInForce_eq (t : Nat) : permitInForce x t = (stateAt x t).mode.permit := by
  cases t with
  | zero => rfl
  | succ t => simp [permitInForce, answerAt_permit]

theorem synced_eq (t : Nat) : (stateAt x t).synced = syncedAt x t := by
  cases t with
  | zero => rfl
  | succ t => simp [stateAt_succ, step, syncedAt]

theorem expected_eq (t : Nat) (h : (stateAt x t).synced = true) :
    (stateAt x t).expected = expectedAt x t := by
  cases t with
  | zero => simp [init] at h
  | succ t =>
    simp only [stateAt_succ, step] at h ⊢
    simp [h, expectedAt]

theorem first_eq (t : Nat) : (stateAt x t).first = (t == 0) := by
  cases t <;> rfl

theorem comm_eq (t : Nat) :
    passesCommWith (stateAt x t).synced (stateAt x t).expected (x t) = passesComm x t := by
  rw [passesComm_eq]
  by_cases h : (stateAt x t).synced = true
  · rw [expected_eq x t h, synced_eq]
  · have h' : (stateAt x t).synced = false := by simpa using h
    have h'' : syncedAt x t = false := by rw [← synced_eq]; exact h'
    simp [passesCommWith, seqFault, h', h'']

theorem prevResetAt_succ (t : Nat) :
    prevResetAt x (t + 1) =
      if passesComm x t then (scanOf (x t)).reset else prevResetAt x t := by
  unfold prevResetAt
  rw [lastBefore_succ]
  cases passesComm x t <;> simp

theorem prevReset_eq (t : Nat) : (stateAt x t).prevReset = prevResetAt x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [prevResetAt_succ, ← ih, ← comm_eq]
    rfl

theorem ageAt_succ (r t : Nat) :
    ageAt x r (t + 1) =
      if changedAt x r t then 0 else ageAt x r t + (if passesComm x t then 1 else 0) := by
  unfold ageAt
  simp only [Nat.add_one_ne_zero, ↓reduceIte, lastBefore_succ]
  by_cases hc : changedAt x r t = true
  · simp only [hc, ↓reduceIte, Option.getD_some]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro u hu
    simp only [List.mem_range] at hu
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h
    omega
  · have hc' : changedAt x r t = false := by simpa using hc
    have ht : t ≠ 0 := by
      intro h
      subst h
      simp [changedAt] at hc'
    obtain ⟨u, hu⟩ := lastBefore_some (p := changedAt x r) (by simp [changedAt])
      (Nat.pos_of_ne_zero ht)
    have hut := (lastBefore_spec hu).1
    simp only [hc', hu, Option.getD_some, ht, Bool.false_eq_true, ↓reduceIte]
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hp : passesComm x t = true
    · simp [hut, hp]
    · simp [hp]

theorem changedAt_eq (r t : Nat) :
    ((stateAt x t).first ||
      (next (stateAt x t) (x t)).mode.permit.testBit r !=
        (stateAt x t).mode.permit.testBit r) = changedAt x r t := by
  cases t <;> rfl

theorem age_eq (t : Nat) :
    (stateAt x t).age = (List.range 3).map fun r => min (ageAt x r t) dEdm := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [stateAt_succ]
    simp only [step]
    apply List.map_congr_left
    intro r hr
    have hr3 : r < 3 := List.mem_range.mp hr
    have hget : (stateAt x t).age.getD r 0 = min (ageAt x r t) dEdm := by
      rw [ih]
      simp [hr3]
    rw [ageAt_succ, changedAt_eq, hget, comm_eq]
    cases changedAt x r t <;> cases passesComm x t <;> simp; omega

theorem agesAt_getD (t r : Nat) (hr : r < 3) : (agesAt x t).getD r 0 = ageAt x r t := by
  simp [agesAt, hr]

theorem auxFault_congr {permit : Nat} {a b : List Nat} {sc : Scan}
    (h : ∀ r < 3, (dEdm ≤ a.getD r 0 ↔ dEdm ≤ b.getD r 0)) :
    auxFault permit a sc = auxFault permit b sc := by
  unfold auxFault
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro ⟨r, hr, h1, h2⟩ <;> exact ⟨r, hr, h1, by have := h r hr; tauto⟩

/-- The machine's checks of segment `t` are the checks that the history defines. -/
theorem failure_eq (t : Nat) : failure (stateAt x t) (x t) = failureAt x t := by
  unfold failure failureAt
  have hseq : seqFault (stateAt x t).synced (stateAt x t).expected (scanOf (x t)) =
      seqFault (syncedAt x t) (expectedAt x t) (scanOf (x t)) := by
    by_cases h : (stateAt x t).synced = true
    · rw [expected_eq x t h, synced_eq]
    · have h' : (stateAt x t).synced = false := by simpa using h
      rw [h', ← synced_eq, h']
      rfl
  have haux : auxFault (stateAt x t).mode.permit (stateAt x t).age (scanOf (x t)) =
      auxFault (stateAt x t).mode.permit (agesAt x t) (scanOf (x t)) := by
    apply auxFault_congr
    intro r hr
    rw [age_eq, agesAt_getD x t r hr]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr,
      Option.map_some, Option.getD_some]
    omega
  simp only [checks, contentChecks, hseq, haux, permitInForce_eq]

theorem resetAcceptance_spec {t : Nat} (h : resetAcceptance x t = true) :
    failureAt x t = none ∧ (scanOf (x t)).stopOk = true ∧
      (stateBefore x t = .resetRequired ∨ stateBefore x t = .fault) ∧
      acceptanceWith (syncedAt x t) (prevResetAt x t) (scanOf (x t)) = true := by
  simp only [resetAcceptance, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true,
    beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem acceptanceWith_spec {synced prevReset : Bool} {sc : Scan}
    (h : acceptanceWith synced prevReset sc = true) :
    synced = true ∧ prevReset = false ∧ sc.reset = true ∧ sc.run = false ∧ sc.auxWord = 0 := by
  simp only [acceptanceWith, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem start_spec {t : Nat} (h : start x t = true) :
    failureAt x t = none ∧ (scanOf (x t)).stopOk = true ∧ stateBefore x t = .standby ∧
      (scanOf (x t)).run = true ∧ (scanOf (x t)).auxWord = 0 := by
  simp only [start, startCondition, Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1, h.2.2⟩

/-- A reset acceptance is exactly a transition from `RESET_REQUIRED` or `FAULT` to `STANDBY`. -/
theorem resetAcceptance_iff (t : Nat) :
    resetAcceptance x t = true ↔
      ((stateAt x t).mode = .resetRequired ∨ (stateAt x t).mode = .fault) ∧
        (stateAt x (t + 1)).mode = .standby := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := resetAcceptance_spec x h
    rw [stateBefore_eq] at h3
    refine ⟨h3, ?_⟩
    rw [mode_succ, (next_inactive h3).1, failure_eq, synced_eq, prevReset_eq]
    exact ⟨h1, h2, h4⟩
  · rintro ⟨h3, h5⟩
    rw [mode_succ, (next_inactive h3).1, failure_eq, synced_eq, prevReset_eq] at h5
    obtain ⟨h1, h2, h4⟩ := h5
    rw [← stateBefore_eq] at h3
    simp only [resetAcceptance, h1, h2, h4, Option.isNone_none, Bool.and_true, Bool.true_and]
    rcases h3 with h3 | h3 <;> simp [h3]

/-- A start is exactly a transition from `STANDBY` to `PRECHARGE`. -/
theorem start_iff (t : Nat) :
    start x t = true ↔
      (stateAt x t).mode = .standby ∧ (stateAt x (t + 1)).mode = .precharge := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5⟩ := start_spec x h
    rw [stateBefore_eq] at h3
    refine ⟨h3, ?_⟩
    rw [mode_succ, (next_standby h3).1, failure_eq]
    exact ⟨h1, h2, by simp [startCondition, h4, h5]⟩
  · rintro ⟨h3, h5⟩
    rw [mode_succ, (next_standby h3).1, failure_eq] at h5
    obtain ⟨h1, h2, h4⟩ := h5
    rw [← stateBefore_eq] at h3
    simp [start, h1, h2, h3, h4]

/-- An answer whose state is neither `RESET_REQUIRED` nor `FAULT` answers a record that passes
every check with `STOP_OK` 1, after such a state or by a reset acceptance to `STANDBY`. -/
theorem run_active (t : Nat) (h1 : (stateAt x (t + 1)).mode ≠ .resetRequired)
    (h2 : (stateAt x (t + 1)).mode ≠ .fault) :
    failureAt x t = none ∧ (scanOf (x t)).stopOk = true ∧
      (((stateAt x t).mode ≠ .resetRequired ∧ (stateAt x t).mode ≠ .fault) ∨
        (resetAcceptance x t = true ∧ (stateAt x (t + 1)).mode = .standby)) := by
  rw [mode_succ] at h1 h2
  obtain ⟨h3, h4, h5⟩ := next_active h1 h2
  rw [failure_eq] at h3
  refine ⟨h3, h4, ?_⟩
  rcases h5 with h5 | ⟨-, h6⟩
  · exact Or.inl h5
  · by_cases hm : (stateAt x t).mode = .resetRequired ∨ (stateAt x t).mode = .fault
    · exact Or.inr ⟨(resetAcceptance_iff x t).mpr ⟨hm, h6⟩, h6⟩
    · exact Or.inl (by tauto)

/-- A state of `PRECHARGE` follows `STANDBY` or `PRECHARGE`. -/
theorem run_into_precharge (t : Nat) (h : (stateAt x (t + 1)).mode = .precharge) :
    (stateAt x t).mode = .standby ∨ (stateAt x t).mode = .precharge := by
  rw [mode_succ] at h
  cases hm : (stateAt x t).mode with
  | resetRequired => exact absurd h (next_inactive (Or.inl hm)).2.1
  | fault => exact absurd h (next_inactive (Or.inr hm)).2.1
  | standby => exact Or.inl rfl
  | precharge => exact Or.inr rfl
  | normal => exact absurd h (next_normal hm).1

/-- Along consecutive answers in `PRECHARGE` after a start at `j`, the precharge count before
segment `j + d + 1` is `d`, and `d < N_pc`. -/
theorem pc_run {j : Nat} (hs : (stateAt x j).mode = .standby)
    (hp : (stateAt x (j + 1)).mode = .precharge) :
    ∀ d, (∀ t, j ≤ t → t ≤ j + d → (stateAt x (t + 1)).mode = .precharge) →
      (stateAt x (j + d + 1)).pcCount = d ∧ d < nPc
  | 0, _ => by
    rw [mode_succ] at hp
    exact ⟨(next_standby hs).2.1 hp, by decide⟩
  | d + 1, h => by
    obtain ⟨ih1, -⟩ := pc_run hs hp d fun t h1 h2 => h t h1 (by omega)
    have hP1 := h (j + d) (by omega) (by omega)
    have hP2 := h (j + d + 1) (by omega) (by omega)
    rw [mode_succ] at hP2
    obtain ⟨-, h3, h4⟩ := (next_precharge hP1).1 hP2
    refine ⟨?_, by omega⟩
    show (next (stateAt x (j + d + 1)) (x (j + d + 1))).pcCount = d + 1
    rw [h3, ih1]

theorem permit_ne_zero {m : Mode} (h : m.permit ≠ 0) : m = .precharge ∨ m = .normal := by
  cases m <;> simp_all [Mode.permit]

/-! ## M1 -/

/-- M1: if answer `a_n` has a nonzero permit, the last reset acceptance `i` and the last start
`j` at or before `n` exist, `1 ≤ i < j ≤ n`, and items 1 to 7 of `Permitted` hold. -/
theorem m1 (n : Nat) (h : (answerAt x n).permit ≠ 0) : ∃ i j, Permitted x n i j := by
  rw [answerAt_permit] at h
  have hn := permit_ne_zero h
  obtain ⟨i, -, hin1, hi, hlast⟩ := exists_last
    (fun t => (stateAt x t).mode = .resetRequired ∨ (stateAt x t).mode = .fault)
    (w := 0) (n := n + 1) (Or.inl rfl) (Nat.zero_le _)
  have hact : ∀ t, i < t → t ≤ n + 1 →
      (stateAt x t).mode ≠ .resetRequired ∧ (stateAt x t).mode ≠ .fault := fun t h1 h2 => by
    have := hlast t h1 h2
    exact ⟨fun e => this (Or.inl e), fun e => this (Or.inr e)⟩
  have hin : i ≤ n := by
    by_contra hc
    have : i = n + 1 := by omega
    subst this
    rcases hn with h1 | h1 <;> rcases hi with h2 | h2 <;> rw [h1] at h2 <;> exact absurd h2 (by decide)
  have hpass : ∀ t, i ≤ t → t ≤ n → failureAt x t = none ∧ (scanOf (x t)).stopOk = true :=
    fun t h1 h2 => by
      obtain ⟨a, b⟩ := hact (t + 1) (by omega) (by omega)
      obtain ⟨h3, h4, -⟩ := run_active x t a b
      exact ⟨h3, h4⟩
  have hacc : resetAcceptance x i = true ∧ (stateAt x (i + 1)).mode = .standby := by
    obtain ⟨a, b⟩ := hact (i + 1) (by omega) (by omega)
    obtain ⟨-, -, h5⟩ := run_active x i a b
    rcases h5 with ⟨h6, h7⟩ | h6
    · rcases hi with h8 | h8
      · exact absurd h8 h6
      · exact absurd h8 h7
    · exact h6
  obtain ⟨-, -, -, hacc'⟩ := resetAcceptance_spec x hacc.1
  obtain ⟨hsy, hpr, hre, hru, hau⟩ := acceptanceWith_spec hacc'
  have hi1 : 1 ≤ i := by
    by_contra hc
    have : i = 0 := by omega
    subst this
    simp [syncedAt] at hsy
  have hgood_prev : good (x (i - 1)) = true := by
    simp only [syncedAt, Bool.and_eq_true] at hsy
    exact hsy.2
  have hin' : i < n := by
    rcases Nat.lt_or_ge i n with h' | h'
    · exact h'
    · have : i = n := by omega
      subst this
      rcases hn with h1 | h1 <;> rw [hacc.2] at h1 <;> exact absurd h1 (by decide)
  obtain ⟨j, hij, hjn, hj, hjlast⟩ := exists_last (fun t => (stateAt x t).mode = .standby)
    (w := i + 1) (n := n) hacc.2 (by omega)
  have hPN : ∀ t, j < t → t ≤ n + 1 →
      (stateAt x t).mode = .precharge ∨ (stateAt x t).mode = .normal := fun t h1 h2 => by
    obtain ⟨a, b⟩ := hact t (by omega) h2
    have c : (stateAt x t).mode ≠ .standby := by
      rcases Nat.lt_or_ge t (n + 1) with h' | h'
      · exact hjlast t h1 (by omega)
      · have : t = n + 1 := by omega
        subst this
        rcases hn with h3 | h3 <;> rw [h3] <;> decide
    cases hm : (stateAt x t).mode <;> simp_all
  have hstart : (stateAt x (j + 1)).mode = .precharge := by
    rcases hPN (j + 1) (by omega) (by omega) with h' | h'
    · exact h'
    · rw [mode_succ] at h'
      exact absurd h' (next_standby hj).2.2
  have hstartj : start x j = true := (start_iff x j).mpr ⟨hj, hstart⟩
  obtain ⟨-, -, -, hrunj, hauxj⟩ := start_spec x hstartj
  have hrun : ∀ t, j ≤ t → t ≤ n → (scanOf (x t)).run = true := fun t h1 h2 => by
    rcases Nat.eq_or_lt_of_le h1 with h' | h'
    · subst h'
      exact hrunj
    · have hm := hPN t h' (by omega)
      have hm' := hPN (t + 1) (by omega) (by omega)
      rw [mode_succ] at hm'
      rcases hm with hm | hm
      · rcases hm' with hm' | hm'
        · exact ((next_precharge hm).1 hm').1
        · exact ((next_precharge hm).2 hm').1
      · rcases hm' with hm' | hm'
        · exact absurd hm' (next_normal hm).1
        · exact (next_normal hm).2 hm'
  have hNN : ∀ t, j < t → t ≤ n → (stateAt x t).mode = .normal →
      (stateAt x (t + 1)).mode = .normal := fun t h1 h2 hm => by
    rcases hPN (t + 1) (by omega) (by omega) with h' | h'
    · rw [mode_succ] at h'
      exact absurd h' (next_normal hm).1
    · exact h'
  refine ⟨i, j, ?_⟩
  exact {
    order := ⟨hi1, by omega, hjn⟩
    lastAcceptance := ⟨by omega, hacc.1, fun t h1 h2 => by
      cases hr : resetAcceptance x t
      · rfl
      · have h3 := ((resetAcceptance_iff x t).mp hr).1
        have h4 := hact t h1 (by omega)
        rcases h3 with h3 | h3
        · exact absurd h3 h4.1
        · exact absurd h3 h4.2⟩
    lastStart := ⟨hjn, hstartj, fun t h1 h2 => by
      cases hr : start x t
      · rfl
      · exact absurd ((start_iff x t).mp hr).1 (hjlast t h1 h2)⟩
    good := fun t h1 h2 => by
      rcases Nat.lt_or_ge t i with h' | h'
      · have : t = i - 1 := by omega
        subst this
        exact hgood_prev
      · exact good_of_failureAt (hpass t h' h2).1
    sequence := fun t h1 h2 => by
      have hc := passesComm_of_failureAt (hpass t h1 h2).1
      have hg : good (x (t - 1)) = true := by
        rcases Nat.lt_or_ge (t - 1) i with h' | h'
        · have : t - 1 = i - 1 := by omega
          rw [this]
          exact hgood_prev
        · exact good_of_failureAt (hpass (t - 1) h' (by omega)).1
      have ht0 : t ≠ 0 := by omega
      simp only [passesComm, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, ht0, hg,
        Bool.not_true, false_or, Bool.false_eq_true] at hc
      exact hc.2
    content := fun t h1 h2 => contentFailureAt_of_failureAt (hpass t h1 h2).1
    stopOk := fun t h1 h2 => (hpass t h1 h2).2
    resetReleased := by
      unfold prevResetAt at hpr
      cases hl : lastBefore (passesComm x) i with
      | none =>
        simp [hl] at hpr
      | some u =>
        simp only [hl] at hpr
        obtain ⟨h1, h2, h3⟩ := lastBefore_spec hl
        exact ⟨u, h1, h2, h3, hpr⟩
    resetPressed := ⟨hre, hru, hau⟩
    started := ⟨hrunj, hauxj⟩
    run := hrun
    beforeAcceptance := by
      rw [answerAt_state, Nat.sub_add_cancel hi1]
      exact hi
    standby := ⟨by rw [answerAt_state]; exact hacc.2, by
      rw [answerAt_state, Nat.sub_add_cancel (by omega : 1 ≤ j)]
      exact hj⟩
    active := fun t h1 h2 => by
      rw [answerAt_state]
      exact hact (t + 1) (by omega) (by omega)
    precharge := fun hp => by
      rw [answerAt_permit] at hp
      have hP : (stateAt x (n + 1)).mode = .precharge := by
        rcases hn with h' | h'
        · exact h'
        · rw [h'] at hp
          simp [Mode.permit] at hp
      have hall : ∀ t, j ≤ t → t ≤ n → (stateAt x (t + 1)).mode = .precharge := by
        intro t h1 h2
        rcases hPN (t + 1) (by omega) (by omega) with h' | h'
        · exact h'
        · have hstay : ∀ d, t + 1 + d ≤ n + 1 → (stateAt x (t + 1 + d)).mode = .normal := by
            intro d
            induction d with
            | zero => intro _; exact h'
            | succ d ih =>
              intro hd
              exact hNN (t + 1 + d) (by omega) (by omega) (ih (by omega))
          have := hstay (n - t) (by omega)
          rw [show t + 1 + (n - t) = n + 1 by omega, hP] at this
          exact absurd this (by decide)
      refine ⟨fun t h1 h2 => by rw [answerAt_state]; exact hall t h1 h2, ?_⟩
      have := pc_run x hj hstart (n - j) fun t h1 h2 => hall t h1 (by omega)
      exact this.2
    normal := fun hp => by
      rw [answerAt_permit] at hp
      have hN : (stateAt x (n + 1)).mode = .normal := by
        rcases hn with h' | h'
        · rw [h'] at hp
          simp [Mode.permit] at hp
        · exact h'
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_first
        (fun t => (stateAt x (t + 1)).mode = .normal) (a := j) (b := n) hN hjn
      have hkj : j < k := by
        rcases Nat.eq_or_lt_of_le hk1 with h' | h'
        · subst h'
          rw [hstart] at hk3
          exact absurd hk3 (by decide)
        · exact h'
      have hbefore : ∀ t, j ≤ t → t < k → (stateAt x (t + 1)).mode = .precharge :=
        fun t h1 h2 => by
          rcases hPN (t + 1) (by omega) (by omega) with h' | h'
          · exact h'
          · exact absurd h' (hk4 t h1 h2)
      have hafter : ∀ d, k + d ≤ n → (stateAt x (k + d + 1)).mode = .normal := by
        intro d
        induction d with
        | zero => intro _; exact hk3
        | succ d ih =>
          intro hd
          exact hNN (k + d + 1) (by omega) (by omega) (ih (by omega))
      have hpk := hbefore (k - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hpk
      have hk3' := hk3
      rw [mode_succ] at hk3'
      have hcond := ((next_precharge hpk).2 hk3').2
      have hpc := pc_run x hj hstart (k - 1 - j) fun t h1 h2 => hbefore t h1 (by omega)
      refine ⟨k, hkj, hk2, by omega, hcond, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
      · rw [answerAt_state]
        exact hbefore t h1 h2
      · rw [answerAt_state]
        have := hafter (t - k) (by omega)
        rwa [show k + (t - k) = t by omega] at this }

/-! ## M2 to M12 -/

/-- M2: the permit of every answer is the permit of its state, so it is `0x00`, `0x03`, or
`0x05`, and no answer permits PRE and POS together or POS without NEG. -/
theorem m2 (t : Nat) :
    (answerAt x t).permit = (answerAt x t).state.permit ∧
      ((answerAt x t).permit = 0x00 ∨ (answerAt x t).permit = 0x03 ∨
        (answerAt x t).permit = 0x05) ∧
      ¬((answerAt x t).permit.testBit 1 = true ∧ (answerAt x t).permit.testBit 2 = true) ∧
      ((answerAt x t).permit.testBit 2 = true → (answerAt x t).permit.testBit 0 = true) := by
  rw [answerAt_permit, answerAt_state]
  cases (stateAt x (t + 1)).mode <;> decide

/-- M3 for one step: a segment that fails a check gets permit 0 and state `FAULT`, with the
failing check's code when the state before was not `FAULT` and the code before otherwise. -/
theorem step_failure {s : State} {y : Input} {c : Nat} (h : failure s y = some c) :
    (step s y).2.permit = 0 ∧ (step s y).2.state = .fault ∧
      (step s y).2.code = if s.mode = .fault then s.diag else c := by
  have hn := next_failure h
  show (next s y).mode.permit = 0 ∧ (next s y).mode = .fault ∧
    (next s y).diag = if s.mode = .fault then s.diag else c
  rw [hn]
  exact ⟨rfl, rfl, rfl⟩

/-- M3: the answer to a segment that fails a check has permit 0 and state `FAULT`, and its code
is the code of the first failing check when the state before was not `FAULT` and the code of the
answer before otherwise. -/
theorem m3 (t c : Nat) (h : failureAt x t = some c) :
    (answerAt x t).permit = 0 ∧ (answerAt x t).state = .fault ∧
      (answerAt x t).code =
        if stateBefore x t = .fault then (answerAt x (t - 1)).code else c := by
  rw [← failure_eq] at h
  obtain ⟨h1, h2, h3⟩ := step_failure h
  refine ⟨h1, h2, ?_⟩
  rw [answerAt_eq, h3, stateBefore_eq]
  split_ifs with hf
  · cases t with
    | zero => simp [init] at hf
    | succ t => rfl
  · rfl

/-- M4: from `FAULT`, the next answer has state `FAULT` with the same code, or it answers a reset
acceptance with state `STANDBY`. -/
theorem m4 (t : Nat) (h : (answerAt x t).state = .fault) :
    ((answerAt x (t + 1)).state = .fault ∧ (answerAt x (t + 1)).code = (answerAt x t).code) ∨
      (resetAcceptance x (t + 1) = true ∧ (answerAt x (t + 1)).state = .standby) := by
  rw [answerAt_state] at h
  rcases next_fault (x := x (t + 1)) h with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨(resetAcceptance_iff x (t + 1)).mpr ⟨Or.inr h, h1⟩, h1⟩

/-- M5: the answer to a segment whose record has `STOP_OK` 0, in particular to a record that
passes the communication checks with `STOP_OK` 0, has permit 0 and state `RESET_REQUIRED` or
`FAULT`. -/
theorem m5 (t : Nat) (hs : (scanOf (x t)).stopOk = false) :
    (answerAt x t).permit = 0 ∧
      ((answerAt x t).state = .resetRequired ∨ (answerAt x t).state = .fault) := by
  have hm : (answerAt x t).state = .resetRequired ∨ (answerAt x t).state = .fault := by
    rw [answerAt_state, mode_succ]
    cases hf : failure (stateAt x t) (x t) with
    | some c => rw [next_failure hf]; exact Or.inr rfl
    | none => exact next_stop hf hs
  refine ⟨?_, hm⟩
  rw [answerAt_permit, ← answerAt_state]
  rcases hm with h | h <;> rw [h] <;> rfl

/-- M6: the answer to a record that passes every check with `STOP_OK` 1 and `RUN` 0, in
`PRECHARGE` or `NORMAL`, has permit 0 and state `STANDBY`. -/
theorem m6 (t : Nat) (hf : failureAt x t = none) (hs : (scanOf (x t)).stopOk = true)
    (hr : (scanOf (x t)).run = false)
    (hm : stateBefore x t = .precharge ∨ stateBefore x t = .normal) :
    (answerAt x t).permit = 0 ∧ (answerAt x t).state = .standby := by
  rw [← failure_eq] at hf
  rw [stateBefore_eq] at hm
  have h := next_standbyRequest hf hs hr hm
  rw [answerAt_permit, answerAt_state, mode_succ, h]
  exact ⟨rfl, rfl⟩

/-- M7: no `N_pc + 1` consecutive answers have state `PRECHARGE`. -/
theorem m7_count (m : Nat) : ¬∀ d, d ≤ nPc → (answerAt x (m + d)).state = .precharge := by
  intro h
  have hP : ∀ t, m ≤ t → t ≤ m + nPc → (stateAt x (t + 1)).mode = .precharge :=
    fun t h1 h2 => by
      have := h (t - m) (by omega)
      rwa [answerAt_state, show m + (t - m) = t by omega] at this
  obtain ⟨j, -, hjm, hj, hjlast⟩ := exists_last (fun t => (stateAt x t).mode ≠ .precharge)
    (w := 0) (n := m) (by rw [stateAt_zero]; decide) (Nat.zero_le _)
  have hall : ∀ t, j ≤ t → t ≤ m + nPc → (stateAt x (t + 1)).mode = .precharge :=
    fun t h1 h2 => by
      rcases Nat.lt_or_ge t m with h' | h'
      · have := hjlast (t + 1) (by omega) (by omega)
        simpa using this
      · exact hP t h' h2
  have hs : (stateAt x j).mode = .standby := by
    rcases run_into_precharge x j (hall j le_rfl (by omega)) with h' | h'
    · exact h'
    · exact absurd h' hj
  have := (pc_run x hs (hall j le_rfl (by omega)) (m + nPc - j)
    fun t h1 h2 => hall t h1 (by omega)).2
  omega

/-- M7: the answer that ends `PRECHARGE` has state `NORMAL` only for a record that meets the
precharge condition. -/
theorem m7_normal (t : Nat) (h1 : (answerAt x t).state = .precharge)
    (h2 : (answerAt x (t + 1)).state = .normal) :
    prechargeCondition (scanOf (x (t + 1))) = true := by
  rw [answerAt_state] at h1 h2
  rw [mode_succ] at h2
  exact ((next_precharge h1).2 h2).2

/-- M8: the answer to a record whose auxiliary contacts fail check 17, in particular one that
passes the communication checks and fails check 17, has permit 0 and state `FAULT`. -/
theorem m8 (t : Nat) (h17 : auxFault (permitInForce x t) (agesAt x t) (scanOf (x t)) = true) :
    (answerAt x t).permit = 0 ∧ (answerAt x t).state = .fault := by
  cases hf : failureAt x t with
  | none => exact absurd hf (auxFault_true_of h17 rfl)
  | some c =>
    obtain ⟨h1, h2, -⟩ := m3 x t c hf
    exact ⟨h1, h2⟩

/-- M9: if segments `t` to `t + k` are good records with consecutive sequence numbers, records
`t + 1` to `t + k` pass the communication checks, from every state before `t`. -/
theorem m9 (s0 : State) (y : Nat → Input) (t k : Nat)
    (hg : ∀ u, t ≤ u → u ≤ t + k → good (y u) = true)
    (hs : ∀ u, t < u → u ≤ t + k →
      (scanOf (y u)).seq = ((scanOf (y (u - 1))).seq + 1) % 2 ^ 32) :
    ∀ u, t < u → u ≤ t + k →
      passesCommWith (stateFrom s0 y u).synced (stateFrom s0 y u).expected (y u) = true := by
  intro u h1 h2
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  have hgv := hg v (by omega) (by omega)
  have hgu := hg (v + 1) (by omega) h2
  have hsu := hs (v + 1) h1 h2
  simp only [Nat.add_sub_cancel] at hsu
  simp [stateFrom, step, passesCommWith, seqFault, hgv, hgu, hsu]

/-- M10: the answers to the first two segments after a board reset have permit 0, the first has
board sequence number 0, and every reset acceptance follows a record that passed the
communication checks with `RESET` 0. -/
theorem m10 :
    (answerAt x 0).permit = 0 ∧ (answerAt x 1).permit = 0 ∧ (answerAt x 0).board = 0 ∧
      ∀ t, (stateBefore x t = .resetRequired ∨ stateBefore x t = .fault) →
        (answerAt x t).state = .standby →
        ∃ u < t, passesComm x u = true ∧ (scanOf (x u)).reset = false := by
  have h1 : (stateAt x 1).mode = .resetRequired ∨ (stateAt x 1).mode = .fault := by
    rw [mode_succ]
    have hi := next_inactive (s := stateAt x 0) (x := x 0) (Or.inl rfl)
    cases hm : (next (stateAt x 0) (x 0)).mode with
    | standby =>
      obtain ⟨-, -, ha⟩ := hi.1.mp hm
      simp [acceptanceWith, init] at ha
    | precharge => exact absurd hm hi.2.1
    | normal => exact absurd hm hi.2.2
    | resetRequired => exact Or.inl rfl
    | fault => exact Or.inr rfl
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [answerAt_permit]
    rcases h1 with h | h <;> rw [h] <;> rfl
  · rw [answerAt_permit, mode_succ]
    have hi := next_inactive (s := stateAt x 1) (x := x 1) h1
    cases hm : (next (stateAt x 1) (x 1)).mode with
    | precharge => exact absurd hm hi.2.1
    | normal => exact absurd hm hi.2.2
    | _ => rfl
  · intro t hm hs
    rw [stateBefore_eq] at hm
    rw [answerAt_state] at hs
    have hr := (resetAcceptance_iff x t).mpr ⟨hm, hs⟩
    obtain ⟨-, -, -, ha⟩ := resetAcceptance_spec x hr
    obtain ⟨-, hpr, -⟩ := acceptanceWith_spec ha
    unfold prevResetAt at hpr
    cases hl : lastBefore (passesComm x) t with
    | none =>
      simp [hl] at hpr
    | some u =>
      simp only [hl] at hpr
      obtain ⟨h2, h3, -⟩ := lastBefore_spec hl
      exact ⟨u, h2, h3, hpr⟩

theorem next_diag_lt {s : State} {y : Input} (h : s.diag < 2 ^ 16) : (next s y).diag < 2 ^ 16 := by
  cases hf : failure s y with
  | some c =>
    rw [next_failure hf]
    split_ifs
    · exact h
    · exact failure_lt hf
  | none =>
    rw [next_pass hf]
    split_ifs
    · unfold rule5
      split <;> split_ifs <;> first | exact h | simp [codeNone, codePrecharge]
    · unfold rule4
      split <;> first | exact h | simp [codeStop]

theorem diag_lt (t : Nat) : (stateAt x t).diag < 2 ^ 16 := by
  induction t with
  | zero => show init.diag < 2 ^ 16; decide
  | succ t ih => exact next_diag_lt ih

theorem answers_eq (t : Nat) : (stateAt x t).answers = t % 2 ^ 32 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show ((stateAt x t).answers + 1) % 2 ^ 32 = (t + 1) % 2 ^ 32
    rw [ih]
    omega

@[simp] theorem length_encodeAnswer (a : Answer) : (encodeAnswer a).length = answerLength := by
  simp [encodeAnswer, answerBody, answerLength]

theorem length_answerBody (a : Answer) : (answerBody a).length = 13 := by
  simp [answerBody]

theorem Mode.ofCode?_code (m : Mode) : Mode.ofCode? (m.code % 256) = some m := by
  cases m <;> rfl

theorem field_answerBody (a : Answer) :
    field (answerBody a) 1 4 = a.board % 2 ^ 32 ∧ field (answerBody a) 5 4 = a.answered % 2 ^ 32 ∧
      field (answerBody a) 9 1 = a.permit % 2 ^ 8 ∧ field (answerBody a) 10 1 = a.state.code % 256 ∧
      field (answerBody a) 11 2 = a.code % 2 ^ 16 ∧ field (answerBody a) 0 1 = answerTag := by
  simp only [answerBody, List.append_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [field_append_of_le, field_append_of_ge, field_beBytes, answerTag]

/-- Decoding an answer's 17 bytes gives the answer when its fields fit their widths. -/
theorem decodeAnswer_encodeAnswer (a : Answer) (h1 : a.board < 2 ^ 32) (h2 : a.answered < 2 ^ 32)
    (h3 : a.permit < 2 ^ 8) (h4 : a.code < 2 ^ 16) : decodeAnswer (encodeAnswer a) = some a := by
  obtain ⟨f1, f5, f9, f10, f11, f0⟩ := field_answerBody a
  have hb := length_answerBody a
  have hcrc : crc (answerBody a) < 256 ^ 4 :=
    lt_of_lt_of_eq (Library.Hashing.Crc.Proof.bitsValue_lt _) (by norm_num)
  have htake : (encodeAnswer a).take 13 = answerBody a := by
    rw [encodeAnswer, List.take_left' hb]
  have hf13 : field (encodeAnswer a) 13 4 = crc (answerBody a) := by
    rw [encodeAnswer, field_append_of_le (by omega), hb, field_beBytes, Nat.mod_eq_of_lt hcrc]
  have hfield : ∀ off len, off + len ≤ 13 → field (encodeAnswer a) off len =
      field (answerBody a) off len := fun off len h => by
    rw [encodeAnswer, field_append_of_ge (by omega)]
  unfold decodeAnswer
  rw [length_encodeAnswer, hfield 0 1 (by omega), f0, hf13, htake,
    hfield 10 1 (by omega), f10, Mode.ofCode?_code, hfield 1 4 (by omega), hfield 5 4 (by omega),
    hfield 9 1 (by omega), hfield 11 2 (by omega), f1, f5, f9, f11, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  simp only [and_self, ↓reduceIte, Option.map_some]

theorem answered_lt (y : Input) :
    (if lengthOk y && crcOk y then (scanOf y).seq else unanswered) < 2 ^ 32 := by
  split
  · exact field_lt _ 1 4
  · decide

/-- M11: every answer is 17 bytes with the tag `0x80` and the CRC of `LINK` and its first 13
bytes, which `decodeAnswer` checks, its board sequence number is `t` modulo `2 ^ 32` for segment
`t`, and its answered sequence number is the record's when the segment decodes to 35 bytes with a
matching CRC, and `0xFFFFFFFF` otherwise. -/
theorem m11 (t : Nat) :
    (machine (stateAt x t) (x t)).2 = encodeAnswer (answerAt x t) ∧
      (encodeAnswer (answerAt x t)).length = answerLength ∧
      decodeAnswer (encodeAnswer (answerAt x t)) = some (answerAt x t) ∧
      (answerAt x t).board = t % 2 ^ 32 ∧
      (answerAt x t).answered =
        (if lengthOk (x t) && crcOk (x t) then (scanOf (x t)).seq else unanswered) := by
  have hb : (answerAt x t).board = t % 2 ^ 32 := answers_eq x t
  refine ⟨rfl, length_encodeAnswer _, ?_, hb, rfl⟩
  apply decodeAnswer_encodeAnswer
  · rw [hb]; exact Nat.mod_lt _ (by decide)
  · exact answered_lt (x t)
  · show (next (stateAt x t) (x t)).mode.permit < 2 ^ 8
    cases (next (stateAt x t) (x t)).mode <;> decide
  · exact diag_lt x (t + 1)

/-- M12 for the machine: the answer to a decode error, or to a record of fewer than 35 bytes, has
permit 0, state `FAULT`, and code `0x1001` or `0x1003` when the state before was not `FAULT`. -/
theorem m12 (t : Nat) (h : x t = .error .decode ∨ ∃ bs, x t = .ok bs ∧ bs.length < scanLength)
    (hf : stateBefore x t ≠ .fault) :
    (answerAt x t).permit = 0 ∧ (answerAt x t).state = .fault ∧
      ((answerAt x t).code = codeDecode ∨ (answerAt x t).code = codeLength) := by
  have hc : failureAt x t = some codeDecode ∨ failureAt x t = some codeLength := by
    rcases h with h | ⟨bs, h, hl⟩
    · left
      simp [failureAt, checks, recordChecks, firstFailure, h, isError]
    · right
      have hl' : bs.length ≠ 35 := by
        unfold scanLength at hl
        omega
      simp [failureAt, checks, recordChecks, firstFailure, h, isError, lengthOk, bytesOf,
        scanLength, hl']
  rcases hc with hc | hc
  · obtain ⟨h1, h2, h3⟩ := m3 x t _ hc
    simp only [hf, ↓reduceIte] at h3
    exact ⟨h1, h2, Or.inl h3⟩
  · obtain ⟨h1, h2, h3⟩ := m3 x t _ hc
    simp only [hf, ↓reduceIte] at h3
    exact ⟨h1, h2, Or.inr h3⟩

end Run

end Demos.Bms.Spec
