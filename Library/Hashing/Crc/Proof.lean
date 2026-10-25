import Library.Hashing.Crc.Program
import Library.Hashing.Crc.Division
import Library.Bytes.Packed

/-! The CRC programs compute the transcription.  A register holds a remainder of the division of
`Library.Hashing.Crc.Division` as its 32 low bits, the coefficient of `x^31` in the least
significant, which `Holds` states.  `TableOf` states that each entry of a table is the division's
remainder after the eight bits of its index from zero bits, which `decide` checks for both tables,
and `byteStep_holds` shows that a step of the table performs the division's eight steps for a
byte.  The loop of `updateWith` divides the bits of the message's bytes from the complement of
the CRC of a prefix, and the CRC of the prefix and the message follows from `lfsr_append`. -/

namespace Library.Hashing.Crc.Proof

open Polynomial Library.Hashing.Crc Library.Hashing.Crc.Spec Library.Hashing.Crc.Division
  Library.Bytes

/-! ## Bits of words -/

/-- The `w` low bits of `v`, the least significant first. -/
def natBits (w v : Nat) : Bits := (List.range w).map v.testBit

theorem length_natBits (w v : Nat) : (natBits w v).length = w := by simp [natBits]

theorem natBits_ext {w a b : Nat} (h : ∀ i < w, a.testBit i = b.testBit i) :
    natBits w a = natBits w b := by
  apply List.ext_getElem (by simp [length_natBits])
  intro i h1 _
  simp only [natBits, List.getElem_map, List.getElem_range]
  exact h i (by simpa [length_natBits] using h1)

theorem natBits_xor (w a b : Nat) :
    natBits w (a ^^^ b) = List.zipWith (· ^^ ·) (natBits w a) (natBits w b) := by
  apply List.ext_getElem (by simp [length_natBits])
  intro i _ _
  simp [natBits, Nat.testBit_xor]

theorem natBits_add (a b v : Nat) : natBits (a + b) v = natBits a v ++ natBits b (v >>> a) := by
  simp [natBits, List.range_add, Nat.testBit_shiftRight]

theorem natBits_zero (w : Nat) : natBits w 0 = List.replicate w false := by
  apply List.ext_getElem (by simp [length_natBits])
  intro i _ _
  simp [natBits]

theorem natBits_mod (w v : Nat) : natBits w (v % 2 ^ w) = natBits w v :=
  natBits_ext fun i hi => by simp [Nat.testBit_mod_two_pow, hi]

theorem natBits_not (v : Nat) : natBits 32 (v ^^^ 0xFFFFFFFF) = (natBits 32 v).map not := by
  apply List.ext_getElem (by simp [length_natBits])
  intro i h1 _
  have hi : i < 32 := by simpa [length_natBits] using h1
  simp only [natBits, List.getElem_map, List.getElem_range, Nat.testBit_xor]
  rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem poly_replicate_false (n : Nat) : poly (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, poly_cons, ih]

/-- Strings of one length with one polynomial are equal. -/
theorem poly_inj : ∀ (S T : Bits), S.length = T.length → poly S = poly T → S = T
  | [], [], _, _ => rfl
  | a :: S, b :: T, hl, h => by
    have hl' : S.length = T.length := by simpa using hl
    have hS : (poly S).coeff S.length = 0 := coeff_eq_zero_of_degree_lt (degree_poly_lt S)
    have hT : (poly T).coeff S.length = 0 :=
      coeff_eq_zero_of_degree_lt (by rw [hl']; exact degree_poly_lt T)
    rw [poly_cons, poly_cons, ← hl'] at h
    have hc := congrArg (fun p => p.coeff S.length) h
    simp only [coeff_add, hS, hT, add_zero] at hc
    have hab : a = b := by cases a <;> cases b <;> simp [coeff_X_pow] at hc ⊢
    subst hab
    rw [poly_inj S T hl' (add_left_cancel h)]

/-! ## The value of a remainder -/

theorem sum_pow_lt (f : Nat → Bool) (k : Nat) :
    ∑ i ∈ Finset.range k, (if f i then 2 ^ i else 0) < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    split <;> omega

theorem testBit_sum_pow (f : Nat → Bool) (k : Nat) : ∀ j,
    (∑ i ∈ Finset.range k, (if f i then 2 ^ i else 0)).testBit j = (decide (j < k) && f j) := by
  induction k with
  | zero => intro j; simp
  | succ k ih =>
    intro j
    rw [Finset.sum_range_succ]
    have hlt := sum_pow_lt f k
    rcases lt_trichotomy j k with h | h | h
    · split
      · rw [add_comm, Nat.testBit_two_pow_add_gt h, ih]; simp [h, Nat.lt_succ_of_lt h]
      · rw [add_zero, ih]; simp [h, Nat.lt_succ_of_lt h]
    · subst h
      split
      · rw [add_comm, Nat.testBit_two_pow_add_eq, ih]; simp [*]
      · rw [add_zero, ih]; simp [*]
    · have hj : ¬ j < k + 1 := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by split <;> omega)
        (Nat.pow_le_pow_right (by decide) (by omega : k + 1 ≤ j)))]
      simp [hj]

theorem bitsValue_lt (S : Bits) : bitsValue S < 2 ^ 32 := sum_pow_lt _ 32

theorem testBit_bitsValue (S : Bits) (j : Nat) :
    (bitsValue S).testBit j = (decide (j < 32) && S.getD j false) :=
  testBit_sum_pow _ 32 j

theorem bitsValue_natBits {v : Nat} (hv : v < 2 ^ 32) : bitsValue (natBits 32 v) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitsValue]
  by_cases hj : j < 32
  · simp [hj, natBits, List.getD_eq_getElem?_getD]
  · simp [hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by decide) (by omega : 32 ≤ j)))]

theorem natBits_bitsValue (S : Bits) (hS : S.length = 32) : natBits 32 (bitsValue S) = S := by
  apply List.ext_getElem (by simp [length_natBits, hS])
  intro i h1 h2
  have hi : i < 32 := by simpa [length_natBits] using h1
  simp [natBits, testBit_bitsValue, hi, List.getD_eq_getElem?_getD, h2]

/-! ## Registers and tables -/

/-- The register `r` holds the 32 bits `S`: its bits from the least significant are `S`, and it
has no others. -/
def Holds (r : UInt64) (S : Bits) : Prop := r.toNat < 2 ^ 32 ∧ natBits 32 r.toNat = S

/-- Each entry `k` of `t` holds the remainder of the division by `x^32 + poly gLow` after the
eight bits of `k` from zero bits. -/
def TableOf (gLow : Bits) (t : Array UInt64) : Prop :=
  ∀ k < 256, Holds t[k]! (lfsr gLow (List.replicate 32 false) (natBits 8 k))

theorem crc32Table_of : TableOf (lowBits 0x04C11DB7) crc32Table := by
  unfold TableOf Holds
  decide +kernel

theorem crc32cTable_of : TableOf (lowBits 0x1EDC6F41) crc32cTable := by
  unfold TableOf Holds
  decide +kernel

/-- A step of the table performs the division's eight steps for the byte in the low eight bits
of `w`. -/
theorem byteStep_holds {gLow : Bits} {t : Array UInt64} (hg : gLow.length = 32)
    (ht : TableOf gLow t) {r : UInt64} {S : Bits} (hr : Holds r S) (w : UInt64) :
    Holds (byteStep t r w) (lfsr gLow S (natBits 8 w.toNat)) := by
  obtain ⟨hlt, rfl⟩ := hr
  have hidx : ((r ^^^ w) &&& 0xFF).toNat = (r.toNat ^^^ w.toNat) % 2 ^ 8 := by
    rw [UInt64.toNat_and, UInt64.toNat_xor, show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hval : (byteStep t r w).toNat =
      (r.toNat >>> 8) ^^^ (t[(r.toNat ^^^ w.toNat) % 2 ^ 8]!).toNat := by
    rw [byteStep, UInt64.toNat_xor, UInt64.toNat_shiftRight, hidx]
    rfl
  obtain ⟨htlt, htbits⟩ := ht ((r.toNat ^^^ w.toNat) % 2 ^ 8) (Nat.mod_lt _ (by decide))
  have hsh : r.toNat >>> 8 < 2 ^ 24 := by rw [Nat.shiftRight_eq_div_pow]; omega
  refine ⟨by rw [hval]; exact Nat.xor_lt_two_pow (by omega) htlt, ?_⟩
  have hm := monic_gen gLow hg
  apply poly_inj _ _ (by rw [length_natBits, length_lfsr gLow hg _ _ (length_natBits _ _)])
  have h1 : natBits 32 (r.toNat >>> 8) = natBits 24 (r.toNat >>> 8) ++ List.replicate 8 false := by
    rw [natBits_add 24 8, Nat.shiftRight_eq_div_pow (r.toNat >>> 8),
      Nat.div_eq_of_lt hsh, natBits_zero]
  have hlow : poly (natBits 32 (r.toNat >>> 8)) %ₘ (X ^ 32 + poly gLow) =
      poly (natBits 32 (r.toNat >>> 8)) :=
    (modByMonic_eq_self_iff hm).mpr (by
      rw [degree_gen gLow hg]
      simpa [length_natBits] using degree_poly_lt (natBits 32 (r.toNat >>> 8)))
  rw [hval, natBits_xor, poly_xor _ _ (by simp [length_natBits]), htbits,
    lfsr_spec gLow hg _ _ (length_natBits _ _),
    lfsr_spec gLow hg (natBits 8 _) (List.replicate 32 false) (by simp),
    poly_replicate_false, mul_zero, zero_add, natBits_mod, natBits_xor,
    poly_xor _ _ (by simp [length_natBits]), natBits_add 8 24 r.toNat, poly_append, ← hlow,
    ← add_modByMonic, h1, poly_append, poly_replicate_false]
  simp only [length_natBits, List.length_replicate]
  exact congrArg (· %ₘ (X ^ 32 + poly gLow)) (by ring)

/-! ## The loop -/

theorem bitsOfBytes_append (A B : List UInt8) :
    bitsOfBytes (A ++ B) = bitsOfBytes A ++ bitsOfBytes B := by
  simp [bitsOfBytes]

theorem bitsOfBytes_singleton (b : UInt8) : bitsOfBytes [b] = natBits 8 b.toNat := by
  simp [bitsOfBytes, natBits]

theorem lfsr_append (gLow S A B : Bits) : lfsr gLow S (A ++ B) = lfsr gLow (lfsr gLow S A) B := by
  induction A generalizing S with
  | nil => rfl
  | cons a A ih => exact ih _

/-- The bytes of the first `n` bytes of `msg`. -/
def messageBytes (msg : Array UInt64) (n : Nat) : List UInt8 := (List.range n).map (byteAt msg)

/-- The program's byte at index `i` has the bits of the packed message's byte `i`. -/
theorem natBits_word (msg : Array UInt64) {i : Nat} (hi : i < 2 ^ 64) :
    natBits 8 (msg[(UInt64.ofNat i >>> 3).toNat]! >>> ((UInt64.ofNat i &&& 7) <<< 3)).toNat =
      natBits 8 (byteAt msg i).toNat := by
  have hit : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' hi
  have hword : (UInt64.ofNat i >>> 3).toNat = i / 8 := by
    rw [UInt64.toNat_shiftRight, hit, show (3 : UInt64).toNat % 64 = 3 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hshift : (UInt64.ofNat i &&& 7) <<< 3 = (8 * (i % 8)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, hit, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  rw [hword, hshift, byteAt, UInt64.toNat_toUInt8, natBits_mod]

theorem loop_holds {gLow : Bits} {t : Array UInt64} (hg : gLow.length = 32) (ht : TableOf gLow t)
    (msg : Array UInt64) {r : UInt64} {S : Bits} (hr : Holds r S) (n : UInt64) :
    Holds (LeanExe.loop n r fun i r => byteStep t r (msg[(i >>> 3).toNat]! >>> ((i &&& 7) <<< 3)))
      (lfsr gLow S (bitsOfBytes (messageBytes msg n.toNat))) := by
  unfold LeanExe.loop
  have hn := UInt64.toNat_lt n
  generalize n.toNat = N at hn ⊢
  induction N with
  | zero => exact hr
  | succ m ih =>
    rw [Nat.fold_succ, messageBytes, List.range_succ, List.map_append, List.map_singleton,
      bitsOfBytes_append, bitsOfBytes_singleton, lfsr_append, ← natBits_word msg (by omega)]
    exact byteStep_holds hg ht (ih (by omega)) _

/-! ## The CRCs -/

theorem holds_not {r : UInt64} {S : Bits} (hr : Holds r S) : Holds (r ^^^ 0xFFFFFFFF) (S.map not) := by
  obtain ⟨hlt, rfl⟩ := hr
  rw [Holds, UInt64.toNat_xor, show (0xFFFFFFFF : UInt64).toNat = 0xFFFFFFFF from rfl, natBits_not]
  exact ⟨Nat.xor_lt_two_pow hlt (by decide), rfl⟩

/-- The register from which `updateWith` starts holds the complement of the low 32 bits of
`crc`. -/
theorem start_holds (crc : UInt64) :
    Holds ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF) ((natBits 32 crc.toNat).map not) := by
  have h : ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF).toNat = (crc.toNat ^^^ 0xFFFFFFFF) % 2 ^ 32 := by
    rw [UInt64.toNat_and, UInt64.toNat_xor, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    rfl
  rw [Holds, h, natBits_mod, natBits_not]
  exact ⟨Nat.mod_lt _ (by decide), rfl⟩

theorem updateWith_holds {gLow : Bits} {t : Array UInt64} (hg : gLow.length = 32)
    (ht : TableOf gLow t) (crc : UInt64) (msg : Array UInt64) (n : UInt64) :
    Holds (updateWith t crc msg n)
      ((lfsr gLow ((natBits 32 crc.toNat).map not) (bitsOfBytes (messageBytes msg n.toNat))).map
        not) :=
  holds_not (loop_holds hg ht msg (start_holds crc) n)

theorem toNat_eq_bitsValue {r : UInt64} {S : Bits} (hr : Holds r S) : r.toNat = bitsValue S := by
  rw [← hr.2, bitsValue_natBits hr.1]

theorem crcWith_eq {gLow : Bits} {t : Array UInt64} (hg : gLow.length = 32) (ht : TableOf gLow t)
    (msg : Array UInt64) (n : UInt64) :
    (crcWith t msg n).toNat = bitsValue (crcBits gLow (bitsOfBytes (messageBytes msg n.toNat))) := by
  have h := updateWith_holds hg ht 0 msg n
  rw [show (natBits 32 (0 : UInt64).toNat).map not = List.replicate 32 true by
    rw [show (0 : UInt64).toNat = 0 from rfl, natBits_zero]; simp] at h
  exact toNat_eq_bitsValue h

theorem updateWith_eq {gLow : Bits} {t : Array UInt64} (hg : gLow.length = 32)
    (ht : TableOf gLow t) (A : List UInt8) (crc : UInt64)
    (hcrc : crc.toNat = bitsValue (crcBits gLow (bitsOfBytes A))) (msg : Array UInt64)
    (n : UInt64) :
    (updateWith t crc msg n).toNat =
      bitsValue (crcBits gLow (bitsOfBytes (A ++ messageBytes msg n.toNat))) := by
  have h := updateWith_holds hg ht crc msg n
  rw [hcrc, natBits_bitsValue _ (by rw [crcBits, List.length_map, length_lfsr gLow hg _ _ (by simp)]),
    crcBits, List.map_map, show not ∘ not = id from funext Bool.not_not, List.map_id,
    ← lfsr_append, ← bitsOfBytes_append] at h
  exact toNat_eq_bitsValue h

/-- `crc32` computes CRC-32 of the first `n` bytes of `msg`. -/
theorem crc32_spec (msg : Array UInt64) (n : UInt64) :
    (crc32 msg n).toNat = Spec.crc32 (messageBytes msg n.toNat) := by
  rw [Division.crc32_eq, crc32Eval, crc32, crcWith_eq (length_lowBits _) crc32Table_of]

/-- `crc32c` computes CRC-32C of the first `n` bytes of `msg`. -/
theorem crc32c_spec (msg : Array UInt64) (n : UInt64) :
    (crc32c msg n).toNat = Spec.crc32c (messageBytes msg n.toNat) := by
  rw [Division.crc32c_eq, crc32cEval, crc32c, crcWith_eq (length_lowBits _) crc32cTable_of]

/-- From CRC-32 of the bytes `A`, `crc32Update` computes CRC-32 of `A` and the first `n` bytes
of `msg`. -/
theorem crc32Update_spec (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32 A)
    (msg : Array UInt64) (n : UInt64) :
    (crc32Update crc msg n).toNat = Spec.crc32 (A ++ messageBytes msg n.toNat) := by
  rw [Division.crc32_eq] at hcrc ⊢
  exact updateWith_eq (length_lowBits _) crc32Table_of A crc hcrc msg n

/-- From CRC-32C of the bytes `A`, `crc32cUpdate` computes CRC-32C of `A` and the first `n` bytes
of `msg`. -/
theorem crc32cUpdate_spec (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32c A)
    (msg : Array UInt64) (n : UInt64) :
    (crc32cUpdate crc msg n).toNat = Spec.crc32c (A ++ messageBytes msg n.toNat) := by
  rw [Division.crc32c_eq] at hcrc ⊢
  exact updateWith_eq (length_lowBits _) crc32cTable_of A crc hcrc msg n

end Library.Hashing.Crc.Proof
