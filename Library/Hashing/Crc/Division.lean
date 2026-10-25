import Library.Hashing.Crc.Spec
import Mathlib.Tactic

/-! A computable form of the CRCs of `Library.Hashing.Crc.Spec`.  `lfsr` divides by a generator
`x^32 + poly gLow` one bit at a time, keeping a remainder of 32 bits with its coefficient of
`x^31` first, and `lfsr_spec` shows that from the remainder `S` it gives the remainder of
`x^k S + x^32 M`.  From 32 ones it gives the sum of V.42's two remainders, so `crc32Eval` and
`crc32cEval` compute `crc32` and `crc32c`.  `rfcProcess_eq` shows that the process of RFC 3720
§12.1 gives the FCS of V.42 for messages of at least 32 bits. -/

namespace Library.Hashing.Crc.Division

open Polynomial Library.Hashing.Crc.Spec

/-! ## Polynomials of bit strings -/

theorem poly_cons (b : Bool) (M : Bits) :
    poly (b :: M) = (if b then X ^ M.length else 0) + poly M := rfl

theorem poly_append (A B : Bits) : poly (A ++ B) = X ^ B.length * poly A + poly B := by
  induction A with
  | nil => simp [poly]
  | cons a A ih =>
    rw [List.cons_append, poly_cons, poly_cons, ih, List.length_append]
    split <;> ring

/-- Over GF(2), the bitwise XOR of two strings of one length is the sum of their polynomials. -/
theorem poly_xor : ∀ (A B : Bits), A.length = B.length →
    poly (List.zipWith (· ^^ ·) A B) = poly A + poly B
  | [], [], _ => by simp [poly]
  | a :: A, b :: B, h => by
    have hl : A.length = B.length := by simpa using h
    rw [List.zipWith_cons_cons, poly_cons, poly_cons, poly_cons, poly_xor A B hl,
      List.length_zipWith, hl, Nat.min_self]
    cases a <;> cases b <;> grind

theorem poly_not (S : Bits) : poly (S.map not) = poly S + poly (List.replicate S.length true) := by
  have : S.map not = List.zipWith (· ^^ ·) S (List.replicate S.length true) := by
    induction S with
    | nil => rfl
    | cons s S ih => simp [List.replicate_succ, ih]
  rw [this, poly_xor _ _ (by simp)]

theorem degree_poly_lt (M : Bits) : (poly M).degree < M.length := by
  induction M with
  | nil => simp [poly]
  | cons b M ih =>
    rw [poly_cons, List.length_cons]
    refine lt_of_le_of_lt (degree_add_le _ _)
      (max_lt ?_ (lt_of_lt_of_le ih (by exact_mod_cast Nat.le_succ _)))
    split
    · rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_self _
    · simp

/-! ## The generators -/

/-- The 32 coefficients of `x^31` to `x^0` of a generator, from the value `h` whose bit `i` is the
coefficient of `x^i`. -/
def lowBits (h : Nat) : Bits := (List.range 32).map fun i => h.testBit (31 - i)

theorem length_lowBits (h : Nat) : (lowBits h).length = 32 := by simp [lowBits]

theorem g32_eq : g32 = X ^ 32 + poly (lowBits 0x04C11DB7) := by
  rw [show lowBits 0x04C11DB7 = [false, false, false, false, false, true, false, false, true, true,
    false, false, false, false, false, true, false, false, false, true, true, true, false, true,
    true, false, true, true, false, true, true, true] from rfl]
  simp only [g32, List.length_cons, List.length_nil, poly, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceAdd, zero_add, add_zero]
  ring

/-- The generator of RFC 3720 §12.1, with its exponents written out. -/
theorem g32c_explicit : g32c = X ^ 32 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 23 + X ^ 22 +
    X ^ 20 + X ^ 19 + X ^ 18 + X ^ 14 + X ^ 13 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 6 + 1 := by
  rw [g32c, hexPoly, show Nat.log2 0x11edc6f41 + 1 = 33 from rfl]
  simp [Finset.sum_range_succ, Nat.testBit]
  ring

theorem g32c_eq : g32c = X ^ 32 + poly (lowBits 0x1EDC6F41) := by
  rw [g32c_explicit, show lowBits 0x1EDC6F41 = [false, false, false, true, true, true, true, false,
    true, true, false, true, true, true, false, false, false, true, true, false, true, true, true,
    true, false, true, false, false, false, false, false, true] from rfl]
  simp only [List.length_cons, List.length_nil, poly, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd,
    zero_add, add_zero]
  ring

theorem monic_gen (gLow : Bits) (hg : gLow.length = 32) : (X ^ 32 + poly gLow).Monic := by
  apply monic_X_pow_add
  have := degree_poly_lt gLow
  rw [hg] at this
  exact_mod_cast this

theorem degree_gen (gLow : Bits) (hg : gLow.length = 32) : (X ^ 32 + poly gLow).degree = 32 := by
  have := degree_poly_lt gLow
  rw [hg] at this
  rw [degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact_mod_cast this), degree_X_pow]
  rfl

/-! ## The division -/

/-- One step of the division: from a remainder `S` of 32 bits, `x^31` first, and the next bit
`b`, the remainder of `x S + b x^32` divided by `x^32 + poly gLow`. -/
def step (gLow : Bits) (S : Bits) (b : Bool) : Bits :=
  match S with
  | [] => []
  | s :: rest => if s ^^ b then List.zipWith (· ^^ ·) (rest ++ [false]) gLow else rest ++ [false]

/-- The division of the bits `M` from the remainder `S`. -/
def lfsr (gLow : Bits) (S : Bits) : Bits → Bits
  | [] => S
  | b :: M => lfsr gLow (step gLow S b) M

theorem length_step (gLow S : Bits) (b : Bool) (hg : gLow.length = 32) (hS : S.length = 32) :
    (step gLow S b).length = 32 := by
  match S, hS with
  | s :: rest, hS =>
    have hr : rest.length = 31 := by simpa using hS
    simp only [step]
    cases s ^^ b <;> simp [hr, hg]

theorem length_lfsr (gLow : Bits) (hg : gLow.length = 32) :
    ∀ (M S : Bits), S.length = 32 → (lfsr gLow S M).length = 32
  | [], _, hS => hS
  | b :: M, S, hS => length_lfsr gLow hg M _ (length_step gLow S b hg hS)

theorem step_spec (gLow S : Bits) (b : Bool) (hg : gLow.length = 32) (hS : S.length = 32) :
    poly (step gLow S b) = (X * poly S + (if b then X ^ 32 else 0)) %ₘ (X ^ 32 + poly gLow) := by
  match S, hS with
  | s :: rest, hS =>
    have hr : rest.length = 31 := by simpa using hS
    have hm := monic_gen gLow hg
    have hlt : ∀ p : (ZMod 2)[X], p.degree < 32 → p %ₘ (X ^ 32 + poly gLow) = p := fun p hp =>
      (modByMonic_eq_self_iff hm).mpr (by rw [degree_gen gLow hg]; exact hp)
    have hshift : (poly (rest ++ [false])).degree < 32 := by
      simpa [hr] using degree_poly_lt (rest ++ [false])
    have hglow : (poly gLow).degree < 32 := by simpa [hg] using degree_poly_lt gLow
    have hpoly : X * poly (s :: rest) + (if b then X ^ 32 else 0) =
        (if s ^^ b then X ^ 32 else 0) + poly (rest ++ [false]) := by
      rw [poly_cons, poly_append, hr]
      cases s <;> cases b <;> simp [poly] <;> grind
    rw [hpoly]
    simp only [step]
    cases s ^^ b
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, hlt _ hshift]
    · simp only [↓reduceIte]
      rw [poly_xor _ _ (by simp [hr, hg])]
      have : X ^ 32 + poly (rest ++ [false]) =
          (poly (rest ++ [false]) + poly gLow) + (X ^ 32 + poly gLow) := by grind
      rw [this, add_modByMonic, modByMonic_self hm, add_zero,
        hlt _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt hshift hglow))]

/-- The division from the remainder `S` of the `k` bits `M` gives the remainder of
`x^k S + x^32 M`. -/
theorem lfsr_spec (gLow : Bits) (hg : gLow.length = 32) :
    ∀ (M S : Bits), S.length = 32 →
      poly (lfsr gLow S M) = (X ^ M.length * poly S + X ^ 32 * poly M) %ₘ (X ^ 32 + poly gLow)
  | [], S, hS => by
    simp only [lfsr, List.length_nil, pow_zero, one_mul, poly, mul_zero, add_zero]
    have := degree_poly_lt S
    rw [hS] at this
    exact ((modByMonic_eq_self_iff (monic_gen gLow hg)).mpr
      (by rw [degree_gen gLow hg]; exact this)).symm
  | b :: M, S, hS => by
    rw [lfsr, lfsr_spec gLow hg M _ (length_step gLow S b hg hS), step_spec gLow S b hg hS]
    apply modByMonic_eq_of_dvd_sub (monic_gen gLow hg)
    have h := dvd_modByMonic_sub (X * poly S + (if b then X ^ 32 else 0)) (X ^ 32 + poly gLow)
    rw [List.length_cons, poly_cons]
    have : X ^ M.length * ((X * poly S + (if b then X ^ 32 else 0)) %ₘ (X ^ 32 + poly gLow)) +
        X ^ 32 * poly M - (X ^ (M.length + 1) * poly S +
          X ^ 32 * ((if b then X ^ M.length else 0) + poly M)) =
        X ^ M.length * ((X * poly S + (if b then X ^ 32 else 0)) %ₘ (X ^ 32 + poly gLow) -
          (X * poly S + (if b then X ^ 32 else 0))) := by
      split_ifs <;> ring
    rw [this]
    exact dvd_mul_of_dvd_right h _

/-! ## The CRCs evaluated -/

theorem coeff_poly : ∀ (S : Bits) (j : Nat),
    (poly S).coeff j = if j < S.length ∧ S.getD (S.length - 1 - j) false = true then 1 else 0
  | [], j => by simp [poly]
  | b :: M, j => by
    rw [poly_cons, coeff_add, coeff_poly M j, List.length_cons]
    rcases lt_trichotomy j M.length with h | h | h
    · rw [show M.length + 1 - 1 - j = (M.length - 1 - j) + 1 by omega, List.getD_cons_succ]
      split <;> simp [coeff_X_pow, h, h.ne, Nat.lt_succ_of_lt h]
    · subst h
      cases b <;> simp [coeff_X_pow]
    · cases b <;> simp [coeff_X_pow, h.ne', show ¬ j < M.length by omega,
        show ¬ j < M.length + 1 by omega]

/-- The integer of a remainder of 32 bits, `x^31` first: bit `i` is the coefficient of
`x^(31 - i)`. -/
def bitsValue (S : Bits) : Nat := ∑ i ∈ Finset.range 32, if S.getD i false then 2 ^ i else 0

theorem value_poly (S : Bits) (hS : S.length = 32) : value (poly S) = bitsValue S := by
  unfold value bitsValue
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < 32 := Finset.mem_range.mp hi
  rw [coeff_poly, hS, show 32 - 1 - (31 - i) = i by omega]
  cases S.getD i false <;> simp [show 31 - i < 32 by omega]

/-- The 32-bit FCS of V.42 for the generator `x^32 + poly gLow`, by the division from 32 ones. -/
def crcBits (gLow M : Bits) : Bits := (lfsr gLow (List.replicate 32 true) M).map not

theorem fcs_eq (gLow M : Bits) (hg : gLow.length = 32) :
    fcs (X ^ 32 + poly gLow) M = poly (crcBits gLow M) := by
  have hl := lfsr_spec gLow hg M (List.replicate 32 true) (by simp)
  have hlen : (lfsr gLow (List.replicate 32 true) M).length = 32 := by
    rw [length_lfsr gLow hg M _ (by simp)]
  rw [crcBits, poly_not, hlen, hl, fcs, complement32, ones32, add_modByMonic]

/-- CRC-32, computed by the division. -/
def crc32Eval (bs : List UInt8) : Nat := bitsValue (crcBits (lowBits 0x04C11DB7) (bitsOfBytes bs))

/-- CRC-32C, computed by the division. -/
def crc32cEval (bs : List UInt8) : Nat :=
  bitsValue (crcBits (lowBits 0x1EDC6F41) (bitsOfBytes bs))

theorem length_crcBits (gLow M : Bits) (hg : gLow.length = 32) : (crcBits gLow M).length = 32 := by
  rw [crcBits, List.length_map, length_lfsr gLow hg M _ (by simp)]

theorem crc32_eq (bs : List UInt8) : crc32 bs = crc32Eval bs := by
  rw [crc32, crc32Eval, g32_eq, fcs_eq _ _ (length_lowBits _),
    value_poly _ (length_crcBits _ _ (length_lowBits _))]

theorem crc32c_eq (bs : List UInt8) : crc32c bs = crc32cEval bs := by
  rw [crc32c, crc32cEval, g32c_eq, fcs_eq _ _ (length_lowBits _),
    value_poly _ (length_crcBits _ _ (length_lowBits _))]

/-! ## The process of RFC 3720 -/

/-- For a message of at least 32 bits, the process of RFC 3720 §12.1 gives the FCS of V.42. -/
theorem rfcProcess_eq (G : (ZMod 2)[X]) (M : Bits) (hM : 32 ≤ M.length) :
    rfcProcess G M = fcs G M := by
  have ht : (M.take 32).length = 32 := by simp [hM]
  obtain ⟨k, hk⟩ : ∃ k, M.length = 32 + k := ⟨M.length - 32, by omega⟩
  have hd : (M.drop 32).length = k := by simp [hk]
  have hM' : poly M = X ^ k * poly (M.take 32) + poly (M.drop 32) := by
    conv_lhs => rw [← List.take_append_drop 32 M]
    rw [poly_append, hd]
  have : X ^ 32 * poly ((M.take 32).map not ++ M.drop 32) =
      X ^ M.length * ones32 + X ^ 32 * poly M := by
    rw [poly_append, poly_not, ht, hd, hM', ones32, hk, pow_add]
    ring
  rw [rfcProcess, this, add_modByMonic, fcs]

end Library.Hashing.Crc.Division
