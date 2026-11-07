import LeanExe.A64.Isla.Walk

/-!
Theorems of `Agrees` for `LDR Xt, [Xn|SP, #(8 * imm)]` of `LeanExe/A64/Machine.lean` with every
byte of the access in the RAM GiB, for every value of the fields `imm12`, `Rn`, and `Rt`, register
31 included.  The traces are those of `tests/isla/tcg` and `tests/isla/kvm` with the arguments
`memory`, under the profiles `tcg` and `kvm`.  The two traces differ: under `kvm`, FEAT_LSE2 lets
an unaligned access within 16 bytes run as one access, and the exception entry of the alignment
fault writes more fields of `PSTATE`, so each profile has its own proof.
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.

A theorem states as premises, in the model's terms, the constraints that the trace's `assume`
events and fixed reads check.  The mask constraint of `traces.sh` puts `u.ttbr0`, the value of
`TTBR0_NS`, at a multiple of 32 in the RAM GiB, and the memory holds the descriptor
`0x0040000040000705` of `LeanExe/A64/Table.lean` at `u.ttbr0 + 8`, which the walk reads.  The
access's address, register `Rn`, the stack pointer for 31, plus the scaled immediate, lies where
the reset constraint puts it, with every byte in the RAM GiB.  On a misaligned stack pointer
`exec` fails, so the paths to the alignment fault's exception entry need no counterpart, and every
other path writes `SEE` and no other register outside the model.

The proofs walk the traces with the tactics of `LeanExe/A64/Isla/Walk.lean`.  A load that runs
byte by byte inserts its eight bytes one at a time into a word, and `ins_chain` gives the word's
value at the end of the path.  Rewriting each insertion during the walk would write the word twice
per byte, so the term's tree would double at each of the eight bytes.  Each theorem rests on lemmas
for the four cases of register 31 among `Rn` and `Rt`, one for each direction.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk
instead of that of all the lemmas that would elaborate at once. -/
set_option Elab.async false

attribute [local congr] run_congr runSome_congr

/-- The eight bytes of a load as one-byte loads, as an unaligned load reads them. -/
theorem bytes_split (m : UInt64 → UInt8) (a : UInt64) :
    bytes m a 8 = bytes m a 1 + bytes m (a + 1) 1 * 256 + bytes m (a + 2) 1 * 65536 +
      bytes m (a + 3) 1 * 16777216 + bytes m (a + 4) 1 * 4294967296 +
      bytes m (a + 5) 1 * 1099511627776 + bytes m (a + 6) 1 * 281474976710656 +
      bytes m (a + 7) 1 * 72057594037927936 := by
  simp only [bytes, UInt64.add_assoc, UInt64.reduceAdd]
  omega

/-- The address `x + c` as the trace computes it, with the immediate `c` reduced modulo
`2 ^ 64`. -/
theorem addr_eq (x : UInt64) (c : Nat) :
    UInt64.ofNat ((x.toNat + c % 18446744073709551616) % 18446744073709551616) =
      x + UInt64.ofNat c := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, Nat.reducePow, Nat.mod_mod]

/-- The address `x + c + i` of byte `i` of an access, as the trace computes it. -/
theorem addr_add (x : UInt64) (c i : Nat) :
    UInt64.ofNat (((x.toNat + c % 18446744073709551616) % 18446744073709551616 + i) %
      18446744073709551616) = x + (UInt64.ofNat c + UInt64.ofNat i) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, Nat.reducePow, Nat.mod_mod]
  omega

/-! Inserting a byte into a word, as an unaligned load assembles its value from one-byte loads:
`(y &&& ~(0xff << k)) ||| (b << k)`. -/

theorem and_mod64 {y M : Nat} (hM : 18446744073709551615 &&& M = M) :
    y &&& M = y % 18446744073709551616 &&& M := by
  calc y &&& M = y &&& (18446744073709551615 &&& M) := by rw [hM]
    _ = (y &&& 18446744073709551615) &&& M := (Nat.and_assoc _ _ _).symm
    _ = y % 18446744073709551616 &&& M := by
        rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_lo {lo k j : Nat} (hlo : lo < 2 ^ k) (hj : k ≤ j) : lo.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by decide) hj))

/-- Replacing byte `k / 8` of a word, in digits: the low `k` bits `lo`, the byte `d`, and the
high bits `hi`. -/
theorem ins_core {lo d hi b k : Nat} (hlo : lo < 2 ^ k) (hd : d < 2 ^ 8) (hb : b < 2 ^ 8)
    (hhi : hi < 2 ^ (56 - k)) :
    (2 ^ k * (2 ^ 8 * hi + d) + lo) &&& (2 ^ k * (2 ^ 8 * (2 ^ (56 - k) - 1) + 0) + (2 ^ k - 1)) |||
      (2 ^ k * (2 ^ 8 * 0 + b) + 0) = 2 ^ k * (2 ^ 8 * hi + b) + lo := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h0 : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
  have h1 : 2 ^ k - 1 < 2 ^ k := by omega
  have h08 : (0 : Nat) < 2 ^ 8 := by decide
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hlo,
    Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h0,
    Nat.testBit_two_pow_mul_add _ hlo]
  by_cases hj : j < k
  · simp only [hj, ↓reduceIte, Nat.testBit_two_pow_sub_one, decide_true, Bool.and_true,
      Nat.zero_testBit, Bool.or_false]
  · simp only [hj, ↓reduceIte]
    rw [Nat.testBit_two_pow_mul_add _ hd, Nat.testBit_two_pow_mul_add _ h08,
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hb]
    by_cases hj8 : j - k < 8
    · simp only [hj8, ↓reduceIte, Nat.zero_testBit, Bool.and_false, Bool.false_or]
    · simp only [hj8, ↓reduceIte, Nat.zero_testBit, Nat.testBit_two_pow_sub_one, Bool.or_false]
      by_cases hj2 : j - k - 8 < 56 - k
      · simp only [hj2, decide_true, Bool.and_true]
      · simp only [hj2, decide_false, Bool.and_false]
        exact (testBit_lo hhi (by omega)).symm

/-- `ins_core` for a word `y` below `2 ^ 64`. -/
theorem ins_byte {y b k : Nat} (hy : y < 2 ^ 64) (hb : b < 2 ^ 8) (hk : k ≤ 56) :
    y &&& (2 ^ k * (2 ^ 8 * (2 ^ (56 - k) - 1) + 0) + (2 ^ k - 1)) |||
      (2 ^ k * (2 ^ 8 * 0 + b) + 0) =
      2 ^ k * (2 ^ 8 * (y / 2 ^ k / 2 ^ 8) + b) + y % 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have e1 : y = 2 ^ k * (2 ^ 8 * (y / 2 ^ k / 2 ^ 8) + y / 2 ^ k % 2 ^ 8) + y % 2 ^ k := by
    rw [Nat.div_add_mod (y / 2 ^ k) (2 ^ 8), Nat.div_add_mod y (2 ^ k)]
  have hhi : y / 2 ^ k / 2 ^ 8 < 2 ^ (56 - k) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hpos (by decide)),
      ← Nat.pow_add, ← Nat.pow_add, show 56 - k + (k + 8) = 64 by omega]
    exact hy
  conv => lhs; rw [e1]
  exact ins_core (Nat.mod_lt _ hpos) (Nat.mod_lt _ (by decide)) hb hhi

/-- Inserting byte 0 of a load into a word, as the unaligned load writes it. -/
theorem ins_0 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744073709551360 ||| bytes m a 1 =
      bytes m a 1 + y % 18446744073709551616 / 256 * 256 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 0) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, Nat.zero_add,
    Nat.add_zero, Nat.one_mul, Nat.div_one, Nat.mod_one] at this
  rw [this]
  omega

/-- Inserting byte 1 of a load into a word, as the unaligned load writes it. -/
theorem ins_8 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744073709486335 ||| bytes m a 1 * 256 % 18446744073709551616 =
      y % 256 + bytes m a 1 * 256 +
        y % 18446744073709551616 / 65536 * 65536 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 8) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 256 % 18446744073709551616 =
      256 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 2 of a load into a word, as the unaligned load writes it. -/
theorem ins_16 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744073692839935 ||| bytes m a 1 * 65536 % 18446744073709551616 =
      y % 65536 + bytes m a 1 * 65536 +
        y % 18446744073709551616 / 16777216 * 16777216 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 16) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 65536 % 18446744073709551616 =
      65536 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 3 of a load into a word, as the unaligned load writes it. -/
theorem ins_24 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744069431361535 ||| bytes m a 1 * 16777216 % 18446744073709551616 =
      y % 16777216 + bytes m a 1 * 16777216 +
        y % 18446744073709551616 / 4294967296 * 4294967296 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 24) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 16777216 % 18446744073709551616 =
      16777216 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 4 of a load into a word, as the unaligned load writes it. -/
theorem ins_32 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446742978492891135 ||| bytes m a 1 * 4294967296 % 18446744073709551616 =
      y % 4294967296 + bytes m a 1 * 4294967296 +
        y % 18446744073709551616 / 1099511627776 * 1099511627776 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 32) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 4294967296 % 18446744073709551616 =
      4294967296 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 5 of a load into a word, as the unaligned load writes it. -/
theorem ins_40 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446463698244468735 ||| bytes m a 1 * 1099511627776 % 18446744073709551616 =
      y % 1099511627776 + bytes m a 1 * 1099511627776 +
        y % 18446744073709551616 / 281474976710656 * 281474976710656 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 40) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 1099511627776 % 18446744073709551616 =
      1099511627776 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 6 of a load into a word, as the unaligned load writes it. -/
theorem ins_48 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18374967954648334335 ||| bytes m a 1 * 281474976710656 % 18446744073709551616 =
      y % 281474976710656 + bytes m a 1 * 281474976710656 +
        y % 18446744073709551616 / 72057594037927936 * 72057594037927936 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 48) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 281474976710656 % 18446744073709551616 =
      281474976710656 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 7 of a load into a word, as the unaligned load writes it. -/
theorem ins_56 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 72057594037927935 ||| bytes m a 1 * 72057594037927936 % 18446744073709551616 =
      y % 72057594037927936 + bytes m a 1 * 72057594037927936 +
        y % 18446744073709551616 / 18446744073709551616 * 18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 56) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 72057594037927936 % 18446744073709551616 =
      72057594037927936 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- The low byte of a word after the insertion of byte 0. -/
theorem ins_base (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    (y &&& 18446744073709551360 ||| bytes m a 1) % 256 = bytes m a 1 ∧
      (y &&& 18446744073709551360 ||| bytes m a 1) < 18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_0]
  omega

/-- The low bytes of a word after the insertion of byte 1, from those before it. -/
theorem ins_step_8 {v l : Nat} (h : v % 256 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446744073709486335 ||| bytes m a 1 * 256 % 18446744073709551616) %
        65536 = l + bytes m a 1 * 256 ∧
      v &&& 18446744073709486335 ||| bytes m a 1 * 256 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_8]
  omega

/-- The low bytes of a word after the insertion of byte 2, from those before it. -/
theorem ins_step_16 {v l : Nat} (h : v % 65536 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446744073692839935 ||| bytes m a 1 * 65536 % 18446744073709551616) %
        16777216 = l + bytes m a 1 * 65536 ∧
      v &&& 18446744073692839935 ||| bytes m a 1 * 65536 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_16]
  omega

/-- The low bytes of a word after the insertion of byte 3, from those before it. -/
theorem ins_step_24 {v l : Nat} (h : v % 16777216 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446744069431361535 ||| bytes m a 1 * 16777216 % 18446744073709551616) %
        4294967296 = l + bytes m a 1 * 16777216 ∧
      v &&& 18446744069431361535 ||| bytes m a 1 * 16777216 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_24]
  omega

/-- The low bytes of a word after the insertion of byte 4, from those before it. -/
theorem ins_step_32 {v l : Nat} (h : v % 4294967296 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446742978492891135 ||| bytes m a 1 * 4294967296 % 18446744073709551616) %
        1099511627776 = l + bytes m a 1 * 4294967296 ∧
      v &&& 18446742978492891135 ||| bytes m a 1 * 4294967296 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_32]
  omega

/-- The low bytes of a word after the insertion of byte 5, from those before it. -/
theorem ins_step_40 {v l : Nat} (h : v % 1099511627776 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446463698244468735 ||| bytes m a 1 * 1099511627776 % 18446744073709551616) %
        281474976710656 = l + bytes m a 1 * 1099511627776 ∧
      v &&& 18446463698244468735 ||| bytes m a 1 * 1099511627776 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_40]
  omega

/-- The low bytes of a word after the insertion of byte 6, from those before it. -/
theorem ins_step_48 {v l : Nat} (h : v % 281474976710656 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18374967954648334335 ||| bytes m a 1 * 281474976710656 % 18446744073709551616) %
        72057594037927936 = l + bytes m a 1 * 281474976710656 ∧
      v &&& 18374967954648334335 ||| bytes m a 1 * 281474976710656 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_48]
  omega

/-- The low bytes of a word after the insertion of byte 7, from those before it. -/
theorem ins_step_56 {v l : Nat} (h : v % 72057594037927936 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 72057594037927935 ||| bytes m a 1 * 72057594037927936 % 18446744073709551616) %
        18446744073709551616 = l + bytes m a 1 * 72057594037927936 ∧
      v &&& 72057594037927935 ||| bytes m a 1 * 72057594037927936 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_56]
  omega

/-- The word that an unaligned load assembles from its eight bytes, inserted one by one into the
word `y`, is their value as `bytes_split` writes it. -/
theorem ins_chain (y : Nat) (m : UInt64 → UInt8) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) :
    (((((((y &&& 18446744073709551360 ||| bytes m a0 1) &&& 18446744073709486335 |||
      bytes m a1 1 * 256 % 18446744073709551616) &&& 18446744073692839935 |||
      bytes m a2 1 * 65536 % 18446744073709551616) &&& 18446744069431361535 |||
      bytes m a3 1 * 16777216 % 18446744073709551616) &&& 18446742978492891135 |||
      bytes m a4 1 * 4294967296 % 18446744073709551616) &&& 18446463698244468735 |||
      bytes m a5 1 * 1099511627776 % 18446744073709551616) &&& 18374967954648334335 |||
      bytes m a6 1 * 281474976710656 % 18446744073709551616) &&& 72057594037927935 |||
      bytes m a7 1 * 72057594037927936 % 18446744073709551616 =
      bytes m a0 1 + bytes m a1 1 * 256 + bytes m a2 1 * 65536 + bytes m a3 1 * 16777216 +
        bytes m a4 1 * 4294967296 + bytes m a5 1 * 1099511627776 +
        bytes m a6 1 * 281474976710656 + bytes m a7 1 * 72057594037927936 := by
  obtain ⟨e0, l0⟩ := ins_base y m a0
  obtain ⟨e1, l1⟩ := ins_step_8 e0 l0 m a1
  obtain ⟨e2, l2⟩ := ins_step_16 e1 l1 m a2
  obtain ⟨e3, l3⟩ := ins_step_24 e2 l2 m a3
  obtain ⟨e4, l4⟩ := ins_step_32 e3 l3 m a4
  obtain ⟨e5, l5⟩ := ins_step_40 e4 l4 m a5
  obtain ⟨e6, l6⟩ := ins_step_48 e5 l5 m a6
  obtain ⟨e7, l7⟩ := ins_step_56 e6 l6 m a7
  exact (Nat.mod_eq_of_lt l7).symm.trans e7

/-! The model's side: `exec` of the form and the end of a path. -/

/-- `exec` of a doubleword load: the stack pointer's check passes, and the state loads the eight
bytes into register `t`. -/
theorem exec_ldr {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.ldr t n imm) s = some s') : s.spAligned n = true ∧
      s' = { s.setX t (load64 s.mem (s.xsp n + .ofNat (8 * imm.val))) with pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · rename_i h1
    rw [Bool.and_eq_true] at h1
    exact ⟨h1.1, (Option.some.inj hs).symm⟩
  · cases hs

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a doubleword load is `exec`'s,
whose state `hs` states.  An unaligned load inserts its bytes one by one into a word, and
`ins_chain` gives the word's value. -/
syntax "ldr_end " term:max : tactic
macro_rules
  | `(tactic| ldr_end $hs) => `(tactic| (
    done_end
    rw [$hs:term]
    simp (disch := omega) only [setX_eq_setRegAt, setRegAt_pc, load64_eq, addr_eq, addr_add,
      ins_chain, bytes_split, UInt64.reduceOfNat, UInt64.add_zero, UInt64.add_assoc,
      UInt64.reduceAdd, xsp_lt, xsp_31, setRegAt_31, setRegAt_lt, State.mk.injEq, and_true,
      true_and, and_self]))

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Xt, [Xn|SP, #(8 * imm)]` in RAM under `tcg`. -/
def ldrTcg : Footprint := isla_trace% "tests/isla/tcg/ldr"

isla_nodes ldrTcg

set_option maxRecDepth 100000 in
theorem ldrTcg_n0 : ldrTcg.trace = ldrTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; ldr_end hs'; done)
        | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; ldr_end hs'; done)
        | mem_side hσ [hn, ht]

/-- The trace of `LDR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldr_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] ldrTcg (memFields t n imm)
      (.ldr t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show ldrTcg.opcode = [.bits 10 0b1111100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := ldrTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrTcg_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Xt, [Xn|SP, #(8 * imm)]` in RAM under `kvm`. -/
def ldrKvm : Footprint := isla_trace% "tests/isla/kvm/ldr"

isla_nodes ldrKvm

set_option maxRecDepth 100000 in
theorem ldrKvm_n0 : ldrKvm.trace = ldrKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; ldr_end hs'; done)
             | mem_side hσ [hn, ht])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  without_info
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; ldr_end hs'; done)
             | mem_side hσ [hn, ht])

/-- The trace of `LDR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldr_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] ldrKvm (memFields t n imm)
      (.ldr t n imm) s := by
  refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
  · rw [show ldrKvm.opcode = [.bits 10 0b1111100101, .field "imm12" 12, .field "Rn" 5,
      .field "Rt" 5] from rfl]
    simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · have hc := ldrKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrKvm_bwd_x_r hc httbr hd ha hs hn ht

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.ldr_tcg
#print axioms TestSupport.A64.Isla.ldr_kvm
