import Library.Hashing.Crc.Bitwise.Program
import Library.Hashing.Crc.Proof
import Library.Hashing.Words.Proof
import LeanExe.Requests.Records

/-! The bitwise functions of `Library.Hashing.Crc.Bitwise` equal the table program of
`Library.Hashing.Crc` for every argument.  A step of the division is linear over GF(2),
`bitStep_xor`, so eight steps of a register are eight steps of its bits above the low byte XORed
with eight steps of its low byte.  Eight steps of a register whose low byte is zero shift it right
by eight bits, `iterate_high`, and eight steps of each of the 256 bytes give that byte's entry of
`crc32Table`, which the kernel checks in `iterate_table`.  `crc32Reg_eq` follows: `crc32Reg` is
`byteStep crc32Table` for every register and byte.  `crc32Byte_eq` states that `crc32Byte` is
`crc32Update` of the one-word array of the byte with the count 1, and `crc32Word_eq` that
`crc32Word` is `crc32Update` of the byte-swapped word with the count `min n 8`.  Through
`Library.Hashing.Crc.Proof.crc32Update_spec`, `crc32Byte_spec` and `crc32Word_spec` give the CRC of
the transcription, the second for the bytes that `LeanExe.Requests.wordBytes` lists, which are
those of a word of a decoded record. -/

namespace Library.Hashing.Crc.Bitwise

open Library.Hashing.Crc Library.Bytes Library.Hashing.Words

/-! ## Steps -/

theorem toNat_and_ff (x : UInt64) : (x &&& 0xFF).toNat = x.toNat % 2 ^ 8 := by
  rw [UInt64.toNat_and, show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_shiftRight_one (z : UInt64) : (z >>> 1).toNat = z.toNat / 2 := by
  rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
    Nat.shiftRight_eq_div_pow, pow_one]

theorem and_one_cases (x : UInt64) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h
  · exact Or.inl (UInt64.toNat_inj.mp (by simp [h]))
  · exact Or.inr (UInt64.toNat_inj.mp (by simp [h]))

theorem xor_and_one (x y : UInt64) : (x ^^^ y) &&& 1 = (x &&& 1) ^^^ (y &&& 1) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  exact Bool.and_xor_distrib_right _ _ _

/-- The generator that a step XORs is linear in the register. -/
theorem select_xor (x y : UInt64) :
    ((x ^^^ y) &&& 1) * 0xEDB88320 =
      ((x &&& 1) * 0xEDB88320) ^^^ ((y &&& 1) * 0xEDB88320) := by
  rw [xor_and_one]
  rcases and_one_cases x with hx | hx <;> rcases and_one_cases y with hy | hy <;>
    rw [hx, hy] <;> decide

/-- A step of the division is linear over GF(2). -/
theorem bitStep_xor (x y : UInt64) : bitStep (x ^^^ y) = bitStep x ^^^ bitStep y := by
  simp only [bitStep]
  rw [UInt64.shiftRight_xor, select_xor]
  ac_rfl

theorem iterate_xor (j : Nat) (x y : UInt64) :
    bitStep^[j] (x ^^^ y) = bitStep^[j] x ^^^ bitStep^[j] y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      bitStep_xor, ih]

theorem bitStep_even {z : UInt64} (h : z.toNat % 2 = 0) : bitStep z = z >>> 1 := by
  have h0 : z &&& 1 = 0 := UInt64.toNat_inj.mp (by simp [h])
  simp only [bitStep, h0, UInt64.zero_mul, UInt64.xor_zero]

/-- Steps of a register whose low `j` bits are zero shift it right by `j` bits. -/
theorem iterate_even (j : Nat) (z : UInt64) (h : z.toNat % 2 ^ j = 0) :
    (bitStep^[j] z).toNat = z.toNat / 2 ^ j := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
    have hz : z.toNat = 2 * (2 ^ j * q) := by rw [hq, pow_succ']; ring
    rw [Function.iterate_succ_apply, bitStep_even (by rw [hz, Nat.mul_mod_right]),
      ih _ (by rw [toNat_shiftRight_one, hz, Nat.mul_div_cancel_left _ (by decide),
        Nat.mul_mod_right]),
      toNat_shiftRight_one, pow_succ', Nat.div_div_eq_div_mul]

/-- Eight steps from each byte give the byte's entry of `crc32Table`. -/
theorem iterate_table : ∀ k < 2 ^ 8, bitStep^[8] (UInt64.ofNat k) = crc32Table[k]! := by
  decide +kernel

theorem iterate_low (x : UInt64) :
    bitStep^[8] (x &&& 0xFF) = crc32Table[(x &&& 0xFF).toNat]! := by
  have h := iterate_table (x &&& 0xFF).toNat
    (by rw [toNat_and_ff]; exact Nat.mod_lt _ (Nat.two_pow_pos 8))
  rwa [UInt64.ofNat_toNat] at h

/-- Eight steps of a register whose low byte is cleared shift it right by eight bits. -/
theorem iterate_high (x : UInt64) : bitStep^[8] (x ^^^ (x &&& 0xFF)) = x >>> 8 := by
  have hx : (x ^^^ (x &&& 0xFF)).toNat = x.toNat ^^^ x.toNat % 2 ^ 8 := by
    rw [UInt64.toNat_xor, toNat_and_ff]
  apply UInt64.toNat_inj.mp
  rw [iterate_even 8 _ (by rw [hx, Nat.xor_mod_two_pow, Nat.mod_mod, Nat.xor_self]), hx,
    Nat.xor_div_two_pow, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 8)), Nat.xor_zero,
    UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl,
    Nat.shiftRight_eq_div_pow]

/-- `crc32Reg` is the table's step `byteStep crc32Table` for every register and byte. -/
theorem crc32Reg_eq (r b : UInt64) : crc32Reg r b = byteStep crc32Table r b := by
  have hsplit : ∀ x : UInt64, x = (x ^^^ (x &&& 0xFF)) ^^^ (x &&& 0xFF) := fun x => by
    rw [UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]
  have hb : (b &&& 0xFF) >>> 8 = 0 := UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_shiftRight, toNat_and_ff, show (8 : UInt64).toNat % 64 = 8 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 8))]
    rfl)
  have hhigh : (r ^^^ (b &&& 0xFF)) >>> 8 = r >>> 8 := by
    rw [UInt64.shiftRight_xor, hb, UInt64.xor_zero]
  have hlow : (r ^^^ (b &&& 0xFF)) &&& 0xFF = (r ^^^ b) &&& 0xFF := UInt64.toNat_inj.mp (by
    simp only [toNat_and_ff, UInt64.toNat_xor, Nat.xor_mod_two_pow, Nat.mod_mod])
  show bitStep^[8] (r ^^^ (b &&& 0xFF)) = byteStep crc32Table r b
  rw [hsplit (r ^^^ (b &&& 0xFF)), iterate_xor, iterate_high, iterate_low, hhigh, hlow]
  rfl

/-! ## The CRC of a byte and of a word -/

/-- A step of the table depends only on the low byte of its byte argument. -/
theorem byteStep_low (t : Array UInt64) (r u v : UInt64) (h : u.toNat % 2 ^ 8 = v.toNat % 2 ^ 8) :
    byteStep t r u = byteStep t r v := by
  have : ((r ^^^ u) &&& 0xFF).toNat = ((r ^^^ v) &&& 0xFF).toNat := by
    simp only [toNat_and_ff, UInt64.toNat_xor, Nat.xor_mod_two_pow, h]
  simp only [byteStep, this]

/-- The word of `updateWith`'s loop at index `i < 8` of a one-word array, shifted to its byte. -/
theorem word_byte (v : UInt64) (i : Nat) (hi : i < 8) :
    #[v][(UInt64.ofNat i >>> 3).toNat]! >>> ((UInt64.ofNat i &&& 7) <<< 3) =
      v >>> (8 * i).toUInt64 := by
  have hit : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hword : (UInt64.ofNat i >>> 3).toNat = 0 := by
    rw [UInt64.toNat_shiftRight, hit, show (3 : UInt64).toNat % 64 = 3 from rfl,
      Nat.shiftRight_eq_div_pow]
    omega
  have hshift : (UInt64.ofNat i &&& 7) <<< 3 = (8 * i).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, hit, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  rw [hword, hshift]
  rfl

theorem crc32Byte_eq (crc b : UInt64) : crc32Byte crc b = crc32Update crc #[b] 1 := by
  have h := word_byte b 0 (by omega)
  rw [show Nat.toUInt64 (8 * 0) = 0 from rfl, UInt64.shiftRight_zero] at h
  show crc32Reg ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF) b ^^^ (0xFFFFFFFF : UInt64) =
    byteStep crc32Table ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF)
      (#[b][(UInt64.ofNat 0 >>> 3).toNat]! >>> ((UInt64.ofNat 0 &&& 7) <<< 3)) ^^^ 0xFFFFFFFF
  rw [h, crc32Reg_eq]

/-- The step of `updateWith`'s loop with CRC-32's table over the one-word array `#[v]`. -/
def wordStep (v : UInt64) (i : Nat) (r : UInt64) : UInt64 :=
  byteStep crc32Table r (#[v][(UInt64.ofNat i >>> 3).toNat]! >>> ((UInt64.ofNat i &&& 7) <<< 3))

theorem fold_min_succ {α : Type} (N j : Nat) (F : Nat → α → α) (init : α) :
    Nat.fold (min N (j + 1)) (fun i _ s => F i s) init =
      if j < N then F j (Nat.fold (min N j) (fun i _ s => F i s) init)
      else Nat.fold (min N j) (fun i _ s => F i s) init := by
  by_cases h : j < N
  · rw [ite_eq_left h, show min N (j + 1) = j + 1 by omega, show min N j = j by omega,
      Nat.fold_succ]
  · rw [ite_eq_right h, show min N (j + 1) = min N j by omega]

/-- The conditional step `regIf k n` of `crc32Word` at position `j`, whose byte argument `v` has
the low byte of byte `7 - j` of `w`, extends the loop of `updateWith` over `#[bswap w]` from
`min n j` to `min n (j + 1)` indices. -/
theorem regIf_fold (n w r0 : UInt64) (j : Nat) (hj : j < 8) (k v : UInt64) (hk : k.toNat = j)
    (hv : v.toNat % 2 ^ 8 = (byteOf w (7 - j)).toNat) (x : UInt64)
    (hx : x = Nat.fold (min n.toNat j) (fun i _ s => wordStep (bswap w) i s) r0) :
    regIf k n x v = Nat.fold (min n.toNat (j + 1)) (fun i _ s => wordStep (bswap w) i s) r0 := by
  rw [fold_min_succ, ← hx]
  unfold regIf
  by_cases h : k < n
  · have h' : j < n.toNat := by rw [UInt64.lt_iff_toNat_lt, hk] at h; exact h
    rw [ite_eq_left h, ite_eq_left h', crc32Reg_eq, wordStep, word_byte _ _ hj]
    apply byteStep_low
    rw [hv, ← byteOf_bswap w j hj, byteOf, UInt64.toNat_toUInt8]
  · have h' : ¬ j < n.toNat := by rw [UInt64.lt_iff_toNat_lt, hk] at h; exact h
    rw [ite_eq_right h, ite_eq_right h']

theorem toNat_byteOf (w : UInt64) (k : Nat) :
    (byteOf w k).toNat = (w >>> (8 * k).toUInt64).toNat % 2 ^ 8 := by
  rw [byteOf, UInt64.toNat_toUInt8]

/-- `crc32Word` is `crc32Update` of the byte-swapped word, whose bytes from the least significant
are those of `w` from the most significant, with the count `min n 8`. -/
theorem crc32Word_eq (crc w n : UInt64) :
    crc32Word crc w n = crc32Update crc #[bswap w] (min n 8) := by
  have e0 : (crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF = Nat.fold (min n.toNat 0)
      (fun i _ s => wordStep (bswap w) i s) ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF) := by
    rw [Nat.min_zero, Nat.fold_zero]
  have e := regIf_fold n w _ 7 (by omega) 7 w rfl
    (by rw [toNat_byteOf, show Nat.toUInt64 (8 * (7 - 7)) = 0 from rfl, UInt64.shiftRight_zero]) _
    (regIf_fold n w _ 6 (by omega) 6 (w >>> 8) rfl (toNat_byteOf w 1).symm _
    (regIf_fold n w _ 5 (by omega) 5 (w >>> 16) rfl (toNat_byteOf w 2).symm _
    (regIf_fold n w _ 4 (by omega) 4 (w >>> 24) rfl (toNat_byteOf w 3).symm _
    (regIf_fold n w _ 3 (by omega) 3 (w >>> 32) rfl (toNat_byteOf w 4).symm _
    (regIf_fold n w _ 2 (by omega) 2 (w >>> 40) rfl (toNat_byteOf w 5).symm _
    (regIf_fold n w _ 1 (by omega) 1 (w >>> 48) rfl (toNat_byteOf w 6).symm _
    (regIf_fold n w _ 0 (by omega) 0 (w >>> 56) rfl (toNat_byteOf w 7).symm _ e0)))))))
  have h1 : crc32Word crc w n = Nat.fold (min n.toNat (7 + 1))
      (fun i _ s => wordStep (bswap w) i s) ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF) ^^^
        0xFFFFFFFF := by
    rw [← e]
    rfl
  rw [h1]
  unfold crc32Update updateWith LeanExe.loop
  rw [UInt64.toNat_min]
  rfl

/-! ## The transcription -/

/-- From CRC-32 of the bytes `A`, `crc32Byte` gives CRC-32 of `A` followed by the low byte of
`b`. -/
theorem crc32Byte_spec (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32 A)
    (b : UInt64) : (crc32Byte crc b).toNat = Spec.crc32 (A ++ [b.toUInt8]) := by
  have hm : Proof.messageBytes #[b] (1 : UInt64).toNat = [b.toUInt8] := by
    show [byteAt #[b] 0] = [b.toUInt8]
    rw [byteAt, show Nat.toUInt64 (8 * (0 % 8)) = 0 from rfl, show (#[b])[0 / 8]! = b from rfl,
      UInt64.shiftRight_zero]
  rw [crc32Byte_eq, Proof.crc32Update_spec A crc hcrc, hm]

/-- The first `k ≤ 8` bytes of `#[bswap w]` are the first `k` bytes of `w` from the most
significant. -/
theorem messageBytes_bswap (w : UInt64) (k : Nat) (hk : k ≤ 8) :
    Proof.messageBytes #[bswap w] k = (List.range k).map fun i => byteOf w (7 - i) := by
  unfold Proof.messageBytes
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have h := byteAt_eq #[bswap w] 0 i (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [h, show (#[bswap w])[0]! = bswap w from rfl, byteOf_bswap _ _ (by omega)]

/-- The byte of `w <<< 8` at position `j` from 1 to 7 is the byte of `w` at `j - 1`. -/
theorem byteOf_shl8 (w : UInt64) (j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ 7) :
    byteOf (w <<< 8) j = byteOf w (j - 1) := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases j <;>
    simp [byteOf, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_toUInt8] <;>
    interval_cases i <;> simp

/-- The bytes that `LeanExe.Requests.wordBytes` lists, at most eight, are the bytes of the word
from the most significant. -/
theorem wordBytes_map (w : UInt64) (k : Nat) (hk : k ≤ 8) :
    (LeanExe.Requests.wordBytes w k).map UInt64.toUInt8 =
      (List.range k).map fun i => byteOf w (7 - i) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [LeanExe.Requests.wordBytes, List.map_cons, ih _ (by omega), List.range_succ_eq_map,
      List.map_cons, List.map_map, show (w >>> 56).toUInt8 = byteOf w (7 - 0) from rfl]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    show byteOf (w <<< 8) (7 - i) = byteOf w (7 - (i + 1))
    rw [byteOf_shl8 _ _ (by omega) (by omega), show 7 - i - 1 = 7 - (i + 1) by omega]

/-- From CRC-32 of the bytes `A`, `crc32Word` gives CRC-32 of `A` followed by the first `n` bytes
of `w` from the most significant, at most eight, which `LeanExe.Requests.wordBytes` lists. -/
theorem crc32Word_spec (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32 A)
    (w n : UInt64) :
    (crc32Word crc w n).toNat =
      Spec.crc32 (A ++ (LeanExe.Requests.wordBytes w (min n.toNat 8)).map UInt64.toUInt8) := by
  rw [crc32Word_eq, Proof.crc32Update_spec A crc hcrc, UInt64.toNat_min,
    wordBytes_map _ _ (Nat.min_le_right _ _), show (8 : UInt64).toNat = 8 from rfl,
    messageBytes_bswap _ _ (Nat.min_le_right _ _)]

end Library.Hashing.Crc.Bitwise
