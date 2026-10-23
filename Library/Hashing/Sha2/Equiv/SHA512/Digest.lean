import Library.Hashing.Sha2.Equiv.SHA512.Lift
import Library.Hashing.Sha2.Equiv.Common.Bytes
import Library.Hashing.Sha2.Equiv.Common.FromBits
import Mathlib.Tactic.IntervalCases

/-! # SHA-512 digest emission

Parallel to `equiv/SHA256/Digest.lean` at 64-bit words, 8 bytes per word,
64-byte (512-bit) full SHA-512 digest. -/

open SHS.Equiv.Bytes
open SHS.Equiv.FromBits
open SHS.Equiv.SHA512.Lift

open SHS.SHA512

namespace SHS.Equiv.SHA512.Digest

open scoped SHS.SHA512

/-- 64-byte digest viewed as a 512-bit MSB-first big-endian `BitVec`. -/
def digestBitVec512 (d : Vector UInt8 64) : BitVec 512 :=
  SHS.Word.fromBits (n := 512)
    (d.toList.flatMap fun b => byteToBits b)

/-- 8-word state → 64-byte big-endian digest. -/
def extractDigest512 (state : Impl.State) : Vector UInt8 64 :=
  Vector.ofFn fun i : Fin 64 =>
    let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
    let byteIdx := i.val % 8
    ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8

/-! ### Per-width `fromBits` 8-byte big-endian reconstruction -/

private theorem getLsbD_ifBit_pos {N : Nat} (hN : 0 < N) (x : Bool) (k : Nat) :
    (if x = true then (1 : BitVec N) else 0).getLsbD k = (decide (k = 0) && x) := by
  cases x <;> simp [BitVec.getLsbD_one, hN]

-- The 64-way `interval_cases i <;> simp` at the bottom of this proof
-- enumerates every bit position of a `BitVec 64`; each case unfolds
-- `byteToBits` plus the eight shifted bytes' `getLsbD`s, so the per-case
-- normalisation costs more than the default 200k-heartbeat budget.  This
-- is the *only* per-bit enumeration in the SHA-512 digest stack; all
-- wider widths (256 / 384 / 512) lift via `fromBits_setWidth_eq`.
set_option maxHeartbeats 1600000 in
/-- 64-bit ground identity: 8 BE bytes from a `UInt64` pack to `w.toBitVec`.
The only place a per-bit `interval_cases` (64 cases) runs in the SHA-512
digest stack; later widths lift via `fromBits_setWidth_eq`. -/
private theorem fromBits_8bytes_BE_64 (w : UInt64) :
    SHS.Word.fromBits (n := 64)
      (((List.range 8).map fun b =>
        ((w >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = w.toBitVec := by
  unfold byteToBits SHS.Word.fromBits
  simp only [show UInt64.ofNat ((7 - 0) * 8) = 56 from rfl,
    show UInt64.ofNat ((7 - 1) * 8) = 48 from rfl,
    show UInt64.ofNat ((7 - 2) * 8) = 40 from rfl,
    show UInt64.ofNat ((7 - 3) * 8) = 32 from rfl,
    show UInt64.ofNat ((7 - 4) * 8) = 24 from rfl,
    show UInt64.ofNat ((7 - 5) * 8) = 16 from rfl,
    show UInt64.ofNat ((7 - 6) * 8) = 8 from rfl,
    show UInt64.ofNat ((7 - 7) * 8) = 0 from rfl,
    List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_nil, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.foldl,
    UInt8.toNat_testBit_eq_getLsbD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    getLsbD_ifBit_pos (by decide : (0 : Nat) < 64)]
  interval_cases i <;> simp

private theorem flatMap_byteToBits_length (l : List UInt8) :
    (l.flatMap byteToBits).length = 8 * l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.length_append, byteToBits_length, ih,
      List.length_cons]
    omega

private theorem fromBits_byteToBits_length (w : UInt64) :
    (((List.range 8).map fun b =>
      ((w >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits).length = 64 := by
  rw [flatMap_byteToBits_length, List.length_map, List.length_range]

theorem fromBits_8bytes_BE_ge64 {N : Nat} (hN : 64 ≤ N) (w : UInt64) :
    SHS.Word.fromBits (n := N)
      (((List.range 8).map fun b =>
        ((w >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend N := by
  rw [← fromBits_setWidth_eq (M := 64) _ (by rw [fromBits_byteToBits_length])
        (by rw [fromBits_byteToBits_length]; exact hN),
      fromBits_8bytes_BE_64]

private theorem fromBits_8bytes_BE_512 (w : UInt64) :
    SHS.Word.fromBits (n := 512)
      (((List.range 8).map fun b =>
        ((w >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend 512 :=
  fromBits_8bytes_BE_ge64 (by decide) w

-- The RHS lists eight parallel `(List.range 8).map …` chunks, one per
-- word index 0..7; the per-word lines are intentionally aligned for
-- visual symmetry and breaking each across multiple lines hurts more
-- than it helps.
set_option linter.style.longLine false in
/-- The 64-byte BE digest list, restated as 8 eight-byte chunks. -/
private theorem digest_list_eq_8chunks (state : Impl.State) :
    (Vector.ofFn (n := 64) fun i : Fin 64 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8).toList =
      (((List.range 8).map fun b => ((state[(0 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(1 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(2 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(3 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(4 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(5 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(6 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(7 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8)) := by
  simp only [Vector.toList_ofFn, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

theorem digestBitVec512_extract (state : Impl.State) :
    digestBitVec512 (extractDigest512 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! ++ H[7]! := by
  unfold digestBitVec512 extractDigest512
  rw [digest_list_eq_8chunks]
  simp only [List.flatMap_append]
  rw [fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width]
  rw [fromBits_8bytes_BE_512, fromBits_8bytes_BE_512, fromBits_8bytes_BE_512,
      fromBits_8bytes_BE_512, fromBits_8bytes_BE_512, fromBits_8bytes_BE_512,
      fromBits_8bytes_BE_512, fromBits_8bytes_BE_512]
  simp only [flatMap_byteToBits_length, List.length_map, List.length_range,
    show (8 : Nat) * 8 = 64 from rfl]
  simp only [show (0 : Nat) = (0 : Fin 8).val from rfl,
             show (1 : Nat) = (1 : Fin 8).val from rfl,
             show (2 : Nat) = (2 : Fin 8).val from rfl,
             show (3 : Nat) = (3 : Fin 8).val from rfl,
             show (4 : Nat) = (4 : Fin 8).val from rfl,
             show (5 : Nat) = (5 : Fin 8).val from rfl,
             show (6 : Nat) = (6 : Fin 8).val from rfl,
             show (7 : Nat) = (7 : Fin 8).val from rfl,
             getElem!_toSpecState]
  generalize state[(0 : Fin 8)].toBitVec = w0
  generalize state[(1 : Fin 8)].toBitVec = w1
  generalize state[(2 : Fin 8)].toBitVec = w2
  generalize state[(3 : Fin 8)].toBitVec = w3
  generalize state[(4 : Fin 8)].toBitVec = w4
  generalize state[(5 : Fin 8)].toBitVec = w5
  generalize state[(6 : Fin 8)].toBitVec = w6
  generalize state[(7 : Fin 8)].toBitVec = w7
  rw [show (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7
            : BitVec (64+64+64+64+64+64+64+64))
       = (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7).setWidth 512 from
       by rw [BitVec.setWidth_eq]]
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib]

/-! ## SHA-384 digest emission (48 bytes = 6 words) -/

private theorem fromBits_8bytes_BE_384 (w : UInt64) :
    SHS.Word.fromBits (n := 384)
      (((List.range 8).map fun b =>
        ((w >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend 384 :=
  fromBits_8bytes_BE_ge64 (by decide) w

def digestBitVec384 (d : Vector UInt8 48) : BitVec 384 :=
  SHS.Word.fromBits (n := 384) (d.toList.flatMap fun b => byteToBits b)

def extractDigest384 (state : Impl.State) : Vector UInt8 48 :=
  Vector.ofFn fun i : Fin 48 =>
    let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
    let byteIdx := i.val % 8
    ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8

-- Same parallel per-word alignment as `digest_list_eq_8chunks`; six
-- chunks here (SHA-384 truncates to 48 bytes = 6 words).
set_option linter.style.longLine false in
private theorem digest384_list_eq_6chunks (state : Impl.State) :
    (Vector.ofFn (n := 48) fun i : Fin 48 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8).toList =
      (((List.range 8).map fun b => ((state[(0 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(1 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(2 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(3 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(4 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(5 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8)) := by
  simp only [Vector.toList_ofFn, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

theorem digestBitVec384_extract (state : Impl.State) :
    digestBitVec384 (extractDigest384 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! := by
  unfold digestBitVec384 extractDigest384
  rw [digest384_list_eq_6chunks]
  simp only [List.flatMap_append]
  rw [fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width, fromBits_append_same_width]
  rw [fromBits_8bytes_BE_384, fromBits_8bytes_BE_384, fromBits_8bytes_BE_384,
      fromBits_8bytes_BE_384, fromBits_8bytes_BE_384, fromBits_8bytes_BE_384]
  simp only [flatMap_byteToBits_length, List.length_map, List.length_range,
    show (8 : Nat) * 8 = 64 from rfl]
  simp only [show (0 : Nat) = (0 : Fin 8).val from rfl,
             show (1 : Nat) = (1 : Fin 8).val from rfl,
             show (2 : Nat) = (2 : Fin 8).val from rfl,
             show (3 : Nat) = (3 : Fin 8).val from rfl,
             show (4 : Nat) = (4 : Fin 8).val from rfl,
             show (5 : Nat) = (5 : Fin 8).val from rfl,
             getElem!_toSpecState]
  generalize state[(0 : Fin 8)].toBitVec = w0
  generalize state[(1 : Fin 8)].toBitVec = w1
  generalize state[(2 : Fin 8)].toBitVec = w2
  generalize state[(3 : Fin 8)].toBitVec = w3
  generalize state[(4 : Fin 8)].toBitVec = w4
  generalize state[(5 : Fin 8)].toBitVec = w5
  rw [show (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5
            : BitVec (64+64+64+64+64+64))
       = (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5).setWidth 384 from
       by rw [BitVec.setWidth_eq]]
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib]

/-! ## SHA-512/256 digest emission (32 bytes = 4 words) -/

private theorem fromBits_8bytes_BE_256 (w : UInt64) :
    SHS.Word.fromBits (n := 256)
      (((List.range 8).map fun b =>
        ((w >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend 256 :=
  fromBits_8bytes_BE_ge64 (by decide) w

def digestBitVec512_256 (d : Vector UInt8 32) : BitVec 256 :=
  SHS.Word.fromBits (n := 256) (d.toList.flatMap fun b => byteToBits b)

def extractDigest512_256 (state : Impl.State) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
    let byteIdx := i.val % 8
    ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8

-- Same parallel per-word alignment as `digest_list_eq_8chunks`; four
-- chunks here (SHA-512/256 truncates to 32 bytes = 4 words).
set_option linter.style.longLine false in
private theorem digest512_256_list_eq_4chunks (state : Impl.State) :
    (Vector.ofFn (n := 32) fun i : Fin 32 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8).toList =
      (((List.range 8).map fun b => ((state[(0 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(1 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(2 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 8).map fun b => ((state[(3 : Fin 8)] >>> (UInt64.ofNat ((7 - b) * 8))) &&& 0xff).toUInt8)) := by
  simp only [Vector.toList_ofFn, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

theorem digestBitVec512_256_extract (state : Impl.State) :
    digestBitVec512_256 (extractDigest512_256 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! := by
  unfold digestBitVec512_256 extractDigest512_256
  rw [digest512_256_list_eq_4chunks]
  simp only [List.flatMap_append]
  rw [fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width]
  rw [fromBits_8bytes_BE_256, fromBits_8bytes_BE_256, fromBits_8bytes_BE_256,
      fromBits_8bytes_BE_256]
  simp only [flatMap_byteToBits_length, List.length_map, List.length_range,
    show (8 : Nat) * 8 = 64 from rfl]
  simp only [show (0 : Nat) = (0 : Fin 8).val from rfl,
             show (1 : Nat) = (1 : Fin 8).val from rfl,
             show (2 : Nat) = (2 : Fin 8).val from rfl,
             show (3 : Nat) = (3 : Fin 8).val from rfl,
             getElem!_toSpecState]
  generalize state[(0 : Fin 8)].toBitVec = w0
  generalize state[(1 : Fin 8)].toBitVec = w1
  generalize state[(2 : Fin 8)].toBitVec = w2
  generalize state[(3 : Fin 8)].toBitVec = w3
  rw [show (w0 ++ w1 ++ w2 ++ w3
            : BitVec (64+64+64+64))
       = (w0 ++ w1 ++ w2 ++ w3).setWidth 256 from
       by rw [BitVec.setWidth_eq]]
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib]

/-! ## SHA-512/224 digest emission (28 bytes — crosses a word boundary)

Unlike the other variants, SHA-512/224 truncates to 224 bits which is
3.5 of the 64-bit hash words.  Rather than reconstruct the partial word
directly, we route through the SHA-512/256 (32-byte) emission and apply
`leftmost 224` via the universal `fromBits_leftmost` identity. -/

def digestBitVec512_224 (d : Vector UInt8 28) : BitVec 224 :=
  SHS.Word.fromBits (n := 224) (d.toList.flatMap fun b => byteToBits b)

def extractDigest512_224 (state : Impl.State) : Vector UInt8 28 :=
  Vector.ofFn fun i : Fin 28 =>
    let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
    let byteIdx := i.val % 8
    ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- The 28-byte SHA-512/224 extraction is the first 28 bytes of the 32-byte
SHA-512/256 extraction (same pointwise formula). -/
private theorem extract224_take_of_extract256 (state : Impl.State) :
    (extractDigest512_224 state).toList =
      (extractDigest512_256 state).toList.take 28 := by
  unfold extractDigest512_224 extractDigest512_256
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [Vector.toList_ofFn]

private theorem flatMap_byteToBits_take (l : List UInt8) (n : Nat) :
    (l.take n).flatMap byteToBits = (l.flatMap byteToBits).take (8 * n) := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [List.take_succ_cons, List.flatMap_cons]
      rw [show 8 * (m + 1) = (byteToBits hd).length + 8 * m from by
        rw [byteToBits_length]; ring]
      rw [List.take_append]
      rw [List.take_of_length_le (Nat.le_add_right _ _)]
      simp [byteToBits_length, ih]

theorem digestBitVec512_224_extract (state : Impl.State) :
    digestBitVec512_224 (extractDigest512_224 state) =
      (digestBitVec512_256 (extractDigest512_256 state)).leftmost 224 := by
  unfold digestBitVec512_224 digestBitVec512_256
  rw [extract224_take_of_extract256, flatMap_byteToBits_take]
  -- Goal: fromBits 224 (take 224 bits) = (fromBits 256 (all bits)).leftmost 224
  rw [fromBits_leftmost (M := 256) (N := 224)
        (bits := (extractDigest512_256 state).toList.flatMap byteToBits)
        (by rw [flatMap_byteToBits_length]; simp)
        (by decide)]

end SHS.Equiv.SHA512.Digest
