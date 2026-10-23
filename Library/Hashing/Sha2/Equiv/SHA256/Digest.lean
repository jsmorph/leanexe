import Library.Hashing.Sha2.Equiv.SHA256.Lift
import Library.Hashing.Sha2.Equiv.Common.Bytes
import Library.Hashing.Sha2.Equiv.Common.FromBits
import Mathlib.Tactic.IntervalCases

/-! # SHA-256 digest emission

Turn an 8-word `Impl.State` into a 32-byte big-endian digest, and prove
that this byte stream — read back into a `BitVec 256` via
`Word.fromBits` — equals the spec's `H[0]! ++ … ++ H[7]!`. -/

open SHS.Equiv.Bytes
open SHS.Equiv.FromBits
open SHS.Equiv.SHA256.Lift

open SHS.SHA256

namespace SHS.Equiv.SHA256.Digest

open scoped SHS.SHA256

/-- 32-byte digest viewed as a 256-bit MSB-first big-endian `BitVec`,
matching how the spec's `H[0]! ++ … ++ H[7]!` is laid out. -/
def digestBitVec (d : Vector UInt8 32) : BitVec 256 :=
  SHS.Word.fromBits (n := 256)
    (d.toList.flatMap fun b => byteToBits b)

/-- Common state-to-bytes extractor used by both `Impl.sha256` and
`implSha256Refactored`: each of the eight `UInt32` words emits four
big-endian bytes. -/
def extractDigest (state : Impl.State) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-! ### Per-width `fromBits` 4-byte big-endian reconstruction

The core identity — `fromBits N (4 bytes of w) = w.toBitVec.zeroExtend N`
— is proved once at the *small* ground width 32 and lifted to every
larger target via `fromBits_setWidth_eq`.  Future SHA-512-family digest
widths (512, 384, 224, 256 of 64-bit words) will follow the same shape:
a parallel `fromBits_8bytes_BE_64` ground lemma + the same universal
lift used by all four truncations.  This avoids re-running a per-width
`N`-way `interval_cases` at every digest size. -/

/-- Selector lemma at any positive width.  Width-generic so the same
body serves every SHA-2 digest width. -/
private theorem getLsbD_ifBit_pos {N : Nat} (hN : 0 < N) (x : Bool) (k : Nat) :
    (if x = true then (1 : BitVec N) else 0).getLsbD k = (decide (k = 0) && x) := by
  cases x <;> simp [BitVec.getLsbD_one, hN]

/-- 32-bit ground identity: at the *native* width of a `UInt32`, the
4-byte BE bit list packs back to exactly `w.toBitVec`.  This is the only
place `interval_cases` runs (32 cases, fast); every wider digest
specialisation lifts via `setWidth` without re-enumerating. -/
private theorem fromBits_4bytes_BE_32 (w : UInt32) :
    SHS.Word.fromBits (n := 32)
      (((List.range 4).map fun b =>
        ((w >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = w.toBitVec := by
  unfold byteToBits SHS.Word.fromBits
  simp only [show UInt32.ofNat ((3 - 0) * 8) = 24 from rfl,
    show UInt32.ofNat ((3 - 1) * 8) = 16 from rfl,
    show UInt32.ofNat ((3 - 2) * 8) = 8 from rfl,
    show UInt32.ofNat ((3 - 3) * 8) = 0 from rfl,
    List.range, List.range.loop, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_nil, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.foldl,
    UInt8.toNat_testBit_eq_getLsbD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    getLsbD_ifBit_pos (by decide : (0 : Nat) < 32)]
  interval_cases i <;> simp

private theorem flatMap_byteToBits_length (l : List UInt8) :
    (l.flatMap byteToBits).length = 8 * l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.length_append, byteToBits_length, ih,
      List.length_cons]
    omega

private theorem fromBits_byteToBits_length (w : UInt32) :
    (((List.range 4).map fun b =>
      ((w >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits).length = 32 := by
  rw [flatMap_byteToBits_length, List.length_map, List.length_range]

/-- 4-byte BE reconstruction at any width `N ≥ 32`.  One-line corollary
of the 32-bit ground identity plus the universal `fromBits_setWidth_eq`
lift: per-width cost is constant in `N`. -/
theorem fromBits_4bytes_BE_ge32 {N : Nat} (hN : 32 ≤ N) (w : UInt32) :
    SHS.Word.fromBits (n := N)
      (((List.range 4).map fun b =>
        ((w >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend N := by
  rw [← fromBits_setWidth_eq (M := 32) _ (by rw [fromBits_byteToBits_length])
        (by rw [fromBits_byteToBits_length]; exact hN),
      fromBits_4bytes_BE_32]

private theorem fromBits_4bytes_BE_256 (w : UInt32) :
    SHS.Word.fromBits (n := 256)
      (((List.range 4).map fun b =>
        ((w >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend 256 :=
  fromBits_4bytes_BE_ge32 (by decide) w

-- The RHS lists eight parallel `(List.range 4).map …` chunks, one per word
-- index 0..7; the per-word lines are intentionally aligned for visual symmetry
-- and breaking each across multiple lines hurts more than it helps.
set_option linter.style.longLine false in
/-- The 32-byte BE digest list, restated as 8 four-byte chunks. -/
private theorem digest_list_eq_8chunks (state : Impl.State) :
    (Vector.ofFn (n := 32) fun i : Fin 32 =>
        let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
        let byteIdx := i.val % 4
        ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8).toList =
      (((List.range 4).map fun b => ((state[(0 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(1 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(2 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(3 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(4 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(5 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(6 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(7 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8)) := by
  simp only [Vector.toList_ofFn, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

/-- Final byte-extraction emission matches the spec's `H[0]! ++ … ++ H[7]!`. -/
theorem digestBitVec_extract (state : Impl.State) :
    digestBitVec (extractDigest state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! ++ H[7]! := by
  unfold digestBitVec extractDigest
  rw [digest_list_eq_8chunks]
  simp only [List.flatMap_append]
  rw [fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width]
  rw [fromBits_4bytes_BE_256, fromBits_4bytes_BE_256, fromBits_4bytes_BE_256,
      fromBits_4bytes_BE_256, fromBits_4bytes_BE_256, fromBits_4bytes_BE_256,
      fromBits_4bytes_BE_256, fromBits_4bytes_BE_256]
  simp only [flatMap_byteToBits_length, List.length_map, List.length_range,
    show (8 : Nat) * 4 = 32 from rfl]
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
            : BitVec (32+32+32+32+32+32+32+32))
       = (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7).setWidth 256 from
       by rw [BitVec.setWidth_eq]]
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib]

/-! ## SHA-224 digest emission

Parallel `Word.fromBits ∘ byteToBits` story at width 224, consumed by
`Sha224.lean`'s top-level rewrite chain.  Same structure as the 256-bit
case: a per-word `fromBits_4bytes_BE_224` plus a 7-chunk split. -/

/-- 224-bit specialisation: same one-line corollary as `_256`. -/
private theorem fromBits_4bytes_BE_224 (w : UInt32) :
    SHS.Word.fromBits (n := 224)
      (((List.range 4).map fun b =>
        ((w >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8).flatMap byteToBits)
    = (w.toBitVec).zeroExtend 224 :=
  fromBits_4bytes_BE_ge32 (by decide) w

/-- 28-byte BE digest viewed as a 224-bit MSB-first big-endian `BitVec`. -/
def digestBitVec224 (d : Vector UInt8 28) : BitVec 224 :=
  SHS.Word.fromBits (n := 224)
    (d.toList.flatMap fun b => byteToBits b)

/-- SHA-224 digest extractor: same big-endian per-word byte layout as
`extractDigest`, restricted to the first seven words. -/
def extractDigest224 (state : Impl.State) : Vector UInt8 28 :=
  Vector.ofFn fun i : Fin 28 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

-- Parallel-aligned per-word chunks (same justification as
-- `digest_list_eq_8chunks` above, truncated to seven words).
set_option linter.style.longLine false in
/-- The 28-byte BE digest list, restated as 7 four-byte chunks (parallel
to `digest_list_eq_8chunks`, truncated to seven words). -/
private theorem digest224_list_eq_7chunks (state : Impl.State) :
    (Vector.ofFn (n := 28) fun i : Fin 28 =>
        let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
        let byteIdx := i.val % 4
        ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8).toList =
      (((List.range 4).map fun b => ((state[(0 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(1 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(2 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(3 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(4 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(5 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8) ++
       ((List.range 4).map fun b => ((state[(6 : Fin 8)] >>> (UInt32.ofNat ((3 - b) * 8))) &&& 0xff).toUInt8)) := by
  simp only [Vector.toList_ofFn, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rfl

/-- SHA-224 byte-extraction emission matches the spec's truncated
`H[0]! ++ … ++ H[6]!`.  Parallel to `digestBitVec_extract` with seven
four-byte chunks instead of eight. -/
theorem digestBitVec224_extract (state : Impl.State) :
    digestBitVec224 (extractDigest224 state) =
      let H := toSpecState state
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! := by
  unfold digestBitVec224 extractDigest224
  rw [digest224_list_eq_7chunks]
  simp only [List.flatMap_append]
  rw [fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width,
      fromBits_append_same_width, fromBits_append_same_width, fromBits_append_same_width]
  rw [fromBits_4bytes_BE_224, fromBits_4bytes_BE_224, fromBits_4bytes_BE_224,
      fromBits_4bytes_BE_224, fromBits_4bytes_BE_224, fromBits_4bytes_BE_224,
      fromBits_4bytes_BE_224]
  simp only [flatMap_byteToBits_length, List.length_map, List.length_range,
    show (8 : Nat) * 4 = 32 from rfl]
  simp only [show (0 : Nat) = (0 : Fin 8).val from rfl,
             show (1 : Nat) = (1 : Fin 8).val from rfl,
             show (2 : Nat) = (2 : Fin 8).val from rfl,
             show (3 : Nat) = (3 : Fin 8).val from rfl,
             show (4 : Nat) = (4 : Fin 8).val from rfl,
             show (5 : Nat) = (5 : Fin 8).val from rfl,
             show (6 : Nat) = (6 : Fin 8).val from rfl,
             getElem!_toSpecState]
  generalize state[(0 : Fin 8)].toBitVec = w0
  generalize state[(1 : Fin 8)].toBitVec = w1
  generalize state[(2 : Fin 8)].toBitVec = w2
  generalize state[(3 : Fin 8)].toBitVec = w3
  generalize state[(4 : Fin 8)].toBitVec = w4
  generalize state[(5 : Fin 8)].toBitVec = w5
  generalize state[(6 : Fin 8)].toBitVec = w6
  rw [show (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6
            : BitVec (32+32+32+32+32+32+32))
       = (w0 ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6).setWidth 224 from
       by rw [BitVec.setWidth_eq]]
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib]

end SHS.Equiv.SHA256.Digest
