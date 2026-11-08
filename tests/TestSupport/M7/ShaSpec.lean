import TestSupport.M7.Sha
import Library.Hashing.Sha256.Proof

/-!
The record machine of the SHA-256 step against FIPS 180-4.  `machRun (shaSpec roundConstants)
sha0` keeps the chaining value of the blocks so far and answers each block with the digest of
every block so far, and `shaSpec_fips` states that each answer, read as 32 bytes, has as its
256-bit value the digest that `SHS.SHA256.sha256` of `Library/Hashing/Sha2/Spec` gives for the
bits of those blocks, for fewer than 2^55 blocks.  The proof places the blocks' words, with their
bytes reversed, in the array of bytes packed eight to a word that the library's `sha256` takes,
so that `hashFrom` compresses the same blocks and the same padding block as the machine, and it
applies `sha256_spec`.
-/

namespace TestSupport.M7.Sha

open Library.Hashing.Words Library.Hashing.Sha256 Library.Bytes LeanExe.Requests
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Pipeline

/-! ## Words -/

theorem toNat_ofNat64 {a : Nat} (h : a < 2 ^ 64) : (UInt64.ofNat a).toNat = a := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem ofNat_add_one {a : Nat} (h : a + 1 < 2 ^ 64) :
    UInt64.ofNat a + 1 = UInt64.ofNat (a + 1) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, toNat_ofNat64 (by omega), toNat_ofNat64 h,
    show (1 : UInt64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

theorem ofNat_sub_one {a : Nat} (h1 : 1 ≤ a) (h : a < 2 ^ 64) :
    UInt64.ofNat a - 1 = UInt64.ofNat (a - 1) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le, toNat_ofNat64 h, toNat_ofNat64 (by omega)]
  all_goals first
    | rfl
    | (rw [UInt64.le_iff_toNat_le, toNat_ofNat64 h]; exact h1)

theorem ofNat_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a == UInt64.ofNat b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : UInt64.ofNat a ≠ UInt64.ofNat b := fun e => h (by
      have := congrArg UInt64.toNat e
      rwa [toNat_ofNat64 ha, toNat_ofNat64 hb] at this)
    simp [h, hne]

theorem ofNat_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, toNat_ofNat64 ha, toNat_ofNat64 hb]

theorem ofNat_shiftRight {a : Nat} (k : Nat) (ha : a < 2 ^ 64) (hk : k < 64) :
    UInt64.ofNat a >>> UInt64.ofNat k = UInt64.ofNat (a / 2 ^ k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_ofNat64 ha, toNat_ofNat64 (by omega),
    toNat_ofNat64 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]

theorem ofNat_shiftLeft {a : Nat} (k : Nat) (hk : k < 64) (h : a * 2 ^ k < 2 ^ 64) :
    UInt64.ofNat a <<< UInt64.ofNat k = UInt64.ofNat (a * 2 ^ k) := by
  have ha : a < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, toNat_ofNat64 ha, toNat_ofNat64 (by omega), toNat_ofNat64 h,
    Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem ofNat_and_low {a : Nat} (k : Nat) (ha : a < 2 ^ 64) (hk : 2 ^ k - 1 < 2 ^ 64) :
    UInt64.ofNat a &&& UInt64.ofNat (2 ^ k - 1) = UInt64.ofNat (a % 2 ^ k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_ofNat64 ha, toNat_ofNat64 hk,
    toNat_ofNat64 (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha), Nat.and_two_pow_sub_one_eq_mod]

theorem half_ofNat (w : UInt64) {a : Nat} (ha : a < 2 ^ 64) :
    half w (UInt64.ofNat a) = if a % 2 = 0 then w >>> 32 else low32 w := by
  unfold half
  rw [show (1 : UInt64) = UInt64.ofNat (2 ^ 1 - 1) from rfl, ofNat_and_low 1 ha (by decide),
    Nat.pow_one, show (0 : UInt64) = UInt64.ofNat 0 from rfl, ofNat_beq (by omega) (by decide)]
  by_cases h : a % 2 = 0 <;> simp [h]

theorem bswap_bswap (w : UInt64) : bswap (bswap w) = w := by
  rw [bswap_eq (bswap w), byteOf_bswap _ 0 (by decide), byteOf_bswap _ 1 (by decide),
    byteOf_bswap _ 2 (by decide), byteOf_bswap _ 3 (by decide), byteOf_bswap _ 4 (by decide),
    byteOf_bswap _ 5 (by decide), byteOf_bswap _ 6 (by decide), byteOf_bswap _ 7 (by decide),
    byteOf_eq, byteOf_eq, byteOf_eq, byteOf_eq, byteOf_eq, byteOf_eq, byteOf_eq, byteOf_eq]
  exact be8_bytes w

/-! ## Bytes -/

set_option maxHeartbeats 1600000 in
/-- Byte `r` of a word, most significant first, is byte `7 - r` counting from the least
significant. -/
theorem wordBytes_byte (w : UInt64) (r : Nat) (hr : r < 8) :
    ((wordBytes w 8)[r]!).toUInt8 = byteOf w (7 - r) := by
  interval_cases r <;>
    (simp only [wordBytes]
     apply UInt8.toBitVec_inj.mp
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp [byteOf, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt8]
     all_goals (interval_cases i <;> simp))

theorem length_wordBytes (w : UInt64) (k : Nat) : (wordBytes w k).length = k := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => simp [wordBytes, ih]

theorem wordBytes_lt (w : UInt64) (r : Nat) (hr : r < 8) : ((wordBytes w 8)[r]!).toNat < 256 := by
  interval_cases r <;>
    (simp only [wordBytes]
     exact top_byte _)

set_option maxHeartbeats 1600000 in
/-- The bytes of a digest word, the 32-bit words of `a` and `b` in its high and low halves. -/
theorem byteOf_digestWord (a b : UInt64) (k : Nat) (hk : k < 8) :
    byteOf ((low32 a <<< 32) ||| low32 b) k =
      if 4 ≤ k then byte32 a.toUInt32 (k - 4) else byte32 b.toUInt32 k := by
  interval_cases k <;>
    (simp only [show ¬ (4 ≤ 0) by decide, show ¬ (4 ≤ 1) by decide, show ¬ (4 ≤ 2) by decide,
       show ¬ (4 ≤ 3) by decide, show 4 ≤ 4 by decide, show 4 ≤ 5 by decide,
       show 4 ≤ 6 by decide, show 4 ≤ 7 by decide, ↓reduceIte]
     apply UInt8.toBitVec_inj.mp
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp [byteOf, byte32, low32, UInt64.toBitVec_or, UInt64.toBitVec_and,
       UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt8,
       UInt32.toBitVec_shiftRight, UInt32.toBitVec_toUInt8, UInt64.toBitVec_toUInt32]
     interval_cases i <;> simp)

/-! ## Lists of pieces of eight -/

/-- Element `8 a + b` of a list of pieces of 8 elements is element `b` of piece `a`. -/
theorem getElem?_flatMap8 {β γ : Type} (f : β → List γ) :
    ∀ (l : List β), (∀ x ∈ l, (f x).length = 8) → ∀ (a b : Nat), b < 8 →
      (l.flatMap f)[8 * a + b]? = (l[a]?).bind fun x => (f x)[b]?
  | [], _, a, b, _ => by simp
  | x :: xs, hf, 0, b, hb => by
      rw [List.flatMap_cons, List.getElem?_append_left (by rw [hf x (by simp)]; omega)]
      simp
  | x :: xs, hf, a + 1, b, hb => by
      rw [List.flatMap_cons, List.getElem?_append_right (by rw [hf x (by simp)]; omega),
        hf x (by simp), show 8 * (a + 1) + b - 8 = 8 * a + b by omega,
        getElem?_flatMap8 f xs (fun y hy => hf y (by simp [hy])) a b hb]
      simp

theorem length_flatMap8 {β γ : Type} (f : β → List γ) :
    ∀ (l : List β), (∀ x ∈ l, (f x).length = 8) → (l.flatMap f).length = 8 * l.length
  | [], _ => rfl
  | x :: xs, hf => by
      rw [List.flatMap_cons, List.length_append, hf x (by simp),
        length_flatMap8 f xs (fun y hy => hf y (by simp [hy])), List.length_cons]
      omega

theorem flatMap_recordBytes (recs : List (List UInt64)) :
    recs.flatMap recordBytes = recs.flatten.flatMap fun w => wordBytes w 8 := by
  induction recs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.flatMap_cons, List.flatten_cons, List.flatMap_append, ih, recordBytes]

theorem eight {r : List UInt64} (h : r.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, r = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  rcases r with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, r⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩

/-! ## The machine -/

/-- The chaining value after the blocks `recs` from the hash value `h`. -/
def chain (h : Words8) (recs : List (List UInt64)) : Words8 :=
  recs.foldl (fun h r => compress roundConstants h (blockWords (inOfList r))) h

/-- The digest words of the blocks `recs`: their chaining value compressed with the padding block
of a message of 64 bytes for each block. -/
def digestOf (recs : List (List UInt64)) : Words4 :=
  digestWords (compress roundConstants (chain iv256 recs)
    (padWords (UInt64.ofNat (64 * recs.length))))

theorem chain_append (h : Words8) (recs : List (List UInt64)) (r : List UInt64) :
    chain h (recs ++ [r]) = compress roundConstants (chain h recs) (blockWords (inOfList r)) := by
  simp [chain, List.foldl_append]

theorem shaSpec_eq (s : ShaState) (r : List UInt64) :
    shaSpec roundConstants s r =
      (⟨compress roundConstants s.h (blockWords (inOfList r)), s.blocks + 1⟩,
        outList (digestWords (compress roundConstants
          (compress roundConstants s.h (blockWords (inOfList r)))
          (padWords ((s.blocks + 1) <<< 6))))) := rfl

/-- The machine's state after the blocks `recs` is their chaining value and their number, and its
answer to block `i` is the digest words of blocks 0 to `i`. -/
theorem machRun_sha (recs : List (List UInt64)) (hn : recs.length < 2 ^ 58) :
    machRun (shaSpec roundConstants) sha0 recs =
      (⟨chain iv256 recs, UInt64.ofNat recs.length⟩,
        (List.range recs.length).map fun i => outList (digestOf (recs.take (i + 1)))) := by
  induction recs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
      rw [List.length_append, List.length_singleton] at hn
      rw [machRun_append, ih (by omega)]
      have e1 : UInt64.ofNat rs.length + 1 = UInt64.ofNat (rs.length + 1) :=
        ofNat_add_one (by omega)
      have e2 : (UInt64.ofNat rs.length + 1) <<< 6 = UInt64.ofNat (64 * (rs.length + 1)) := by
        rw [e1, show (6 : UInt64) = UInt64.ofNat 6 from rfl,
          ofNat_shiftLeft 6 (by decide) (by omega)]
        exact congrArg UInt64.ofNat (by simp only [Nat.reducePow]; omega)
      rw [shaSpec_eq]
      dsimp only
      refine Prod.ext ?_ ?_
      · rw [chain_append, e1, List.length_append, List.length_singleton]
      · dsimp only
        rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
          List.map_singleton]
        refine congrArg₂ HAppend.hAppend (List.map_congr_left fun i hi => ?_)
          (congrArg (fun x => [x]) ?_)
        · rw [List.mem_range] at hi
          rw [List.take_append_of_le_length (by omega)]
        · rw [List.take_of_length_le (by simp), digestOf, chain_append, List.length_append,
            List.length_singleton, e2]

/-! ## The library's message -/

/-- The words of the blocks `recs` with their bytes reversed: the blocks' bytes packed eight to a
word, the first byte least significant, as the library's `sha256` takes a message. -/
def blockMsg (recs : List (List UInt64)) : Array UInt64 := (recs.flatten.map bswap).toArray

theorem blockMsg_get {recs : List (List UInt64)} {i : Nat} {w : UInt64}
    (h : recs.flatten[i]? = some w) : (blockMsg recs)[i]! = bswap w := by
  rw [getElem!_def]
  simp only [blockMsg, List.getElem?_toArray, List.getElem?_map, h, Option.map_some]

theorem flatten_get {recs : List (List UInt64)} (h8 : ∀ r ∈ recs, r.length = 8) {j k : Nat}
    (hk : k < 8) : recs.flatten[8 * j + k]? = (recs[j]?).bind fun r => r[k]? := by
  have e := getElem?_flatMap8 id recs h8 j k hk
  rwa [List.flatMap_id] at e

/-- Word `i` of the padded message, for a word of the message's `M` blocks. -/
theorem paddedWord_msg (msg : Array UInt64) {M i : Nat} (hM : M < 2 ^ 55) (hi : i < 16 * M) :
    paddedWord msg (UInt64.ofNat (64 * M)) (UInt64.ofNat (64 * M)) (UInt64.ofNat (16 * M + 15))
        (UInt64.ofNat i) =
      half (bswap msg[i / 2]!) (UInt64.ofNat i) := by
  have h1 : (UInt64.ofNat i == UInt64.ofNat (16 * M + 15)) = false := by
    rw [ofNat_beq (by omega) (by omega)]; simp; omega
  have h2 : (UInt64.ofNat i + 1 == UInt64.ofNat (16 * M + 15)) = false := by
    rw [ofNat_add_one (by omega), ofNat_beq (by omega) (by omega)]; simp; omega
  have h3 : UInt64.ofNat (64 * M) >>> 2 = UInt64.ofNat (16 * M) := by
    rw [show (2 : UInt64) = UInt64.ofNat 2 from rfl, ofNat_shiftRight 2 (by omega) (by decide)]
    exact congrArg UInt64.ofNat (by simp only [Nat.reducePow]; omega)
  have h4 : UInt64.ofNat i < UInt64.ofNat (16 * M) := (ofNat_lt (by omega) (by omega)).mpr hi
  have h5 : (UInt64.ofNat i >>> 1).toNat = i / 2 := by
    rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_shiftRight 1 (by omega) (by decide),
      toNat_ofNat64 (by omega), Nat.pow_one]
  simp only [paddedWord, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]

/-- Word `16 M + t` of the padded message of `M` blocks, a word of its padding block. -/
theorem paddedWord_pad (msg : Array UInt64) {M t : Nat} (hM : M < 2 ^ 55) (ht : t < 16) :
    paddedWord msg (UInt64.ofNat (64 * M)) (UInt64.ofNat (64 * M)) (UInt64.ofNat (16 * M + 15))
        (UInt64.ofNat (16 * M + t)) =
      if t = 15 then low32 (UInt64.ofNat (64 * M) <<< 3)
      else if t = 14 then low32 (UInt64.ofNat (64 * M) >>> 29)
      else if t = 0 then 0x80000000 else 0 := by
  have h1 : (UInt64.ofNat (16 * M + t) == UInt64.ofNat (16 * M + 15)) = decide (t = 15) := by
    rw [ofNat_beq (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have h2 : (UInt64.ofNat (16 * M + t) + 1 == UInt64.ofNat (16 * M + 15)) = decide (t = 14) := by
    rw [ofNat_add_one (by omega), ofNat_beq (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have h3 : UInt64.ofNat (64 * M) >>> 2 = UInt64.ofNat (16 * M) := by
    rw [show (2 : UInt64) = UInt64.ofNat 2 from rfl, ofNat_shiftRight 2 (by omega) (by decide)]
    exact congrArg UInt64.ofNat (by simp only [Nat.reducePow]; omega)
  have h4 : ¬ UInt64.ofNat (16 * M + t) < UInt64.ofNat (16 * M) := by
    rw [ofNat_lt (by omega) (by omega)]; omega
  have h5 : (UInt64.ofNat (16 * M + t) == UInt64.ofNat (16 * M)) = decide (t = 0) := by
    rw [ofNat_beq (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have h6 : (UInt64.ofNat (64 * M) &&& 7) <<< 3 = 0 := by
    rw [show (7 : UInt64) = UInt64.ofNat (2 ^ 3 - 1) from rfl, ofNat_and_low 3 (by omega)
      (by decide), show 64 * M % 2 ^ 3 = 0 by omega]
    rfl
  simp only [paddedWord, h1, h2, h3, h4, h5, h6, decide_eq_true_eq, ↓reduceIte]
  by_cases t15 : t = 15
  · simp [t15]
  by_cases t14 : t = 14
  · simp [t14]
  by_cases t0 : t = 0
  · subst t0
    simp only [t15, t14, ↓reduceIte, Nat.add_zero]
    have hz : ∀ x : UInt64, (x &&& (((1 : UInt64) <<< (0 : UInt64)) - 1)) |||
        ((0x80 : UInt64) <<< (0 : UInt64)) = 0x80 := by
      intro x
      apply UInt64.toBitVec_inj.mp
      simp
    rw [hz, half_ofNat _ (by omega), ite_eq_left (by omega : 16 * M % 2 = 0)]
    rfl
  · simp [t15, t14, t0]

/-- The sixteen words of `loadBlock`, each the padded message's word at `base` plus its index. -/
theorem loadBlock_fields (msg : Array UInt64) (n len last base : UInt64) :
    loadBlock msg n len last base =
      ⟨paddedWord msg n len last base, paddedWord msg n len last (base + UInt64.ofNat 1),
        paddedWord msg n len last (base + UInt64.ofNat 2),
        paddedWord msg n len last (base + UInt64.ofNat 3),
        paddedWord msg n len last (base + UInt64.ofNat 4),
        paddedWord msg n len last (base + UInt64.ofNat 5),
        paddedWord msg n len last (base + UInt64.ofNat 6),
        paddedWord msg n len last (base + UInt64.ofNat 7),
        paddedWord msg n len last (base + UInt64.ofNat 8),
        paddedWord msg n len last (base + UInt64.ofNat 9),
        paddedWord msg n len last (base + UInt64.ofNat 10),
        paddedWord msg n len last (base + UInt64.ofNat 11),
        paddedWord msg n len last (base + UInt64.ofNat 12),
        paddedWord msg n len last (base + UInt64.ofNat 13),
        paddedWord msg n len last (base + UInt64.ofNat 14),
        paddedWord msg n len last (base + UInt64.ofNat 15)⟩ := rfl

/-- The words that `loadBlock` reads for block `j` of the message of the blocks `recs` are the
block's words that `blockWords` gives. -/
theorem loadBlock_msg {recs : List (List UInt64)} (h8 : ∀ r ∈ recs, r.length = 8)
    (hM : recs.length < 2 ^ 55) {j : Nat} (hj : j < recs.length) :
    loadBlock (blockMsg recs) (UInt64.ofNat (64 * recs.length)) (UInt64.ofNat (64 * recs.length))
        (UInt64.ofNat (16 * recs.length + 15)) (UInt64.ofNat j <<< 4) =
      blockWords (inOfList recs[j]) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hr⟩ := eight (h8 _ (List.getElem_mem hj))
  have hw : ∀ k (hk : k < 8), (blockMsg recs)[8 * j + k]! =
      bswap ([a0, a1, a2, a3, a4, a5, a6, a7][k]'(by simp; omega)) := fun k hk =>
    blockMsg_get (by rw [flatten_get h8 hk, List.getElem?_eq_getElem hj, hr]; simp)
  have key : ∀ t (ht : t < 16),
      paddedWord (blockMsg recs) (UInt64.ofNat (64 * recs.length))
          (UInt64.ofNat (64 * recs.length)) (UInt64.ofNat (16 * recs.length + 15))
          ((UInt64.ofNat j <<< 4) + UInt64.ofNat t) =
        if t % 2 = 0 then [a0, a1, a2, a3, a4, a5, a6, a7][t / 2]! >>> 32
        else low32 [a0, a1, a2, a3, a4, a5, a6, a7][t / 2]! := by
    intro t ht
    rw [base_add j t (by omega), paddedWord_msg _ hM (by omega),
      show (16 * j + t) / 2 = 8 * j + t / 2 by omega, hw _ (by omega), bswap_bswap,
      half_ofNat _ (by omega), show (16 * j + t) % 2 = t % 2 by omega,
      getElem!_pos [a0, a1, a2, a3, a4, a5, a6, a7] (t / 2) (by simp; omega)]
  have key0 := key 0 (by decide)
  rw [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at key0
  rw [loadBlock_fields, key0, key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide), key 8 (by decide),
    key 9 (by decide), key 10 (by decide), key 11 (by decide), key 12 (by decide),
    key 13 (by decide), key 14 (by decide), key 15 (by decide), hr]
  simp [inOfList, blockWords]

/-- The words that `loadBlock` reads after the message's `M` blocks are the padding block. -/
theorem loadBlock_pad (msg : Array UInt64) {M : Nat} (hM : M < 2 ^ 55) :
    loadBlock msg (UInt64.ofNat (64 * M)) (UInt64.ofNat (64 * M)) (UInt64.ofNat (16 * M + 15))
        (UInt64.ofNat M <<< 4) =
      padWords (UInt64.ofNat (64 * M)) := by
  have key : ∀ t (ht : t < 16),
      paddedWord msg (UInt64.ofNat (64 * M)) (UInt64.ofNat (64 * M))
          (UInt64.ofNat (16 * M + 15)) ((UInt64.ofNat M <<< 4) + UInt64.ofNat t) =
        if t = 15 then low32 (UInt64.ofNat (64 * M) <<< 3)
        else if t = 14 then low32 (UInt64.ofNat (64 * M) >>> 29)
        else if t = 0 then 0x80000000 else 0 := fun t ht => by
    rw [base_add M t (by omega), paddedWord_pad _ hM ht]
  have key0 := key 0 (by decide)
  rw [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at key0
  rw [loadBlock_fields, key0, key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide), key 8 (by decide),
    key 9 (by decide), key 10 (by decide), key 11 (by decide), key 12 (by decide),
    key 13 (by decide), key 14 (by decide), key 15 (by decide)]
  simp [padWords]

/-- The library's final hash value of the message of the blocks `recs` is the machine's chaining
value compressed with the padding block. -/
theorem hashFrom_blocks {recs : List (List UInt64)} (h8 : ∀ r ∈ recs, r.length = 8)
    (hM : recs.length < 2 ^ 55) :
    hashFrom roundConstants iv256 (blockMsg recs) (UInt64.ofNat (64 * recs.length))
        (UInt64.ofNat (64 * recs.length)) =
      compress roundConstants (chain iv256 recs) (padWords (UInt64.ofNat (64 * recs.length))) := by
  have hn : (UInt64.ofNat (64 * recs.length)).toNat < 2 ^ 61 := by
    rw [toNat_ofNat64 (by omega)]; omega
  have hb : (UInt64.ofNat (64 * recs.length) >>> 6) +
      (if (UInt64.ofNat (64 * recs.length) &&& 63) < 56 then (1 : UInt64) else 2) =
        UInt64.ofNat (recs.length + 1) := by
    apply UInt64.toNat_inj.mp
    rw [blocks_toNat _ hn, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega)]
    unfold blockCount
    split <;> omega
  have hl : (UInt64.ofNat (recs.length + 1) <<< 4) - 1 = UInt64.ofNat (16 * recs.length + 15) := by
    rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, ofNat_shiftLeft 4 (by decide) (by omega),
      ofNat_sub_one (by omega) (by omega)]
    exact congrArg UInt64.ofNat (by simp only [Nat.reducePow]; omega)
  have hk : ∀ k, k ≤ recs.length →
      Nat.fold k (fun i _ s => compress roundConstants s
          (loadBlock (blockMsg recs) (UInt64.ofNat (64 * recs.length))
            (UInt64.ofNat (64 * recs.length)) (UInt64.ofNat (16 * recs.length + 15))
            (UInt64.ofNat i <<< 4))) iv256 =
        chain iv256 (recs.take k) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Nat.fold_succ, ih (by omega), loadBlock_msg h8 hM (by omega),
        List.take_succ_eq_append_getElem (by omega), chain_append]
  unfold hashFrom
  dsimp only
  rw [hb, hl, LeanExe.loop, toNat_ofNat64 (by omega), Nat.fold_succ, loadBlock_pad _ hM]
  have := hk recs.length (Nat.le_refl _)
  rw [List.take_length] at this
  exact congrArg (fun h => compress roundConstants h (padWords (UInt64.ofNat (64 * recs.length))))
    this

/-! ## The digest -/

/-- The 32 bytes of a digest record of four words, the most significant first. -/
def digestVec (ws : List UInt64) : Vector UInt8 32 :=
  Vector.ofFn fun j => ((recordBytes ws)[j.val]!).toUInt8

/-- The bytes of a list of byte values. -/
def byteArrayOf (bs : List UInt64) : ByteArray := ⟨(bs.map UInt64.toUInt8).toArray⟩

theorem getElem!_flatMap8 {β γ : Type} [Inhabited γ] (f : β → List γ) (l : List β)
    (hf : ∀ x ∈ l, (f x).length = 8) {a b : Nat} (ha : a < l.length) (hb : b < 8) :
    (l.flatMap f)[8 * a + b]! = (f l[a])[b]! := by
  rw [getElem!_def, getElem?_flatMap8 f l hf a b hb, List.getElem?_eq_getElem ha,
    Option.bind_some, getElem!_def]

/-- The library's digest bytes of the final hash value `d` are the bytes of the digest record
that `digestWords` gives. -/
theorem bytes_digest (d : Words8) :
    Words4.bytes 32 ⟨pair d.w0 d.w1, pair d.w2 d.w3, pair d.w4 d.w5, pair d.w6 d.w7⟩ =
      digestVec (outList (digestWords d)) := by
  apply Vector.ext
  intro j hj
  rw [Words4.bytes, Vector.getElem_ofFn, digestVec, Vector.getElem_ofFn]
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r, j = 8 * q + r ∧ r < 8 := ⟨j / 8, j % 8, by omega, by omega⟩
  have hq : q < 4 := by omega
  have key : ∀ x y : UInt64, byteOf (pair x y) r = byteOf ((low32 x <<< 32) ||| low32 y) (7 - r) := by
    intro x y
    rw [byteOf_digestWord x y (7 - r) (by omega)]
    by_cases h4 : r < 4
    · rw [byteOf_pair_low x y r h4, ite_eq_left (by omega : 4 ≤ 7 - r),
        show 7 - r - 4 = 3 - r by omega]
    · rw [byteOf_pair_high x y r (by omega) hr, ite_eq_right (by omega : ¬ 4 ≤ 7 - r)]
  rw [byteAt_eq _ _ _ hr, recordBytes,
    getElem!_flatMap8 (fun w => wordBytes w 8) _ (fun x _ => length_wordBytes x 8)
      (by simp only [outList, List.length_cons, List.length_nil]; omega) hr, wordBytes_byte _ _ hr]
  interval_cases q
  · exact key d.w0 d.w1
  · exact key d.w2 d.w3
  · exact key d.w4 d.w5
  · exact key d.w6 d.w7

/-- The library's bytes of the message of the blocks `recs` are the bytes of the blocks. -/
theorem bytes_blockMsg {recs : List (List UInt64)} (h8 : ∀ r ∈ recs, r.length = 8) :
    bytes (blockMsg recs) (64 * recs.length) = byteArrayOf (recs.flatMap recordBytes) := by
  have hfl := flatMap_recordBytes recs
  have h8w : ∀ w ∈ recs.flatten, (wordBytes w 8).length = 8 := fun w _ => length_wordBytes w 8
  have hlen : recs.flatten.length = 8 * recs.length := by
    have := length_flatMap8 id recs h8
    rwa [List.flatMap_id] at this
  have hbl : (recs.flatMap recordBytes).length = 64 * recs.length := by
    rw [hfl, length_flatMap8 _ _ h8w, hlen]; omega
  unfold bytes byteArrayOf
  congr 1
  apply Array.ext
  · simp [hbl]
  · intro p h1 h2
    simp only [Array.getElem_map, Array.getElem_range, List.getElem_toArray, List.getElem_map]
    obtain ⟨a, b, rfl, hb⟩ : ∃ a b, p = 8 * a + b ∧ b < 8 := ⟨p / 8, p % 8, by omega, by omega⟩
    have ha : a < recs.flatten.length := by simp at h1; omega
    rw [byteAt_eq _ _ _ hb, blockMsg_get (List.getElem?_eq_getElem ha), byteOf_bswap _ _ hb,
      ← wordBytes_byte _ _ hb, ← getElem!_flatMap8 (fun w => wordBytes w 8) _ h8w ha hb, ← hfl,
      getElem!_pos _ _ (by rw [hbl]; omega)]

/-! ## FIPS 180-4 -/

theorem sha256_congr {M M' : SHS.Message} (e : M = M') (h : M.length < 2 ^ 64) :
    SHS.SHA256.sha256 M h = SHS.SHA256.sha256 M' (e ▸ h) := by
  subst e; rfl

/-- The machine's answer to block `i`, read as 32 bytes, is the SHA-256 digest of FIPS 180-4 §6.2
of the bytes of blocks 0 to `i`, for fewer than 2^55 blocks of 8 words. -/
theorem shaSpec_fips (recs : List (List UInt64)) (h8 : ∀ r ∈ recs, r.length = 8)
    (hn : recs.length < 2 ^ 55) (i : Nat) (hi : i < recs.length) :
    ∃ h, digestBitVec (digestVec (machRun (shaSpec roundConstants) sha0 recs).2[i]!) =
      SHS.SHA256.sha256 (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes)))
        h := by
  have h8' : ∀ r ∈ recs.take (i + 1), r.length = 8 := fun r hr => h8 r (List.mem_of_mem_take hr)
  have hlt : (recs.take (i + 1)).length = i + 1 := by rw [List.length_take]; omega
  have hN : (UInt64.ofNat (64 * (recs.take (i + 1)).length)).toNat < 2 ^ 61 := by
    rw [toNat_ofNat64 (by omega)]; omega
  have hs := sha256_spec (blockMsg (recs.take (i + 1))) _ hN
  refine ⟨_, Eq.trans (congrArg digestBitVec ?_) (hs.trans (sha256_congr
    (congrArg bytesToBitMessage (by rw [toNat_ofNat64 (by omega), bytes_blockMsg h8'])) _))⟩
  rw [machRun_sha recs (by omega), getElem!_pos _ _ (by simp; omega), List.getElem_map,
    List.getElem_range]
  unfold sha256 sha256With
  dsimp only
  rw [hashFrom_blocks h8' (by omega), bytes_digest]
  rfl

end TestSupport.M7.Sha
