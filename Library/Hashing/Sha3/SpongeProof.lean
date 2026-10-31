import Library.Hashing.Sha3.RoundProof
import Library.Bytes.Packed
import LeanExe.Dialect.Lemmas

/-! The lane program's sponge computes Algorithm 8 of the transcription.  The string of a state of
lanes is `toBits (toState s)`, whose bit `t` is bit `t % 64` of lane `t / 64`.  KECCAK-p[1600, 24]
of that string is the string of `keccakF s`, and `xorBlock` XORs a block of the padded message
into the string as step 6 of Algorithm 8 does. -/

namespace Library.Hashing.Sha3.SpongeProof

open Library.Hashing.Sha3 Library.Hashing.Sha3.Spec Library.Hashing.Sha3.RoundProof

/-! ## Strings read bit by bit -/

/-- Bit `t` of a concatenation of strings of length `n` is bit `t % n` of string `t / n`. -/
theorem getD_flatMap {α β : Type} (f : α → List β) (n : Nat) (a0 : α) (d : β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = n) → ∀ t, t < l.length * n →
      (l.flatMap f).getD t d = (f (l.getD (t / n) a0)).getD (t % n) d
  | [], _, t, ht => by simp at ht
  | a :: l, hf, t, ht => by
    have hn : (f a).length = n := hf a List.mem_cons_self
    have ht' : t < l.length * n + n := by
      rw [List.length_cons, Nat.add_mul, Nat.one_mul] at ht; exact ht
    have hpos : 0 < n := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at ht
    have happ : ((a :: l).flatMap f).getD t d =
        if t < n then (f a).getD t d else (l.flatMap f).getD (t - n) d := by
      rw [List.flatMap_cons]
      split
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), hn]
    rw [happ]
    split
    · rename_i h
      simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [getD_flatMap f n a0 d l (fun a ha => hf a (List.mem_cons_of_mem _ ha)) (t - n)
        (by omega)]
      have h1 : t / n = (t - n) / n + 1 := Nat.div_eq_sub_div hpos (by omega)
      have h2 : t % n = (t - n) % n := Nat.mod_eq_sub_mod (by omega)
      rw [h1, h2, List.getD_cons_succ]

/-- A concatenation of strings of length `n` has length `n` times their number. -/
theorem length_flatMap_of_length {α β : Type} (f : α → List β) (n : Nat) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = n) → (l.flatMap f).length = l.length * n
  | [], _ => by simp
  | a :: l, hf => by
    rw [List.flatMap_cons, List.length_append, hf a List.mem_cons_self,
      length_flatMap_of_length f n l (fun a ha => hf a (List.mem_cons_of_mem _ ha)),
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem getD_finRange {k i : Nat} (d : Fin k) (h : i < k) :
    (List.finRange k).getD i d = ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_map_finRange {k z : Nat} (g : Fin k → Bool) (hz : z < k) :
    ((List.finRange k).map g).getD z false = g ⟨z, hz⟩ := by
  simp [List.getD_eq_getElem?_getD, hz]

theorem length_toBits (A : StateArray 6) : (toBits A).length = 1600 := by
  have hlane : ∀ i j, (Spec.lane A i j).length = 64 := by
    intro i j; rw [Spec.lane, List.length_map, List.length_finRange]; rfl
  have hplane : ∀ j, (plane A j).length = 320 := by
    intro j
    rw [plane, length_flatMap_of_length _ 64 _ (fun i _ => hlane i j)]
    simp
  rw [toBits, length_flatMap_of_length _ 320 _ (fun j _ => hplane j)]
  simp

/-- Bit `t` of the string of a state array, as §3.1.3 orders it. -/
theorem getD_toBits (A : StateArray 6) {t : Nat} (ht : t < 1600) :
    (toBits A).getD t false =
      A ⟨t / 64 % 5, by omega⟩ ⟨t / 320, by omega⟩ ⟨t % 64, by simp [laneSize]; omega⟩ := by
  have hlane : ∀ i j, (Spec.lane A i j).length = 64 := by
    intro i j; rw [Spec.lane, List.length_map, List.length_finRange]; rfl
  have hplane : ∀ j, (plane A j).length = 320 := by
    intro j
    rw [plane, length_flatMap_of_length _ 64 _ (fun i _ => hlane i j)]
    simp
  unfold toBits
  rw [getD_flatMap _ 320 0 false _ (fun j _ => hplane j) t (by simp; omega),
    getD_finRange _ (by omega)]
  unfold plane
  rw [getD_flatMap _ 64 0 false _ (fun i _ => hlane i _) (t % 320) (by simp; omega),
    getD_finRange _ (by omega)]
  unfold Spec.lane
  rw [getD_map_finRange _ (by simp [laneSize]; omega)]
  congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

/-- §3.1.2 inverts §3.1.3. -/
theorem toStateArray_toBits (A : StateArray 6) : toStateArray 6 (toBits A) = A := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz : z.val < 64 := z.isLt
  unfold toStateArray
  rw [getD_toBits A (by simp only [laneSize]; omega)]
  congr 1 <;> apply Fin.ext <;> simp only [laneSize] <;> omega

/-- Bit `t` of the string of the lanes is bit `t % 64` of lane `t / 64`. -/
theorem getD_lanes (s : Lanes) {t : Nat} (ht : t < 1600) :
    (toBits (toState s)).getD t false = bit ((laneList s).getD (t / 64) 0) (t % 64) := by
  rw [getD_toBits _ ht]
  simp only [toState, laneWord]
  congr 2
  omega

/-- KECCAK-p[1600, 24] of the string of the lanes is the string of `keccakF`. -/
theorem keccakP_lanes (s : Lanes) :
    keccakP 6 24 (toBits (toState s)) = toBits (toState (keccakF s)) := by
  rw [keccakF_spec, keccakP, toStateArray_toBits]
  congr 2
  funext A k
  congr 1
  omega

/-! ## Absorbing a block -/

/-- Strings of booleans that agree bit by bit are equal. -/
theorem ext_getD {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length)
    (h : ∀ t, t < l₁.length → l₁.getD t false = l₂.getD t false) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro t h₁ h₂
  have := h t h₁
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂, Option.getD_some] at this
  exact this

theorem getD_xor {X Y : Bits} {t : Nat} (hX : t < X.length) (hY : t < Y.length) :
    (Spec.xor X Y).getD t false = (X.getD t false ^^ Y.getD t false) := by
  simp [Spec.xor, List.getD_eq_getElem?_getD, hX, hY]

theorem length_xor (X Y : Bits) : (Spec.xor X Y).length = min X.length Y.length := by
  simp [Spec.xor]

theorem getD_append_zeros (X : Bits) (c t : Nat) :
    (X ++ zeros c).getD t false = X.getD t false := by
  by_cases h : t < X.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have h1 : X.length ≤ t := Nat.le_of_not_lt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none h1, zeros, List.getElem?_replicate]
    split <;> rfl

/-- The lanes of `xorBlock`: lane `i` XORed with word `base + i` of the padded message when
`i < rw`. -/
theorem laneList_xorBlock (s : Lanes) (msg : Array UInt64) (n sfx rw last base : UInt64)
    {i : Nat} (hi : i < 25) :
    (laneList (xorBlock s msg n sfx rw last base)).getD i 0 =
      ((laneList s).getD i 0 ^^^
        if UInt64.ofNat i < rw then paddedWord msg n sfx last (base + UInt64.ofNat i) else 0) := by
  interval_cases i <;> rfl

/-- The string of `rw` words from word `base` of the padded message: bit `t` is bit `t % 64` of
word `base + t / 64`. -/
def blockBits (msg : Array UInt64) (n sfx last base rw : UInt64) : Bits :=
  (List.range (64 * rw.toNat)).map fun t =>
    bit (paddedWord msg n sfx last (base + UInt64.ofNat (t / 64))) (t % 64)

/-- `xorBlock` is step 6 of Algorithm 8: the state's string XORed with a block followed by
`c = 1600 - r` zeros. -/
theorem xorBlock_spec (s : Lanes) (msg : Array UInt64) (n sfx rw last base : UInt64)
    (hrw : rw.toNat ≤ 25) :
    toBits (toState (xorBlock s msg n sfx rw last base)) =
      Spec.xor (toBits (toState s))
        (blockBits msg n sfx last base rw ++ zeros (1600 - 64 * rw.toNat)) := by
  have hlen :
      (blockBits msg n sfx last base rw ++ zeros (1600 - 64 * rw.toNat)).length = 1600 := by
    simp [blockBits, zeros]; omega
  apply ext_getD (by rw [length_xor, hlen, length_toBits, length_toBits]; rfl)
  intro t ht
  rw [length_toBits] at ht
  rw [getD_lanes _ ht, getD_xor (by rw [length_toBits]; exact ht) (by rw [hlen]; exact ht),
    getD_lanes _ ht, laneList_xorBlock _ _ _ _ _ _ _ (by omega), bit_xor,
    getD_append_zeros]
  congr 1
  have hlt : (UInt64.ofNat (t / 64) < rw) = (t < 64 * rw.toNat) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    apply propext; omega
  by_cases h : t < 64 * rw.toNat
  · have h' : UInt64.ofNat (t / 64) < rw := by rw [hlt]; exact h
    simp only [h', ↓reduceIte, blockBits, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range h, Option.map_some, Option.getD_some]
  · have h' : ¬ UInt64.ofNat (t / 64) < rw := by rw [hlt]; exact h
    have hb : (blockBits msg n sfx last base rw).length ≤ t := by simp [blockBits]; omega
    simp only [h', ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_none hb,
      Option.getD_none, bit_zero]

theorem zero_lanes : toBits (toState zeroLanes) = zeros 1600 := by
  apply ext_getD (by rw [length_toBits, zeros, List.length_replicate])
  intro t ht
  rw [length_toBits] at ht
  rw [getD_lanes _ ht]
  have : (laneList zeroLanes).getD (t / 64) 0 = 0 := by
    have : t / 64 < 25 := by omega
    interval_cases (t / 64) <;> rfl
  simp only [this, zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, ht, ↓reduceIte,
    Option.getD_some, bit_zero]

/-! ## The absorbing loop -/

/-- The string of the padded message: bit `t` is bit `t % 64` of word `t / 64`. -/
def paddedBits (msg : Array UInt64) (n sfx last : UInt64) (len : Nat) : Bits :=
  (List.range len).map fun t => bit (paddedWord msg n sfx last (UInt64.ofNat (t / 64))) (t % 64)

theorem ofNat_block (k j : Nat) (rw : UInt64) :
    UInt64.ofNat k * rw + UInt64.ofNat j = UInt64.ofNat (k * rw.toNat + j) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
  rw [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]

/-- Block `i` of the padded message's string is `blockBits` from word `i rw`. -/
theorem block_eq (msg : Array UInt64) (n sfx last rw : UInt64) {blocks i : Nat}
    (hi : i < blocks) :
    ((paddedBits msg n sfx last (blocks * (64 * rw.toNat))).drop (i * (64 * rw.toNat))).take
        (64 * rw.toNat) = blockBits msg n sfx last (UInt64.ofNat i * rw) rw := by
  have hle : i * (64 * rw.toNat) + 64 * rw.toNat ≤ blocks * (64 * rw.toNat) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  apply ext_getD (by simp [paddedBits, blockBits]; omega)
  intro t ht
  have ht' : t < 64 * rw.toNat := by simp [paddedBits] at ht; omega
  simp only [paddedBits, blockBits, List.getD_eq_getElem?_getD, List.getElem?_take, ht',
    ↓reduceIte, List.getElem?_drop, List.getElem?_map,
    List.getElem?_range (show i * (64 * rw.toNat) + t < blocks * (64 * rw.toNat) by omega),
    List.getElem?_range ht', Option.map_some, Option.getD_some]
  rw [ofNat_block]
  have h1 : (i * (64 * rw.toNat) + t) / 64 = i * rw.toNat + t / 64 := by
    rw [show i * (64 * rw.toNat) = 64 * (i * rw.toNat) by ring]; omega
  have h2 : (i * (64 * rw.toNat) + t) % 64 = t % 64 := by
    rw [show i * (64 * rw.toNat) = 64 * (i * rw.toNat) by ring]; omega
  rw [h1, h2]

/-- After the absorbing loop, the state's string is the state of Algorithm 8 after step 6, for a
padded message whose string is `paddedBits` of `blocks` blocks of `rw` words. -/
theorem absorb_spec (msg : Array UInt64) (n rw sfx : UInt64) (hrw : rw.toNat ≤ 25)
    (P : Bits) (hP : P = paddedBits msg n sfx ((n / (8 * rw) + 1) * rw - 1)
      ((n / (8 * rw) + 1).toNat * (64 * rw.toNat))) :
    toBits (toState (absorb msg n rw sfx)) =
      (List.range (n / (8 * rw) + 1).toNat).foldl
        (fun S i => keccakP 6 24 (Spec.xor S ((P.drop (i * (64 * rw.toNat))).take
          (64 * rw.toNat) ++ zeros (1600 - 64 * rw.toNat)))) (zeros 1600) := by
  unfold absorb
  simp only
  refine LeanExe.Dialect.loop_induction
    (P := fun k s => toBits (toState s) = (List.range k).foldl
      (fun S i => keccakP 6 24 (Spec.xor S ((P.drop (i * (64 * rw.toNat))).take
        (64 * rw.toNat) ++ zeros (1600 - 64 * rw.toNat)))) (zeros 1600)) zero_lanes ?_
  intro k s hk ih
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih, ← keccakP_lanes,
    xorBlock_spec _ _ _ _ _ _ _ hrw, hP, block_eq _ _ _ _ _ hk]


/-! ## The padded message -/

/-- The bits of bytes, least significant first in each byte, as `h2b` of Appendix B.1 reads them. -/
def bitsOfBytes (bs : List UInt8) : Bits := bs.flatMap fun b => (List.range 8).map b.toNat.testBit

theorem bit_shiftLeft (a : UInt64) {k z : Nat} (hk : k < 64) (hz : z < 64) :
    bit (a <<< k.toUInt64) z = (decide (k ≤ z) && a.toNat.testBit (z - k)) := by
  have hk' : k.toUInt64.toNat % 64 = k := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [bit, UInt64.toNat_shiftLeft, hk', Nat.testBit_mod_two_pow, hz, decide_true,
    Bool.true_and, Nat.testBit_shiftLeft, ge_iff_le]

theorem bit_mask {k : Nat} (hk : k < 64) (z : Nat) :
    bit ((1 <<< k.toUInt64) - 1) z = decide (z < k) := by
  have hk' : k.toUInt64.toNat % 64 = k := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  have h1 : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k := by
    rw [UInt64.toNat_shiftLeft, hk', UInt64.toNat_one, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  have h2 : ((1 <<< k.toUInt64) - 1 : UInt64).toNat = 2 ^ k - 1 := by
    rw [UInt64.toNat_sub_of_le _ _
      (by rw [UInt64.le_iff_toNat_le, h1]; simp; exact Nat.one_le_two_pow), h1, UInt64.toNat_one]
  simp only [bit, h2, Nat.testBit_two_pow_sub_one]

/-- Bit `z` of word `j` of the first `n` bytes: the message's bit when it lies below byte `n`. -/
theorem bit_messageWord (msg : Array UInt64) (n j : UInt64) {z : Nat} (hz : z < 64)
    (hj : 8 * j.toNat + 8 < 2 ^ 64) :
    bit (messageWord msg n j) z =
      (decide (64 * j.toNat + z < 8 * n.toNat) && bit msg[j.toNat]! z) := by
  have h8j : (8 * j).toNat = 8 * j.toNat := by
    rw [UInt64.toNat_mul]; simp; omega
  have h8j8 : (8 * j + 8).toNat = 8 * j.toNat + 8 := by
    rw [UInt64.toNat_add, h8j]; simp; omega
  unfold messageWord
  by_cases h1 : 8 * j + 8 ≤ n
  · simp only [h1, ↓reduceIte]
    rw [UInt64.le_iff_toNat_le, h8j8] at h1
    simp; omega
  · simp only [h1, ↓reduceIte]
    rw [UInt64.le_iff_toNat_le, h8j8] at h1
    by_cases h2 : 8 * j < n
    · simp only [h2, ↓reduceIte]
      rw [UInt64.lt_iff_toNat_lt, h8j] at h2
      have hsub : (8 * (n - 8 * j)).toNat = 8 * (n.toNat - 8 * j.toNat) := by
        rw [UInt64.toNat_mul,
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h8j]; omega), h8j]
        simp; omega
      have hm : (1 <<< (8 * (n - 8 * j)) : UInt64) =
          1 <<< (8 * (n.toNat - 8 * j.toNat)).toUInt64 := by
        congr 1; apply UInt64.toNat_inj.mp; rw [hsub]; simp; omega
      rw [hm, bit_and, bit_mask (by omega)]
      cases bit msg[j.toNat]! z
      · simp
      · simp; omega
    · simp only [h2, ↓reduceIte, bit_zero]
      rw [UInt64.lt_iff_toNat_lt, h8j] at h2
      simp; omega

/-- Bit `z` of the word that holds the suffix byte `sfx` at byte `n % 8` of word `n / 8`. -/
theorem bit_sfxWord (n sfx j : UInt64) {z : Nat} (hz : z < 64) :
    bit (if j == n / 8 then sfx <<< (8 * (n % 8)) else 0) z =
      (decide (j.toNat = n.toNat / 8) && decide (8 * (n.toNat % 8) ≤ z) &&
        sfx.toNat.testBit (z - 8 * (n.toNat % 8))) := by
  have hk : (8 * (n % 8) : UInt64) = (8 * (n.toNat % 8)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul, UInt64.toNat_mod, Nat.toUInt64, UInt64.toNat_ofNat']
    simp only [show (8 : UInt64).toNat = 8 from rfl]
  by_cases hj : j = n / 8
  · have hj' : j.toNat = n.toNat / 8 := by rw [hj, UInt64.toNat_div]; rfl
    simp only [hj, beq_self_eq_true, ↓reduceIte, hk]
    rw [bit_shiftLeft _ (by omega) hz, ← hj, hj']
    simp
  · have hj' : ¬ j.toNat = n.toNat / 8 := fun h =>
      hj (UInt64.toNat_inj.mp (by rw [h, UInt64.toNat_div]; rfl))
    have hb : (j == n / 8) = false := by simpa using hj
    simp [hb, bit_zero, hj']

/-- Bit `z` of the word that holds the last bit of the padding at bit 63 of word `last`. -/
theorem bit_lastWord (j last : UInt64) (z : Nat) :
    bit (if j == last then 0x8000000000000000 else 0) z =
      (decide (j = last) && decide (z = 63)) := by
  by_cases hj : j = last
  · subst hj
    have : (0x8000000000000000 : UInt64).toNat = 2 ^ 63 := rfl
    simp only [beq_self_eq_true, ↓reduceIte, bit, this, Nat.testBit_two_pow, decide_true,
      Bool.true_and]
    by_cases h : z = 63
    · simp [h]
    · simp [h]; omega
  · have hb : (j == last) = false := by simpa using hj
    simp [hb, bit_zero, hj]

/-- Bit `k` of byte `i` of a packed array is bit `8 (i % 8) + k` of word `i / 8`. -/
theorem testBit_byteAt (msg : Array UInt64) (i : Nat) {k : Nat} (hk : k < 8) :
    (Library.Bytes.byteAt msg i).toNat.testBit k = bit msg[i / 8]! (8 * (i % 8) + k) := by
  have hs : (8 * (i % 8)).toUInt64.toNat % 64 = 8 * (i % 8) := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [Library.Bytes.byteAt, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hs, bit,
    Nat.testBit_mod_two_pow, hk, decide_true, Bool.true_and, Nat.testBit_shiftRight]


theorem length_bitsOfBytes (bs : List UInt8) : (bitsOfBytes bs).length = 8 * bs.length := by
  rw [bitsOfBytes, length_flatMap_of_length _ 8 _ (fun b _ => by simp), Nat.mul_comm]

theorem getD_bitsOfBytes (bs : List UInt8) {t : Nat} (ht : t < 8 * bs.length) :
    (bitsOfBytes bs).getD t false = (bs.getD (t / 8) 0).toNat.testBit (t % 8) := by
  rw [bitsOfBytes, getD_flatMap _ 8 0 false _ (fun b _ => by simp) t (by omega)]
  simp [List.getD_eq_getElem?_getD, Nat.mod_lt t (by decide : 0 < 8)]

/-- Bit `t` of the first `n` bytes of a packed array is bit `t % 64` of word `t / 64`. -/
theorem getD_message (msg : Array UInt64) (n : Nat) {t : Nat} (ht : t < 8 * n) :
    (bitsOfBytes ((List.range n).map (Library.Bytes.byteAt msg))).getD t false =
      bit msg[t / 64]! (t % 64) := by
  rw [getD_bitsOfBytes _ (by simp; omega)]
  have h : ((List.range n).map (Library.Bytes.byteAt msg)).getD (t / 8) 0 =
      Library.Bytes.byteAt msg (t / 8) := by
    simp [List.getD_eq_getElem?_getD, show t / 8 < n by omega]
  rw [h, testBit_byteAt _ _ (by omega)]
  congr 2 <;> omega

theorem length_pad101 (x m : Nat) : (pad101 x m).length = ((-(m : Int) - 2) % x).toNat + 2 := by
  simp [pad101, zeros]

theorem getD_pad101 (x m i : Nat) :
    (pad101 x m).getD i false = (i == 0 || i == ((-(m : Int) - 2) % x).toNat + 1) := by
  simp only [pad101, zeros]
  generalize ((-(m : Int) - 2) % x).toNat = j
  simp only [List.getD_eq_getElem?_getD, List.cons_append, List.nil_append]
  rcases i with _ | i
  · simp
  · simp only [List.getElem?_cons_succ, List.getElem?_append, List.length_replicate,
      List.getElem?_replicate]
    by_cases h1 : i < j
    · simp [h1]; omega
    · by_cases h2 : i = j
      · simp [h2]
      · have : i - j ≠ 0 := by omega
        simp [h1, h2, this]

theorem getD_append_left {X Y : Bits} {t : Nat} (h : t < X.length) :
    (X ++ Y).getD t false = X.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {X Y : Bits} {t : Nat} (h : X.length ≤ t) :
    (X ++ Y).getD t false = Y.getD (t - X.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- The zeros of pad10*1 of Algorithm 9 number `R B - m - 2` when `R (B - 1) < m + 2 ≤ R B`. -/
theorem pad101_zeros {R B m : Nat} (h1 : m + 2 ≤ R * B) (h2 : R * B < m + 2 + R) :
    ((-(m : Int) - 2) % (R : Int)).toNat = R * B - m - 2 := by
  have : (-(m : Int) - 2) = ((R * B - m - 2 : Nat) : Int) + (R : Int) * (-(B : Int)) := by
    push_cast [Nat.sub_sub, Nat.cast_sub h1]; ring
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

/-- A message of `8 N` bits, a suffix of `s ≤ 6` bits, and pad10*1 to a length `L = R B` are the
string of `g` when `g` gives the message's bits below `8 N`, the bits of the suffix followed by the
padding's first bit and the padding's last bit in the next byte, and the padding's last bit
after it. -/
theorem padded_of_regions (M suffix : Bits) (R B N : Nat) (g : Nat → Bool)
    (hM : M.length = 8 * N) (hs : suffix.length ≤ 6)
    (h1 : 8 * N + suffix.length + 2 ≤ R * B) (h2 : R * B < 8 * N + suffix.length + 2 + R)
    (hmsg : ∀ t, t < 8 * N → g t = M.getD t false)
    (hsfx : ∀ t, 8 * N ≤ t → t < 8 * N + 8 →
      g t = ((suffix ++ [true]).getD (t - 8 * N) false || decide (t = R * B - 1)))
    (hpad : ∀ t, 8 * N + 8 ≤ t → t < R * B → g t = decide (t = R * B - 1)) :
    M ++ suffix ++ pad101 R (M ++ suffix).length = (List.range (R * B)).map g := by
  have hj := pad101_zeros (R := R) (B := B) (m := 8 * N + suffix.length) h1 h2
  have hlen : (M ++ suffix).length = 8 * N + suffix.length := by simp [hM]
  rw [hlen]
  apply ext_getD (by
    rw [List.length_append, hlen, length_pad101, hj, List.length_map, List.length_range]; omega)
  intro t ht
  rw [List.length_append, hlen, length_pad101, hj] at ht
  rw [show ((List.range (R * B)).map g).getD t false = g t by
    simp [List.getD_eq_getElem?_getD, show t < R * B by omega]]
  by_cases ha : t < 8 * N
  · rw [getD_append_left (by simp [hM]; omega), getD_append_left (by rw [hM]; exact ha), hmsg t ha]
  · by_cases hb : t < 8 * N + suffix.length
    · rw [getD_append_left (by simp [hM]; omega), getD_append_right (by rw [hM]; omega),
        hsfx t (by omega) (by omega), hM, getD_append_left (by omega)]
      simp; omega
    · rw [getD_append_right (by simp [hM]; omega), getD_pad101, hj]
      simp only [List.length_append, hM]
      by_cases hc : t < 8 * N + 8
      · rw [hsfx t (by omega) hc]
        by_cases hd : t = 8 * N + suffix.length
        · subst hd
          simp
        · rw [getD_append_right (by omega)]
          have h0 : ¬ t - (8 * N + suffix.length) = 0 := by omega
          have h0' : t - 8 * N - suffix.length ≠ 0 := by omega
          have hnil : [true].getD (t - 8 * N - suffix.length) false = false := by
            simp [List.getD_eq_getElem?_getD, h0']
          rw [hnil]
          by_cases he : t = R * B - 1
          · have : t - (8 * N + suffix.length) = R * B - (8 * N + suffix.length) - 2 + 1 := by
              omega
            simp only [this, beq_self_eq_true, Bool.or_true, decide_eq_true he]
          · have : t - (8 * N + suffix.length) ≠ R * B - (8 * N + suffix.length) - 2 + 1 := by
              omega
            simp [h0, this, he]
      · rw [hpad t (by omega) (by omega)]
        have h0 : ¬ t - (8 * N + suffix.length) = 0 := by omega
        by_cases he : t = R * B - 1
        · have : t - (8 * N + suffix.length) = R * B - (8 * N + suffix.length) - 2 + 1 := by
            omega
          simp only [this, beq_self_eq_true, Bool.or_true, decide_eq_true he]
        · have : t - (8 * N + suffix.length) ≠ R * B - (8 * N + suffix.length) - 2 + 1 := by
            omega
          simp [h0, this, he]

/-- The block arithmetic of a message of `n` bytes at a rate of `rw` words: the blocks
`B = n / (8 rw) + 1`, their words `B rw = Q + rw` with `Q = (n / (8 rw)) rw`, and `n = 8 Q + ρ`
with `ρ < 8 rw`. -/
theorem block_arith (n rw : UInt64) (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25)
    (hn : n.toNat < 2 ^ 61) :
    (n / (8 * rw) + 1).toNat = n.toNat / (8 * rw.toNat) + 1 ∧
    ((n / (8 * rw) + 1) * rw - 1).toNat = n.toNat / (8 * rw.toNat) * rw.toNat + rw.toNat - 1 ∧
    n.toNat = 8 * (n.toNat / (8 * rw.toNat) * rw.toNat) + n.toNat % (8 * rw.toNat) ∧
    n.toNat % (8 * rw.toNat) < 8 * rw.toNat := by
  have h8rw : (8 * rw).toNat = 8 * rw.toNat := by
    rw [UInt64.toNat_mul]; simp; omega
  have hq : (n / (8 * rw)).toNat = n.toNat / (8 * rw.toNat) := by
    rw [UInt64.toNat_div, h8rw]
  have hqle : n.toNat / (8 * rw.toNat) ≤ n.toNat := Nat.div_le_self _ _
  have hB : (n / (8 * rw) + 1).toNat = n.toNat / (8 * rw.toNat) + 1 := by
    rw [UInt64.toNat_add, hq]; simp; omega
  have hn8 : n.toNat = 8 * (n.toNat / (8 * rw.toNat) * rw.toNat) + n.toNat % (8 * rw.toNat) := by
    have h := Nat.div_add_mod n.toNat (8 * rw.toNat)
    have : 8 * rw.toNat * (n.toNat / (8 * rw.toNat)) =
        8 * (n.toNat / (8 * rw.toNat) * rw.toNat) := by ring
    omega
  have hQle : n.toNat / (8 * rw.toNat) * rw.toNat ≤ n.toNat := by omega
  have hBrw : ((n / (8 * rw) + 1) * rw).toNat =
      n.toNat / (8 * rw.toNat) * rw.toNat + rw.toNat := by
    rw [UInt64.toNat_mul, hB, Nat.add_mul, Nat.one_mul]; simp; omega
  refine ⟨hB, ?_, hn8, Nat.mod_lt _ (by omega)⟩
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hBrw]; simp; omega), hBrw]
  simp

/-- Bit `t` of the program's padded words, below the padded length `B (64 rw)`. -/
theorem bit_padded (msg : Array UInt64) (n rw sfx : UInt64) (hrw0 : 0 < rw.toNat)
    (hrw : rw.toNat ≤ 25) (hn : n.toNat < 2 ^ 61) {t : Nat}
    (ht : t < (n / (8 * rw) + 1).toNat * (64 * rw.toNat)) :
    bit (paddedWord msg n sfx ((n / (8 * rw) + 1) * rw - 1) (UInt64.ofNat (t / 64))) (t % 64) =
      ((decide (t < 8 * n.toNat) && bit msg[t / 64]! (t % 64)) ||
        (decide (t / 64 = n.toNat / 8) && decide (8 * (n.toNat % 8) ≤ t % 64) &&
          sfx.toNat.testBit (t % 64 - 8 * (n.toNat % 8))) ||
        decide (t = (n / (8 * rw) + 1).toNat * (64 * rw.toNat) - 1)) := by
  obtain ⟨hB, hlast, hn8, hρ⟩ := block_arith n rw hrw0 hrw hn
  rw [hB] at ht ⊢
  set Q := n.toNat / (8 * rw.toNat) * rw.toNat
  have hBR : (n.toNat / (8 * rw.toNat) + 1) * (64 * rw.toNat) = 64 * Q + 64 * rw.toNat := by ring
  rw [hBR] at ht ⊢
  have hj64 : (UInt64.ofNat (t / 64)).toNat = t / 64 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  rw [paddedWord, bit_or, bit_or, bit_messageWord _ _ _ (Nat.mod_lt _ (by decide))
      (by rw [hj64]; omega), bit_sfxWord _ _ _ (Nat.mod_lt _ (by decide)), bit_lastWord, hj64]
  have hl : (UInt64.ofNat (t / 64) = (n / (8 * rw) + 1) * rw - 1) ↔ t / 64 = Q + rw.toNat - 1 := by
    rw [← UInt64.toNat_inj, hj64, hlast]
  have e1 : decide (64 * (t / 64) + t % 64 < 8 * n.toNat) = decide (t < 8 * n.toNat) := by
    congr 1; apply propext; omega
  have e2 : (decide (UInt64.ofNat (t / 64) = (n / (8 * rw) + 1) * rw - 1) &&
      decide (t % 64 = 63)) = decide (t = 64 * Q + 64 * rw.toNat - 1) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, hl]
    omega
  rw [e1, e2]

/-- The message of `n` bytes, its suffix, and pad10*1 of Algorithm 9 are the string of the
program's padded words, `n / (8 rw) + 1` blocks of `rw` words, when the byte `sfx` holds the
suffix followed by the first bit of the padding. -/
theorem padded_eq (msg : Array UInt64) (n rw sfx : UInt64) (suffix : Bits)
    (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25) (hn : n.toNat < 2 ^ 61)
    (hs : suffix.length ≤ 6)
    (hsfx : ∀ i, sfx.toNat.testBit i = (suffix ++ [true]).getD i false) :
    bitsOfBytes ((List.range n.toNat).map (Library.Bytes.byteAt msg)) ++ suffix ++
        pad101 (64 * rw.toNat)
          (bitsOfBytes ((List.range n.toNat).map (Library.Bytes.byteAt msg)) ++ suffix).length =
      paddedBits msg n sfx ((n / (8 * rw) + 1) * rw - 1)
        ((n / (8 * rw) + 1).toNat * (64 * rw.toNat)) := by
  obtain ⟨hB, -, hn8, hρ⟩ := block_arith n rw hrw0 hrw hn
  have hRB : 64 * rw.toNat * (n / (8 * rw) + 1).toNat =
      (n / (8 * rw) + 1).toNat * (64 * rw.toNat) := Nat.mul_comm _ _
  have hBR : (n / (8 * rw) + 1).toNat * (64 * rw.toNat) =
      64 * (n.toNat / (8 * rw.toNat) * rw.toNat) + 64 * rw.toNat := by rw [hB]; ring
  have hsfx8 : ∀ i, 8 ≤ i → sfx.toNat.testBit i = false := by
    intro i hi
    rw [hsfx, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  rw [paddedBits, ← hRB]
  apply padded_of_regions _ _ _ _ n.toNat _ (by rw [length_bitsOfBytes]; simp) hs
    (by rw [hRB, hBR]; omega) (by rw [hRB, hBR]; omega)
  · intro t ht
    rw [getD_message _ _ ht, bit_padded _ _ _ _ hrw0 hrw hn (by rw [hBR]; omega)]
    have : ¬ (t / 64 = n.toNat / 8 ∧ 8 * (n.toNat % 8) ≤ t % 64) := by omega
    have h3 : t ≠ (n / (8 * rw) + 1).toNat * (64 * rw.toNat) - 1 := by rw [hBR]; omega
    by_cases hb : bit msg[t / 64]! (t % 64)
    · simp [ht, hb]
    · simp only [ht, decide_true, hb, Bool.and_false, Bool.false_or, h3, decide_false,
        Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
  · intro t ht1 ht2
    rw [hRB, bit_padded _ _ _ _ hrw0 hrw hn (by rw [hBR]; omega)]
    have h1 : t / 64 = n.toNat / 8 := by omega
    have h2 : 8 * (n.toNat % 8) ≤ t % 64 := by omega
    have h3 : t % 64 - 8 * (n.toNat % 8) = t - 8 * n.toNat := by omega
    have h4 : ¬ t < 8 * n.toNat := by omega
    simp only [h4, decide_false, Bool.false_and, Bool.false_or, h1, h2, decide_true,
      Bool.true_and, h3, hsfx]
  · intro t ht1 ht2
    rw [hRB] at ht2 ⊢
    rw [bit_padded _ _ _ _ hrw0 hrw hn ht2]
    have h4 : ¬ t < 8 * n.toNat := by omega
    have h5 : (decide (t / 64 = n.toNat / 8) && decide (8 * (n.toNat % 8) ≤ t % 64) &&
        sfx.toNat.testBit (t % 64 - 8 * (n.toNat % 8))) = false := by
      by_cases h1 : t / 64 = n.toNat / 8
      · by_cases h2 : 8 * (n.toNat % 8) ≤ t % 64
        · simp [h1, h2, hsfx8 (t % 64 - 8 * (n.toNat % 8)) (by omega)]
        · simp [h2]
      · simp [h1]
    simp only [h4, decide_false, Bool.false_and, Bool.false_or, h5]

end Library.Hashing.Sha3.SpongeProof
