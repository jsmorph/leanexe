import Library.Hashing.Sha2.Spec
import Library.Hashing.Sha2.Equiv.Common.Chunks
import Library.Hashing.Sha2.Equiv.Common.FromBits
import Library.Hashing.Sha2.Equiv.SHA256.Pipeline
import Library.Hashing.Sha2.Equiv.SHA512.Pipeline
import Mathlib.Tactic.IntervalCases

/-! The Merkle–Damgård reduction for SHA-256 and SHA-512 of FIPS 180-4: two distinct messages with
equal digests give two distinct pairs of a hash value and a block on which the compression function
agrees.  The proof holds for any compression function on eight words of `w` bits and blocks of
sixteen words, with the padding of §5.1 and the parsing of §5.2 at that width.  The digests of
SHA-224, SHA-384, and SHA-512/t omit part of the final hash value, so the reduction does not apply
to them. -/

namespace Library.Hashing.MerkleDamgard

open SHS SHS.Equiv.Chunks SHS.Equiv.FromBits

/-- Two distinct pairs of a hash value and a block with the same image under `f`. -/
def Collision {S B : Type} (f : S → B → S) : Prop :=
  ∃ s b s' b', (s, b) ≠ (s', b') ∧ f s b = f s' b'

theorem foldl_concat_collision {S B : Type} (f : S → B → S) (h : S) (L L' : List B) (b b' : B)
    (hb : b ≠ b') (heq : (L ++ [b]).foldl f h = (L' ++ [b']).foldl f h) : Collision f := by
  rw [List.foldl_concat, List.foldl_concat] at heq
  exact ⟨_, _, _, _, fun hp => hb (Prod.mk.inj hp).2, heq⟩

/-- Folds of two lists of one length agree only on equal lists or at a collision. -/
theorem eq_or_collision {S B : Type} (f : S → B → S) (h : S) :
    ∀ bs bs' : List B, bs.length = bs'.length → bs.foldl f h = bs'.foldl f h →
      bs = bs' ∨ Collision f := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil =>
    intro bs' hl _
    cases bs' with
    | nil => exact Or.inl rfl
    | cons _ _ => simp at hl
  | append_singleton L b ih =>
    intro bs' hl heq
    rcases List.eq_nil_or_concat' bs' with rfl | ⟨L', b', rfl⟩
    · simp at hl
    · rw [List.foldl_concat, List.foldl_concat] at heq
      by_cases hp : (L.foldl f h, b) = (L'.foldl f h, b')
      · obtain ⟨hs, rfl⟩ := Prod.mk.inj hp
        rcases ih L' (by simpa using hl) hs with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr hc
      · exact Or.inr ⟨_, _, _, _, hp, heq⟩

/-- Two lists of `N` slices of `n` elements agree when every slice agrees. -/
theorem eq_of_slices {α : Type} (n N : Nat) (P P' : List α) (hP : P.length = n * N)
    (hP' : P'.length = n * N)
    (h : ∀ i < N, (P.drop (i * n)).take n = (P'.drop (i * n)).take n) : P = P' := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n * N
  · have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
    have hi : j / n < N := (Nat.div_lt_iff_lt_mul hn).mpr (by rwa [Nat.mul_comm])
    have e := congrArg (fun l => l[j % n]?) (h (j / n) hi)
    simp only [List.getElem?_take_of_lt (Nat.mod_lt j hn), List.getElem?_drop,
      Nat.div_add_mod'] at e
    exact e
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem natFromBits_concat (L : List Bool) (b : Bool) :
    natFromBits (L ++ [b]) = 2 * natFromBits L + (if b then 1 else 0) := by
  simp only [natFromBits, List.foldl_concat]

theorem natFromBits_inj : ∀ l l' : List Bool, l.length = l'.length →
    natFromBits l = natFromBits l' → l = l' := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro l' hl _
    cases l' with
    | nil => rfl
    | cons _ _ => simp at hl
  | append_singleton L b ih =>
    intro l' hl h
    rcases List.eq_nil_or_concat' l' with rfl | ⟨L', b', rfl⟩
    · simp at hl
    · rw [natFromBits_concat, natFromBits_concat] at h
      have hb : b = b' ∧ natFromBits L = natFromBits L' := by
        cases b <;> cases b' <;> simp at h ⊢ <;> omega
      rw [hb.1, ih L' (by simpa using hl) hb.2]

theorem fromBits_inj {N : Nat} (l l' : List Bool) (hl : l.length = N) (hl' : l'.length = N)
    (h : Word.fromBits (n := N) l = Word.fromBits (n := N) l') : l = l' := by
  have e := congrArg BitVec.toNat h
  rw [fromBits_toNat_of_length_le l hl.le, fromBits_toNat_of_length_le l' hl'.le] at e
  exact natFromBits_inj l l' (hl.trans hl'.symm) e

/-- The block of FIPS 180-4 §5.2 that holds the sixteen words of `w` bits of `b`. -/
def block (w : Nat) (b : List Bool) : Vector (BitVec w) 16 :=
  let words := b.toChunks w |>.map (Word.fromBits (n := w)) |>.toArray
  Vector.ofFn (n := 16) fun i => words[i]?.getD 0

/-- The parsing of FIPS 180-4 §5.2 into blocks of sixteen words of `w` bits. -/
def parse (w : Nat) (M : List Bool) : Array (Vector (BitVec w) 16) :=
  M.toChunks (16 * w) |>.toArray |>.map (block w)

/-- The number of zero bits in the padding of FIPS 180-4 §5.1 for words of `w` bits. -/
def zeros (w ℓ : Nat) : Nat := min { k < 16 * w | ℓ + 1 + k ≡ 14 * w [MOD 16 * w] }

/-- The length field of `L` bits that holds `ℓ`, most significant bit first. -/
def lengthBits (L ℓ : Nat) : List Bool := (List.range L).reverse.map ℓ.testBit

/-- The padding of FIPS 180-4 §5.1 for words of `w` bits: blocks of `16 w` bits and a length
field of `2 w` bits. -/
def pad (w : Nat) (M : List Bool) : List Bool :=
  M ++ [true] ++ List.replicate (zeros w M.length) false ++ lengthBits (2 * w) M.length

/-- The final hash value of FIPS 180-4 §6.2 and §6.4 for the compression function `f`. -/
def final (w : Nat) (f : Vector (BitVec w) 8 → Vector (BitVec w) 16 → Vector (BitVec w) 8)
    (H0 : Vector (BitVec w) 8) (M : List Bool) : Vector (BitVec w) 8 :=
  (parse w (pad w M)).foldl f H0

/-- The digest of FIPS 180-4 §6.2 and §6.4: the concatenation of the eight words of the final
hash value. -/
def digest {w : Nat} (H : Vector (BitVec w) 8) : BitVec (w + w + w + w + w + w + w + w) :=
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6] ++ H[7]

theorem block_word (w : Nat) (hw : 0 < w) (b : List Bool) (hb : b.length = 16 * w) (i : Nat)
    (hi : i < 16) : (block w b)[i] = Word.fromBits (n := w) ((b.drop (i * w)).take w) := by
  rw [block, Vector.getElem_ofFn, toChunks_eq_drop_take w hw b 16 (by rw [hb, Nat.mul_comm])]
  simp [hi]

theorem block_inj (w : Nat) (hw : 0 < w) (b b' : List Bool) (hb : b.length = 16 * w)
    (hb' : b'.length = 16 * w) (h : block w b = block w b') : b = b' := by
  apply eq_of_slices w 16 b b' (by rw [hb, Nat.mul_comm]) (by rw [hb', Nat.mul_comm])
  intro i hi
  have hle : i * w + w ≤ 16 * w := by
    have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hi)
    rwa [Nat.succ_mul] at this
  apply fromBits_inj (N := w) _ _ (by simp [hb]; omega) (by simp [hb']; omega)
  rw [← block_word w hw b hb i hi, ← block_word w hw b' hb' i hi, h]

theorem parse_toList (w N : Nat) (hw : 0 < w) (P : List Bool) (hP : P.length = 16 * w * N) :
    (parse w P).toList =
      (List.range N).map fun i => block w ((P.drop (i * (16 * w))).take (16 * w)) := by
  rw [parse, Array.toList_map, List.toList_toArray,
    toChunks_eq_drop_take (16 * w) (by omega) P N hP, List.map_map]
  rfl

theorem length_lengthBits (L ℓ : Nat) : (lengthBits L ℓ).length = L := by
  simp [lengthBits]

theorem lengthBits_inj (L ℓ ℓ' : Nat) (hℓ : ℓ < 2 ^ L) (hℓ' : ℓ' < 2 ^ L)
    (h : lengthBits L ℓ = lengthBits L ℓ') : ℓ = ℓ' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · exact List.map_inj_left.mp h i (by simpa using hi)
  · have hp : 2 ^ L ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hℓ hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hℓ' hp)]

theorem zeros_spec (w ℓ : Nat) (hw : 0 < w) : ℓ + 1 + zeros w ℓ ≡ 14 * w [MOD 16 * w] := by
  have hB : 0 < 16 * w := by omega
  have hex : ∃ k ∈ List.range (16 * w), decide (ℓ + 1 + k ≡ 14 * w [MOD 16 * w]) = true := by
    have hlt := Nat.mod_lt (ℓ + 1) hB
    refine ⟨(16 * w - (ℓ + 1) % (16 * w) + 14 * w) % (16 * w),
      List.mem_range.mpr (Nat.mod_lt _ hB), decide_eq_true ?_⟩
    refine ((Nat.mod_modEq (ℓ + 1) (16 * w)).symm.add (Nat.mod_modEq _ (16 * w))).trans ?_
    rw [show (ℓ + 1) % (16 * w) + (16 * w - (ℓ + 1) % (16 * w) + 14 * w) = 16 * w + 14 * w by
      omega]
    exact Nat.add_modEq_left
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
  have hp := List.find?_some hk
  simp only [zeros, hk, Option.getD_some]
  exact of_decide_eq_true hp

theorem length_pad (w : Nat) (M : List Bool) :
    (pad w M).length = M.length + 1 + zeros w M.length + 2 * w := by
  simp only [pad, List.length_append, List.length_singleton, List.length_replicate,
    length_lengthBits]

theorem pad_length_dvd (w : Nat) (hw : 0 < w) (M : List Bool) :
    (pad w M).length = 16 * w * ((pad w M).length / (16 * w)) := by
  have e : (pad w M).length ≡ 0 [MOD 16 * w] := by
    rw [length_pad]
    refine ((zeros_spec w M.length hw).add_right (2 * w)).trans ?_
    rw [show 14 * w + 2 * w = 16 * w by omega]
    simp [Nat.ModEq]
  exact (Nat.mul_div_cancel' (Nat.modEq_zero_iff_dvd.mp e)).symm

theorem last_slice (A T : List Bool) (B n : Nat) (hlen : (A ++ T).length = B * (n + 1))
    (hT : T.length ≤ B) : ((A ++ T).drop (n * B)).take B = A.drop (n * B) ++ T := by
  rw [List.length_append, Nat.mul_succ, Nat.mul_comm] at hlen
  rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]

theorem append_inj {m n : Nat} {x x' : BitVec m} {y y' : BitVec n} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have e := congrArg (fun z => z.getLsbD (i + n)) h
    simpa [BitVec.getLsbD_append] using e
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have e := congrArg (fun z => z.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using e

theorem digest_inj {w : Nat} {H H' : Vector (BitVec w) 8} (h : digest H = digest H') : H = H' := by
  obtain ⟨h, h7⟩ := append_inj h
  obtain ⟨h, h6⟩ := append_inj h
  obtain ⟨h, h5⟩ := append_inj h
  obtain ⟨h, h4⟩ := append_inj h
  obtain ⟨h, h3⟩ := append_inj h
  obtain ⟨h, h2⟩ := append_inj h
  obtain ⟨h0, h1⟩ := append_inj h
  apply Vector.ext
  intro i hi
  interval_cases i <;> assumption

/-- Distinct messages of fewer than `2 ^ (2 w)` bits with equal final hash values give a
collision of the compression function. -/
theorem collision_of_final_eq (w : Nat) (hw : 0 < w)
    (f : Vector (BitVec w) 8 → Vector (BitVec w) 16 → Vector (BitVec w) 8)
    (H0 : Vector (BitVec w) 8) (M M' : List Bool) (hM : M.length < 2 ^ (2 * w))
    (hM' : M'.length < 2 ^ (2 * w)) (hne : M ≠ M') (heq : final w f H0 M = final w f H0 M') :
    Collision f := by
  obtain ⟨N, hP⟩ : ∃ N, (pad w M).length = 16 * w * N := ⟨_, pad_length_dvd w hw M⟩
  obtain ⟨N', hP'⟩ : ∃ N', (pad w M').length = 16 * w * N' := ⟨_, pad_length_dvd w hw M'⟩
  have hfold := heq
  rw [final, final, ← Array.foldl_toList, ← Array.foldl_toList,
    parse_toList w N hw _ hP, parse_toList w N' hw _ hP'] at hfold
  have hslice : ∀ (Q : List Bool) (K : Nat), (pad w Q).length = 16 * w * K → ∀ i < K,
      (((pad w Q).drop (i * (16 * w))).take (16 * w)).length = 16 * w := by
    intro Q K hQ i hi
    have := Nat.mul_le_mul_left (16 * w) (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this
    simp only [List.length_take, List.length_drop, hQ, Nat.mul_comm i (16 * w)]
    omega
  by_cases hl : M.length = M'.length
  · have hNN : N = N' := by
      have e : 16 * w * N = 16 * w * N' := by rw [← hP, ← hP', length_pad, length_pad, hl]
      exact Nat.eq_of_mul_eq_mul_left (by omega) e
    subst hNN
    rcases eq_or_collision f H0 _ _ (by simp) hfold with hb | hc
    · exfalso
      apply hne
      have hs : pad w M = pad w M' := by
        apply eq_of_slices (16 * w) N _ _ hP hP'
        intro i hi
        apply block_inj w hw _ _ (hslice M N hP i hi) (hslice M' N hP' i hi)
        have e := congrArg (fun l => l[i]?) hb
        simpa [hi] using e
      unfold pad at hs
      rw [← hl] at hs
      exact List.append_cancel_right (List.append_cancel_right (List.append_cancel_right hs))
    · exact hc
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
      refine ⟨N - 1, ?_⟩
      rcases N with _ | N
      · rw [length_pad] at hP
        omega
      · omega
    obtain ⟨n', rfl⟩ : ∃ n', N' = n' + 1 := by
      refine ⟨N' - 1, ?_⟩
      rcases N' with _ | N'
      · rw [length_pad] at hP'
        omega
      · omega
    rw [List.range_succ, List.range_succ, List.map_append, List.map_append, List.map_singleton,
      List.map_singleton] at hfold
    apply foldl_concat_collision f H0 _ _ _ _ _ hfold
    intro hbl
    apply hl
    have hs := block_inj w hw _ _ (hslice M (n + 1) hP n (by omega))
      (hslice M' (n' + 1) hP' n' (by omega)) hbl
    unfold pad at hP hP' hs
    rw [last_slice _ _ _ _ hP (by rw [length_lengthBits]; omega),
      last_slice _ _ _ _ hP' (by rw [length_lengthBits]; omega)] at hs
    exact lengthBits_inj (2 * w) _ _ hM hM'
      (List.append_inj' hs (by rw [length_lengthBits, length_lengthBits])).2

/-- Two distinct messages with equal SHA-256 digests give a collision of the SHA-256 compression
function of FIPS 180-4 §6.2.2. -/
theorem sha256_collision (M M' : Message) (hM : M.length < 2 ^ 64) (hM' : M'.length < 2 ^ 64)
    (hne : M ≠ M') (heq : SHA256.sha256 M hM = SHA256.sha256 M' hM') :
    Collision SHA256.compress :=
  collision_of_final_eq 32 (by decide) SHA256.compress SHA256.H0_256 M M' hM hM' hne
    (digest_inj (H := final 32 SHA256.compress SHA256.H0_256 M)
      (H' := final 32 SHA256.compress SHA256.H0_256 M') heq)

/-- Two distinct messages with equal SHA-512 digests give a collision of the SHA-512 compression
function of FIPS 180-4 §6.4.2. -/
theorem sha512_collision (M M' : Message) (hM : M.length < 2 ^ 128) (hM' : M'.length < 2 ^ 128)
    (hne : M ≠ M') (heq : SHA512.sha512 M hM = SHA512.sha512 M' hM') :
    Collision SHA512.compress :=
  collision_of_final_eq 64 (by decide) SHA512.compress SHA512.H0_512 M M' hM hM' hne
    (digest_inj (H := final 64 SHA512.compress SHA512.H0_512 M)
      (H' := final 64 SHA512.compress SHA512.H0_512 M') heq)

theorem flatMap_inj {α β : Type} (g : α → List β) (k : Nat) (hk : 0 < k)
    (hlen : ∀ a, (g a).length = k) (hg : ∀ a a', g a = g a' → a = a') :
    ∀ l l' : List α, l.flatMap g = l'.flatMap g → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons a' l' =>
      have e := congrArg List.length h
      simp [hlen] at e
      omega
  | cons a l ih =>
    intro l' h
    cases l' with
    | nil =>
      have e := congrArg List.length h
      simp [hlen] at e
      omega
    | cons a' l' =>
      rw [List.flatMap_cons, List.flatMap_cons] at h
      obtain ⟨ha, hl⟩ := List.append_inj h (by rw [hlen, hlen])
      rw [hg a a' ha, ih l' hl]

theorem byteToBits_inj (b b' : UInt8) (h : Equiv.Bytes.byteToBits b = Equiv.Bytes.byteToBits b') :
    b = b' :=
  UInt8.toNat_inj.mp (lengthBits_inj 8 _ _ b.toNat_lt b'.toNat_lt h)

theorem bytesToBitMessage_inj (B B' : ByteArray)
    (h : Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage B =
      Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage B') : B = B' := by
  have e := flatMap_inj Equiv.Bytes.byteToBits 8 (by decide) Equiv.Bytes.byteToBits_length
    byteToBits_inj _ _ h
  cases B
  cases B'
  rw [ByteArray.mk.injEq]
  exact Array.toList_inj.mp e

/-- Two distinct strings of fewer than `2 ^ 61` bytes with equal SHA-256 digests give a collision
of the SHA-256 compression function. -/
theorem sha256_bytes_collision (B B' : ByteArray) (hB : B.size < 2 ^ 61)
    (hB' : B'.size < 2 ^ 61) (hne : B ≠ B')
    (heq : SHA256.sha256 (Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage B)
        (Equiv.SHA256.Pipeline.bitLen_lt_of_size_lt B hB) =
      SHA256.sha256 (Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage B')
        (Equiv.SHA256.Pipeline.bitLen_lt_of_size_lt B' hB')) :
    Collision SHA256.compress :=
  sha256_collision _ _ _ _ (fun h => hne (bytesToBitMessage_inj B B' h)) heq

/-- Two distinct strings of fewer than `2 ^ 61` bytes with equal SHA-512 digests give a collision
of the SHA-512 compression function. -/
theorem sha512_bytes_collision (B B' : ByteArray) (hB : B.size < 2 ^ 61)
    (hB' : B'.size < 2 ^ 61) (hne : B ≠ B')
    (heq : SHA512.sha512 (Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage B)
        (Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt B hB) =
      SHA512.sha512 (Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage B')
        (Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt B' hB')) :
    Collision SHA512.compress :=
  sha512_collision _ _ _ _ (fun h => hne (bytesToBitMessage_inj B B' h)) heq

#print axioms sha256_collision
#print axioms sha512_collision
#print axioms sha256_bytes_collision
#print axioms sha512_bytes_collision

end Library.Hashing.MerkleDamgard
