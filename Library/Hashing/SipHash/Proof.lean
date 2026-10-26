import Library.Hashing.SipHash.Program
import Library.Bytes.LittleEndian
import Mathlib.Tactic

/-! The SipHash programs compute the transcription.  The program's rotation by shifts is the
transcription's `BitVec` rotation at each of SipRound's amounts, so `sipRound` is SipRound, and the
loops of `rounds` and of `sipHashWith` are the iterations and the fold of the specification.  The
packed message's word `i` is the message word `m_i` of §2 for `i < n / 8`, and `lastWord` is the
last, which `messageWords_eq` states.  The key words are the little-endian words of the key's
bytes, packed as the message is. -/

namespace Library.Hashing.SipHash.Proof

open Library.Hashing.SipHash Library.Bytes
open Library.Hashing.SipHash.Spec (State)

/-! ## SipRound -/

theorem rotl_13 (x : UInt64) : rotl x 13 = Spec.rotl x 13 := by
  apply UInt64.toBitVec_inj.mp
  simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_16 (x : UInt64) : rotl x 16 = Spec.rotl x 16 := by
  apply UInt64.toBitVec_inj.mp
  simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_17 (x : UInt64) : rotl x 17 = Spec.rotl x 17 := by
  apply UInt64.toBitVec_inj.mp
  simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_21 (x : UInt64) : rotl x 21 = Spec.rotl x 21 := by
  apply UInt64.toBitVec_inj.mp
  simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_32 (x : UInt64) : rotl x 32 = Spec.rotl x 32 := by
  apply UInt64.toBitVec_inj.mp
  simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem sipRound_eq (v : State) : sipRound v = Spec.sipRound v := by
  simp only [sipRound, Spec.sipRound, rotl_13, rotl_16, rotl_17, rotl_21, rotl_32]

theorem rounds_succ (n : Nat) (s : State) :
    Spec.rounds (n + 1) s = Spec.sipRound (Spec.rounds n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (Spec.sipRound s)

theorem rounds_eq (k : UInt64) (v : State) : rounds k v = Spec.rounds k.toNat v := by
  unfold rounds LeanExe.loop
  induction k.toNat with
  | zero => rfl
  | succ m ih =>
    simp only [Nat.fold_succ]
    rw [ih, sipRound_eq, rounds_succ]

theorem compress_eq (c : UInt64) (v : State) (m : UInt64) :
    compress c v m = Spec.compress c.toNat v m := by
  simp only [compress, Spec.compress, rounds_eq]

/-! ## Little-endian words -/

/-- The little-endian word of the eight bytes of `w` is `w`. -/
theorem le64_bytes (w : UInt64) : Spec.le64 ((List.range 8).map (byteOf w)) = w := by
  rw [Spec.le64, foldr_byteOf]
  exact UInt64.ofNat_toNat

/-! ## The message words -/

/-- The value of the program's last message word. -/
theorem lastWord_toNat (msg : Array UInt64) (n : UInt64) :
    (lastWord msg n).toNat =
      msg[n.toNat / 8]!.toNat % 256 ^ (n.toNat % 8) + 256 ^ 7 * (n.toNat % 256) := by
  have hr : n.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have hs : ((n &&& 7) <<< 3).toNat = 8 * (n.toNat % 8) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show n.toNat % 2 ^ 3 * 2 ^ 3 < 2 ^ 64 by omega)]
    omega
  have hpow : ((1 : UInt64) <<< ((n &&& 7) <<< 3)).toNat = 2 ^ (8 * (n.toNat % 8)) := by
    rw [UInt64.toNat_shiftLeft, hs, Nat.mod_eq_of_lt (show 8 * (n.toNat % 8) < 64 by omega),
      show (1 : UInt64).toNat = 1 from rfl, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2)
        (show 8 * (n.toNat % 8) < 64 by omega))]
  have hmask : (((1 : UInt64) <<< ((n &&& 7) <<< 3)) - 1).toNat =
      2 ^ (8 * (n.toNat % 8)) - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, hpow]; exact Nat.one_le_two_pow), hpow]
    rfl
  have hhigh : (n <<< 56).toNat = 2 ^ 56 * (n.toNat % 256) := by
    rw [UInt64.toNat_shiftLeft, show (56 : UInt64).toNat % 64 = 56 from rfl, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 64 = 256 * 2 ^ 56 by norm_num, Nat.mul_mod_mul_right, mul_comm]
  have hlow : msg[n.toNat / 8]!.toNat % 2 ^ (8 * (n.toNat % 8)) < 2 ^ 56 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) (by omega))
  have hq : (n >>> 3).toNat = n.toNat / 8 := by
    rw [UInt64.toNat_shiftRight, show (3 : UInt64).toNat % 64 = 3 from rfl,
      Nat.shiftRight_eq_div_pow]
  rw [lastWord, UInt64.toNat_or, UInt64.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hhigh,
    hq, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hlow, pow_mul]
  norm_num
  ring

/-- The message words of the first `n` bytes of `msg` are the array's first `n / 8` words and
`lastWord msg n`. -/
theorem messageWords_eq (msg : Array UInt64) (n : UInt64) :
    Spec.messageWords ((List.range n.toNat).map (byteAt msg)) =
      (List.range (n.toNat / 8)).map (fun i => msg[i]!) ++ [lastWord msg n] := by
  set b := n.toNat with hb
  set q := b / 8 with hqdef
  have hw : (b + 1 + 7) / 8 = q + 1 := by omega
  set L := (List.range b).map (byteAt msg) with hLdef
  have hL : L.length = b := by simp [L]
  set p := L ++ List.replicate (8 * (q + 1) - 1 - b) 0 ++ [UInt8.ofNat (b % 256)] with hp
  have hplen : p.length = 8 * (q + 1) := by simp [p, hL]; omega
  have hget : ∀ k, k < 8 * (q + 1) →
      p.getD k 0 = if k < b then byteAt msg k else if k = 8 * q + 7 then UInt8.ofNat (b % 256)
        else 0 := by
    intro k hk
    simp only [p, List.append_assoc, List.getD_eq_getElem?_getD]
    by_cases h1 : k < b
    · rw [List.getElem?_append_left (by rw [hL]; exact h1)]
      simp [L, h1]
    · rw [List.getElem?_append_right (by rw [hL]; omega), hL]
      by_cases h2 : k - b < 8 * (q + 1) - 1 - b
      · rw [List.getElem?_append_left (by simpa using h2)]
        simp [h2, h1, show k ≠ 8 * q + 7 by omega]
      · rw [List.getElem?_append_right (by simp; omega), List.length_replicate,
          show k - b - (8 * (q + 1) - 1 - b) = 0 by omega]
        simp [show k = 8 * q + 7 by omega, show ¬ 8 * q + 7 < b by omega]
  unfold Spec.messageWords
  simp only [hL, hw]
  rw [← hp, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi : i < q := List.mem_range.mp hi
    rw [chunk_eq p (8 * i) 8 (by omega)]
    have : (List.range 8).map (fun j => p.getD (8 * i + j) 0) =
        (List.range 8).map (byteOf msg[i]!) :=
      List.map_congr_left fun j hj => by
        have hj : j < 8 := List.mem_range.mp hj
        rw [hget _ (by omega)]
        simp only [show 8 * i + j < b by omega, ↓reduceIte]
        exact byteAt_eq _ _ _ hj
    rw [this, le64_bytes]
  · congr 1
    rw [chunk_eq p (8 * q) 8 (by omega)]
    have hr : b % 8 < 8 := Nat.mod_lt _ (by decide)
    have hterm : ∀ j ∈ Finset.range 7, ((p.getD (8 * q + j) 0).toNat * 256 ^ j) =
        if j < b % 8 then msg[q]!.toNat / 256 ^ j % 256 * 256 ^ j else 0 := by
      intro j hj
      have hj : j < 7 := Finset.mem_range.mp hj
      rw [hget _ (by omega)]
      by_cases h : j < b % 8
      · simp only [show 8 * q + j < b by omega, h, ↓reduceIte]
        rw [byteAt_eq _ _ _ (by omega), byteOf_toNat _ (by omega)]
      · simp [show ¬ 8 * q + j < b by omega, h, show j ≠ 7 by omega]
    have hfilter : (Finset.range 7).filter (· < b % 8) = Finset.range (b % 8) := by
      ext j; simp; omega
    have hlast : (p.getD (8 * q + 7) 0).toNat = b % 256 := by
      rw [hget _ (by omega)]
      simp [show ¬ 8 * q + 7 < b by omega, UInt8.toNat_ofNat']
    apply UInt64.toNat_inj.mp
    rw [lastWord_toNat, Spec.le64, UInt64.toNat_ofNat', foldr_range, Finset.sum_range_succ,
      Finset.sum_congr rfl hterm, ← Finset.sum_filter, hfilter, sum_digits, hlast, ← hb, ← hqdef]
    have hlt : msg[q]!.toNat % 256 ^ (b % 8) < 256 ^ 7 :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_of_lt (by omega)]
    ring

/-! ## The functions -/

theorem loop_eq (c : UInt64) (msg : Array UInt64) (v : State) (q : Nat) (hq : q < 2 ^ 64) :
    Nat.fold q (fun i _ v => compress c v msg[(UInt64.ofNat i).toNat]!) v =
      ((List.range q).map (fun i => msg[i]!)).foldl (Spec.compress c.toNat) v := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [Nat.fold_succ]
    rw [ih (by omega), List.range_succ, List.map_append, List.foldl_append, List.map_singleton,
      List.foldl_cons, List.foldl_nil, compress_eq, UInt64.toNat_ofNat_of_lt' (by
        show q < 2 ^ 64; omega)]

theorem key_take (k0 k1 : UInt64) :
    ((List.range 16).map (byteAt #[k0, k1])).take 8 = (List.range 8).map (byteOf k0) := by
  apply List.ext_getElem (by simp)
  intro j _ h2
  have hj : j < 8 := by simpa using h2
  have h := byteAt_eq #[k0, k1] 0 j hj
  simp only [Nat.mul_zero, Nat.zero_add] at h
  simp only [List.getElem_take, List.getElem_map, List.getElem_range, h]
  rfl

theorem key_drop (k0 k1 : UInt64) :
    (((List.range 16).map (byteAt #[k0, k1])).drop 8).take 8 = (List.range 8).map (byteOf k1) := by
  apply List.ext_getElem (by simp)
  intro j _ h2
  have hj : j < 8 := by simpa using h2
  have h := byteAt_eq #[k0, k1] 1 j hj
  simp only [Nat.mul_one] at h
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range, h]
  rfl

/-- `sipHashWith` computes SipHash-c-d of the key whose 16 bytes are those of `k0` and `k1` and of
the first `n` bytes of `msg`. -/
theorem sipHashWith_eq (c d k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) :
    sipHashWith c d k0 k1 msg n =
      Spec.sipHash c.toNat d.toNat ((List.range 16).map (byteAt #[k0, k1]))
        ((List.range n.toNat).map (byteAt msg)) := by
  have hq : (n >>> 3).toNat = n.toNat / 8 := by
    rw [UInt64.toNat_shiftRight, show (3 : UInt64).toNat % 64 = 3 from rfl,
      Nat.shiftRight_eq_div_pow]
  simp only [sipHashWith, Spec.sipHash, Spec.finalize, key_take, key_drop, le64_bytes,
    messageWords_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold LeanExe.loop
  rw [hq, loop_eq c msg _ _ (by have := n.toNat_lt; omega), compress_eq, rounds_eq]
  rfl

/-- `siphash24` computes SipHash-2-4. -/
theorem siphash24_spec (k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) :
    siphash24 k0 k1 msg n =
      Spec.sipHash 2 4 ((List.range 16).map (byteAt #[k0, k1]))
        ((List.range n.toNat).map (byteAt msg)) :=
  sipHashWith_eq 2 4 k0 k1 msg n

/-- `siphash13` computes SipHash-1-3. -/
theorem siphash13_spec (k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) :
    siphash13 k0 k1 msg n =
      Spec.sipHash 1 3 ((List.range 16).map (byteAt #[k0, k1]))
        ((List.range n.toNat).map (byteAt msg)) :=
  sipHashWith_eq 1 3 k0 k1 msg n

end Library.Hashing.SipHash.Proof
