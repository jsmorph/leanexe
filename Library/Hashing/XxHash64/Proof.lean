import Library.Hashing.XxHash64.Program
import Library.Bytes.LittleEndian
import Mathlib.Tactic

/-! The XXH64 program computes the transcription.  The program's rotations by shifts are the
transcription's `BitVec` rotations at each amount that XXH64 uses, so `stripeAt`, `converge`, and
`avalanche` compute steps 2, 3, and 6.  For the bytes `M` of the packed message, `lane_le` reads
the eight bytes from position `8 i` as word `i` of the array and `half_le` reads four as its low
half.  The stripe loop of step 2 and the loop of lanes of 8 bytes of step 5 then follow by
induction on the number of stripes or lanes that remain, and the single bytes by `byte_eq`. -/

namespace Library.Hashing.XxHash64.Proof

open Library.Hashing.XxHash64 Library.Bytes
open Library.Hashing.XxHash64.Spec (Accs PRIME64_1 PRIME64_2 PRIME64_3 PRIME64_4 PRIME64_5)

/-! ## Rotations and the steps on words -/

theorem rotl_1 (x : UInt64) : rotl x 1 = Spec.rotl x 1 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_7 (x : UInt64) : rotl x 7 = Spec.rotl x 7 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_11 (x : UInt64) : rotl x 11 = Spec.rotl x 11 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_12 (x : UInt64) : rotl x 12 = Spec.rotl x 12 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_18 (x : UInt64) : rotl x 18 = Spec.rotl x 18 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_23 (x : UInt64) : rotl x 23 = Spec.rotl x 23 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_27 (x : UInt64) : rotl x 27 = Spec.rotl x 27 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem rotl_31 (x : UInt64) : rotl x 31 = Spec.rotl x 31 := by
  apply UInt64.toBitVec_inj.mp; simp [rotl, Spec.rotl, BitVec.rotateLeft_def]

theorem round_eq (acc lane : UInt64) : round acc lane = Spec.round acc lane := by
  simp only [round, Spec.round, rotl_31]

theorem converge_eq (a : Accs) : converge a = Spec.converge a := by
  simp only [converge, Spec.converge, Spec.mergeAccumulator, mergeAccumulator, round_eq, rotl_1,
    rotl_7, rotl_12, rotl_18]

theorem avalanche_eq (acc : UInt64) : avalanche acc = Spec.avalanche acc := rfl

/-! ## The bytes of the packed message -/

theorem getD_bytes (msg : Array UInt64) {n k : Nat} (hk : k < n) :
    ((List.range n).map (byteAt msg)).getD k 0 = byteOf msg[k / 8]! (k % 8) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- The eight bytes of the message from position `8 i` are word `i`. -/
theorem lane_le (msg : Array UInt64) {n i : Nat} (h : 8 * i + 8 ≤ n) :
    Spec.le ((((List.range n).map (byteAt msg)).drop (8 * i)).take 8) = msg[i]! := by
  rw [chunk_eq _ _ _ (by simp; omega)]
  have : (List.range 8).map (fun t => ((List.range n).map (byteAt msg)).getD (8 * i + t) 0) =
      (List.range 8).map (byteOf msg[i]!) :=
    List.map_congr_left fun t ht => by
      have ht : t < 8 := List.mem_range.mp ht
      rw [getD_bytes msg (by omega), show (8 * i + t) / 8 = i by omega,
        show (8 * i + t) % 8 = t by omega]
  rw [this, Spec.le, foldr_byteOf]
  exact UInt64.ofNat_toNat

/-- The four bytes of the message from position `8 i` are the low half of word `i`. -/
theorem half_le (msg : Array UInt64) {n i : Nat} (h : 8 * i + 4 ≤ n) :
    Spec.le ((((List.range n).map (byteAt msg)).drop (8 * i)).take 4) = msg[i]! &&& 0xFFFFFFFF := by
  rw [chunk_eq _ _ _ (by simp; omega)]
  apply UInt64.toNat_inj.mp
  rw [Spec.le, UInt64.toNat_ofNat', foldr_range, UInt64.toNat_and,
    show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have : ∀ t ∈ Finset.range 4,
      (((List.range n).map (byteAt msg)).getD (8 * i + t) 0).toNat * 256 ^ t =
        (msg[i]!.toNat / 256 ^ t % 256) * 256 ^ t := fun t ht => by
    have ht : t < 4 := Finset.mem_range.mp ht
    rw [getD_bytes msg (by omega), show (8 * i + t) / 8 = i by omega,
      show (8 * i + t) % 8 = t by omega, byteOf_toNat _ (by omega)]
  rw [Finset.sum_congr rfl this, sum_digits, show (256 : Nat) ^ 4 = 2 ^ 32 by norm_num,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num))]

/-- The program's byte at index `q` is byte `q` of the message. -/
theorem byte_eq (msg : Array UInt64) {q : Nat} (hq : q < 2 ^ 64) :
    (msg[(UInt64.ofNat q >>> 3).toNat]! >>> ((UInt64.ofNat q &&& 7) <<< 3)) &&& 0xFF =
      (byteOf msg[q / 8]! (q % 8)).toUInt64 := by
  have hit : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hq
  have hword : (UInt64.ofNat q >>> 3).toNat = q / 8 := by
    rw [UInt64.toNat_shiftRight, hit, show (3 : UInt64).toNat % 64 = 3 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hshift : ((UInt64.ofNat q &&& 7) <<< 3).toNat = 8 * (q % 8) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, hit, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show q % 2 ^ 3 * 2 ^ 3 < 2 ^ 64 by omega)]
    omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hword, hshift,
    Nat.mod_eq_of_lt (show 8 * (q % 8) < 64 by omega), show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt8.toNat_toUInt64, byteOf, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight,
    show (8 * (q % 8)).toUInt64.toNat = 8 * (q % 8) from
      UInt64.toNat_ofNat_of_lt' (show 8 * (q % 8) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 8 * (q % 8) < 64 by omega)]

/-! ## The loops -/

theorem fold_eq {α : Type} (f : Nat → α → α) (k : Nat) (init : α) :
    Nat.fold k (fun i _ a => f i a) init = (List.range k).foldl (fun a i => f i a) init := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.fold_succ, ih, List.range_succ, List.foldl_append]
    rfl

theorem getD_take_drop (l : List UInt8) {a b x : Nat} (hx : x < b) :
    ((l.drop a).take b).getD x 0 = l.getD (a + x) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hx]

/-- Lane `t` of stripe `j` of the message is word `4 j + t`. -/
theorem lane_stripe (msg : Array UInt64) {n j t : Nat} (h : 32 * j + 32 ≤ n) (ht : t < 4) :
    Spec.lane ((((List.range n).map (byteAt msg)).drop (32 * j)).take 32) t = msg[4 * j + t]! := by
  set M := (List.range n).map (byteAt msg)
  have hlen : (((M.drop (32 * j)).take 32)).length = 32 := by simp [M]; omega
  have : (((M.drop (32 * j)).take 32).drop (8 * t)).take 8 = (M.drop (8 * (4 * j + t))).take 8 := by
    rw [chunk_eq ((M.drop (32 * j)).take 32) (8 * t) 8 (by omega),
      chunk_eq M (8 * (4 * j + t)) 8 (by simp [M]; omega)]
    apply List.map_congr_left
    intro i hi
    have hi : i < 8 := List.mem_range.mp hi
    rw [getD_take_drop _ (by omega), show 32 * j + (8 * t + i) = 8 * (4 * j + t) + i by ring]
  rw [Spec.lane, this, lane_le msg (by omega)]

/-- Step 2 on stripe `j` of the message is `stripeAt`. -/
theorem stripe_eq (msg : Array UInt64) (a : Accs) {n j : Nat} (h : 32 * j + 32 ≤ n)
    (hn : n < 2 ^ 64) :
    Spec.stripe a ((((List.range n).map (byteAt msg)).drop (32 * j)).take 32) =
      stripeAt msg a (UInt64.ofNat j) := by
  have hw : ∀ t : UInt64, t.toNat < 4 →
      ((UInt64.ofNat j <<< 2) + t).toNat = 4 * j + t.toNat := by
    intro t ht
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega),
      show (2 : UInt64).toNat % 64 = 2 from rfl, Nat.shiftLeft_eq]
    omega
  have e0 : (UInt64.ofNat j <<< 2).toNat = 4 * j := by simpa using hw 0 (by decide)
  have e1 : ((UInt64.ofNat j <<< 2) + 1).toNat = 4 * j + 1 := hw 1 (by decide)
  have e2 : ((UInt64.ofNat j <<< 2) + 2).toNat = 4 * j + 2 := hw 2 (by decide)
  have e3 : ((UInt64.ofNat j <<< 2) + 3).toNat = 4 * j + 3 := hw 3 (by decide)
  rw [Spec.stripe, lane_stripe msg h (by decide : 0 < 4), lane_stripe msg h (by decide : 1 < 4),
    lane_stripe msg h (by decide : 2 < 4), lane_stripe msg h (by decide : 3 < 4), stripeAt]
  simp only [e0, e1, e2, e3, round_eq, Nat.add_zero]

/-- Step 2 from stripe `n / 32 - k` of the message: the stripes in turn, and the bytes after the
last stripe. -/
theorem stripes_from (msg : Array UInt64) {n : Nat} (hn : n < 2 ^ 64) (k : Nat) (hk : k ≤ n / 32)
    (a : Accs) :
    Spec.stripes a (((List.range n).map (byteAt msg)).drop (32 * (n / 32 - k))) =
      ((List.range' (n / 32 - k) k).foldl (fun a j => stripeAt msg a (UInt64.ofNat j)) a,
        ((List.range n).map (byteAt msg)).drop (32 * (n / 32))) := by
  induction k generalizing a with
  | zero =>
    rw [Spec.stripes]
    split_ifs with h
    · simp at h; omega
    · simp
  | succ k ih =>
    rw [Spec.stripes]
    split_ifs with h
    · rw [stripe_eq msg a (by omega) hn, List.drop_drop,
        show 32 * (n / 32 - (k + 1)) + 32 = 32 * (n / 32 - k) by omega, ih (by omega),
        List.range'_succ, List.foldl_cons, show n / 32 - (k + 1) + 1 = n / 32 - k by omega]
    · simp at h; omega

/-- The first loop of step 5 from lane `n / 8 - k` of the message: the lanes in turn, and the
bytes after the last lane. -/
theorem lanes8_from (msg : Array UInt64) {n : Nat} (k : Nat) (hk : k ≤ n / 8) (acc : UInt64) :
    Spec.lanes8 acc (((List.range n).map (byteAt msg)).drop (8 * (n / 8 - k))) =
      ((List.range' (n / 8 - k) k).foldl
          (fun acc i => Spec.rotl (acc ^^^ Spec.round 0 msg[i]!) 27 * PRIME64_1 + PRIME64_4) acc,
        ((List.range n).map (byteAt msg)).drop (8 * (n / 8))) := by
  induction k generalizing acc with
  | zero =>
    rw [Spec.lanes8]
    split_ifs with h
    · simp at h; omega
    · simp
  | succ k ih =>
    rw [Spec.lanes8]
    split_ifs with h
    · simp only
      rw [lane_le msg (by omega), List.drop_drop,
        show 8 * (n / 8 - (k + 1)) + 8 = 8 * (n / 8 - k) by omega, ih (by omega), List.range'_succ,
        List.foldl_cons, show n / 8 - (k + 1) + 1 = n / 8 - k by omega]
    · simp at h; omega

theorem xxh64_def (m : List UInt8) (seed : UInt64) :
    Spec.xxh64 m seed =
      let pre := if 32 ≤ m.length then
          (Spec.converge (Spec.stripes (Spec.initAccs seed) m).1,
            (Spec.stripes (Spec.initAccs seed) m).2)
        else (seed + PRIME64_5, m)
      Spec.avalanche (Spec.consume (pre.1 + UInt64.ofNat m.length) pre.2) := by
  unfold Spec.xxh64
  by_cases h : 32 ≤ m.length
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]

theorem consume_def (acc : UInt64) (m : List UInt8) :
    Spec.consume acc m = Spec.bytes (Spec.lane4 (Spec.lanes8 acc m).1 (Spec.lanes8 acc m).2).1
      (Spec.lane4 (Spec.lanes8 acc m).1 (Spec.lanes8 acc m).2).2 := rfl

section Phases

variable (msg : Array UInt64) (n : UInt64)

theorem toNat_shr5 : (n >>> 5).toNat = n.toNat / 32 := by
  rw [UInt64.toNat_shiftRight, show (5 : UInt64).toNat % 64 = 5 from rfl, Nat.shiftRight_eq_div_pow]

theorem toNat_shr3 : (n >>> 3).toNat = n.toNat / 8 := by
  rw [UInt64.toNat_shiftRight, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftRight_eq_div_pow]

/-- Steps 1 to 3 and the bytes after the stripes. -/
theorem start_eq (seed : UInt64) :
    (if 32 ≤ ((List.range n.toNat).map (byteAt msg)).length then
        (Spec.converge (Spec.stripes (Spec.initAccs seed) ((List.range n.toNat).map (byteAt msg))).1,
          (Spec.stripes (Spec.initAccs seed) ((List.range n.toNat).map (byteAt msg))).2)
      else (seed + PRIME64_5, (List.range n.toNat).map (byteAt msg))) =
      (start msg n seed, ((List.range n.toNat).map (byteAt msg)).drop (32 * (n.toNat / 32))) := by
  have hn := n.toNat_lt
  have hst := stripes_from msg hn (n.toNat / 32) le_rfl ⟨seed + PRIME64_1 + PRIME64_2,
    seed + PRIME64_2, seed, seed - PRIME64_1⟩
  rw [Nat.sub_self, Nat.mul_zero, List.drop_zero, List.range'_eq_map_range] at hst
  simp only [Nat.zero_add, show (fun x : Nat => x) = id from rfl, List.map_id] at hst
  have hinit : Spec.initAccs seed =
      ⟨seed + PRIME64_1 + PRIME64_2, seed + PRIME64_2, seed, seed - PRIME64_1⟩ := by
    simp [Spec.initAccs]
  rw [List.length_map, List.length_range, start]
  by_cases hlt : n.toNat < 32
  · have : n < 32 := by rw [UInt64.lt_iff_toNat_lt]; exact hlt
    simp only [show ¬ 32 ≤ n.toNat by omega, ↓reduceIte, this,
      show n.toNat / 32 = 0 by omega, Nat.mul_zero, List.drop_zero]
  · have : ¬ n < 32 := by rw [UInt64.lt_iff_toNat_lt]; exact hlt
    simp only [show 32 ≤ n.toNat by omega, ↓reduceIte, this, hinit, converge_eq]
    unfold LeanExe.loop
    rw [toNat_shr5, fold_eq, hst]

/-- The lanes of 8 bytes of step 5. -/
theorem lanes8_eq (acc : UInt64) :
    Spec.lanes8 acc (((List.range n.toNat).map (byteAt msg)).drop (32 * (n.toNat / 32))) =
      (lanes8 msg n acc, ((List.range n.toNat).map (byteAt msg)).drop (8 * (n.toNat / 8))) := by
  have hn := n.toNat_lt
  have h52 : ((n >>> 5) <<< 2).toNat = 4 * (n.toNat / 32) := by
    rw [UInt64.toNat_shiftLeft, toNat_shr5, show (2 : UInt64).toNat % 64 = 2 from rfl,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    ring
  have hcount : ((n >>> 3) - ((n >>> 5) <<< 2)).toNat = n.toNat / 8 - 4 * (n.toNat / 32) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h52, toNat_shr3]; omega), h52,
      toNat_shr3]
  have hl := lanes8_from msg (n := n.toNat) (n.toNat / 8 - 4 * (n.toNat / 32)) (by omega) acc
  rw [show n.toNat / 8 - (n.toNat / 8 - 4 * (n.toNat / 32)) = 4 * (n.toNat / 32) by omega,
    show 8 * (4 * (n.toNat / 32)) = 32 * (n.toNat / 32) by ring, List.range'_eq_map_range,
    List.foldl_map] at hl
  rw [hl, lanes8]
  congr 1
  unfold LeanExe.loop
  rw [hcount, fold_eq]
  apply List.foldl_ext
  intro a i hi
  have hi : i < n.toNat / 8 - 4 * (n.toNat / 32) := List.mem_range.mp hi
  have hidx : ((n >>> 5 <<< 2) + UInt64.ofNat i).toNat = 4 * (n.toNat / 32) + i := by
    rw [UInt64.toNat_add, h52, UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  simp only [hidx, round_eq, rotl_27]

/-- The lane of 4 bytes of step 5. -/
theorem lane4_eq (acc : UInt64) :
    Spec.lane4 acc (((List.range n.toNat).map (byteAt msg)).drop (8 * (n.toNat / 8))) =
      (lane4 msg n acc, ((List.range n.toNat).map (byteAt msg)).drop (n.toNat - n.toNat % 4)) := by
  have h7 : (n &&& 7).toNat = n.toNat % 8 := by
    rw [UInt64.toNat_and, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  rw [Spec.lane4, lane4]
  by_cases h : n.toNat % 8 < 4
  · have : (n &&& 7) < 4 := by rw [UInt64.lt_iff_toNat_lt, h7]; exact h
    simp only [List.length_drop, List.length_map, List.length_range,
      show 8 * (n.toNat / 8) = n.toNat - n.toNat % 4 by omega,
      show ¬ 4 ≤ n.toNat - (n.toNat - n.toNat % 4) by omega, ↓reduceIte, this]
  · have : ¬ (n &&& 7) < 4 := by rw [UInt64.lt_iff_toNat_lt, h7]; exact h
    simp only [List.length_drop, List.length_map, List.length_range,
      show 4 ≤ n.toNat - 8 * (n.toNat / 8) by omega, ↓reduceIte, this, List.drop_drop,
      half_le msg (show 8 * (n.toNat / 8) + 4 ≤ n.toNat by omega), toNat_shr3, rotl_23,
      show 8 * (n.toNat / 8) + 4 = n.toNat - n.toNat % 4 by omega]

/-- The single bytes of step 5. -/
theorem bytes_eq (acc : UInt64) :
    Spec.bytes acc (((List.range n.toNat).map (byteAt msg)).drop (n.toNat - n.toNat % 4)) =
      bytes msg n acc := by
  have hn := n.toNat_lt
  set M := (List.range n.toNat).map (byteAt msg) with hM
  have hlen : M.length = n.toNat := by simp [M]
  have hb : (n &&& 3).toNat = n.toNat % 4 := by
    rw [UInt64.toNat_and, show (3 : UInt64).toNat = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hp : (n - (n &&& 3)).toNat = n.toNat - n.toNat % 4 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hb]; omega), hb]
  have hdrop : M.drop (n.toNat - n.toNat % 4) =
      (List.range (n.toNat % 4)).map fun i => M.getD (n.toNat - n.toNat % 4 + i) 0 := by
    rw [← chunk_eq M _ _ (by omega), List.take_of_length_le (by simp [hlen]; omega)]
  rw [hdrop, Spec.bytes, List.foldl_map, bytes]
  unfold LeanExe.loop
  rw [hb, fold_eq]
  apply List.foldl_ext
  intro a i hi
  have hi : i < n.toNat % 4 := List.mem_range.mp hi
  have hq : (n - (n &&& 3)) + UInt64.ofNat i = UInt64.ofNat (n.toNat - n.toNat % 4 + i) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, hp, UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega),
      UInt64.toNat_ofNat_of_lt' (show n.toNat - n.toNat % 4 + i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  simp only [hq, byte_eq msg (show n.toNat - n.toNat % 4 + i < 2 ^ 64 by omega), hM,
    getD_bytes msg (show n.toNat - n.toNat % 4 + i < n.toNat by omega), rotl_11]

end Phases

/-- `xxh64` computes XXH64 of the first `n` bytes of `msg` with the seed `seed`. -/
theorem xxh64_eq (msg : Array UInt64) (n seed : UInt64) :
    xxh64 msg n seed = Spec.xxh64 ((List.range n.toNat).map (byteAt msg)) seed := by
  have hlen : UInt64.ofNat ((List.range n.toNat).map (byteAt msg)).length = n := by
    rw [List.length_map, List.length_range, UInt64.ofNat_toNat]
  simp only [xxh64_def, start_eq, hlen, consume_def, lanes8_eq, lane4_eq, bytes_eq, xxh64,
    avalanche_eq]

end Library.Hashing.XxHash64.Proof
