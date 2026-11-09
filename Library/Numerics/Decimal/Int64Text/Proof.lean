import Library.Numerics.Decimal.Int64Text.Program
import Library.Numerics.Decimal.Int64Text.Inverse
import LeanExe.Dialect.Lemmas
import LeanExe.ProofKit.Signed64

/-!
The program equals the specification: `printInt64_eq` and `readInt64_eq`.  The printer's proof
reads element `j` of the digits of `m` as `m / 10 ^ (L - 1 - j) % 10` (`digitWords_getElem?`), the
count of digits through `Nat.length_toDigits_le_iff` (`digitCount_toNat`), and digit `k` as the
quotient by `10 ^ k` of `k` divisions by 10 (`digitByte_eq`).  The reader's proof reads the scan
of at most 19 digits as the specification's `digitsValue`, which stays below `10 ^ 19 < 2 ^ 64`
(`scanDigits_spec`), and compares the program's tests with `magnitude`'s through `magnitude_cons`.
`readInt64_printInt64` and `printInt64_of_read` restate the specification's inverse theorems for
the program.
-/

namespace Library.Numerics.Decimal.Int64Text

open Library.Numerics.Decimal.Shared.StrconvGrammar

/-! ## The printer -/

theorem div_pow_succ (m t : Nat) : m / 10 / 10 ^ t = m / 10 ^ (t + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- Element `j` of the digits of `m`, counted from the most significant. -/
theorem digitWords_getElem? (m j : Nat) :
    (digitWords m)[j]? = if j < (digitWords m).length then
      some (UInt64.ofNat (m / 10 ^ ((digitWords m).length - 1 - j) % 10 + 48)) else none := by
  induction m using Nat.strong_induction_on generalizing j with
  | _ m ih =>
    by_cases hm : m < 10
    · rw [digitWords_small hm]
      rcases j with _ | j
      · simp [Nat.mod_eq_of_lt hm]
      · simp
    · have hq : 0 < m / 10 := by omega
      have he : m % 10 < 10 := Nat.mod_lt _ (by decide)
      have hD : digitWords m = digitWords (m / 10) ++ [UInt64.ofNat (m % 10 + 48)] := by
        conv_lhs => rw [(Nat.div_add_mod m 10).symm]
        exact digitWords_snoc hq he
      rw [hD, List.length_append, List.length_singleton]
      have ihq := ih (m / 10) (by omega)
      by_cases hj : j < (digitWords (m / 10)).length
      · rw [List.getElem?_append_left hj, ihq j, ite_eq_left hj, ite_eq_left (by omega),
          show (digitWords (m / 10)).length + 1 - 1 - j =
            ((digitWords (m / 10)).length - 1 - j) + 1 by omega, ← div_pow_succ]
      · rw [List.getElem?_append_right (by omega)]
        by_cases hj' : j = (digitWords (m / 10)).length
        · subst hj'
          simp
        · rw [ite_eq_right (by omega), List.getElem?_eq_none (by simp; omega)]

theorem digitWords_length_le (m : Nat) (hm : m < 2 ^ 64) : (digitWords m).length ≤ 20 := by
  rw [digitWords, List.length_map]
  exact (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by omega)

theorem digitWords_length_pos (m : Nat) : 0 < (digitWords m).length := by
  rw [digitWords, List.length_map]
  exact Nat.length_toDigits_pos

/-- `L ≤ k` for the count `L` of digits of `m` exactly when `m < 10 ^ k`. -/
theorem digitWords_length_le_iff (m k : Nat) (hk : 0 < k) :
    (digitWords m).length ≤ k ↔ m < 10 ^ k := by
  rw [digitWords, List.length_map]
  exact Nat.length_toDigits_le_iff (by decide) hk

theorem digitCount_toNat (m : UInt64) : (digitCount m).toNat = (digitWords m.toNat).length := by
  have hm := m.toNat_lt
  have hL1 := digitWords_length_pos m.toNat
  have hL20 := digitWords_length_le m.toNat hm
  have key := LeanExe.Dialect.loop_induction (n := 19) (init := ((1 : UInt64), m / 10))
    (f := fun _ s => if s.2 != 0 then (s.1 + 1, s.2 / 10) else s)
    (fun k s => s.1.toNat = min (k + 1) (digitWords m.toNat).length ∧
      s.2.toNat = m.toNat / 10 ^ s.1.toNat)
    ⟨by simp; omega, by simp⟩
    (by
      intro k s hk ⟨h1, h2⟩
      have hc : 0 < s.1.toNat := by omega
      have hiff := digitWords_length_le_iff m.toNat s.1.toNat hc
      have hpow : 0 < 10 ^ s.1.toNat := by positivity
      by_cases hq : s.2 = 0
      · have hz : s.2.toNat = 0 := by rw [hq]; rfl
        have hlt : m.toNat < 10 ^ s.1.toNat := by
          by_contra hge
          have := Nat.div_pos (Nat.le_of_not_lt hge) hpow
          omega
        have hle := hiff.mpr hlt
        have hb : (s.2 != 0) = false := by rw [hq]; rfl
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, h2⟩
      · have hnz : s.2.toNat ≠ 0 := fun h => hq (UInt64.toNat_inj.mp (by simpa using h))
        have hge : 10 ^ s.1.toNat ≤ m.toNat := by
          by_contra hlt
          rw [Nat.div_eq_of_lt (Nat.lt_of_not_le hlt)] at h2
          omega
        have hgt : s.1.toNat < (digitWords m.toNat).length := by
          by_contra hle
          exact absurd (hiff.mp (Nat.le_of_not_lt hle)) (Nat.not_lt_of_le hge)
        have hbne : (s.2 != 0) = true := bne_iff_ne.mpr hq
        simp only [hbne, ↓reduceIte]
        have hs1 : (s.1 + 1).toNat = s.1.toNat + 1 := by
          rw [UInt64.toNat_add]
          simp only [UInt64.reduceToNat]
          omega
        refine ⟨by rw [hs1]; omega, ?_⟩
        rw [UInt64.toNat_div, h2, hs1]
        simp only [UInt64.reduceToNat]
        rw [Nat.div_div_eq_div_mul, pow_succ])
  simp only [UInt64.reduceToNat] at key
  rw [digitCount, key.1]
  omega

theorem digitByte_eq (m k : UInt64) :
    digitByte m k = UInt64.ofNat (m.toNat / 10 ^ k.toNat % 10 + 48) := by
  have key := LeanExe.Dialect.loop_induction (n := k) (init := m) (f := fun _ q => q / 10)
    (fun j q => q.toNat = m.toNat / 10 ^ j) (by simp)
    (by
      intro j q _ hq
      show (q / 10).toNat = _
      simp only [UInt64.toNat_div, hq, UInt64.reduceToNat]
      rw [Nat.div_div_eq_div_mul, pow_succ])
  apply UInt64.toNat_inj.mp
  have hlt : m.toNat / 10 ^ k.toNat % 10 + 48 < 2 ^ 64 := by omega
  rw [digitByte, UInt64.toNat_add, UInt64.toNat_mod, key, UInt64.toNat_ofNat_of_lt' (by
    simp only [UInt64.size]; omega)]
  simp only [UInt64.reduceToNat]
  omega

theorem lt_zero_iff (x : Int64) : x < 0 ↔ x.toInt < 0 := by
  rw [Int64.lt_iff_toInt_lt]
  simp

/-- The program's magnitude of `x` is `|x|`. -/
theorem magnitude_word (x : Int64) :
    (if x < 0 then 0 - x.toUInt64 else x.toUInt64).toNat = x.toInt.natAbs := by
  have hc := LeanExe.ProofKit.Signed64.toInt_cond x
  have hw := x.toUInt64.toNat_lt
  by_cases hx : x < 0
  · rw [ite_eq_left hx]
    have hneg := (lt_zero_iff x).mp hx
    apply Int.ofNat_inj.mp
    rw [Int.ofNat_natAbs_of_nonpos (by omega), UInt64.toNat_sub]
    simp only [UInt64.reduceToNat] at hc ⊢
    split at hc <;> omega
  · rw [ite_eq_right hx]
    have hnn : 0 ≤ x.toInt := by have := (lt_zero_iff x).not.mp hx; omega
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hnn]
    split at hc <;> omega

theorem build_getElem? {α : Type} (n : UInt64) (f : UInt64 → α) (i : Nat) :
    (LeanExe.build n f)[i]? = if i < n.toNat then some (f (UInt64.ofNat i)) else none := by
  unfold LeanExe.build
  rw [Array.getElem?_ofFn]
  split <;> rfl

/-- The printer writes the specification's text. -/
theorem printInt64_eq (x : Int64) : printInt64 x = expectedPrint x := by
  apply Array.ext_getElem?
  intro i
  rw [← Array.getElem?_toList (xs := expectedPrint x), print_toList]
  have hM := magnitude_word x
  generalize hm : (if x < 0 then 0 - x.toUInt64 else x.toUInt64) = M at hM
  have hL := digitCount_toNat M
  rw [hM] at hL
  have hL20 := digitWords_length_le x.toInt.natAbs (by rw [← hM]; exact M.toNat_lt)
  have hL1 := digitWords_length_pos x.toInt.natAbs
  generalize hLdef : (digitWords x.toInt.natAbs).length = L at hL hL20 hL1
  have hget := digitWords_getElem? x.toInt.natAbs
  rw [hLdef] at hget
  have hsign : (if x < 0 then (1 : UInt64) else 0).toNat = if x.toInt < 0 then 1 else 0 := by
    by_cases hx : x < 0
    · rw [ite_eq_left hx, ite_eq_left ((lt_zero_iff x).mp hx)]; rfl
    · rw [ite_eq_right hx, ite_eq_right ((lt_zero_iff x).not.mp hx)]; rfl
  simp only [printInt64, hm]
  generalize hS : (if x < 0 then (1 : UInt64) else 0) = S at hsign
  generalize hN : x.toInt.natAbs = N at hget hM
  rw [build_getElem?]
  have hsize : (digitCount M + S).toNat = L + (if x.toInt < 0 then 1 else 0) := by
    rw [UInt64.toNat_add, hL, hsign]
    split <;> omega
  rw [hsize]
  by_cases hneg : x.toInt < 0
  · simp only [hneg, ↓reduceIte] at hsign ⊢
    rcases i with _ | i
    · have hs : UInt64.ofNat 0 < S := by
        rw [UInt64.lt_iff_toNat_lt, hsign]; decide
      rw [ite_eq_left (by omega), ite_eq_left hs]
      rfl
    · rw [List.singleton_append, List.getElem?_cons_succ, hget]
      by_cases hi : i < L
      · rw [ite_eq_left (by omega), ite_eq_left hi]
        have hnot : ¬ UInt64.ofNat (i + 1) < S := by
          rw [UInt64.lt_iff_toNat_lt, hsign, UInt64.toNat_ofNat_of_lt' (by
            simp only [UInt64.size]; omega)]
          omega
        have hk : (digitCount M + S - 1 - UInt64.ofNat (i + 1)).toNat = L - 1 - i := by
          rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_add, hL, hsign,
            UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
          simp only [UInt64.reduceToNat, Nat.reducePow]
          omega
        rw [ite_eq_right hnot, digitByte_eq, hM, hk]
      · rw [ite_eq_right (by omega), ite_eq_right hi]
  · simp only [hneg, ↓reduceIte, List.nil_append] at hsign ⊢
    rw [hget]
    by_cases hi : i < L
    · rw [ite_eq_left (by omega), ite_eq_left hi]
      have hnot : ¬ UInt64.ofNat i < S := by
        rw [UInt64.lt_iff_toNat_lt, hsign]; omega
      have hk : (digitCount M + S - 1 - UInt64.ofNat i).toNat = L - 1 - i := by
        rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_add, hL, hsign,
          UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        simp only [UInt64.reduceToNat, Nat.reducePow]
        omega
      rw [ite_eq_right hnot, digitByte_eq, hM, hk]
    · rw [ite_eq_right (by omega), ite_eq_right hi]

/-! ## The reader -/

/-- The value of digits from an initial value `v` is at least `v · 10 ^ n` for `n` digits. -/
theorem foldl_ge (l : List UInt64) (v : Nat) :
    v * 10 ^ l.length ≤ l.foldl (fun v d => 10 * v + (d.toNat - 48)) v := by
  induction l generalizing v with
  | nil => simp
  | cons w l ih =>
    simp only [List.foldl_cons, List.length_cons]
    calc v * 10 ^ (l.length + 1) = (10 * v) * 10 ^ l.length := by rw [pow_succ]; ring
      _ ≤ (10 * v + (w.toNat - 48)) * 10 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := ih _

/-- The value of digits from an initial value `v` is below `(v + 1) · 10 ^ n` for `n` digits. -/
theorem foldl_lt (l : List UInt64) (v : Nat) (h : ∀ w ∈ l, isDigitWord w = true) :
    l.foldl (fun v d => 10 * v + (d.toNat - 48)) v < (v + 1) * 10 ^ l.length := by
  induction l generalizing v with
  | nil => simp
  | cons w l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hw := (isDigitWord_iff w).mp (h w List.mem_cons_self)
    calc _ < (10 * v + (w.toNat - 48) + 1) * 10 ^ l.length :=
          ih _ fun u hu => h u (List.mem_cons_of_mem w hu)
      _ ≤ (10 * (v + 1)) * 10 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = (v + 1) * 10 ^ (l.length + 1) := by rw [pow_succ]; ring

theorem digitsValue_lt (l : List UInt64) (h : ∀ w ∈ l, isDigitWord w = true) :
    digitsValue l < 10 ^ l.length := by
  have := foldl_lt l 0 h
  simpa [digitsValue] using this

theorem magnitude_ge {ds : List UInt64} {v : Nat} (h : magnitude ds = some v) :
    10 ^ (ds.length - 1) ≤ v := by
  obtain ⟨d, rest, hds, hd1, -, -, hv⟩ := magnitude_some h
  subst hds
  rw [hv, digitsValue, List.foldl_cons, List.length_cons, Nat.add_sub_cancel]
  calc 10 ^ rest.length ≤ (10 * 0 + (d.toNat - 48)) * 10 ^ rest.length :=
        Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ _ := foldl_ge rest _

/-- `magnitude` of a nonempty list: digits whose first is not 0. -/
theorem magnitude_cons (d : UInt64) (rest : List UInt64) :
    magnitude (d :: rest) = if ((d :: rest).all isDigitWord && d != 48) = true then
      some (digitsValue (d :: rest)) else none := by
  have hd : (49 ≤ d && d ≤ 57) = (isDigitWord d && d != 48) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, isDigitWord_iff, bne_iff_ne, ne_eq,
      UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.reduceToNat]
    omega
  have h : (49 ≤ d && d ≤ 57 && rest.all isDigitWord) =
      ((d :: rest).all isDigitWord && d != 48) := by
    rw [hd, List.all_cons]
    cases isDigitWord d <;> cases (d != 48) <;> cases rest.all isDigitWord <;> rfl
  rw [magnitude, h]

/-- The scan of the `count` words from `start` to the end of `s` tests them for digits and, when
they are, gives their value. -/
theorem scanDigits_spec (s : Array UInt64) (start count : UInt64) (hs : s.size < 2 ^ 64)
    (hsz : start.toNat + count.toNat = s.size) (hc : count.toNat ≤ 19) :
    (scanDigits s start count).1 = (s.toList.drop start.toNat).all isDigitWord ∧
      ((s.toList.drop start.toNat).all isDigitWord = true →
        (scanDigits s start count).2.toNat = digitsValue (s.toList.drop start.toNat)) := by
  have hlen : (s.toList.drop start.toNat).length = count.toNat := by simp; omega
  have key := LeanExe.Dialect.loop_induction (n := count) (init := (true, (0 : UInt64)))
    (f := fun i st => (st.1 && isDigitW s[(start + i).toNat]!,
      10 * st.2 + (s[(start + i).toNat]! - 48)))
    (fun k st => st.1 = ((s.toList.drop start.toNat).take k).all isDigitWord ∧
      (st.1 = true → st.2.toNat = digitsValue ((s.toList.drop start.toNat).take k)))
    ⟨by simp, by simp [digitsValue]⟩
    (by
      intro k st hk ⟨h1, h2⟩
      have hkl : k < (s.toList.drop start.toNat).length := by omega
      have hidx : (start + UInt64.ofNat k).toNat = start.toNat + k := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        omega
      have hw : s[(start + UInt64.ofNat k).toNat]! = (s.toList.drop start.toNat)[k] := by
        rw [hidx, List.getElem_drop, Array.getElem_toList, getElem!_pos s _ (by omega)]
      rw [hw, List.take_succ_eq_append_getElem hkl, List.all_append, ← h1]
      have hdig : isDigitW (s.toList.drop start.toNat)[k] =
          isDigitWord (s.toList.drop start.toNat)[k] := rfl
      refine ⟨by simp only [List.all_cons, List.all_nil, Bool.and_true]; rfl, ?_⟩
      intro hst
      simp only [Bool.and_eq_true] at hst
      obtain ⟨hst1, hst2⟩ := hst
      have hv := h2 hst1
      have hall : ∀ w ∈ (s.toList.drop start.toNat).take k, isDigitWord w = true := by
        rw [h1] at hst1
        exact List.all_eq_true.mp hst1
      have hbound := digitsValue_lt _ hall
      have htk : ((s.toList.drop start.toNat).take k).length = k := by simp; omega
      rw [htk] at hbound
      have h10 : 10 ^ k ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by omega)
      have hwd := (isDigitWord_iff _).mp (hdig ▸ hst2)
      rw [digitsValue_snoc, UInt64.toNat_add, UInt64.toNat_mul, hv,
        UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hwd.1)]
      simp only [UInt64.reduceToNat]
      omega)
  have htake : (s.toList.drop start.toNat).take count.toNat = s.toList.drop start.toNat := by
    rw [List.take_of_length_le (by omega)]
  rw [htake] at key
  simp only [scanDigits]
  exact ⟨key.1, fun h => key.2 (key.1.trans h)⟩

theorem word_toInt64 (r : UInt64) (h : r.toNat < 2 ^ 63) : r.toInt64 = Int64.ofInt r.toNat := by
  apply Int64.toInt_inj.mp
  rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have hc := LeanExe.ProofKit.Signed64.toInt_cond r.toInt64
  have hr : r.toInt64.toUInt64 = r := rfl
  rw [hr, ite_eq_left h] at hc
  exact hc

theorem neg_word_toInt64 (r : UInt64) (h1 : 1 ≤ r.toNat) (h2 : r.toNat ≤ 2 ^ 63) :
    (0 - r).toInt64 = Int64.ofInt (-(r.toNat : Int)) := by
  apply Int64.toInt_inj.mp
  rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have hc := LeanExe.ProofKit.Signed64.toInt_cond (0 - r).toInt64
  have hr : (0 - r).toInt64.toUInt64 = 0 - r := rfl
  have hsub : (0 - r).toNat = 2 ^ 64 - r.toNat := by
    rw [UInt64.toNat_sub, UInt64.toNat_zero]
    omega
  rw [hr, hsub, ite_eq_right (by omega)] at hc
  rw [hc]
  omega

theorem toList_cons_of_size (s : Array UInt64) (h : s.size ≠ 0) : ∃ a t, s.toList = a :: t := by
  cases hs : s.toList with
  | nil =>
    have := congrArg List.length hs
    simp at this
    simp [this] at h
  | cons a t => exact ⟨a, t, rfl⟩

theorem getElem!_of_toList (s : Array UInt64) (i : Nat) (h : i < s.size) :
    s[i]! = s.toList[i]'(by simpa using h) := by
  rw [getElem!_pos s i h, Array.getElem_toList]

/-- The specification on a text that starts with `-`. -/
theorem expectedRead_minus (s : Array UInt64) (t : List UInt64) (hl : s.toList = 45 :: t) :
    expectedRead s = match magnitude t with
      | some v => if v ≤ 2 ^ 63 then (true, Int64.ofInt (-(v : Int))) else (false, 0)
      | none => (false, 0) := by
  unfold expectedRead
  rw [hl, denote_minus _ (by simp) (by simp), List.tail_cons]
  cases magnitude t with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    by_cases hv : v ≤ 2 ^ 63
    · rw [ite_eq_left (by omega), ite_eq_left hv]
    · rw [ite_eq_right (by omega), ite_eq_right hv]

/-- The specification on a text that neither starts with `-` nor is `0`. -/
theorem expectedRead_plain (s : Array UInt64) (h48 : s.toList ≠ [48])
    (h45 : ¬ s.toList.head? = some 45) :
    expectedRead s = match magnitude s.toList with
      | some v => if v < 2 ^ 63 then (true, Int64.ofInt (v : Int)) else (false, 0)
      | none => (false, 0) := by
  unfold expectedRead
  rw [denote_plain _ h48 h45]
  cases magnitude s.toList with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    by_cases hv : v < 2 ^ 63
    · rw [ite_eq_left (by omega), ite_eq_left hv]
    · rw [ite_eq_right (by omega), ite_eq_right hv]

theorem isDigitWord_ne48 {d : UInt64} (h : (isDigitWord d && d != 48) = true) :
    49 ≤ d.toNat := by
  simp only [Bool.and_eq_true, isDigitWord_iff, bne_iff_ne, ne_eq] at h
  have : d.toNat ≠ 48 := fun e => h.2 (UInt64.toNat_inj.mp (by simpa using e))
  omega

/-- The reader returns the specification's result on every array that memory can hold. -/
theorem readInt64_eq (s : Array UInt64) (hs : s.size < 2 ^ 64) :
    readInt64 s = expectedRead s := by
  have hn : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hlen : s.toList.length = s.size := by simp
  simp only [readInt64]
  by_cases h0 : s.size = 0
  · have he : s.toList = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hz : (s.size.toUInt64 == 0) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, hn, h0]; rfl
    rw [ite_eq_left hz]
    simp [expectedRead, he, denote, magnitude]
  have hz : ¬ (s.size.toUInt64 == 0) = true := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, hn]; simpa using h0
  rw [ite_eq_right hz]
  obtain ⟨a, t, hl⟩ := toList_cons_of_size s h0
  have hsz : s.size = t.length + 1 := by rw [← hlen, hl]; rfl
  have h0a : s[(0 : UInt64).toNat]! = a := by
    rw [getElem!_of_toList s _ (by simp; omega)]
    simp [hl]
  rw [h0a]
  by_cases ha : a = 45
  · subst ha
    have hb : ((45 : UInt64) == 45) = true := rfl
    simp only [hb, ↓reduceIte, Bool.not_true, Bool.and_false, Bool.or_false]
    rw [expectedRead_minus s t hl]
    generalize hC : s.size.toUInt64 - 1 = C
    have hCn : C.toNat = t.length := by
      rw [← hC, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]
      simp only [UInt64.reduceToNat]
      omega
    by_cases ht0 : t = []
    · subst ht0
      have h1 : ((C == 0 || C > 19) = true) := by
        simp [← UInt64.toNat_inj, hCn]
      rw [ite_eq_left h1]
      simp [magnitude]
    by_cases ht19 : 19 < t.length
    · have h1 : ((C == 0 || C > 19) = true) := by
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hCn]
        right
        simpa using ht19
      rw [ite_eq_left h1]
      cases hm : magnitude t with
      | none => rfl
      | some v =>
        have hge := magnitude_ge hm
        have h10 : 10 ^ 19 ≤ 10 ^ (t.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        dsimp only
        rw [ite_eq_right (by simp only [Nat.reducePow] at h10 ⊢; omega)]
    have h1 : ¬ ((C == 0 || C > 19) = true) := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hCn,
        not_or, ← UInt64.toNat_inj]
      have : t.length ≠ 0 := fun e => ht0 (List.eq_nil_of_length_eq_zero e)
      simp only [UInt64.reduceToNat]
      omega
    rw [ite_eq_right h1]
    obtain ⟨d, rest, htd⟩ : ∃ d rest, t = d :: rest := by
      cases t with
      | nil => exact absurd rfl ht0
      | cons d rest => exact ⟨d, rest, rfl⟩
    have htl : 1 ≤ t.length := by rw [htd]; simp
    have hdrop : s.toList.drop (1 : UInt64).toNat = t := by rw [hl]; rfl
    have hspec := scanDigits_spec s 1 C hs (by simp only [UInt64.reduceToNat]; omega) (by omega)
    rw [hdrop] at hspec
    have h1d : s[(1 : UInt64).toNat]! = d := by
      rw [getElem!_of_toList s _ (by simp; omega)]
      simp [hl, htd]
    rw [h1d]
    generalize hR : scanDigits s 1 C = R at hspec
    rw [htd, magnitude_cons d rest]
    rw [htd] at hspec
    by_cases hc : ((d :: rest).all isDigitWord && d != 48) = true
    · have hall : (d :: rest).all isDigitWord = true := by
        simp only [Bool.and_eq_true] at hc; exact hc.1
      have hdn : (d != 48) = true := by simp only [Bool.and_eq_true] at hc; exact hc.2
      have hR1 : R.1 = true := by rw [hspec.1, hall]
      have hR2 := hspec.2 hall
      have hd' : (isDigitWord d && d != 48) = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hc ⊢; exact ⟨hc.1.1, hc.2⟩
      have hpos : 0 < digitsValue (d :: rest) := digitsValue_pos (isDigitWord_ne48 hd')
      rw [ite_eq_left hc]
      simp only [hR1, hdn, Bool.true_and, Bool.and_true]
      by_cases hv : digitsValue (d :: rest) ≤ 2 ^ 63
      · have hle : (decide (R.2 ≤ 9223372036854775808)) = true := by
          simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hR2, UInt64.reduceToNat]
          omega
        rw [ite_eq_left hle, ite_eq_left hv, neg_word_toInt64 R.2 (by omega) (by omega), hR2]
      · have hle : ¬ (decide (R.2 ≤ 9223372036854775808)) = true := by
          simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hR2, UInt64.reduceToNat]
          omega
        rw [ite_eq_right hle, ite_eq_right hv]
    · rw [ite_eq_right hc]
      have hfalse : ¬ (R.1 && d != 48 && decide (R.2 ≤ 9223372036854775808)) = true := by
        rw [hspec.1]
        intro h
        apply hc
        simp only [Bool.and_eq_true] at h ⊢
        exact h.1
      rw [ite_eq_right hfalse]
  · have hb : (a == 45) = false := by simpa using ha
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true]
    have hC : (s.size.toUInt64 - 0).toNat = t.length + 1 := by
      rw [UInt64.sub_zero, hn, hsz]
    generalize s.size.toUInt64 - 0 = C at hC
    have h45 : ¬ s.toList.head? = some 45 := by rw [hl]; simpa using ha
    by_cases h19 : 19 < t.length + 1
    · have h1 : ((C == 0 || C > 19) = true) := by
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hC]
        right
        simpa using h19
      rw [ite_eq_left h1]
      have h48 : s.toList ≠ [48] := by
        rw [hl]; intro e; simp only [List.cons.injEq] at e; rw [e.2] at h19; simp at h19
      rw [expectedRead_plain s h48 h45]
      cases hm : magnitude s.toList with
      | none => rfl
      | some v =>
        have hge := magnitude_ge hm
        rw [hlen, hsz] at hge
        have h10 : 10 ^ 19 ≤ 10 ^ (t.length + 1 - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        dsimp only
        rw [ite_eq_right (by simp only [Nat.reducePow] at h10 ⊢; omega)]
    have h1 : ¬ ((C == 0 || C > 19) = true) := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hC,
        not_or, ← UInt64.toNat_inj]
      simp only [UInt64.reduceToNat]
      omega
    rw [ite_eq_right h1]
    have hdrop : s.toList.drop (0 : UInt64).toNat = a :: t := by rw [hl]; rfl
    have hspec := scanDigits_spec s 0 C hs (by simp only [UInt64.reduceToNat]; omega) (by omega)
    rw [hdrop] at hspec
    rw [h0a]
    generalize hR : scanDigits s 0 C = R at hspec
    by_cases h48 : s.toList = [48]
    · rw [hl] at h48
      simp only [List.cons.injEq] at h48
      obtain ⟨rfl, rfl⟩ := h48
      have hall : ([48] : List UInt64).all isDigitWord = true := rfl
      have hR1 : R.1 = true := by rw [hspec.1, hall]
      have hR2 := hspec.2 hall
      have hR0 : R.2 = 0 := UInt64.toNat_inj.mp (by rw [hR2]; rfl)
      have hC1 : (C == 1) = true := by
        rw [beq_iff_eq, ← UInt64.toNat_inj, hC]; rfl
      have hcond : (R.1 && ((48 : UInt64) != 48 || C == 1) &&
          decide (R.2 ≤ 9223372036854775807)) = true := by
        rw [hR1, hC1, hR0]; rfl
      rw [ite_eq_left hcond, hR0]
      have he : expectedRead s = (true, Int64.ofInt 0) :=
        expectedRead_eq (by rw [hl, denote_zero]) (by decide) (by decide)
      rw [he]
      rfl
    rw [expectedRead_plain s h48 h45, hl, magnitude_cons a t]
    by_cases hc : ((a :: t).all isDigitWord && a != 48) = true
    · have hall : (a :: t).all isDigitWord = true := by
        simp only [Bool.and_eq_true] at hc; exact hc.1
      have hdn : (a != 48) = true := by simp only [Bool.and_eq_true] at hc; exact hc.2
      have hR1 : R.1 = true := by rw [hspec.1, hall]
      have hR2 := hspec.2 hall
      rw [ite_eq_left hc]
      simp only [hR1, hdn, Bool.true_and, Bool.true_or, Bool.and_true]
      by_cases hv : digitsValue (a :: t) < 2 ^ 63
      · have hle : (decide (R.2 ≤ 9223372036854775807)) = true := by
          simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hR2, UInt64.reduceToNat]
          omega
        rw [ite_eq_left hle, ite_eq_left hv, word_toInt64 R.2 (by omega), hR2]
      · have hle : ¬ (decide (R.2 ≤ 9223372036854775807)) = true := by
          simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hR2, UInt64.reduceToNat]
          omega
        rw [ite_eq_right hle, ite_eq_right hv]
    · rw [ite_eq_right hc]
      have hfalse : ¬ (R.1 && (a != 48 || C == 1) && decide (R.2 ≤ 9223372036854775807)) = true := by
        rw [hspec.1]
        intro h
        simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h.1.2 with ha48 | hC1
        · exact hc (by simp only [Bool.and_eq_true]; exact ⟨h.1.1, ha48⟩)
        · have hl0 : t.length = 0 := by
            rw [beq_iff_eq, ← UInt64.toNat_inj, hC] at hC1; simpa using hC1
          have ht : t = [] := List.eq_nil_of_length_eq_zero hl0
          have ha48 : a = 48 := by
            by_contra hne
            exact hc (by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]; exact ⟨h.1.1, hne⟩)
          exact h48 (by rw [hl, ha48, ht])
      rw [ite_eq_right hfalse]

/-- The printer's text has at most 20 bytes: a magnitude of at most `2 ^ 63 < 10 ^ 19` has at
most 19 digits. -/
theorem expectedPrint_size (x : Int64) : (expectedPrint x).size ≤ 20 := by
  rw [← Array.length_toList, print_toList, List.length_append]
  have hlt := x.toInt_lt
  have hle := x.le_toInt
  have habs : (x.toInt.natAbs : Int) ≤ 2 ^ 63 := by
    by_cases h : 0 ≤ x.toInt
    · rw [Int.natAbs_of_nonneg h]; omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]; omega
  have hL := (digitWords_length_le_iff x.toInt.natAbs 19 (by decide)).mpr (by
    have : x.toInt.natAbs ≤ 2 ^ 63 := by exact_mod_cast habs
    simp only [Nat.reducePow] at this ⊢
    omega)
  by_cases hneg : x.toInt < 0
  · rw [ite_eq_left hneg]
    simp only [List.length_singleton]
    omega
  · rw [ite_eq_right hneg]
    simp only [List.length_nil]
    omega

/-- The reader returns `(true, x)` on the printer's text of `x`. -/
theorem readInt64_printInt64 (x : Int64) : readInt64 (printInt64 x) = (true, x) := by
  rw [printInt64_eq, readInt64_eq _ (by have := expectedPrint_size x; omega),
    expectedRead_print]

/-- Every text that the reader accepts is the printer's text of the value it returns. -/
theorem printInt64_of_read {s : Array UInt64} {x : Int64} (hs : s.size < 2 ^ 64)
    (h : readInt64 s = (true, x)) : printInt64 x = s := by
  rw [readInt64_eq s hs] at h
  rw [printInt64_eq]
  exact expectedPrint_of_read h

/-- The reader rejects with `(false, 0)` every array that is no printer's text. -/
theorem readInt64_reject {s : Array UInt64} (hs : s.size < 2 ^ 64)
    (h : ∀ x, printInt64 x ≠ s) : readInt64 s = (false, 0) := by
  rw [readInt64_eq s hs]
  exact expectedRead_reject s fun x => by rw [← printInt64_eq]; exact h x

end Library.Numerics.Decimal.Int64Text
