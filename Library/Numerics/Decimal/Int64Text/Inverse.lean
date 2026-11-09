import Library.Numerics.Decimal.Int64Text.Spec
import Mathlib.Data.List.Induction
import Mathlib.Tactic

/-!
The specification's reader and printer are inverse.  `expectedRead_print` states that the reader
returns `(true, x)` on the text of `x`, and `expectedPrint_of_read` that every text the reader
accepts is the printer's text of the value it returns, so the grammar's texts are exactly the
printer's texts.  The proofs read `toString` through Lean's `Int.repr_eq_ite` and `Nat.toList_repr`
as the characters of `Nat.toDigits 10`, and `digitWords_snoc` splits off the last digit with
`Nat.toDigits_append_toDigits`.
-/

namespace Library.Numerics.Decimal.Int64Text

open Library.Numerics.Decimal.Shared.StrconvGrammar

/-- The words of the decimal digits of `m`, as `toString` writes them. -/
def digitWords (m : Nat) : List UInt64 := (Nat.toDigits 10 m).map fun c => c.toUInt8.toUInt64

theorem ofNat_digit_toNat {e : Nat} (h : e < 10) : (UInt64.ofNat (e + 48)).toNat = e + 48 :=
  UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)

theorem digitChar_word {e : Nat} (h : e < 10) :
    (Nat.digitChar e).toUInt8.toUInt64 = UInt64.ofNat (e + 48) := by
  interval_cases e <;> rfl

theorem digitWords_small {e : Nat} (h : e < 10) : digitWords e = [UInt64.ofNat (e + 48)] := by
  rw [digitWords, Nat.toDigits_of_lt_base h, List.map_singleton, digitChar_word h]

theorem digitWords_snoc {a e : Nat} (ha : 0 < a) (he : e < 10) :
    digitWords (10 * a + e) = digitWords a ++ [UInt64.ofNat (e + 48)] := by
  rw [digitWords, ← Nat.toDigits_append_toDigits (by decide) ha he, Nat.toDigits_of_lt_base he,
    List.map_append, List.map_singleton, digitChar_word he, digitWords]

/-- The text of `x` is its sign and the digits of its magnitude. -/
theorem print_toList (x : Int64) :
    (expectedPrint x).toList = (if x.toInt < 0 then [45] else []) ++ digitWords x.toInt.natAbs := by
  have h : (toString x).toList = (Int.repr x.toInt).toList := rfl
  have hmap : (expectedPrint x).toList = (toString x).toList.map fun c => c.toUInt8.toUInt64 := by
    simp [expectedPrint, words, ascii]
  have hminus : ("-" : String).toList = ['-'] := by decide
  rw [hmap, h, Int.repr_eq_ite]
  by_cases hx : 0 ≤ x.toInt
  · rw [ite_eq_left hx, ite_eq_right (by omega), Nat.toList_repr, List.nil_append, digitWords,
      show x.toInt.toNat = x.toInt.natAbs by omega]
  · rw [ite_eq_right hx, ite_eq_left (by omega), String.toList_append, hminus, Nat.toList_repr,
      List.map_append, digitWords, show (-x.toInt).toNat = x.toInt.natAbs by omega]
    rfl

theorem isDigitWord_iff (w : UInt64) : isDigitWord w = true ↔ 48 ≤ w.toNat ∧ w.toNat ≤ 57 := by
  simp [isDigitWord, UInt64.le_iff_toNat_le]

theorem isDigitWord_digit {e : Nat} (h : e < 10) : isDigitWord (UInt64.ofNat (e + 48)) = true := by
  rw [isDigitWord_iff, ofNat_digit_toNat h]
  omega

theorem digitsValue_snoc (l : List UInt64) (w : UInt64) :
    digitsValue (l ++ [w]) = 10 * digitsValue l + (w.toNat - 48) := by
  simp [digitsValue, List.foldl_append]

/-- Every word of `digitWords m` is a digit, the value of the digits is `m`, and the first digit
is not 0 when `m` is positive. -/
theorem digitWords_facts (m : Nat) :
    (∀ w ∈ digitWords m, isDigitWord w = true) ∧ digitsValue (digitWords m) = m ∧
      ∃ d rest, digitWords m = d :: rest ∧ (0 < m → 49 ≤ d.toNat) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 10
    · rw [digitWords_small hm]
      refine ⟨by simpa using isDigitWord_digit hm, ?_, _, [], rfl, ?_⟩
      · simp only [digitsValue, List.foldl_cons, List.foldl_nil, ofNat_digit_toNat hm]
        omega
      · intro _
        rw [ofNat_digit_toNat hm]
        omega
    · have hq : 0 < m / 10 := by omega
      have he : m % 10 < 10 := Nat.mod_lt _ (by decide)
      have hsplit : m = 10 * (m / 10) + m % 10 := (Nat.div_add_mod m 10).symm
      obtain ⟨h1, h2, d, rest, h3, h4⟩ := ih (m / 10) (by omega)
      rw [hsplit, digitWords_snoc hq he]
      refine ⟨?_, ?_, d, rest ++ [UInt64.ofNat (m % 10 + 48)], by rw [h3]; rfl, fun _ => h4 hq⟩
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact h1 w hw
        · rw [List.mem_singleton.mp hw]
          exact isDigitWord_digit he
      · rw [digitsValue_snoc, h2, ofNat_digit_toNat he]
        omega

theorem digitWords_zero : digitWords 0 = [48] := digitWords_small (by decide)

/-- The digits of a positive number are a text of `nonzero *digit` whose value is the number. -/
theorem magnitude_digitWords {m : Nat} (hm : 0 < m) : magnitude (digitWords m) = some m := by
  obtain ⟨h1, h2, d, rest, h3, h4⟩ := digitWords_facts m
  have hd := h1 d (by rw [h3]; exact List.mem_cons_self)
  rw [isDigitWord_iff] at hd
  have hall : rest.all isDigitWord = true :=
    List.all_eq_true.mpr fun w hw => h1 w (by rw [h3]; exact List.mem_cons_of_mem d hw)
  have h49 := h4 hm
  rw [h3, magnitude, ← h3, h2]
  simp [UInt64.le_iff_toNat_le, hall, h49, hd.2]

/-- A text of `nonzero *digit` is a nonempty list of digits whose first digit is not 0. -/
theorem magnitude_some {ds : List UInt64} {v : Nat} (h : magnitude ds = some v) :
    ∃ d rest, ds = d :: rest ∧ 49 ≤ d.toNat ∧ d.toNat ≤ 57 ∧
      (∀ w ∈ rest, isDigitWord w = true) ∧ v = digitsValue ds := by
  match ds, h with
  | d :: rest, h =>
    simp only [magnitude] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      exact ⟨d, rest, rfl, UInt64.le_iff_toNat_le.mp h1, UInt64.le_iff_toNat_le.mp h2, h3,
        (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

theorem digitsValue_pos {d : UInt64} {rest : List UInt64} (hd : 49 ≤ d.toNat) :
    0 < digitsValue (d :: rest) := by
  have key : ∀ (l : List UInt64) (v : Nat), 0 < v →
      0 < l.foldl (fun v d => 10 * v + (d.toNat - 48)) v := by
    intro l
    induction l with
    | nil => intro v hv; simpa using hv
    | cons w l ih => intro v hv; exact ih (10 * v + (w.toNat - 48)) (by omega)
  exact key rest (10 * 0 + (d.toNat - 48)) (by omega)

/-- A text of `nonzero *digit` is the text of its value. -/
theorem digitWords_of_magnitude (ds : List UInt64) :
    ∀ v, magnitude ds = some v → digitWords v = ds := by
  induction ds using List.reverseRecOn with
  | nil => intro v h; simp [magnitude] at h
  | append_singleton l a ih =>
    intro v h
    obtain ⟨d, rest, hds, hd1, hd2, hrest, hv⟩ := magnitude_some h
    rcases List.eq_nil_or_concat l with hl | ⟨l', b, hl⟩
    · subst hl
      simp only [List.nil_append, List.cons.injEq] at hds
      obtain ⟨had, -⟩ := hds
      rw [← had] at hd1 hd2
      have hv' : v = a.toNat - 48 := by simp [hv, digitsValue]
      rw [hv', digitWords_small (by omega)]
      congr 1
      apply UInt64.toNat_inj.mp
      rw [ofNat_digit_toNat (by omega)]
      omega
    · have hla : l ≠ [] := by simp [hl]
      obtain ⟨d', rest', hl2⟩ : ∃ d' rest', l = d' :: rest' := by
        cases l with
        | nil => exact absurd rfl hla
        | cons d' rest' => exact ⟨d', rest', rfl⟩
      have hdd : d' = d ∧ rest' ++ [a] = rest := by
        rw [hl2] at hds
        simpa using hds
      have ha : isDigitWord a = true := hrest a (by rw [← hdd.2]; simp)
      rw [isDigitWord_iff] at ha
      have hml : magnitude l = some (digitsValue l) := by
        rw [hl2, magnitude, hdd.1]
        have hall : rest'.all isDigitWord = true :=
          List.all_eq_true.mpr fun w hw => hrest w (by rw [← hdd.2]; simp [hw])
        simp [UInt64.le_iff_toNat_le, hall, hd1, hd2]
      have hpos : 0 < digitsValue l := by rw [hl2, hdd.1]; exact digitsValue_pos hd1
      have hv' : v = 10 * digitsValue l + (a.toNat - 48) := by rw [hv, digitsValue_snoc]
      rw [hv', digitWords_snoc hpos (by omega), ih _ hml]
      congr 2
      apply UInt64.toNat_inj.mp
      rw [ofNat_digit_toNat (by omega)]
      omega

theorem denote_zero : denote [48] = some 0 := by simp [denote]

/-- `denote` of a text that starts with `-` and is not `0`. -/
theorem denote_minus (s : List UInt64) (h48 : s ≠ [48]) (h45 : s.head? = some 45) :
    denote s = (magnitude s.tail).map fun n : Nat => -(n : Int) := by
  unfold denote
  rw [ite_eq_right h48, ite_eq_left h45]
  cases magnitude s.tail <;> rfl

/-- `denote` of a text that neither starts with `-` nor is `0`. -/
theorem denote_plain (s : List UInt64) (h48 : s ≠ [48]) (h45 : ¬ s.head? = some 45) :
    denote s = (magnitude s).map fun n : Nat => (n : Int) := by
  unfold denote
  rw [ite_eq_right h48, ite_eq_right h45]
  cases magnitude s <;> rfl

theorem expectedRead_eq {s : Array UInt64} {n : Int} (h : denote s.toList = some n)
    (h1 : -2 ^ 63 ≤ n) (h2 : n < 2 ^ 63) : expectedRead s = (true, Int64.ofInt n) := by
  simp only [expectedRead, h]
  exact ite_eq_left ⟨h1, h2⟩

/-- The reader returns `(true, x)` on the text of `x`. -/
theorem expectedRead_print (x : Int64) : expectedRead (expectedPrint x) = (true, x) := by
  have hlt := x.toInt_lt
  have hle := x.le_toInt
  obtain ⟨hdig, hval, d, rest, hdr, hpos⟩ := digitWords_facts x.toInt.natAbs
  have hd := hdig d (by rw [hdr]; exact List.mem_cons_self)
  rw [isDigitWord_iff] at hd
  have hden : denote (expectedPrint x).toList = some x.toInt := by
    rw [print_toList]
    by_cases hneg : x.toInt < 0
    · have hm : 0 < x.toInt.natAbs := by omega
      rw [ite_eq_left hneg, denote_minus ([45] ++ digitWords x.toInt.natAbs) (by simp) (by simp)]
      simp only [List.tail_cons, List.singleton_append, magnitude_digitWords hm, Option.map_some]
      rw [Int.ofNat_natAbs_of_nonpos (by omega), Int.neg_neg]
    · rw [ite_eq_right hneg, List.nil_append]
      by_cases hz : x.toInt = 0
      · rw [hz]
        simp [digitWords_zero, denote]
      · have hm : 0 < x.toInt.natAbs := by omega
        have h48 : digitWords x.toInt.natAbs ≠ [48] := by
          intro h
          have := hval
          rw [h] at this
          simp [digitsValue] at this
          omega
        have h45 : ¬ (digitWords x.toInt.natAbs).head? = some 45 := by
          rw [hdr]
          intro h
          simp only [List.head?_cons, Option.some.injEq] at h
          rw [h] at hd
          simp at hd
        rw [denote_plain _ h48 h45, magnitude_digitWords hm]
        simp only [Option.map_some]
        rw [Int.natAbs_of_nonneg (by omega)]
  rw [expectedRead_eq hden hle hlt, Int64.ofInt_toInt]

/-- Every text that the reader accepts is the printer's text of the value it returns. -/
theorem expectedPrint_of_read {s : Array UInt64} {x : Int64} (h : expectedRead s = (true, x)) :
    expectedPrint x = s := by
  unfold expectedRead at h
  split at h
  · rename_i n hn
    split at h
    · rename_i hr
      obtain ⟨hr1, hr2⟩ := hr
      have hx : x = Int64.ofInt n := (Prod.mk.inj h).2.symm
      have hxn : x.toInt = n := by rw [hx, Int64.toInt_ofInt_of_le hr1 hr2]
      apply Array.toList_inj.mp
      rw [print_toList, hxn]
      by_cases h48 : s.toList = [48]
      · have h0 : n = 0 := by
          rw [h48, denote_zero] at hn
          exact (Option.some.inj hn).symm
        subst h0
        rw [h48]
        simp [digitWords_zero]
      · by_cases h45 : s.toList.head? = some 45
        · rw [denote_minus _ h48 h45] at hn
          obtain ⟨v, hv, hvn⟩ := Option.map_eq_some_iff.mp hn
          obtain ⟨d, rest, hds, hd1, -, -, hval⟩ := magnitude_some hv
          have hpos : 0 < v := by rw [hval, hds]; exact digitsValue_pos hd1
          have hcons : s.toList = 45 :: s.toList.tail := by
            cases hs : s.toList with
            | nil => rw [hs] at h45; simp at h45
            | cons a t => rw [hs] at h45; simp at h45; rw [h45]; rfl
          rw [← hvn, ite_eq_left (by omega), Int.natAbs_neg, Int.natAbs_natCast,
            digitWords_of_magnitude _ v hv]
          conv_rhs => rw [hcons]
          rfl
        · rw [denote_plain _ h48 h45] at hn
          obtain ⟨v, hv, hvn⟩ := Option.map_eq_some_iff.mp hn
          rw [← hvn, ite_eq_right (by omega), Int.natAbs_natCast, digitWords_of_magnitude _ v hv]
          rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The reader accepts exactly the printer's texts. -/
theorem expectedRead_eq_true_iff (s : Array UInt64) (x : Int64) :
    expectedRead s = (true, x) ↔ expectedPrint x = s :=
  ⟨expectedPrint_of_read, fun h => h ▸ expectedRead_print x⟩

/-- The reader rejects with `(false, 0)` every array that is no printer's text. -/
theorem expectedRead_reject (s : Array UInt64) (h : ∀ x, expectedPrint x ≠ s) :
    expectedRead s = (false, 0) := by
  unfold expectedRead
  split
  · rename_i n hn
    split
    · rename_i hr
      exact absurd (expectedPrint_of_read (expectedRead_eq hn hr.1 hr.2)) (h _)
    · rfl
  · rfl

end Library.Numerics.Decimal.Int64Text
