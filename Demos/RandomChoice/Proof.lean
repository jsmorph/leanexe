module

public import Demos.RandomChoice.Program
public import Demos.RandomChoice.Spec
public import Demos.RandomHistogram.Proof
public import Mathlib.Data.List.GetD

@[expose] public section

/-! The programs of the pure core equal their specifications: `parseArg_eq`, `pick_eq`, and
`render_eq`.

`parseArg`'s loop over the buffer is a fold of `parseStep index` over its bytes (`loop_bytes` of the
random histogram).  The fold counts zero bytes and leaves the rest of a state unchanged while the
count differs from `index` (`fold_skip`, `fold_after`), and over an argument without a zero byte,
from the count `index`, it computes the specification's value and decides whether the argument is a
numeral below `2^64` (`fold_argument`).  `fold_parse` proves the equation by induction on the
number of zero bytes before the argument, splitting the buffer at its first zero byte as
`List.splitOn` does.  `pick_eq` rests on `0 - n = 2^64 - n` and `(2^64 - n) mod n = 2^64 mod n`.
`render`'s fold writes the words of each value's line after those of the values before it
(`putLine_get`, `fill_fold`) into an array of `textSize` words (`textSize_eq`), so the array holds
`textWords`, the digit words of each value followed by a newline. -/

namespace Demos.RandomChoice

open LeanExe Library.Numerics.Decimal.Int64Text

/-! ## parseArg -/

/-- `parseStep index` on a byte. -/
abbrev byteStep (index : UInt64) (s : UInt64 × UInt64 × Bool × Bool) (b : UInt8) :
    UInt64 × UInt64 × Bool × Bool :=
  parseStep index s b.toUInt64

/-- A byte other than 0 leaves a state whose count differs from `index` unchanged. -/
theorem byteStep_skip {index z v : UInt64} {ok ne : Bool} {b : UInt8} (hb : b ≠ 0)
    (hz : z ≠ index) : byteStep index (z, v, ok, ne) b = (z, v, ok, ne) := by
  have hb' : b.toUInt64 ≠ 0 := fun e => hb (RandomHistogram.toUInt64_eq_zero.mp e)
  have hz' : (z == index) = false := by simpa using hz
  have hb0 : (b.toUInt64 == 0) = false := by simpa using hb'
  simp only [byteStep, parseStep, hb0, hz', Bool.false_eq_true, ↓reduceIte]

/-- The byte 0 raises the count. -/
theorem byteStep_zero (index z v : UInt64) (ok ne : Bool) :
    byteStep index (z, v, ok, ne) 0 = (z + 1, v, ok, ne) := by
  simp [byteStep, parseStep]

/-- Over bytes other than 0, a state whose count differs from `index` stays unchanged. -/
theorem fold_skip {index z v : UInt64} {ok ne : Bool} (hz : z ≠ index) :
    ∀ l : List UInt8, (0 : UInt8) ∉ l → l.foldl (byteStep index) (z, v, ok, ne) = (z, v, ok, ne)
  | [], _ => rfl
  | b :: l, h => by
    have hb : b ≠ 0 := fun e => h (e ▸ List.mem_cons_self)
    rw [List.foldl_cons, byteStep_skip hb hz]
    exact fold_skip hz l (fun m => h (List.mem_cons_of_mem _ m))

/-- After argument `index`, the fold raises the count over each zero byte and keeps the rest of
the state. -/
theorem fold_after {index v : UInt64} {ok ne : Bool} :
    ∀ (l : List UInt8) (z : UInt64), index.toNat < z.toNat → z.toNat + l.length < 2 ^ 64 →
      ∃ z', l.foldl (byteStep index) (z, v, ok, ne) = (z', v, ok, ne) ∧ index.toNat < z'.toNat
  | [], z, hz, _ => ⟨z, rfl, hz⟩
  | b :: l, z, hz, hlen => by
    rw [List.foldl_cons]
    by_cases hb : b = 0
    · subst hb
      rw [byteStep_zero]
      have hsum : (z + 1).toNat = z.toNat + 1 := by
        rw [UInt64.toNat_add]
        simp only [UInt64.reduceToNat]
        simp only [List.length_cons] at hlen
        omega
      exact fold_after l (z + 1) (by omega) (by simp only [List.length_cons] at hlen; omega)
    · have hne : z ≠ index := fun e => by rw [e] at hz; omega
      rw [byteStep_skip hb hne]
      exact fold_after l z hz (by simp only [List.length_cons] at hlen; omega)

/-- `parseStep` on a byte other than 0 of argument `index`. -/
theorem parseStep_arg (index v : UInt64) (ok ne : Bool) (b : UInt64) (hb : b ≠ 0) :
    parseStep index (index, v, ok, ne) b =
      if (48 ≤ b && b ≤ 57 &&
          (v < 1844674407370955161 || (v == 1844674407370955161 && b ≤ 53))) = true then
        (index, 10 * v + (b - 48), ok, true)
      else (index, v, false, true) := by
  have hb' : (b == 0) = false := by simpa using hb
  simp only [parseStep, hb', beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

/-- Over an argument without a zero byte, from the count `index`, the fold keeps the count,
records whether the argument has a byte, and decides whether the argument is digits whose numeral
lies below `2^64`, in which case it holds the numeral's value. -/
theorem fold_argument (index : UInt64) (arg : List UInt8) (h : (0 : UInt8) ∉ arg) :
    ∃ v ok, arg.foldl (byteStep index) (index, 0, true, false) =
        (index, v, ok, decide (arg ≠ [])) ∧
      (ok = true ↔ (∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57) ∧ RandomHistogram.numeral arg < 2 ^ 64) ∧
      (ok = true → v.toNat = RandomHistogram.numeral arg) := by
  induction arg using List.reverseRecOn with
  | nil => exact ⟨0, true, rfl, by simp [RandomHistogram.numeral], fun _ => rfl⟩
  | append_singleton pre b ih =>
    have hpre : (0 : UInt8) ∉ pre := fun m => h (List.mem_append_left _ m)
    have hb : b ≠ 0 := fun e => h (e ▸ List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨v, ok, hfold, hok, hv⟩ := ih hpre
    rw [List.foldl_append, hfold, RandomHistogram.numeral_snoc]
    simp only [List.foldl_cons, List.foldl_nil]
    have hbne : b.toUInt64 ≠ 0 := fun e => hb (RandomHistogram.toUInt64_eq_zero.mp e)
    have hbn : b.toUInt64.toNat = b.toNat := by simp
    have hall : (∀ x ∈ pre ++ [b], 48 ≤ x ∧ x ≤ 57) ↔
        (∀ x ∈ pre, 48 ≤ x ∧ x ≤ 57) ∧ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
      constructor
      · intro hx
        have hb' := (RandomHistogram.digit_iff b).mp (hx b (List.mem_append_right _ (List.mem_singleton_self _)))
        exact ⟨fun x m => hx x (List.mem_append_left _ m), hb'.1, hb'.2⟩
      · rintro ⟨hp, h48, h57⟩ x m
        rcases List.mem_append.mp m with m | m
        · exact hp x m
        · rw [List.mem_singleton.mp m]
          exact (RandomHistogram.digit_iff b).mpr ⟨h48, h57⟩
    have hvb : (v == 1844674407370955161) = true ↔ v.toNat = 1844674407370955161 := by
      rw [beq_iff_eq]
      constructor
      · rintro rfl
        rfl
      · intro e
        exact UInt64.toNat_inj.mp (by rw [e]; rfl)
    have hc : (48 ≤ b.toUInt64 && b.toUInt64 ≤ 57 &&
        (v < 1844674407370955161 || (v == 1844674407370955161 && b.toUInt64 ≤ 53))) = true ↔
        (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∧
          (v.toNat < 1844674407370955161 ∨ (v.toNat = 1844674407370955161 ∧ b.toNat ≤ 53)) := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hvb,
        UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hbn, UInt64.reduceToNat]
    by_cases hcond : (48 ≤ b.toUInt64 && b.toUInt64 ≤ 57 &&
        (v < 1844674407370955161 || (v == 1844674407370955161 && b.toUInt64 ≤ 53))) = true
    · obtain ⟨⟨h48, h57⟩, hsmall⟩ := hc.mp hcond
      refine ⟨10 * v + (b.toUInt64 - 48), ok, ?_, ?_, ?_⟩
      · simp only [byteStep]
        rw [parseStep_arg index v ok _ _ hbne, ite_eq_left hcond]
        simp
      · rw [hall]
        constructor
        · intro hokt
          obtain ⟨hpd, _⟩ := hok.mp hokt
          have := hv hokt
          exact ⟨⟨hpd, h48, h57⟩, by omega⟩
        · rintro ⟨⟨hpd, _⟩, hlt⟩
          exact hok.mpr ⟨hpd, by omega⟩
      · intro hokt
        have hvn := hv hokt
        have h48' : (48 : UInt64) ≤ b.toUInt64 := by
          rw [UInt64.le_iff_toNat_le, hbn]
          simpa using h48
        rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub_of_le _ _ h48', hbn]
        simp only [UInt64.reduceToNat]
        omega
    · refine ⟨v, false, ?_, ?_, fun e => absurd e (by simp)⟩
      · simp only [byteStep]
        rw [parseStep_arg index v ok _ _ hbne, ite_eq_right hcond]
        simp
      · simp only [Bool.false_eq_true, false_iff]
        rw [hall]
        rintro ⟨⟨hpd, h48, h57⟩, hlt⟩
        have hnot := mt hc.mpr hcond
        by_cases hokt : ok = true
        · have hvn := hv hokt
          apply hnot
          exact ⟨⟨h48, h57⟩, by omega⟩
        · exact hokt (hok.mpr ⟨hpd, by omega⟩)

/-- The value that `parseArg` returns from its final state. -/
def result (index : UInt64) (s : UInt64 × UInt64 × Bool × Bool) : UInt64 :=
  if index < s.1 && s.2.2.1 && s.2.2.2 && s.2.1 != 0 then s.2.1 else 0

/-- The value that `parseSpec` gives for an argument, or for a missing one. -/
def specValue (arg : Option (List UInt8)) : UInt64 :=
  match arg >>= decimal with
  | some n => if 1 ≤ n ∧ n < 2 ^ 64 then UInt64.ofNat n else 0
  | none => 0

theorem argument_none {l : List UInt8} (h : (0 : UInt8) ∉ l) (i : Nat) : argument l i = none := by
  simp [argument, List.splitOn_eq_singleton h]

theorem argument_zero {arg : List UInt8} (harg : (0 : UInt8) ∉ arg) (rest : List UInt8) :
    argument (arg ++ 0 :: rest) 0 = some arg := by
  unfold argument
  rw [List.splitOn_append_cons_self_of_not_mem harg]
  have hne := List.splitOn_ne_nil 0 rest
  cases e : rest.splitOn 0 with
  | nil => exact absurd e hne
  | cons first more => simp

theorem argument_succ {pre : List UInt8} (hpre : (0 : UInt8) ∉ pre) (rest : List UInt8) (i : Nat) :
    argument (pre ++ 0 :: rest) (i + 1) = argument rest i := by
  unfold argument
  rw [List.splitOn_append_cons_self_of_not_mem hpre]
  simp

/-- The final value of an argument whose fold ended in a count above `index`. -/
theorem result_arg {index v : UInt64} {ok : Bool} {z : UInt64} {arg : List UInt8}
    (hz : index.toNat < z.toNat)
    (hok : ok = true ↔ (∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57) ∧ RandomHistogram.numeral arg < 2 ^ 64)
    (hv : ok = true → v.toNat = RandomHistogram.numeral arg) :
    result index (z, v, ok, decide (arg ≠ [])) = specValue (some arg) := by
  unfold result specValue
  change (if (decide (index < z) && ok && decide (arg ≠ []) && v != 0) = true then v else 0) =
    (match (if arg ≠ [] ∧ ∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57 then some (RandomHistogram.numeral arg) else none) with
      | some n => if 1 ≤ n ∧ n < 2 ^ 64 then UInt64.ofNat n else 0
      | none => 0)
  have hz' : decide (index < z) = true := by simp [UInt64.lt_iff_toNat_lt, hz]
  rw [hz']
  by_cases hokt : ok = true
  · obtain ⟨hdig, hlt⟩ := hok.mp hokt
    have hvn := hv hokt
    by_cases hne : arg = []
    · subst hne
      simp
    · rw [ite_eq_left (show arg ≠ [] ∧ ∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57 from ⟨hne, hdig⟩)]
      have hb : (true && ok && decide (arg ≠ []) && v != 0) = (v != 0) := by
        simp [hokt, hne]
      rw [hb]
      by_cases hzero : v = 0
      · have hnum : RandomHistogram.numeral arg = 0 := by rw [← hvn, hzero]; rfl
        simp [hzero, hnum]
      · have hpos : 1 ≤ RandomHistogram.numeral arg := by
          have : v.toNat ≠ 0 := fun e => hzero (UInt64.toNat_inj.mp (by simpa using e))
          omega
        have hvz : (v != 0) = true := by simpa using hzero
        rw [ite_eq_left hvz]
        show v = if 1 ≤ RandomHistogram.numeral arg ∧ RandomHistogram.numeral arg < 2 ^ 64 then UInt64.ofNat (RandomHistogram.numeral arg) else 0
        rw [ite_eq_left ⟨hpos, hlt⟩]
        apply UInt64.toNat_inj.mp
        rw [hvn, UInt64.toNat_ofNat_of_lt' hlt]
  · have hokf : ok = false := by simpa using hokt
    have hb : (true && ok && decide (arg ≠ []) && v != 0) = false := by simp [hokf]
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hgood : arg ≠ [] ∧ ∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57
    · rw [ite_eq_left hgood]
      have hge : ¬ RandomHistogram.numeral arg < 2 ^ 64 := fun hlt => hokt (hok.mpr ⟨hgood.2, hlt⟩)
      show (0 : UInt64) =
        if 1 ≤ RandomHistogram.numeral arg ∧ RandomHistogram.numeral arg < 2 ^ 64 then UInt64.ofNat (RandomHistogram.numeral arg) else 0
      rw [ite_eq_right (fun hc => hge hc.2)]
    · rw [ite_eq_right hgood]

/-- From a count `z` that is `i` below `index`, the fold computes the specification's value of
argument `i` of the remaining bytes. -/
theorem fold_parse (index : UInt64) :
    ∀ (i : Nat) (l : List UInt8) (z : UInt64), z.toNat + i = index.toNat →
      z.toNat + l.length < 2 ^ 64 →
      result index (l.foldl (byteStep index) (z, 0, true, false)) = specValue (argument l i)
  | 0, l, z, hz, hlen => by
    have hzi : z = index := UInt64.toNat_inj.mp (by omega)
    subst hzi
    by_cases h0 : (0 : UInt8) ∈ l
    · obtain ⟨arg, rest, rfl, harg⟩ := RandomHistogram.split_first 0 l h0
      obtain ⟨v, ok, hfold, hok, hv⟩ := fold_argument z arg harg
      rw [List.foldl_append, hfold, List.foldl_cons, byteStep_zero, argument_zero harg rest]
      simp only [List.length_append, List.length_cons] at hlen
      have hsum : (z + 1).toNat = z.toNat + 1 := by
        rw [UInt64.toNat_add]
        simp only [UInt64.reduceToNat]
        omega
      obtain ⟨z', hafter, hz'⟩ := fold_after (index := z) (v := v) (ok := ok)
        (ne := decide (arg ≠ [])) rest (z + 1) (by omega) (by omega)
      rw [hafter]
      exact result_arg hz' hok hv
    · obtain ⟨v, ok, hfold, -, -⟩ := fold_argument z l h0
      rw [hfold, argument_none h0]
      simp [result, specValue]
  | i + 1, l, z, hz, hlen => by
    have hne : z ≠ index := fun e => by rw [e] at hz; omega
    by_cases h0 : (0 : UInt8) ∈ l
    · obtain ⟨pre, rest, rfl, hpre⟩ := RandomHistogram.split_first 0 l h0
      rw [List.foldl_append, fold_skip hne pre hpre, List.foldl_cons, byteStep_zero,
        argument_succ hpre]
      simp only [List.length_append, List.length_cons] at hlen
      have hsum : (z + 1).toNat = z.toNat + 1 := by
        rw [UInt64.toNat_add]
        simp only [UInt64.reduceToNat]
        omega
      exact fold_parse index i rest (z + 1) (by omega) (by omega)
    · rw [fold_skip hne l h0, argument_none h0]
      have hnot : ¬ index < z := fun h => by
        have := UInt64.lt_iff_toNat_lt.mp h
        omega
      simp [result, specValue, hnot]

/-- `parseArg` computes `parseSpec` on every buffer of fewer than `2^64` bytes. -/
theorem parseArg_eq (args : Bytes) (index : UInt64) (h : args.data.size < 2 ^ 64) :
    parseArg args index = parseSpec (args, index) := by
  have hloop := RandomHistogram.loop_bytes args h ((0 : UInt64), (0 : UInt64), true, false) (parseStep index)
  show result index (LeanExe.loop args.size ((0 : UInt64), (0 : UInt64), true, false) fun i s =>
    parseStep index s (args.get i)) = specValue (argument args.data.data.toList index.toNat)
  rw [hloop]
  exact fold_parse index index.toNat _ 0 (by simp) (by simpa using h)

/-! ## pick -/

/-- `pick` computes `pickSpec` on every word. -/
theorem pick_eq (n w : UInt64) : pick n w = pickSpec (n, w) := by
  unfold pick pickSpec accepts
  dsimp only
  by_cases hn : n = 0
  · subst hn
    simp
  · have hpos : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hn
      · exact e
    have hlt : n.toNat < 2 ^ 64 := n.toNat_lt
    have hsize : UInt64.size = 2 ^ 64 := rfl
    have hsub : (0 - n).toNat = 2 ^ 64 - n.toNat := by
      rw [UInt64.toNat_sub]
      simp only [UInt64.toNat_zero]
      omega
    have hthreshold : ((0 - n) % n).toNat = 2 ^ 64 % n.toNat := by
      rw [UInt64.toNat_mod, hsub]
      conv_rhs => rw [show (2 : Nat) ^ 64 = (2 ^ 64 - n.toNat) + n.toNat by omega]
      rw [Nat.add_mod_right]
    have hle : (0 - n) % n ≤ w ↔ 2 ^ 64 % n.toNat ≤ w.toNat := by
      rw [UInt64.le_iff_toNat_le, hthreshold]
    have hn' : (n != 0) = true := by simpa using hn
    simp only [hn', Bool.true_and, decide_eq_true_eq]
    by_cases hc : 2 ^ 64 % n.toNat ≤ w.toNat
    · rw [ite_eq_left (hle.mpr hc), ite_eq_left hc]
      have hmod : w.toNat % n.toNat < n.toNat := Nat.mod_lt _ hpos
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' (by omega)]
      generalize w.toNat % n.toNat = m at hmod ⊢
      simp only [UInt64.reduceToNat]
      omega
    · rw [ite_eq_right (mt hle.mp hc), ite_eq_right hc]

/-! ## render -/

/-- The words of the line of `v`: its decimal digits and a newline. -/
def lineWords (v : UInt64) : List UInt64 := digitWords v.toNat ++ [10]

/-- The words of the lines of `values`. -/
def textWords (values : List UInt64) : List UInt64 := values.flatMap lineWords

theorem lineWords_length (v : UInt64) : (lineWords v).length = (digitCount v).toNat + 1 := by
  simp [lineWords, digitCount_toNat]

theorem textWords_cons (v : UInt64) (l : List UInt64) :
    textWords (v :: l) = lineWords v ++ textWords l := by
  simp [textWords]

theorem textWords_snoc (l : List UInt64) (v : UInt64) :
    textWords (l ++ [v]) = textWords l ++ lineWords v := by
  simp [textWords]

theorem textWords_length_le (l : List UInt64) : (textWords l).length ≤ 21 * l.length := by
  induction l with
  | nil => simp [textWords]
  | cons v l ih =>
    have := digitWords_length_le _ v.toNat_lt
    rw [textWords_cons, List.length_append, lineWords_length, digitCount_toNat,
      List.length_cons]
    omega

/-- `textSize` adds the length of each line to its initial count. -/
theorem textSize_fold :
    ∀ (l : List UInt64) (t : UInt64), t.toNat + (textWords l).length < 2 ^ 64 →
      (l.foldl (fun total v => total + digitCount v + 1) t).toNat = t.toNat + (textWords l).length
  | [], t, _ => by simp [textWords]
  | v :: l, t, h => by
    rw [textWords_cons, List.length_append, lineWords_length] at h ⊢
    rw [List.foldl_cons]
    have hstep : (t + digitCount v + 1).toNat = t.toNat + ((digitCount v).toNat + 1) := by
      rw [UInt64.toNat_add, UInt64.toNat_add]
      simp only [UInt64.reduceToNat]
      omega
    rw [textSize_fold l _ (by rw [hstep]; omega), hstep]
    omega

theorem textSize_eq (values : Array UInt64) (h : values.size < 2 ^ 59) :
    (textSize values).toNat = (textWords values.toList).length := by
  have hlen : (textWords values.toList).length ≤ 21 * values.size := by
    simpa using textWords_length_le values.toList
  unfold textSize
  rw [← Array.foldl_toList, textSize_fold _ 0 (by simp; omega)]
  simp

/-- Digit `k` of `v`, counted from the most significant, as `putLine` reads it. -/
theorem digitByte_word (v k : UInt64) (hk : k.toNat < (digitCount v).toNat) :
    digitByte v (digitCount v - 1 - k) = (digitWords v.toNat).getD k.toNat 0 := by
  have hL := digitCount_toNat v
  have hget := digitWords_getElem? v.toNat k.toNat
  have hlen : k.toNat < (digitWords v.toNat).length := by omega
  have hidx : (digitCount v - 1 - k).toNat = (digitWords v.toNat).length - 1 - k.toNat := by
    have hk : k.toNat < 2 ^ 64 := k.toNat_lt
    have h20 := digitWords_length_le v.toNat v.toNat_lt
    rw [UInt64.toNat_sub, UInt64.toNat_sub, hL]
    simp only [UInt64.reduceToNat, Nat.reducePow]
    omega
  rw [ite_eq_left hlen] at hget
  rw [List.getD_eq_getElem?_getD, hget, Option.getD_some, digitByte_eq, hidx]

/-- `putLine` writes the line of `v` from `pos` and keeps the words before `pos`. -/
theorem putLine_get (text : Array UInt64) (pos v : UInt64)
    (hfit : pos.toNat + (lineWords v).length ≤ text.size) (hsmall : text.size < 2 ^ 64) :
    (putLine text pos v).size = text.size ∧
      ∀ i < pos.toNat + (lineWords v).length, (putLine text pos v)[i]! =
        if i < pos.toNat then text[i]! else (lineWords v).getD (i - pos.toNat) 0 := by
  have hlen := lineWords_length v
  have hdw : (digitWords v.toNat).length = (digitCount v).toNat := (digitCount_toNat v).symm
  generalize hL : (digitCount v).toNat = L at hlen hdw
  have key := LeanExe.Dialect.loop_induction (n := digitCount v) (init := text)
    (f := fun k t => t.set! (pos + k).toNat (digitByte v (digitCount v - 1 - k)))
    (fun k t => t.size = text.size ∧ ∀ i < text.size, t[i]! =
      if pos.toNat ≤ i ∧ i < pos.toNat + k then (digitWords v.toNat).getD (i - pos.toNat) 0
      else text[i]!)
    ⟨rfl, fun i _ => by rw [ite_eq_right (by omega)]⟩
    (by
      intro k t hk ⟨hsize, hget⟩
      rw [hL] at hk
      have hk64 : k < 2 ^ 64 := by omega
      have hpos : (pos + UInt64.ofNat k).toNat = pos.toNat + k := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hk64]
        omega
      have hdigit := digitByte_word v (UInt64.ofNat k)
        (by rw [UInt64.toNat_ofNat_of_lt' hk64, hL]; omega)
      rw [UInt64.toNat_ofNat_of_lt' hk64] at hdigit
      refine ⟨by simp [hsize], fun i hi => ?_⟩
      show (t.set! (pos + UInt64.ofNat k).toNat _)[i]! = _
      rw [hpos, LeanExe.Dialect.get_set _ _ _ _ (by omega), hdigit]
      by_cases he : i = pos.toNat + k
      · rw [ite_eq_left he, ite_eq_left (by omega), he, Nat.add_sub_cancel_left]
      · rw [ite_eq_right he, hget i hi]
        by_cases hin : pos.toNat ≤ i ∧ i < pos.toNat + k
        · rw [ite_eq_left hin, ite_eq_left (by omega)]
        · rw [ite_eq_right hin, ite_eq_right (by omega)])
  rw [hL] at key
  obtain ⟨hsize, hget⟩ := key
  have hnl : (pos + digitCount v).toNat = pos.toNat + L := by
    rw [UInt64.toNat_add, hL]
    omega
  unfold putLine
  simp only
  refine ⟨by rw [← hsize]; simp, fun i hi => ?_⟩
  rw [hnl, LeanExe.Dialect.get_set _ _ _ _ (by omega)]
  by_cases he : i = pos.toNat + L
  · rw [ite_eq_left he, ite_eq_right (by omega), lineWords,
      List.getD_append_right _ _ _ _ (by omega)]
    simp [he, hdw]
  · rw [ite_eq_right he, hget i (by omega)]
    by_cases hlt : i < pos.toNat
    · rw [ite_eq_right (by omega), ite_eq_left hlt]
    · rw [ite_eq_left (by omega), ite_eq_right hlt, lineWords, List.getD_append _ _ _ _ (by omega)]

/-- The fold of `render` writes the lines of the values after those of `done`. -/
theorem fill_fold (total : Nat) (htotal : total < 2 ^ 64) :
    ∀ (values done : List UInt64) (arr : Array UInt64) (pos : UInt64),
      arr.size = total → pos.toNat = (textWords done).length →
      (textWords done).length + (textWords values).length ≤ total →
      (∀ i < pos.toNat, arr[i]! = (textWords done).getD i 0) →
      (values.foldl (fun s v => (putLine s.1 s.2 v, s.2 + digitCount v + 1)) (arr, pos)).1.size =
          total ∧
        (values.foldl (fun s v => (putLine s.1 s.2 v, s.2 + digitCount v + 1))
          (arr, pos)).2.toNat = (textWords (done ++ values)).length ∧
        ∀ i < (textWords (done ++ values)).length,
          (values.foldl (fun s v => (putLine s.1 s.2 v, s.2 + digitCount v + 1)) (arr, pos)).1[i]! =
            (textWords (done ++ values)).getD i 0
  | [], done, arr, pos, hsize, hpos, _, hget => by
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨hsize, hpos, fun i hi => hget i (by omega)⟩
  | v :: values, done, arr, pos, hsize, hpos, hfit, hget => by
    simp only [List.foldl_cons]
    rw [textWords_cons, List.length_append] at hfit
    have hline := lineWords_length v
    obtain ⟨hsize', hget'⟩ := putLine_get arr pos v (by omega) (by omega)
    have hnext : (pos + digitCount v + 1).toNat = (textWords (done ++ [v])).length := by
      rw [UInt64.toNat_add, UInt64.toNat_add, textWords_snoc, List.length_append]
      simp only [UInt64.reduceToNat]
      omega
    have key := fill_fold total htotal values (done ++ [v]) (putLine arr pos v)
      (pos + digitCount v + 1) (by rw [hsize', hsize]) hnext
      (by rw [textWords_snoc, List.length_append]; omega)
      (by
        intro i hi
        rw [hnext, textWords_snoc, List.length_append] at hi
        rw [hget' i (by omega), textWords_snoc]
        by_cases hlt : i < pos.toNat
        · rw [ite_eq_left hlt, hget i hlt, List.getD_append _ _ _ _ (by omega)]
        · rw [ite_eq_right hlt, List.getD_append_right _ _ _ _ (by omega), hpos])
    simpa using key

/-- `render` computes `renderSpec` on every array of fewer than `2^59` values. -/
theorem render_eq (values : Array UInt64) (h : values.size < 2 ^ 59) :
    render values = renderSpec values := by
  have hlen : (textWords values.toList).length ≤ 21 * values.size := by
    simpa using textWords_length_le values.toList
  have htotal := textSize_eq values h
  obtain ⟨hsize, -, hget⟩ := fill_fold (textWords values.toList).length (by omega) values.toList []
    (LeanExe.build (textSize values) fun _ => (0 : UInt64)) 0
    (by rw [LeanExe.Dialect.build_size, htotal]) (by simp [textWords]) (by simp [textWords])
    (fun i hi => absurd hi (by simp))
  simp only [List.nil_append] at hsize hget
  rw [Array.foldl_toList] at hsize hget
  generalize hs : values.foldl (fun s v => (putLine s.1 s.2 v, s.2 + digitCount v + 1))
    (LeanExe.build (textSize values) fun _ => (0 : UInt64), (0 : UInt64)) = s at hsize hget
  have hlist : s.1.toList = textWords values.toList := by
    apply List.ext_getElem
    · simp [hsize]
    · intro i h1 h2
      have hi : i < s.1.size := by simpa using h1
      rw [Array.getElem_toList, ← getElem!_pos s.1 i hi, hget i h2, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h2, Option.getD_some]
  have hcount : textSize values = s.1.size.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [htotal, LeanExe.Dialect.size_toUInt64 _ (by omega), hsize]
  have hrender : render values = Bytes.build s.1.size.toUInt64 fun i => s.1[i.toNat]! := by
    unfold render
    simp only [hs]
    rw [hcount]
  rw [hrender, RandomHistogram.build_words s.1 (by omega), hlist]
  unfold renderSpec
  refine congrArg (fun l : List UInt8 => (⟨⟨l.toArray⟩⟩ : Bytes)) ?_
  rw [textWords, List.map_flatMap]
  refine congrArg (fun f => List.flatMap f values.toList) (funext fun v => ?_)
  rw [lineWords, List.map_append, RandomHistogram.digitWords_bytes]
  rfl

end Demos.RandomChoice
