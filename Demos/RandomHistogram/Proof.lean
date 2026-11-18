import Demos.RandomHistogram.Program
import Demos.RandomHistogram.Spec
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas
import Library.Numerics.Decimal.Int64Text.Proof

/-! The programs of the pure core equal their specifications: `parseN_eq`, `histogram_eq`, and
`render_eq`, and the counts of `histogramSpec` sum to the number of words (`histogramSpec_sum`).

`parseN`'s loop over the buffer is a fold of `parseStep` over its bytes (`loop_bytes`).  The fold
leaves a state of phase 0 unchanged over bytes other than 0 (`fold_phase0`) and a state of phase 2
unchanged over every byte (`fold_phase2`), and over an argument without a zero byte it computes the
specification's value and decides whether the argument is a numeral below `2^64` (`fold_argument`).
The proof splits the buffer at its first two zero bytes, as `List.splitOn` does.  `histogram`'s fold
raises count `w mod 10` at each word (`fold_countWord`).  `render`'s array holds the digit words of
each count, which `digitWords_getElem?` and `digitCount_toNat` of the library's `Int64` printer
give, followed by a newline (`appendLine_toList`). -/

namespace Demos.RandomHistogram

open LeanExe Library.Numerics.Decimal.Int64Text

/-! ## parseN -/

/-- A loop over the positions of `bytes` that passes the byte at each position to `f` is a fold of
`f` over the bytes. -/
theorem loop_bytes {α : Type} (bytes : Bytes) (h : bytes.data.size < 2 ^ 64) (init : α)
    (f : α → UInt64 → α) :
    LeanExe.loop bytes.size init (fun i s => f s (bytes.get i)) =
      bytes.data.data.toList.foldl (fun s b => f s b.toUInt64) init := by
  have hsize : bytes.size.toNat = bytes.data.size := Bytes.size_toNat bytes h
  have key := LeanExe.Dialect.loop_induction (n := bytes.size) (init := init)
    (f := fun i s => f s (bytes.get i))
    (fun k s => s = (bytes.data.data.toList.take k).foldl (fun s b => f s b.toUInt64) init)
    (by simp)
    (by
      intro k s hk hs
      rw [hsize] at hk
      have hk64 : k < 2 ^ 64 := by omega
      have hget : bytes.get (UInt64.ofNat k) = bytes.data[k].toUInt64 := by
        simp only [Bytes.get, UInt64.toNat_ofNat_of_lt' hk64, hk, ↓reduceDIte]
      rw [List.take_add_one, List.foldl_append, ← hs, hget]
      have hlen : k < bytes.data.data.toList.length := by simpa using hk
      rw [List.getElem?_eq_getElem hlen]
      simp [ByteArray.getElem_eq_getElem_data])
  rw [hsize] at key
  rw [key, List.take_of_length_le (by simp)]

/-- `parseStep` on a byte. -/
abbrev byteStep (s : UInt64 × UInt64 × Bool × Bool) (b : UInt8) : UInt64 × UInt64 × Bool × Bool :=
  parseStep s b.toUInt64

/-- The value of a decimal numeral, as `decimal` computes it. -/
def numeral (text : List UInt8) : Nat := text.foldl (fun value b => 10 * value + (b.toNat - 48)) 0

theorem numeral_snoc (text : List UInt8) (b : UInt8) :
    numeral (text ++ [b]) = 10 * numeral text + (b.toNat - 48) := by
  simp [numeral, List.foldl_append]

theorem toUInt64_eq_zero {b : UInt8} : b.toUInt64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    apply UInt8.toNat_inj.mp
    have := congrArg UInt64.toNat h
    simpa using this
  · rintro rfl
    rfl

/-- Before the first zero byte, the fold keeps its state. -/
theorem fold_phase0 (v : UInt64) (ok ne : Bool) :
    ∀ l : List UInt8, (0 : UInt8) ∉ l → l.foldl byteStep (0, v, ok, ne) = (0, v, ok, ne)
  | [], _ => rfl
  | b :: l, h => by
    have hb : b ≠ 0 := fun e => h (e ▸ List.mem_cons_self)
    have hb' : b.toUInt64 ≠ 0 := fun e => hb (toUInt64_eq_zero.mp e)
    rw [List.foldl_cons]
    have : byteStep (0, v, ok, ne) b = (0, v, ok, ne) := by
      simp [byteStep, parseStep, hb']
    rw [this]
    exact fold_phase0 v ok ne l (fun m => h (List.mem_cons_of_mem _ m))

/-- After the second zero byte, the fold keeps its state. -/
theorem fold_phase2 (v : UInt64) (ok ne : Bool) :
    ∀ l : List UInt8, l.foldl byteStep (2, v, ok, ne) = (2, v, ok, ne)
  | [] => rfl
  | b :: l => by
    rw [List.foldl_cons]
    have : byteStep (2, v, ok, ne) b = (2, v, ok, ne) := by simp [byteStep, parseStep]
    rw [this]
    exact fold_phase2 v ok ne l

theorem digit_iff (b : UInt8) : (48 ≤ b ∧ b ≤ 57) ↔ (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  simp only [UInt8.le_iff_toNat_le, UInt8.reduceToNat]

/-- `parseStep` in phase 1 on a byte other than 0. -/
theorem parseStep_one (v : UInt64) (ok ne : Bool) (b : UInt64) (hb : b ≠ 0) :
    parseStep (1, v, ok, ne) b =
      if (48 ≤ b && b ≤ 57 &&
          (v < 1844674407370955161 || (v == 1844674407370955161 && b ≤ 53))) = true then
        (1, 10 * v + (b - 48), ok, true)
      else (1, v, false, true) := by
  have h1 : ((1 : UInt64) == 0) = false := by decide
  have h2 : ((1 : UInt64) == 1) = true := by decide
  have hb' : (b == 0) = false := by simpa using hb
  simp only [parseStep, h1, h2, hb', Bool.false_eq_true, ↓reduceIte]

/-- Over an argument without a zero byte, from phase 1, the fold stays in phase 1, records whether
the argument has a byte, and decides whether the argument is digits whose numeral lies below
`2^64`, in which case it holds the numeral's value. -/
theorem fold_argument (arg : List UInt8) (h : (0 : UInt8) ∉ arg) :
    ∃ v ok, arg.foldl byteStep (1, 0, true, false) = (1, v, ok, decide (arg ≠ [])) ∧
      (ok = true ↔ (∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57) ∧ numeral arg < 2 ^ 64) ∧
      (ok = true → v.toNat = numeral arg) := by
  induction arg using List.reverseRecOn with
  | nil => exact ⟨0, true, rfl, by simp [numeral], fun _ => rfl⟩
  | append_singleton pre b ih =>
    have hpre : (0 : UInt8) ∉ pre := fun m => h (List.mem_append_left _ m)
    have hb : b ≠ 0 := fun e => h (e ▸ List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨v, ok, hfold, hok, hv⟩ := ih hpre
    rw [List.foldl_append, hfold, numeral_snoc]
    simp only [List.foldl_cons, List.foldl_nil]
    have hbne : b.toUInt64 ≠ 0 := fun e => hb (toUInt64_eq_zero.mp e)
    have hbn : b.toUInt64.toNat = b.toNat := by simp
    have hblt := b.toNat_lt
    have hall : (∀ x ∈ pre ++ [b], 48 ≤ x ∧ x ≤ 57) ↔
        (∀ x ∈ pre, 48 ≤ x ∧ x ≤ 57) ∧ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
      constructor
      · intro hx
        have hb' := (digit_iff b).mp (hx b (List.mem_append_right _ (List.mem_singleton_self _)))
        exact ⟨fun x m => hx x (List.mem_append_left _ m), hb'.1, hb'.2⟩
      · rintro ⟨hp, h48, h57⟩ x m
        rcases List.mem_append.mp m with m | m
        · exact hp x m
        · rw [List.mem_singleton.mp m]
          exact (digit_iff b).mpr ⟨h48, h57⟩
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
        rw [parseStep_one v ok _ _ hbne, ite_eq_left hcond]
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
        rw [parseStep_one v ok _ _ hbne, ite_eq_right hcond]
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

/-- A list that holds `a` splits at its first `a`. -/
theorem split_first {α : Type} [DecidableEq α] (a : α) :
    ∀ l : List α, a ∈ l → ∃ s t, l = s ++ a :: t ∧ a ∉ s
  | [], h => absurd h List.not_mem_nil
  | x :: l, h => by
    by_cases hx : x = a
    · exact ⟨[], l, by simp [hx], List.not_mem_nil⟩
    · have hl : a ∈ l := by
        rcases List.mem_cons.mp h with e | m
        · exact absurd e.symm hx
        · exact m
      obtain ⟨s, t, rfl, hs⟩ := split_first a l hl
      refine ⟨x :: s, t, rfl, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => hx e.symm, hs⟩

theorem argument_none {l : List UInt8} (h : (0 : UInt8) ∉ l) : argument l = none := by
  simp [argument, List.splitOn_eq_singleton h]

theorem argument_missing {name rest : List UInt8} (hname : (0 : UInt8) ∉ name)
    (hrest : (0 : UInt8) ∉ rest) : argument (name ++ 0 :: rest) = none := by
  simp [argument, List.splitOn_append_cons_self_of_not_mem hname, List.splitOn_eq_singleton hrest]

theorem argument_some {name arg : List UInt8} (hname : (0 : UInt8) ∉ name)
    (harg : (0 : UInt8) ∉ arg) (tail : List UInt8) :
    argument (name ++ 0 :: (arg ++ 0 :: tail)) = some arg := by
  unfold argument
  rw [List.splitOn_append_cons_self_of_not_mem hname,
    List.splitOn_append_cons_self_of_not_mem harg]
  cases e : tail.splitOn 0 with
  | nil => exact absurd e (List.splitOn_ne_nil _ _)
  | cons first more => rfl

/-- `parseN` computes `parseSpec` on every buffer of fewer than `2^64` bytes. -/
theorem parseN_eq (args : Bytes) (h : args.data.size < 2 ^ 64) : parseN args = parseSpec args := by
  unfold parseN parseSpec
  rw [loop_bytes args h]
  generalize args.data.data.toList = l
  change (if (l.foldl byteStep (0, 0, true, false)).1 == 2 && _ && _ && _ != 0 then _ else _) = _
  by_cases h0 : (0 : UInt8) ∈ l
  · obtain ⟨name, rest, rfl, hname⟩ := split_first 0 l h0
    rw [List.foldl_append, fold_phase0 0 true false name hname, List.foldl_cons]
    have hstep : byteStep (0, 0, true, false) 0 = (1, 0, true, false) := by decide
    rw [hstep]
    by_cases h1 : (0 : UInt8) ∈ rest
    · obtain ⟨arg, tail, rfl, harg⟩ := split_first 0 rest h1
      obtain ⟨v, ok, hfold, hok, hv⟩ := fold_argument arg harg
      rw [List.foldl_append, hfold, List.foldl_cons]
      have hstep2 : byteStep (1, v, ok, decide (arg ≠ [])) 0 = (2, v, ok, decide (arg ≠ [])) := by
        simp [byteStep, parseStep]
      rw [hstep2, fold_phase2, argument_some hname harg tail]
      change (if ((2 : UInt64) == 2 && ok && decide (arg ≠ []) && v != 0) = true then v else 0) =
        (match (if arg ≠ [] ∧ ∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57 then some (numeral arg) else none) with
          | some n => if 1 ≤ n ∧ n < 2 ^ 64 then UInt64.ofNat n else 0
          | none => 0)
      by_cases hokt : ok = true
      · obtain ⟨hdig, hlt⟩ := hok.mp hokt
        have hvn := hv hokt
        by_cases hne : arg = []
        · subst hne
          simp
        · rw [ite_eq_left (show arg ≠ [] ∧ ∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57 from ⟨hne, hdig⟩)]
          have hb : ((2 : UInt64) == 2 && ok && decide (arg ≠ []) && v != 0) = (v != 0) := by
            simp [hokt, hne]
          rw [hb]
          by_cases hz : v = 0
          · have hzero : numeral arg = 0 := by rw [← hvn, hz]; rfl
            simp [hz, hzero]
          · have hpos : 1 ≤ numeral arg := by
              have : v.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
              omega
            have hvz : (v != 0) = true := by simpa using hz
            rw [ite_eq_left hvz]
            show v = if 1 ≤ numeral arg ∧ numeral arg < 2 ^ 64 then UInt64.ofNat (numeral arg) else 0
            rw [ite_eq_left ⟨hpos, hlt⟩]
            apply UInt64.toNat_inj.mp
            rw [hvn, UInt64.toNat_ofNat_of_lt' hlt]
      · have hokf : ok = false := by simpa using hokt
        have hb : ((2 : UInt64) == 2 && ok && decide (arg ≠ []) && v != 0) = false := by
          simp [hokf]
        rw [hb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hgood : arg ≠ [] ∧ ∀ b ∈ arg, 48 ≤ b ∧ b ≤ 57
        · rw [ite_eq_left hgood]
          have hge : ¬ numeral arg < 2 ^ 64 := fun hlt => hokt (hok.mpr ⟨hgood.2, hlt⟩)
          show (0 : UInt64) =
            if 1 ≤ numeral arg ∧ numeral arg < 2 ^ 64 then UInt64.ofNat (numeral arg) else 0
          rw [ite_eq_right (fun hc => hge hc.2)]
        · rw [ite_eq_right hgood]
    · obtain ⟨v, ok, hfold, -, -⟩ := fold_argument rest h1
      rw [hfold, argument_missing hname h1]
      rfl
  · rw [fold_phase0 0 true false l h0, argument_none h0]
    rfl

/-! ## histogram -/

theorem residue_toNat (w : UInt64) : (w % 10).toNat = w.toNat % 10 := by
  simp [UInt64.toNat_mod]

/-- Over the words `l`, from ten counts `c`, `countWord` raises count `m` by the number of words
whose residue is `m`. -/
theorem fold_countWord :
    ∀ (l : List UInt64) (c : Array UInt64), c.size = 10 →
      (l.foldl countWord c).size = 10 ∧
        ∀ m < 10, (l.foldl countWord c)[m]! =
          c[m]! + UInt64.ofNat (l.countP fun w => decide (w.toNat % 10 = m))
  | [], c, hc => ⟨hc, fun m _ => by simp⟩
  | w :: l, c, hc => by
    rw [List.foldl_cons]
    have hm : (w % 10).toNat < 10 := by rw [residue_toNat]; omega
    have hsize : (countWord c w).size = 10 := by simp [countWord, hc]
    obtain ⟨hs, hget⟩ := fold_countWord l (countWord c w) hsize
    refine ⟨hs, fun m hm10 => ?_⟩
    rw [hget m hm10]
    simp only [countWord]
    rw [LeanExe.Dialect.get_set _ _ _ _ (by omega), List.countP_cons, residue_toNat]
    by_cases he : m = w.toNat % 10
    · subst he
      rw [ite_eq_left rfl, ite_eq_left (decide_eq_true rfl)]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    · have hne : decide (w.toNat % 10 = m) = false := decide_eq_false fun e => he e.symm
      rw [ite_eq_right he, hne]
      simp

/-- `histogram` computes `histogramSpec` on every array. -/
theorem histogram_eq (ws : Array UInt64) : histogram ws = histogramSpec ws := by
  have hzero : (LeanExe.build 10 fun _ => (0 : UInt64)).size = 10 :=
    LeanExe.Dialect.build_size _ _
  obtain ⟨hs, hget⟩ := fold_countWord ws.toList _ hzero
  show ws.foldl countWord (LeanExe.build 10 fun _ => 0) = histogramSpec ws
  rw [← Array.foldl_toList]
  apply Array.ext
  · rw [hs]
    simp [histogramSpec]
  · intro m h1 _
    have hm : m < 10 := by rw [hs] at h1; exact h1
    have e := hget m hm
    rw [LeanExe.Dialect.build_get (show m < (10 : UInt64).toNat by simpa using hm),
      getElem!_pos _ m h1] at e
    rw [e]
    simp [histogramSpec]

/-- The counts of `histogramSpec` sum to the number of words, for an array of fewer than `2^64`
words. -/
theorem histogramSpec_sum (ws : Array UInt64) (h : ws.size < 2 ^ 64) :
    ((histogramSpec ws).toList.map UInt64.toNat).sum = ws.size := by
  have hcount : ∀ m, (ws.toList.countP fun w => decide (w.toNat % 10 = m)) < 2 ^ 64 := fun m =>
    lt_of_le_of_lt List.countP_le_length (by simpa using h)
  have hsum : ∀ l : List UInt64,
      ((List.range 10).map fun m => l.countP fun w => decide (w.toNat % 10 = m)).sum =
        l.length := by
    intro l
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [List.countP_cons, List.length_cons]
      rw [List.sum_map_add, ih]
      have hr : w.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
      congr 1
      generalize w.toNat % 10 = r at hr
      interval_cases r <;> decide
  have hlist : (histogramSpec ws).toList.map UInt64.toNat =
      (List.range 10).map fun m => ws.toList.countP fun w => decide (w.toNat % 10 = m) := by
    apply List.ext_getElem
    · simp [histogramSpec]
    · intro i h1 _
      simp only [histogramSpec, List.getElem_map, Array.getElem_toList, Array.getElem_ofFn,
        List.getElem_range]
      exact UInt64.toNat_ofNat_of_lt' (hcount i)
  rw [hlist, hsum, Array.length_toList]

/-! ## render -/

/-- The digit words of `c`'s decimal digits, then a newline, follow the text of `appendLine`. -/
theorem appendLine_toList (text : Array UInt64) (c : UInt64) :
    (appendLine text c).toList = text.toList ++ digitWords c.toNat ++ [10] := by
  have hL := digitCount_toNat c
  have hL20 := digitWords_length_le c.toNat c.toNat_lt
  have hget := digitWords_getElem? c.toNat
  generalize hLdef : (digitWords c.toNat).length = L at hL hL20 hget
  have key := LeanExe.Dialect.loop_induction (n := digitCount c) (init := text)
    (f := fun k t => t.push (digitByte c (digitCount c - 1 - k)))
    (fun k t => t.toList = text.toList ++ (digitWords c.toNat).take k) (by simp)
    (by
      intro k t hk ht
      rw [hL] at hk
      have hk64 : k < 2 ^ 64 := by omega
      have hidx : (digitCount c - 1 - UInt64.ofNat k).toNat = L - 1 - k := by
        rw [UInt64.toNat_sub, UInt64.toNat_sub, hL, UInt64.toNat_ofNat_of_lt' hk64]
        simp only [UInt64.reduceToNat]
        omega
      have hlen : k < (digitWords c.toNat).length := by omega
      have hdigit : digitByte c (digitCount c - 1 - UInt64.ofNat k) =
          (digitWords c.toNat)[k] := by
        have := hget k
        rw [List.getElem?_eq_getElem hlen, ite_eq_left (by omega)] at this
        rw [digitByte_eq, hidx]
        exact (Option.some.inj this).symm
      rw [Array.toList_push, ht, List.take_add_one, List.getElem?_eq_getElem hlen, List.append_assoc,
        hdigit]
      rfl)
  rw [hL] at key
  unfold appendLine
  simp only
  rw [Array.toList_push, key, ← hLdef, List.take_length]

/-- The bytes of a count's decimal text, as `renderSpec` writes them, are its digit words'
bytes. -/
theorem digitWords_bytes (n : Nat) :
    (digitWords n).map UInt64.toUInt8 = (toString n).toList.map fun c => c.toNat.toUInt8 := by
  rw [digitWords, List.map_map]
  have hs : (toString n).toList = Nat.toDigits 10 n := Nat.toList_repr
  rw [hs]
  apply List.map_congr_left
  intro ch _
  apply UInt8.toNat_inj.mp
  simp only [Function.comp_apply, UInt64.toNat_toUInt8, UInt8.toNat_toUInt64, Char.toUInt8,
    UInt32.toNat_toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', Char.toNat]
  omega

/-- The words of `render`'s array: the digit words of each of the ten counts, each followed by a
newline. -/
theorem render_text (counts : Array UInt64) :
    (LeanExe.loop 10 (#[] : Array UInt64) fun m t => appendLine t counts[m.toNat]!).toList =
      (List.range 10).flatMap fun m => digitWords (counts.getD m 0).toNat ++ [10] := by
  have key := LeanExe.Dialect.loop_induction (n := 10) (init := (#[] : Array UInt64))
    (f := fun m t => appendLine t counts[m.toNat]!)
    (fun k t => t.toList = (List.range k).flatMap fun m =>
      digitWords (counts.getD m 0).toNat ++ [10]) (by simp)
    (by
      intro k t hk ht
      have hk' : k < 10 := hk
      have hc : counts[(UInt64.ofNat k).toNat]! = counts.getD k 0 := by
        rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        simp only [getElem!_def, Array.getD_eq_getD_getElem?]
        cases counts[k]? <;> rfl
      show (appendLine t counts[(UInt64.ofNat k).toNat]!).toList = _
      rw [appendLine_toList, ht, hc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc])
  exact key

/-- A buffer built from the words of an array holds their low bytes. -/
theorem build_words (t : Array UInt64) (h : t.size < 2 ^ 64) :
    Bytes.build t.size.toUInt64 (fun i => t[i.toNat]!) = ⟨⟨(t.toList.map UInt64.toUInt8).toArray⟩⟩ := by
  have hn : t.size.toUInt64.toNat = t.size := LeanExe.Dialect.size_toUInt64 t h
  unfold Bytes.build
  congr 2
  apply Array.toList_inj.mp
  rw [Array.toList_ofFn, List.toList_toArray]
  apply List.ext_getElem
  · simp [hn]
  · intro i h1 _
    have hi : i < t.size := by simpa [hn] using h1
    rw [List.getElem_ofFn, List.getElem_map, Array.getElem_toList]
    show (t[(UInt64.ofNat i).toNat]!).toUInt8 = _
    rw [UInt64.toNat_ofNat_of_lt' (hi.trans h), getElem!_pos t i hi]

/-- `render`'s array holds at most 210 words: ten lines of at most 20 digits and a newline. -/
theorem render_text_size (counts : Array UInt64) :
    (LeanExe.loop 10 (#[] : Array UInt64) fun m t => appendLine t counts[m.toNat]!).size ≤ 210 := by
  rw [← Array.length_toList, render_text, List.length_flatMap]
  have hline : ∀ m ∈ List.range 10,
      (digitWords (counts.getD m 0).toNat ++ [10]).length ≤ 21 := by
    intro m _
    have := digitWords_length_le _ (counts.getD m 0).toNat_lt
    simp only [List.length_append, List.length_singleton]
    omega
  calc ((List.range 10).map fun m => (digitWords (counts.getD m 0).toNat ++ [10]).length).sum
      ≤ ((List.range 10).map fun _ => 21).sum := List.sum_le_sum (fun m hm => hline m hm)
    _ = 210 := by decide

/-- `render` computes `renderSpec` on every array. -/
theorem render_eq (counts : Array UInt64) : render counts = renderSpec counts := by
  have hsize := render_text_size counts
  obtain ⟨t, ht⟩ : ∃ t, LeanExe.loop 10 (#[] : Array UInt64)
      (fun m t => appendLine t counts[m.toNat]!) = t := ⟨_, rfl⟩
  have key := render_text counts
  rw [ht] at key hsize
  have hrender : render counts = Bytes.build t.size.toUInt64 fun i => t[i.toNat]! := by
    unfold render
    simp only [ht]
  rw [hrender, build_words t (by omega), key, List.map_flatMap]
  unfold renderSpec
  refine congrArg (fun l : List UInt8 => (⟨⟨l.toArray⟩⟩ : Bytes)) ?_
  refine congrArg (fun f => List.flatMap f (List.range 10)) (funext fun m => ?_)
  rw [List.map_append, digitWords_bytes]
  rfl

end Demos.RandomHistogram
