import Demos.Rcv.Spec
import Demos.Rcv.Program
import LeanExe.Dialect.Lemmas
import Mathlib.Data.Nat.BitIndices

/-!
Facts about words and masks for the refinement of `Demos.Rcv.Program.count`: the position of a word
as `classify` decides it, the masks of the specification's candidate lists, `members`, the
candidates of a mask, and `LeanExe.loop` as a fold over a list.
-/

namespace Demos.Rcv.Refine

open Demos.Rcv Demos.Rcv.Spec

/-! ## Words and bits -/

theorem bne_zero (w : UInt64) : (w != 0) = (w.toNat != 0) := by
  by_cases h : w = 0
  · subst h; rfl
  · have h' : w.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
    rw [show (w != 0) = true from bne_iff_ne.mpr h,
      show (w.toNat != 0) = true from bne_iff_ne.mpr h']

theorem toUInt64_eq {w : UInt64} {x : Nat} (h : w.toNat = x) : x.toUInt64 = w := by
  subst h
  simp

/-- A word equals a number below `2 ^ 64` whose bits below 64 it has. -/
theorem toNat_eq_of_testBit {w : UInt64} {x : Nat} (hx : x < 2 ^ 64)
    (h : ∀ j, j < 64 → w.toNat.testBit j = x.testBit j) : w.toNat = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · exact h j hj
  · have hp : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (UInt64.toNat_lt w) hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hp)]

theorem two_pow_and_ne_zero (j c : Nat) : 2 ^ j &&& c ≠ 0 ↔ c.testBit j = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Nat.testBit_two_pow] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨rfl, hc⟩ := hi
    exact hc
  · intro h hz
    have := congrArg (fun x => Nat.testBit x j) hz
    simp [Nat.testBit_and, h] at this

theorem bitIndex_shift : ∀ j : Fin 64,
    Program.bitIndex ((1 : UInt64) <<< UInt64.ofNat j.val) = UInt64.ofNat j.val := by
  decide +kernel

theorem toNat_shift : ∀ j : Fin 64, ((1 : UInt64) <<< UInt64.ofNat j.val).toNat = 2 ^ j.val := by
  decide +kernel

theorem position_shift : ∀ j : Fin 63,
    position ((1 : UInt64) <<< UInt64.ofNat j.val) = .single (j.val + 1) := by
  decide +kernel

theorem bitIndex_shift' {j : Nat} (hj : j < 64) :
    Program.bitIndex ((1 : UInt64) <<< UInt64.ofNat j) = UInt64.ofNat j :=
  bitIndex_shift ⟨j, hj⟩

theorem toNat_shift' {j : Nat} (hj : j < 64) : ((1 : UInt64) <<< UInt64.ofNat j).toNat = 2 ^ j :=
  toNat_shift ⟨j, hj⟩

theorem position_shift' {j : Nat} (hj : j < 63) :
    position ((1 : UInt64) <<< UInt64.ofNat j) = .single (j + 1) :=
  position_shift ⟨j, hj⟩

theorem bitIndex_le (w : UInt64) : (Program.bitIndex w).toNat ≤ 63 := by
  unfold Program.bitIndex
  dsimp only
  split_ifs <;> decide

theorem bit63_iff (w : UInt64) :
    w.toNat.testBit 63 = true ↔ (0x7FFFFFFFFFFFFFFF : UInt64) < w := by
  have hw : w.toNat < 18446744073709551616 := UInt64.toNat_lt w
  rw [UInt64.lt_iff_toNat_lt,
    show (0x7FFFFFFFFFFFFFFF : UInt64).toNat = 9223372036854775807 from rfl]
  constructor
  · intro h
    by_contra hlt
    rw [Nat.testBit_lt_two_pow (show w.toNat < 2 ^ 63 by norm_num; omega)] at h
    exact absurd h (by simp)
  · intro h
    exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by norm_num; omega) (by norm_num; omega)

/-- `(m >>> i) &&& 1`, the test of bit `i` that the program applies to a mask. -/
theorem bit_test (m : UInt64) {i : Nat} (hi : i < 64) :
    ((m >>> UInt64.ofNat i) &&& 1 != 0) = m.toNat.testBit i := by
  rw [bne_zero, Nat.testBit, Nat.one_and_eq_mod_two]
  congr 1
  have h64 : i < 2 ^ 64 := by omega
  simp [UInt64.toNat_ofNat_of_lt' h64, Nat.mod_eq_of_lt hi]

theorem shift_and_ne_zero (m : UInt64) {j : Nat} (hj : j < 64) :
    ((1 : UInt64) <<< UInt64.ofNat j &&& m != 0) = m.toNat.testBit j := by
  rw [bne_zero, UInt64.toNat_and, toNat_shift' hj]
  cases h : m.toNat.testBit j
  · have : ¬ (2 ^ j &&& m.toNat ≠ 0) := fun h' => by
      rw [(two_pow_and_ne_zero j m.toNat).mp h'] at h; cases h
    simp only [ne_eq, Decidable.not_not] at this
    simp [this]
  · have := (two_pow_and_ne_zero j m.toNat).mpr h
    simp [this]

/-! ## Positions -/

theorem mem_marks {w : UInt64} {i : Nat} :
    i ∈ marks w ↔ 1 ≤ i ∧ i ≤ 63 ∧ w.toNat.testBit (i - 1) = true := by
  unfold marks
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨j, ⟨hj, hb⟩, rfl⟩
    exact ⟨by omega, by omega, by simpa using hb⟩
  · rintro ⟨h1, h2, hb⟩
    exact ⟨i - 1, ⟨by omega, hb⟩, by omega⟩

theorem marks_nil {w : UInt64} (h : marks w = []) (h63 : w.toNat.testBit 63 = false) : w = 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_zero]
  apply toNat_eq_of_testBit (by norm_num)
  intro j hj
  rw [Nat.zero_testBit]
  by_cases hj63 : j = 63
  · subst hj63; exact h63
  · cases hb : w.toNat.testBit j
    · rfl
    · have hm : j + 1 ∈ marks w := mem_marks.mpr ⟨by omega, by omega, by simpa using hb⟩
      rw [h] at hm
      simp at hm

theorem marks_single {w : UInt64} {a : Nat} (h : marks w = [a]) (h63 : w.toNat.testBit 63 = false) :
    1 ≤ a ∧ a ≤ 63 ∧ w = (1 : UInt64) <<< UInt64.ofNat (a - 1) := by
  have ha : a ∈ marks w := by rw [h]; simp
  obtain ⟨h1, h2, hb⟩ := mem_marks.mp ha
  refine ⟨h1, h2, ?_⟩
  apply UInt64.toNat_inj.mp
  rw [toNat_shift' (show a - 1 < 64 by omega)]
  apply toNat_eq_of_testBit (Nat.pow_lt_pow_right (by norm_num) (by omega))
  intro j hj
  rw [Nat.testBit_two_pow]
  by_cases hja : j = a - 1
  · subst hja; simpa using hb
  · by_cases hj63 : j = 63
    · subst hj63
      rw [h63]
      simp only [Bool.false_eq, decide_eq_false_iff_not]
      omega
    · cases hb' : w.toNat.testBit j
      · simp only [Bool.false_eq, decide_eq_false_iff_not]
        omega
      · have hm : j + 1 ∈ marks w := mem_marks.mpr ⟨by omega, by omega, by simpa using hb'⟩
        rw [h] at hm
        simp at hm
        omega

theorem position_zero : position 0 = .empty := by
  decide +kernel

theorem position_of_bit63 {w : UInt64} (h : w.toNat.testBit 63 = true) :
    position w = .multiple := by
  unfold position
  rw [ite_eq_left h]

theorem position_multiple {w : UInt64} (h0 : w ≠ 0) (h63 : w.toNat.testBit 63 = false)
    (hs : ∀ j, j < 63 → w ≠ (1 : UInt64) <<< UInt64.ofNat j) : position w = .multiple := by
  unfold position
  rw [ite_eq_right (by simp [h63])]
  rcases hm : marks w with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact absurd (marks_nil hm h63) h0
  · obtain ⟨h1, h2, hw⟩ := marks_single hm h63
    exact absurd hw (hs (a - 1) (by omega))
  · rfl

theorem position_single {w : UInt64} {i : Nat} (h : position w = .single i) :
    1 ≤ i ∧ i ≤ 63 ∧ w = (1 : UInt64) <<< UInt64.ofNat (i - 1) := by
  unfold position at h
  split at h
  · cases h
  · next h63 =>
    have h63' : w.toNat.testBit 63 = false := by simpa using h63
    rcases hm : marks w with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rw [hm] at h; cases h
    · rw [hm] at h
      cases h
      exact marks_single hm h63'
    · rw [hm] at h; cases h

/-- `classify` reads the position of a word: it passes an empty word and a single word for a
candidate outside `cont`, gives the candidate of a single word inside `cont`, and gives 67 for a
multiple word. -/
theorem classify_eq (w cont : UInt64) :
    Program.classify w cont =
      match position w with
      | .empty => 0
      | .multiple => 67
      | .single i => if cont.toNat.testBit (i - 1) then UInt64.ofNat i else 0 := by
  unfold Program.classify
  by_cases h0 : w = 0
  · subst h0
    rw [position_zero]
    rfl
  · rw [ite_eq_right (by simpa using h0)]
    by_cases h63 : (0x7FFFFFFFFFFFFFFF : UInt64) < w
    · rw [ite_eq_left h63, position_of_bit63 ((bit63_iff w).mpr h63)]
    · rw [ite_eq_right h63]
      have hb : w.toNat.testBit 63 = false := by
        cases hh : w.toNat.testBit 63
        · rfl
        · exact absurd ((bit63_iff w).mp hh) h63
      dsimp only
      by_cases hs : (1 : UInt64) <<< Program.bitIndex w = w
      · have hj := bitIndex_le w
        have hjw : Program.bitIndex w = UInt64.ofNat (Program.bitIndex w).toNat :=
          UInt64.ofNat_toNat.symm
        generalize (Program.bitIndex w).toNat = j at hj hjw
        rw [hjw] at hs ⊢
        have hj63 : j < 63 := by
          by_contra hc
          have hj' : j = 63 := by omega
          subst hj'
          rw [← hs, toNat_shift' (by norm_num), Nat.testBit_two_pow] at hb
          simp at hb
        rw [ite_eq_right (by simpa using hs), ← hs, position_shift' hj63]
        simp only [Nat.add_sub_cancel]
        rw [shift_and_ne_zero cont (by omega)]
        congr 1
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one]
        omega
      · rw [ite_eq_left (by simpa using hs), position_multiple h0 hb]
        intro j hj heq
        apply hs
        rw [heq, bitIndex_shift' (by omega)]

/-! ## Masks -/

/-- The candidates `i` from 1 to `n` whose bit `i - 1` the mask `m` holds, in increasing order. -/
def members (m : UInt64) (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun i => m.toNat.testBit (i - 1)

theorem mem_members {m : UInt64} {n i : Nat} :
    i ∈ members m n ↔ 1 ≤ i ∧ i ≤ n ∧ m.toNat.testBit (i - 1) = true := by
  simp only [members, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by omega⟩, h3⟩

theorem members_sublist (m : UInt64) (n : Nat) : (members m n).Sublist (List.range' 1 n) :=
  List.filter_sublist

theorem sorted_of_sublist {s : List Nat} {n : Nat} (h : s.Sublist (List.range' 1 n)) :
    s.Pairwise (· < ·) :=
  (List.pairwise_lt_range' (s := 1) (n := n)).sublist h

theorem mask_eq_sum (s : List Nat) : mask s = ((s.map (· - 1)).map (2 ^ ·)).sum := by
  simp only [mask, List.map_map]
  rfl

/-- Bit `j` of the mask of an increasing list of candidates is set exactly when it holds `j + 1`. -/
theorem testBit_mask {s : List Nat} (hs : s.Pairwise (· < ·)) (hpos : ∀ i ∈ s, 1 ≤ i)
    (j : Nat) :
    (mask s).testBit j = decide (j + 1 ∈ s) := by
  have hsorted : (s.map (· - 1)).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    exact hs.imp_of_mem fun hx hy h => by
      have := hpos _ hx
      have := hpos _ hy
      omega
  have hbits := Nat.bitIndices_sum_map_two_pow hsorted
  rw [← mask_eq_sum] at hbits
  have key : (mask s).testBit j = true ↔ j + 1 ∈ s := by
    rw [← Nat.mem_bitIndices, hbits, List.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have := hpos i hi
      rwa [Nat.sub_add_cancel this]
    · intro h
      exact ⟨j + 1, h, rfl⟩
  by_cases h : j + 1 ∈ s
  · simp [key.mpr h, h]
  · have : (mask s).testBit j = false := by
      cases hb : (mask s).testBit j
      · rfl
      · exact absurd (key.mp hb) h
    simp [this, h]

theorem testBit_mask_sublist {s : List Nat} {n : Nat} (h : s.Sublist (List.range' 1 n)) (j : Nat) :
    (mask s).testBit j = decide (j + 1 ∈ s) :=
  testBit_mask (sorted_of_sublist h)
    (fun _ hi => (List.mem_range'_1.mp (h.subset hi)).1) j

theorem mask_lt {s : List Nat} {n : Nat} (h : s.Sublist (List.range' 1 n)) : mask s < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_mask_sublist h]
  simp only [decide_eq_false_iff_not]
  intro hm
  have := List.mem_range'_1.mp (h.subset hm)
  omega

theorem mask_members {m : UInt64} {n : Nat} (hm : m.toNat < 2 ^ n) :
    mask (members m n) = m.toNat := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_mask_sublist (members_sublist m n)]
  by_cases hj : j < n
  · simp [mem_members, hj]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [mem_members]
    omega

theorem mask_singleton (i : Nat) : mask [i] = 2 ^ (i - 1) := by
  simp [mask]

/-! ## Loops as folds -/

theorem loop_eq_foldl {α : Type} (n : UInt64) (init : α) (f : UInt64 → α → α) :
    LeanExe.loop n init f = (List.range n.toNat).foldl (fun s i => f (UInt64.ofNat i) s) init := by
  unfold LeanExe.loop
  generalize n.toNat = m
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.fold_succ, ih, List.range_succ, List.foldl_append]; rfl

theorem foldl_range_congr {α : Type} {m : Nat} {f g : α → Nat → α}
    (h : ∀ i, i < m → ∀ s, f s i = g s i) (init : α) :
    (List.range m).foldl f init = (List.range m).foldl g init := by
  induction m generalizing init with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun i hi s => h i (by omega) s)]
    simp [h m (by omega)]

/-- A loop over the candidates `0` to `n - 1` whose step changes the state only at the members of
the mask `m` is a fold over `members m n`. -/
theorem loop_members {α : Type} {m n : UInt64} {init : α} {f : UInt64 → α → α}
    {g : α → Nat → α}
    (hf : ∀ i, i < n.toNat → ∀ s, f (UInt64.ofNat i) s =
      if m.toNat.testBit i then g s (i + 1) else s) :
    LeanExe.loop n init f = (members m n.toNat).foldl g init := by
  rw [loop_eq_foldl, foldl_range_congr (fun i hi s => hf i hi s), members, List.foldl_filter,
    List.range'_eq_map_range, List.foldl_map]
  apply foldl_range_congr
  intro i _ s
  simp [Nat.add_comm 1 i]

end Demos.Rcv.Refine
