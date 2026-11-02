import LeanExe.Dialect.Build
import Library.Sorting.Heapsort.Program
import Library.Sorting.StraightInsertion.Program

/-! Quicksort, Algorithm Q of TAOCP §5.2.2, on an array of words, in place, with indices from 0
and subfiles written as half-open ranges `[l, e)`.  Steps Q2 to Q6 partition a subfile around its
first word `K`: `scanUp` and `scanDown` are steps Q3 and Q4, and `part` exchanges the words that
stop them until the scans cross, then puts `K` at its final position `j`.  Steps Q2 to Q8 form the
tail loop `stages`, which keeps the current subfile and a stack of pending subfiles: of the two
parts of a partition, it pushes the larger when both exceed `M = 9` words, continues with the
smaller, and takes the next subfile from the stack when the current one has at most `M` words.
Step Q9, `straightInsertion`, then sorts the whole array, in which every word lies within `M`
positions of its final place. -/

namespace Library.Sorting.Quicksort

open Library.Sorting.Heapsort (swap)
open Library.Sorting.StraightInsertion (straightInsertion)

theorem succ_toNat {i e : UInt64} (h : i < e) : (i + 1).toNat = i.toNat + 1 := by
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_add, UInt64.reduceToNat]
  have := UInt64.toNat_lt e
  omega

theorem pred_toNat {l j : UInt64} (h : l < j) : (j - 1).toNat = j.toNat - 1 := by
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt j
  omega

/-- Step Q3: from `i`, the first position below `e` whose word is not below `K`, or `e`.  Knuth's
sentinel `K_{N+1} = ∞` stops the scan at the end of the file, and the program tests `i < e`. -/
def scanUp (K e i : UInt64) (a : Array UInt64) : UInt64 :=
  if i < e then (if a[i.toNat]! < K then scanUp K e (i + 1) a else i) else i
termination_by (e - i).toNat
decreasing_by
  have h : i < e := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
  have := UInt64.toNat_lt e
  omega

/-- Step Q4: from `j`, the last position above `l` whose word is not above `K`, or `l`, where the
word `K` itself stops the scan. -/
def scanDown (K l j : UInt64) (a : Array UInt64) : UInt64 :=
  if l < j then (if K < a[j.toNat]! then scanDown K l (j - 1) a else j) else j
termination_by j.toNat
decreasing_by
  have h : l < j := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt j
  omega

theorem scanUp_ge (K e : UInt64) (a : Array UInt64) (i : UInt64) :
    i.toNat ≤ (scanUp K e i a).toNat := by
  rw [scanUp]
  split
  · rename_i h
    split
    · have := scanUp_ge K e a (i + 1)
      rw [succ_toNat h] at this
      omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _
termination_by (e - i).toNat
decreasing_by
  have h : i < e := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
  have := UInt64.toNat_lt e
  omega

theorem scanDown_bounds (K l : UInt64) (a : Array UInt64) (j : UInt64) :
    (scanDown K l j a).toNat ≤ j.toNat ∧
      (l ≤ j → l.toNat ≤ (scanDown K l j a).toNat) := by
  rw [scanDown]
  split
  · rename_i h
    split
    · have := scanDown_bounds K l a (j - 1)
      rw [pred_toNat h] at this
      have hl : l ≤ j - 1 := by
        rw [UInt64.le_iff_toNat_le, pred_toNat h]; rw [UInt64.lt_iff_toNat_lt] at h; omega
      exact ⟨by omega, fun _ => this.2 hl⟩
    · exact ⟨Nat.le_refl _, fun h' => UInt64.le_iff_toNat_le.mp h'⟩
  · exact ⟨Nat.le_refl _, fun h' => UInt64.le_iff_toNat_le.mp h'⟩
termination_by j.toNat
decreasing_by
  have h : l < j := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt j
  omega

/-- Steps Q3 to Q6 on the subfile with first position `l` and end `e`, from the positions `i` and
`j`: while the scans of steps Q3 and Q4 from `i + 1` and `j - 1` have not crossed, step Q6
exchanges the words where they stop, and when they cross, step Q5 exchanges the first word `K`
with the word where step Q4 stopped, its final position, which the result returns with the
array. -/
def part (K l e i j : UInt64) (a : Array UInt64) : UInt64 × Array UInt64 :=
  if i < j then
    if scanUp K e (i + 1) a < scanDown K l (j - 1) a then
      part K l e (scanUp K e (i + 1) a) (scanDown K l (j - 1) a)
        (swap (scanUp K e (i + 1) a) (scanDown K l (j - 1) a) a)
    else (scanDown K l (j - 1) a, swap l (scanDown K l (j - 1) a) a)
  else (j, a)
termination_by (j - i).toNat
decreasing_by
  have h1 : i < j := by assumption
  have h4 : scanUp K e (i + 1) a < scanDown K l (j - 1) a := by assumption
  have h2 := scanUp_ge K e a (i + 1)
  have h3 := (scanDown_bounds K l a (j - 1)).1
  rw [succ_toNat h1] at h2
  rw [pred_toNat h1] at h3
  simp only [UInt64.lt_iff_toNat_lt] at h1 h4
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt j
  omega

theorem part_fst (K l e : UInt64) (a : Array UInt64) (i j : UInt64) (hl : l ≤ i) (hij : i < j) :
    l.toNat ≤ (part K l e i j a).1.toNat ∧ (part K l e i j a).1.toNat < j.toNat := by
  rw [part, ite_eq_left hij]
  have hlj : l ≤ j - 1 := by
    rw [UInt64.le_iff_toNat_le, pred_toNat hij]; rw [UInt64.le_iff_toNat_le] at hl
    rw [UInt64.lt_iff_toNat_lt] at hij; omega
  have hd := scanDown_bounds K l a (j - 1)
  rw [pred_toNat hij] at hd
  have hj := UInt64.lt_iff_toNat_lt.mp hij
  split
  · rename_i h4
    have hu := scanUp_ge K e a (i + 1)
    rw [succ_toNat hij] at hu
    have hl' : l ≤ scanUp K e (i + 1) a := by
      rw [UInt64.le_iff_toNat_le]; rw [UInt64.le_iff_toNat_le] at hl; omega
    have := part_fst K l e (swap (scanUp K e (i + 1) a) (scanDown K l (j - 1) a) a) _ _ hl' h4
    have h5 := UInt64.lt_iff_toNat_lt.mp h4
    exact ⟨this.1, by omega⟩
  · dsimp only
    exact ⟨hd.2 hlj, by omega⟩
termination_by (j - i).toNat
decreasing_by
  have h4 : scanUp K e (i + 1) a < scanDown K l (j - 1) a := by assumption
  have h2 := scanUp_ge K e a (i + 1)
  have h3 := (scanDown_bounds K l a (j - 1)).1
  rw [succ_toNat hij] at h2
  rw [pred_toNat hij] at h3
  have h5 := UInt64.lt_iff_toNat_lt.mp h4
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt j
  have := UInt64.lt_iff_toNat_lt.mp hij
  omega

/-- The number of words of `[l, e)`, and 0 when `e ≤ l`. -/
def span (l e : UInt64) : Nat := if l ≤ e then (e - l).toNat else 0

/-- The sizes of the first `n` subfiles of the stack `st`, whose entry `k` is
`[st[2k], st[2k+1])`. -/
def stacked (st : Array UInt64) : Nat → Nat
  | 0 => 0
  | k + 1 => stacked st k + span st[2 * k]! st[2 * k + 1]!

theorem span_eq {l e : UInt64} (h : l ≤ e) : span l e = e.toNat - l.toNat := by
  rw [span, ite_eq_left h, UInt64.toNat_sub_of_le _ _ h]

theorem get_set_ne (st : Array UInt64) (i m : Nat) (v : UInt64) (h : m ≠ i) :
    (st.set! i v)[m]! = st[m]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hm : m < st.size
  · rw [getElem!_pos _ m (by simpa using hm), Array.getElem_setIfInBounds hm,
      ite_eq_right (Ne.symm h), getElem!_pos st m hm]
  · rw [getElem!_neg _ m (by simpa using hm), getElem!_neg st m hm]

theorem stacked_set (st : Array UInt64) (i : Nat) (v : UInt64) :
    ∀ k, 2 * k ≤ i → stacked (st.set! i v) k = stacked st k
  | 0, _ => rfl
  | k + 1, h => by
    rw [stacked, stacked, stacked_set st i v k (by omega), get_set_ne _ _ _ _ (by omega),
      get_set_ne _ _ _ _ (by omega)]

theorem get_set_self (st : Array UInt64) (i : Nat) (v : UInt64) (h : i < st.size) :
    (st.set! i v)[i]! = v := by
  simp only [Array.set!_eq_setIfInBounds]
  rw [getElem!_pos _ i (by simpa using h), Array.getElem_setIfInBounds h, ite_eq_left rfl]

/-- A push adds at most the size of the pushed subfile, and exactly that size when the stack has
room for it. -/
theorem stacked_push (st : Array UInt64) (sp lo hi : UInt64) (hsp : sp.toNat < 64) :
    stacked ((st.set! (2 * sp).toNat lo).set! (2 * sp + 1).toNat hi) (sp + 1).toNat ≤
      stacked st sp.toNat + span lo hi := by
  have h2 : (2 * sp).toNat = 2 * sp.toNat := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]; omega
  have h21 : (2 * sp + 1).toNat = 2 * sp.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  have hs1 : (sp + 1).toNat = sp.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  rw [h2, h21, hs1, stacked, stacked_set _ _ _ _ (by omega), stacked_set _ _ _ _ (by omega)]
  apply Nat.add_le_add_left
  by_cases h1 : 2 * sp.toNat + 1 < st.size
  · rw [get_set_self _ _ _ (by rw [Array.size_set!]; exact h1), get_set_ne _ _ _ _ (by omega),
      get_set_self _ _ _ (by omega)]
    exact Nat.le_refl _
  · have h0 : ((st.set! (2 * sp.toNat) lo).set! (2 * sp.toNat + 1) hi)[2 * sp.toNat + 1]! = 0 := by
      rw [getElem!_neg _ _ (by simp; omega)]; rfl
    rw [h0]
    unfold span
    split
    · rename_i hle
      have hx : ((st.set! (2 * sp.toNat) lo).set! (2 * sp.toNat + 1) hi)[2 * sp.toNat]! = 0 :=
        UInt64.toNat_inj.mp (by rw [UInt64.le_iff_toNat_le] at hle; simp at hle ⊢; omega)
      rw [hx]
      exact Nat.zero_le _
    · exact Nat.zero_le _

theorem dec_left (l e j : UInt64) (S sp : Nat) (hc : l < e)
    (hj : l.toNat ≤ j.toNat ∧ j.toNat < e.toNat) :
    2 * (span l j + S) + sp < 2 * (span l e + S) + sp := by
  have he := UInt64.lt_iff_toNat_lt.mp hc
  rw [span_eq (UInt64.le_iff_toNat_le.mpr hj.1), span_eq (UInt64.le_iff_toNat_le.mpr (by omega))]
  omega

theorem dec_right (l e j : UInt64) (S sp : Nat) (hc : l < e)
    (hj : l.toNat ≤ j.toNat ∧ j.toNat < e.toNat) :
    2 * (span (j + 1) e + S) + sp < 2 * (span l e + S) + sp := by
  have he := UInt64.lt_iff_toNat_lt.mp hc
  have hj1 : (j + 1).toNat = j.toNat + 1 := succ_toNat (UInt64.lt_iff_toNat_lt.mpr hj.2)
  rw [span_eq (UInt64.le_iff_toNat_le.mpr (by omega)),
    span_eq (UInt64.le_iff_toNat_le.mpr (by omega)), hj1]
  omega

theorem dec_push_left (l e j sp : UInt64) (st : Array UInt64) (hc : l < e)
    (hj : l.toNat ≤ j.toNat ∧ j.toNat < e.toNat) (hsp : sp < 64) :
    2 * (span l j + stacked ((st.set! (2 * sp).toNat (j + 1)).set! (2 * sp + 1).toNat e)
        (sp + 1).toNat) + (sp + 1).toNat < 2 * (span l e + stacked st sp.toNat) + sp.toNat := by
  have h64 := UInt64.lt_iff_toNat_lt.mp hsp
  simp only [UInt64.reduceToNat] at h64
  have hp := stacked_push st sp (j + 1) e h64
  have he := UInt64.lt_iff_toNat_lt.mp hc
  have hj1 : (j + 1).toNat = j.toNat + 1 := succ_toNat (UInt64.lt_iff_toNat_lt.mpr hj.2)
  have hs1 : (sp + 1).toNat = sp.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  rw [span_eq (UInt64.le_iff_toNat_le.mpr (by omega)), hj1] at hp
  rw [span_eq (UInt64.le_iff_toNat_le.mpr hj.1), span_eq (UInt64.le_iff_toNat_le.mpr (by omega))]
  omega

theorem dec_push_right (l e j sp : UInt64) (st : Array UInt64) (hc : l < e)
    (hj : l.toNat ≤ j.toNat ∧ j.toNat < e.toNat) (hsp : sp < 64) :
    2 * (span (j + 1) e + stacked ((st.set! (2 * sp).toNat l).set! (2 * sp + 1).toNat j)
        (sp + 1).toNat) + (sp + 1).toNat < 2 * (span l e + stacked st sp.toNat) + sp.toNat := by
  have h64 := UInt64.lt_iff_toNat_lt.mp hsp
  simp only [UInt64.reduceToNat] at h64
  have hp := stacked_push st sp l j h64
  have he := UInt64.lt_iff_toNat_lt.mp hc
  have hj1 : (j + 1).toNat = j.toNat + 1 := succ_toNat (UInt64.lt_iff_toNat_lt.mpr hj.2)
  have hs1 : (sp + 1).toNat = sp.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  rw [span_eq (UInt64.le_iff_toNat_le.mpr hj.1)] at hp
  rw [span_eq (UInt64.le_iff_toNat_le.mpr (by omega)),
    span_eq (UInt64.le_iff_toNat_le.mpr (by omega)), hj1]
  omega

/-- A pop removes the size of the subfile on top of the stack. -/
theorem dec_pop (l e sp : UInt64) (st : Array UInt64) (h : 0 < sp ∧ sp ≤ 64) :
    2 * (span st[(2 * (sp - 1)).toNat]! st[(2 * (sp - 1) + 1).toNat]! + stacked st (sp - 1).toNat) +
      (sp - 1).toNat < 2 * (span l e + stacked st sp.toNat) + sp.toNat := by
  have h0 := UInt64.lt_iff_toNat_lt.mp h.1
  have h64 := UInt64.le_iff_toNat_le.mp h.2
  simp only [UInt64.reduceToNat] at h0 h64
  have hs : (sp - 1).toNat = sp.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have h2 : (2 * (sp - 1)).toNat = 2 * (sp.toNat - 1) := by
    simp only [UInt64.toNat_mul, hs, UInt64.reduceToNat]; omega
  have h21 : (2 * (sp - 1) + 1).toNat = 2 * (sp.toNat - 1) + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hs, UInt64.reduceToNat]; omega
  obtain ⟨k, hk⟩ : ∃ k, sp.toNat = k + 1 := ⟨sp.toNat - 1, by omega⟩
  rw [h2, h21, hs, hk, Nat.add_sub_cancel, stacked]
  omega

/-- Steps Q2 to Q8 with the current subfile `[l, e)`, the stack `st` of `sp` pending subfiles, and
the array.  A subfile of more than `M = 9` words is partitioned around its first word.  When both
parts exceed `M` and the stack has room, step Q7 pushes the larger part and continues with the
smaller.  Otherwise it continues with the larger part, which is the one part that exceeds `M` when
only one does, and which step Q8 replaces at the next stage when neither does.  Step Q8 takes the
subfile on top of the stack when the current one has at most `M` words, and the loop ends when the
stack is empty.  Knuth's stack never holds more than `lg N` entries, so a stack of 64 entries
covers every array in memory, and a part that a full stack could not take would stay for step
Q9. -/
def stages (l e sp : UInt64) (st a : Array UInt64) : Array UInt64 :=
  if l < e ∧ 9 < e - l then
    let r := part a[l.toNat]! l e l e a
    if 9 < r.1 - l ∧ 9 < e - (r.1 + 1) ∧ sp < 64 then
      if r.1 - l ≤ e - (r.1 + 1) then
        stages l r.1 (sp + 1) ((st.set! (2 * sp).toNat (r.1 + 1)).set! (2 * sp + 1).toNat e) r.2
      else stages (r.1 + 1) e (sp + 1) ((st.set! (2 * sp).toNat l).set! (2 * sp + 1).toNat r.1) r.2
    else if r.1 - l ≤ e - (r.1 + 1) then stages (r.1 + 1) e sp st r.2
    else stages l r.1 sp st r.2
  else if 0 < sp ∧ sp ≤ 64 then
    stages st[(2 * (sp - 1)).toNat]! st[(2 * (sp - 1) + 1).toNat]! (sp - 1) st a
  else a
termination_by 2 * (span l e + stacked st sp.toNat) + sp.toNat
decreasing_by
  all_goals try simp only [r] at *
  · obtain ⟨hc, -⟩ : l < e ∧ 9 < e - l := by assumption
    obtain ⟨-, -, hsp⟩ : 9 < (part a[l.toNat]! l e l e a).1 - l ∧
        9 < e - ((part a[l.toNat]! l e l e a).1 + 1) ∧ sp < 64 := by assumption
    exact dec_push_left l e _ sp st hc
      (part_fst _ l e a l e (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hc) hsp
  · obtain ⟨hc, -⟩ : l < e ∧ 9 < e - l := by assumption
    obtain ⟨-, -, hsp⟩ : 9 < (part a[l.toNat]! l e l e a).1 - l ∧
        9 < e - ((part a[l.toNat]! l e l e a).1 + 1) ∧ sp < 64 := by assumption
    exact dec_push_right l e _ sp st hc
      (part_fst _ l e a l e (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hc) hsp
  · obtain ⟨hc, -⟩ : l < e ∧ 9 < e - l := by assumption
    exact dec_right l e _ _ _ hc
      (part_fst _ l e a l e (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hc)
  · obtain ⟨hc, -⟩ : l < e ∧ 9 < e - l := by assumption
    exact dec_left l e _ _ _ hc
      (part_fst _ l e a l e (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hc)
  · exact dec_pop l e sp st (by assumption)

/-- Algorithm Q: steps Q1 to Q8 with an empty stack of 64 entries, then step Q9, straight
insertion over the whole array. -/
def quicksort (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  straightInsertion (stages 0 n 0 (LeanExe.build 128 fun _ => 0) xs)

end Library.Sorting.Quicksort
