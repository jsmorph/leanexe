import Library.Sorting.RadixSort.Program
import Library.Sorting.RadixSort.Spec
import Library.Sorting.Sorted
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Card

/-! The proof that `radixSort` returns the array's elements in nondecreasing order.  A pass on the
byte at bit `s` puts the word at position `j` at `pos s src j`, the number of words with a smaller
byte plus the number of words before `j` with the same byte.  These positions are distinct and
below the size, so the pass permutes the array, and two words with the same byte keep their order,
so the pass is stable.  After the passes on the low `k` bytes, the words are in nondecreasing order
of their values modulo `2^(8k)`, and after eight passes in nondecreasing order. -/

namespace Library.Sorting.RadixSort

open LeanExe.Dialect

theorem digit_lt (s x : UInt64) : (digit s x).toNat < 256 := by
  unfold digit
  rw [UInt64.toNat_and]
  have := Nat.and_le_right (n := (x >>> s).toNat) (m := (255 : UInt64).toNat)
  simp only [UInt64.reduceToNat] at this ⊢
  omega

theorem digit_eq (s x : UInt64) (k : Nat) (hk : k < 8) (hs : s.toNat = 8 * k) :
    (digit s x).toNat = x.toNat / 2 ^ (8 * k) % 256 := by
  unfold digit
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs, Nat.mod_eq_of_lt (show 8 * k < 64 by omega),
    Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem countP_le_eq (s : UInt64) (v : Nat) : ∀ L : List UInt64,
    L.countP (fun x => decide ((digit s x).toNat ≤ v)) =
      L.countP (fun x => decide ((digit s x).toNat < v)) +
        L.countP (fun x => decide ((digit s x).toNat = v))
  | [] => rfl
  | x :: L => by
    simp only [List.countP_cons, decide_eq_true_eq, countP_le_eq s v L]
    split_ifs <;> omega

theorem countP_take_succ (p : UInt64 → Bool) (src : Array UInt64) (j : Nat) (hj : j < src.size) :
    (src.toList.take (j + 1)).countP p =
      (src.toList.take j).countP p + if p src[j]! then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj), List.countP_append]
  simp [getElem!_pos src j hj]

/-! ### Steps D1 to D4 -/

theorem zero_loop (count : Array UInt64) (hc : count.size = 256) :
    (LeanExe.loop 256 count fun v c => c.set! v.toNat 0).size = 256 ∧
      ∀ v, v < 256 → (LeanExe.loop 256 count fun v c => c.set! v.toNat 0)[v]! = 0 := by
  obtain ⟨h1, h2⟩ := loop_induction (n := 256) (init := count) (f := fun v c => c.set! v.toNat 0)
    (fun k (c : Array UInt64) => c.size = 256 ∧ ∀ v, v < k → c[v]! = 0)
    ⟨hc, fun v hv => absurd hv (Nat.not_lt_zero _)⟩ (by
      intro k c hk ⟨c1, c2⟩
      have hk2 : k < 256 := by simpa using hk
      have hk' : (UInt64.ofNat k).toNat = k :=
        UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
      refine ⟨by rw [Array.size_set!]; exact c1, fun v hv => ?_⟩
      rw [hk', get_set c k 0 v (by omega)]
      by_cases e : v = k
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact c2 v (by omega))
  exact ⟨h1, fun v hv => h2 v (by simpa using hv)⟩

theorem count_loop (s : UInt64) (src c0 : Array UInt64) (hs : c0.size = 256)
    (hz : ∀ v, v < 256 → c0[v]! = 0) (hn : src.size < 2 ^ 64) :
    (LeanExe.loop src.size.toUInt64 c0 fun j c =>
        let d := digit s src[j.toNat]!
        c.set! d.toNat (c[d.toNat]! + 1)).size = 256 ∧
      ∀ v, v < 256 → (LeanExe.loop src.size.toUInt64 c0 fun j c =>
        let d := digit s src[j.toNat]!
        c.set! d.toNat (c[d.toNat]! + 1))[v]!.toNat =
          src.toList.countP (fun x => decide ((digit s x).toNat = v)) := by
  have hN : src.size.toUInt64.toNat = src.size := size_toUInt64 src hn
  obtain ⟨h1, h2⟩ := loop_induction (n := src.size.toUInt64) (init := c0)
    (f := fun j c =>
      let d := digit s src[j.toNat]!
      c.set! d.toNat (c[d.toNat]! + 1))
    (fun k (c : Array UInt64) => c.size = 256 ∧ ∀ v, v < 256 →
      c[v]!.toNat = (src.toList.take k).countP (fun x => decide ((digit s x).toNat = v)))
    ⟨hs, fun v hv => by rw [hz v hv]; simp⟩ (by
      intro j c hj ⟨c1, c2⟩
      rw [hN] at hj
      have hj' : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega)
      simp only [hj']
      have hd := digit_lt s src[j]!
      have hle : (src.toList.take j).countP
          (fun x => decide ((digit s x).toNat = (digit s src[j]!).toNat)) ≤ j :=
        le_trans List.countP_le_length (by simp)
      refine ⟨by rw [Array.size_set!]; exact c1, fun v hv => ?_⟩
      rw [get_set c _ _ v (by rw [c1]; exact hd), countP_take_succ _ src j hj]
      by_cases e : v = (digit s src[j]!).toNat
      · subst e
        rw [ite_eq_left rfl, UInt64.toNat_add, c2 _ hd]
        simp only [decide_true, ite_true, UInt64.reduceToNat]
        omega
      · rw [ite_eq_right e, c2 v hv]
        simp only [decide_eq_true_eq]
        rw [ite_eq_right (fun h => e h.symm), Nat.add_zero])
  rw [hN, List.take_of_length_le (by simp)] at h2
  exact ⟨h1, h2⟩

theorem prefix_loop (s : UInt64) (L : List UInt64) (hL : L.length < 2 ^ 64) (c0 : Array UInt64)
    (hs : c0.size = 256)
    (h0 : ∀ v, v < 256 → c0[v]!.toNat = L.countP (fun x => decide ((digit s x).toNat = v))) :
    (LeanExe.loop 255 c0 fun v c =>
        c.set! (v + 1).toNat (c[(v + 1).toNat]! + c[v.toNat]!)).size = 256 ∧
      ∀ v, v < 256 → (LeanExe.loop 255 c0 fun v c =>
        c.set! (v + 1).toNat (c[(v + 1).toNat]! + c[v.toNat]!))[v]!.toNat =
          L.countP (fun x => decide ((digit s x).toNat ≤ v)) := by
  obtain ⟨h1, h2⟩ := loop_induction (n := 255) (init := c0)
    (f := fun v c => c.set! (v + 1).toNat (c[(v + 1).toNat]! + c[v.toNat]!))
    (fun i (c : Array UInt64) => c.size = 256 ∧ ∀ v, v < 256 →
      c[v]!.toNat = if v ≤ i then L.countP (fun x => decide ((digit s x).toNat ≤ v))
        else L.countP (fun x => decide ((digit s x).toNat = v)))
    ⟨hs, fun v hv => by
      rw [h0 v hv]
      split_ifs with h
      · congr 1; funext x; exact decide_eq_decide.mpr (by omega)
      · rfl⟩
    (by
      intro i c hi ⟨c1, c2⟩
      have hi2 : i < 255 := by simpa using hi
      have e1 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
      have e2 : (UInt64.ofNat i + 1).toNat = i + 1 := by
        rw [UInt64.toNat_add, e1]; simp only [UInt64.reduceToNat]; omega
      rw [e1, e2]
      refine ⟨by rw [Array.size_set!]; exact c1, fun v hv => ?_⟩
      rw [get_set c _ _ v (by omega)]
      by_cases e : v = i + 1
      · subst e
        rw [ite_eq_left (show i + 1 = i + 1 from rfl), UInt64.toNat_add, c2 (i + 1) hv,
          c2 i (by omega), ite_eq_right (show ¬i + 1 ≤ i by omega),
          ite_eq_left (show i ≤ i from le_refl i), ite_eq_left (show i + 1 ≤ i + 1 from le_refl _)]
        have h3 := countP_le_eq s (i + 1) L
        have h4 : L.countP (fun x => decide ((digit s x).toNat < i + 1)) =
            L.countP (fun x => decide ((digit s x).toNat ≤ i)) := by
          congr 1; funext x; exact decide_eq_decide.mpr (by omega)
        have hlen := List.countP_le_length (p := fun x => decide ((digit s x).toNat ≤ i + 1))
          (l := L)
        omega
      · rw [ite_eq_right e, c2 v hv]
        by_cases h : v ≤ i
        · rw [ite_eq_left h, ite_eq_left (show v ≤ i + 1 by omega)]
        · rw [ite_eq_right h, ite_eq_right (show ¬v ≤ i + 1 by omega)])
  refine ⟨h1, fun v hv => ?_⟩
  rw [h2 v hv]
  exact ite_eq_left (by simp only [UInt64.reduceToNat]; omega)

/-- Steps D1 to D4: `count[v]` is the number of words whose byte is at most `v`. -/
theorem countDigits_spec (s : UInt64) (src count : Array UInt64) (hc : count.size = 256)
    (hn : src.size < 2 ^ 64) :
    (countDigits s src count).size = 256 ∧ ∀ v, v < 256 →
      (countDigits s src count)[v]!.toNat =
        src.toList.countP (fun x => decide ((digit s x).toNat ≤ v)) := by
  obtain ⟨z1, z2⟩ := zero_loop count hc
  obtain ⟨q1, q2⟩ := count_loop s src _ z1 z2 hn
  exact prefix_loop s src.toList (by simpa using hn) _ q1 q2

/-! ### Steps D5 and D6 -/

/-- The position of the word at `j` after the pass on the byte at bit `s`. -/
def pos (s : UInt64) (src : Array UInt64) (j : Nat) : Nat :=
  src.toList.countP (fun x => decide ((digit s x).toNat < (digit s src[j]!).toNat)) +
    (src.toList.take j).countP (fun x => decide ((digit s x).toNat = (digit s src[j]!).toNat))

/-- The words before `j` with the byte of `src[j]` are fewer than all the words with that byte. -/
theorem countP_take_lt (s : UInt64) (src : Array UInt64) (j : Nat) (hj : j < src.size) :
    (src.toList.take j).countP (fun x => decide ((digit s x).toNat = (digit s src[j]!).toNat)) <
      src.toList.countP (fun x => decide ((digit s x).toNat = (digit s src[j]!).toNat)) := by
  have h1 := countP_take_succ (fun x => decide ((digit s x).toNat = (digit s src[j]!).toNat))
    src j hj
  have h2 := (List.take_sublist (j + 1) src.toList).countP_le
    (p := fun x => decide ((digit s x).toNat = (digit s src[j]!).toNat))
  simp only [decide_true, ite_true] at h1
  omega

theorem pos_lt_le (s : UInt64) (src : Array UInt64) (j : Nat) (hj : j < src.size) :
    pos s src j < src.toList.countP (fun x => decide ((digit s x).toNat ≤ (digit s src[j]!).toNat))
    := by
  unfold pos
  rw [countP_le_eq]
  have := countP_take_lt s src j hj
  omega

theorem pos_lt (s : UInt64) (src : Array UInt64) (j : Nat) (hj : j < src.size) :
    pos s src j < src.size := by
  have h := pos_lt_le s src j hj
  have := List.countP_le_length
    (p := fun x => decide ((digit s x).toNat ≤ (digit s src[j]!).toNat)) (l := src.toList)
  simp only [Array.length_toList] at this
  omega

/-- A word with a smaller byte is written to an earlier position. -/
theorem pos_lt_of_digit_lt (s : UInt64) (src : Array UInt64) (j j' : Nat) (hj : j < src.size)
    (h : (digit s src[j]!).toNat < (digit s src[j']!).toNat) : pos s src j < pos s src j' := by
  have h1 := pos_lt_le s src j hj
  have h2 : src.toList.countP (fun x => decide ((digit s x).toNat ≤ (digit s src[j]!).toNat)) ≤
      src.toList.countP (fun x => decide ((digit s x).toNat < (digit s src[j']!).toNat)) :=
    List.countP_mono_left fun x _ hx => by simp only [decide_eq_true_eq] at hx ⊢; omega
  unfold pos at h1 ⊢
  omega

/-- Of two words with the same byte, the earlier is written to the earlier position. -/
theorem pos_lt_of_lt (s : UInt64) (src : Array UInt64) (j j' : Nat) (hj' : j' < src.size)
    (hjj : j < j') (h : (digit s src[j]!).toNat = (digit s src[j']!).toNat) :
    pos s src j < pos s src j' := by
  unfold pos
  rw [h]
  have h1 := countP_take_succ (fun x => decide ((digit s x).toNat = (digit s src[j']!).toNat))
    src j (by omega)
  have h2 : (src.toList.take (j + 1)).Sublist (src.toList.take j') := by
    rw [show src.toList.take (j + 1) = (src.toList.take j').take (j + 1) by
      rw [List.take_take]; congr 1; omega]
    exact List.take_sublist _ _
  have h3 := h2.countP_le (p := fun x => decide ((digit s x).toNat = (digit s src[j']!).toNat))
  simp only [h, decide_true, ite_true] at h1
  omega

theorem pos_injective (s : UInt64) (src : Array UInt64) (j j' : Nat) (hj : j < src.size)
    (hj' : j' < src.size) (h : pos s src j = pos s src j') : j = j' := by
  rcases Nat.lt_trichotomy (digit s src[j]!).toNat (digit s src[j']!).toNat with d | d | d
  · exact absurd h (Nat.ne_of_lt (pos_lt_of_digit_lt s src j j' hj d))
  · rcases Nat.lt_trichotomy j j' with c | c | c
    · exact absurd h (Nat.ne_of_lt (pos_lt_of_lt s src j j' hj' c d))
    · exact c
    · exact absurd h.symm (Nat.ne_of_lt (pos_lt_of_lt s src j' j hj c d.symm))
  · exact absurd h.symm (Nat.ne_of_lt (pos_lt_of_digit_lt s src j' j hj' d))

/-- Steps D5 and D6 put the word at `j` at `pos s src j`. -/
theorem distribute_spec (s : UInt64) (src dst count : Array UInt64) (hn : src.size < 2 ^ 64)
    (hd : dst.size = src.size) (hc : count.size = 256)
    (hcount : ∀ v, v < 256 →
      count[v]!.toNat = src.toList.countP (fun x => decide ((digit s x).toNat ≤ v))) :
    (distribute s src dst count).1.size = src.size ∧ (distribute s src dst count).2.size = 256 ∧
      ∀ j, j < src.size → (distribute s src dst count).1[pos s src j]! = src[j]! := by
  have hN : src.size.toUInt64.toNat = src.size := size_toUInt64 src hn
  obtain ⟨h1, h2, _, h4⟩ := loop_induction (n := src.size.toUInt64) (init := (dst, count))
    (f := fun k st =>
      let x := src[(src.size.toUInt64 - 1 - k).toNat]!
      let d := digit s x
      let i := st.2[d.toNat]! - 1
      (st.1.set! i.toNat x, st.2.set! d.toNat i))
    (fun k (st : Array UInt64 × Array UInt64) => st.1.size = src.size ∧ st.2.size = 256 ∧
      (∀ v, v < 256 → st.2[v]!.toNat =
        src.toList.countP (fun x => decide ((digit s x).toNat < v)) +
          (src.toList.take (src.size - k)).countP (fun x => decide ((digit s x).toNat = v))) ∧
      ∀ j, src.size - k ≤ j → j < src.size → st.1[pos s src j]! = src[j]!)
    ⟨hd, hc, fun v hv => by
      rw [hcount v hv, Nat.sub_zero, List.take_of_length_le (by simp), countP_le_eq],
      fun j hj hj' => by omega⟩
    (by
      intro k st hk ⟨c1, c2, c3, c4⟩
      rw [hN] at hk
      have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
      have hj : (src.size.toUInt64 - 1 - UInt64.ofNat k).toNat = src.size - 1 - k := by
        simp only [UInt64.toNat_sub, hN, hk', UInt64.reduceToNat]
        omega
      simp only [hj]
      generalize hjdef : src.size - 1 - k = j
      have hjlt : j < src.size := by omega
      have hsk : src.size - k = j + 1 := by omega
      have hsk1 : src.size - (k + 1) = j := by omega
      have hd := digit_lt s src[j]!
      have hval := c3 _ hd
      rw [hsk, countP_take_succ _ src j hjlt] at hval
      simp only [decide_true, ite_true] at hval
      have hpos : (st.2[(digit s src[j]!).toNat]! - 1).toNat = pos s src j := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          simp only [UInt64.reduceToNat]; omega)), hval]
        simp only [UInt64.reduceToNat]
        unfold pos
        omega
      rw [hpos]
      have hplt := pos_lt s src j hjlt
      refine ⟨by rw [Array.size_set!]; exact c1, by rw [Array.size_set!]; exact c2,
        fun v hv => ?_, fun j' hj1 hj2 => ?_⟩
      · rw [get_set _ _ _ v (by rw [c2]; exact hd), hsk1]
        by_cases e : v = (digit s src[j]!).toNat
        · subst e
          rw [ite_eq_left rfl, hpos]
          rfl
        · rw [ite_eq_right e, c3 v hv, hsk, countP_take_succ _ src j hjlt]
          simp only [decide_eq_true_eq]
          rw [ite_eq_right (fun h => e h.symm), Nat.add_zero]
      · rw [get_set _ _ _ _ (by rw [c1]; exact hplt)]
        rw [hsk1] at hj1
        by_cases e : j' = j
        · subst e
          rw [ite_eq_left rfl]
        · rw [ite_eq_right (fun h => e (pos_injective s src j' j hj2 hjlt h))]
          exact c4 j' (by omega) hj2)
  rw [hN] at h4
  exact ⟨h1, h2, fun j hj => h4 j (by omega) hj⟩

/-! ### One pass -/

/-- A pass permutes the words, and when a relation `R` holds between the words of the input in
order, the output is in nondecreasing order of the byte, with `R` between words of the same byte. -/
theorem pass_spec (s : UInt64) (src dst count : Array UInt64) (hn : src.size < 2 ^ 64)
    (hd : dst.size = src.size) (hc : count.size = 256) :
    (distribute s src dst (countDigits s src count)).1.size = src.size ∧
      (distribute s src dst (countDigits s src count)).2.size = 256 ∧
      (distribute s src dst (countDigits s src count)).1.toList.Perm src.toList ∧
      ∀ R : UInt64 → UInt64 → Prop, src.toList.Pairwise R →
        (distribute s src dst (countDigits s src count)).1.toList.Pairwise fun a b =>
          (digit s a).toNat < (digit s b).toNat ∨
            ((digit s a).toNat = (digit s b).toNat ∧ R a b) := by
  obtain ⟨k1, k2⟩ := countDigits_spec s src count hc hn
  obtain ⟨d1, d2, d3⟩ := distribute_spec s src dst _ hn hd k1 k2
  generalize distribute s src dst (countDigits s src count) = r at d1 d2 d3 ⊢
  set out := r.1
  let σ : Fin src.size → Fin src.size := fun j => ⟨pos s src j, pos_lt s src j j.isLt⟩
  have hinj : Function.Injective σ := fun a b h =>
    Fin.ext (pos_injective s src a b a.isLt b.isLt (congrArg Fin.val h))
  have hbij := Finite.injective_iff_bijective.mp hinj
  let e : Equiv.Perm (Fin src.size) := Equiv.ofBijective σ hbij
  have hsrc : src.toList = List.ofFn (fun j : Fin src.size => src[j.val]!) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_ofFn, Array.getElem_toList]
    rw [getElem!_pos src i (by simpa using h1)]
  have hout : out.toList = List.ofFn (fun p : Fin src.size => out[p.val]!) := by
    apply List.ext_getElem (by simp [d1])
    intro i h1 h2
    simp only [List.getElem_ofFn, Array.getElem_toList]
    rw [getElem!_pos out i (by simpa using h1)]
  have hcomp : (fun j : Fin src.size => src[j.val]!) =
      (fun p : Fin src.size => out[p.val]!) ∘ e := by
    funext j
    exact (d3 j j.isLt).symm
  refine ⟨d1, d2, ?_, fun R hR => ?_⟩
  · rw [hout, hsrc, hcomp]
    exact (Equiv.Perm.ofFn_comp_perm e _).symm
  · have hsurj : ∀ p, p < src.size → ∃ j, j < src.size ∧ pos s src j = p := by
      intro p hp
      obtain ⟨j, hj⟩ := hbij.2 ⟨p, hp⟩
      exact ⟨j.val, j.isLt, congrArg Fin.val hj⟩
    rw [List.pairwise_iff_getElem]
    intro p q hp hq hpq
    simp only [Array.length_toList] at hp hq
    rw [d1] at hp hq
    obtain ⟨j, hj, ep⟩ := hsurj p hp
    obtain ⟨j', hj', eq'⟩ := hsurj q hq
    simp only [Array.getElem_toList]
    rw [← getElem!_pos out p (by rw [d1]; exact hp), ← getElem!_pos out q (by rw [d1]; exact hq),
      ← ep, ← eq', d3 j hj, d3 j' hj']
    rcases Nat.lt_trichotomy (digit s src[j]!).toNat (digit s src[j']!).toNat with d | d | d
    · exact .inl d
    · refine .inr ⟨d, ?_⟩
      have hjj : j < j' := by
        rcases Nat.lt_trichotomy j j' with c | c | c
        · exact c
        · subst c
          omega
        · have := pos_lt_of_lt s src j' j hj c d.symm
          omega
      have := List.pairwise_iff_getElem.mp hR j j' (by simpa using hj) (by simpa using hj') hjj
      simpa [getElem!_pos src j hj, getElem!_pos src j' hj'] using this
    · have := pos_lt_of_digit_lt s src j' j hj' d
      omega

/-! ### The passes -/

theorem low_succ (x : UInt64) (k : Nat) :
    x.toNat % 2 ^ (8 * (k + 1)) =
      x.toNat % 2 ^ (8 * k) + 2 ^ (8 * k) * (x.toNat / 2 ^ (8 * k) % 256) := by
  rw [show 8 * (k + 1) = 8 * k + 8 by ring, pow_add, Nat.mod_mul]
  norm_num

/-- Two words in order by byte `k`, or with equal byte `k` and in order modulo `2^(8k)`, are in
order modulo `2^(8(k + 1))`. -/
theorem low_step (k : Nat) (a b : UInt64)
    (h : a.toNat / 2 ^ (8 * k) % 256 < b.toNat / 2 ^ (8 * k) % 256 ∨
      (a.toNat / 2 ^ (8 * k) % 256 = b.toNat / 2 ^ (8 * k) % 256 ∧
        a.toNat % 2 ^ (8 * k) ≤ b.toNat % 2 ^ (8 * k))) :
    a.toNat % 2 ^ (8 * (k + 1)) ≤ b.toNat % 2 ^ (8 * (k + 1)) := by
  rw [low_succ, low_succ]
  have hP : 0 < 2 ^ (8 * k) := by positivity
  have ha := Nat.mod_lt a.toNat hP
  generalize a.toNat / 2 ^ (8 * k) % 256 = da at h ⊢
  generalize b.toNat / 2 ^ (8 * k) % 256 = db at h ⊢
  generalize a.toNat % 2 ^ (8 * k) = la at h ha ⊢
  generalize b.toNat % 2 ^ (8 * k) = lb at h ⊢
  generalize 2 ^ (8 * k) = P at h hP ha ⊢
  rcases h with h | ⟨rfl, h⟩
  · have := Nat.mul_le_mul_left P (show da + 1 ≤ db by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · omega

/-- The passes from byte `k`, on words in nondecreasing order modulo `2^(8k)`, return a permutation
of the words in nondecreasing order. -/
theorem passes_spec (m : Nat) : ∀ (k : Nat) (s : UInt64) (src dst count : Array UInt64),
    8 - k = m → k ≤ 8 → s.toNat = 8 * k → src.size < 2 ^ 64 → dst.size = src.size →
    count.size = 256 →
    src.toList.Pairwise (fun a b => a.toNat % 2 ^ (8 * k) ≤ b.toNat % 2 ^ (8 * k)) →
    (passes s src dst count).toList.Perm src.toList ∧
      (passes s src dst count).toList.Pairwise (· ≤ ·) := by
  induction m with
  | zero =>
    intro k s src dst count hm hk hs hn hd hc hp
    have hk8 : k = 8 := by omega
    subst hk8
    rw [passes, ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hs]; simp)]
    refine ⟨List.Perm.refl _, hp.imp fun {a b} h => ?_⟩
    rw [UInt64.le_iff_toNat_le]
    have ha := UInt64.toNat_lt a
    have hb := UInt64.toNat_lt b
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  | succ m ih =>
    intro k s src dst count hm hk hs hn hd hc hp
    have hk8 : k < 8 := by omega
    rw [passes, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hs]; simp; omega)]
    obtain ⟨p1, p2, p3, p4⟩ := pass_spec s src dst count hn hd hc
    have hsort := p4 _ hp
    generalize distribute s src dst (countDigits s src count) = r at p1 p2 p3 hsort ⊢
    obtain ⟨out, c'⟩ := r
    simp only at p1 p2 p3 hsort ⊢
    have hs8 : (s + 8).toNat = 8 * (k + 1) := by
      simp only [UInt64.toNat_add, hs, UInt64.reduceToNat]
      omega
    have hsorted : out.toList.Pairwise
        (fun a b => a.toNat % 2 ^ (8 * (k + 1)) ≤ b.toNat % 2 ^ (8 * (k + 1))) :=
      hsort.imp fun {a b} h => low_step k a b (by
        rwa [digit_eq s a k hk8 hs, digit_eq s b k hk8 hs] at h)
    obtain ⟨q1, q2⟩ := ih (k + 1) (s + 8) out src c' (by omega) (by omega) hs8
      (by rw [p1]; exact hn) p1.symm p2 hsorted
    exact ⟨q1.trans p3, q2⟩

/-- `radixSort xs = expected xs` for every array of fewer than `2^64` words. -/
theorem radixSort_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    radixSort xs = expected xs := by
  obtain ⟨hp, hs⟩ := passes_spec 8 0 0 xs (LeanExe.build xs.size.toUInt64 fun _ => 0)
    (LeanExe.build 256 fun _ => 0) rfl (by omega) (by simp) hsize
    (by rw [build_size, size_toUInt64 xs hsize]) (by rw [build_size]; simp)
    (List.pairwise_of_forall fun a b => by simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one,
      le_refl])
  show passes 0 xs (LeanExe.build xs.size.toUInt64 fun _ => 0) (LeanExe.build 256 fun _ => 0) =
    expected xs
  unfold expected
  rw [← Library.Sorting.eq_mergeSort_of_sorted_perm hs hp, Array.toArray_toList]

end Library.Sorting.RadixSort
