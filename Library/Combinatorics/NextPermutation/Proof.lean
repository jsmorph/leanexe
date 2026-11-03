import Library.Combinatorics.NextPermutation.Program
import Library.Combinatorics.NextPermutation.Spec
import Library.Sorting.Heapsort.Proof
import Library.Sorting.Sorted

/-! The proof that `nextPerm` computes the next arrangement.  A list in nonincreasing order is
greater than or equal to each of its arrangements, and a list in nondecreasing order is less than or
equal to each.  With `j` the last ascent of the input `P ++ p :: S`, the suffix `S` is
nonincreasing, the program's result is `P ++ q :: S'`, where `q` is the least word of `S` above `p`
and `S'` holds the other words of `p :: S` in nondecreasing order, and an arrangement above the
input either has a greater word at its first difference inside `P` or starts its remainder with a
word of `S` above `p`. -/

namespace Library.Combinatorics.NextPermutation

open Library.Sorting.Heapsort (swap swap_get swap_perm wle_trans wle_of_lt wle_of_not_lt
  wle_refl)

/-! ### Lexicographic order -/

theorem lt_of_append_lt_append (P A B : List UInt64) (h : P ++ A < P ++ B) : A < B := by
  induction P with
  | nil => simpa using h
  | cons x P ih =>
    rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff] at h
    rcases h with h | ⟨_, h⟩
    · exact absurd h (UInt64.lt_irrefl x)
    · exact ih h

theorem append_lt_append (P A B : List UInt64) (h : A < B) : P ++ A < P ++ B := by
  induction P with
  | nil => simpa using h
  | cons x P ih =>
    rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff]
    exact .inr ⟨rfl, ih⟩

/-- A list above `P ++ M` has a greater word at its first difference inside `P` or continues `P`
with a list above `M`. -/
theorem lt_split (P M Z : List UInt64) (h : P ++ M < Z) :
    (∃ P1 x P2 y Z2, P = P1 ++ x :: P2 ∧ Z = P1 ++ y :: Z2 ∧ x < y) ∨
      ∃ Z', Z = P ++ Z' ∧ M < Z' := by
  induction P generalizing Z with
  | nil => exact .inr ⟨Z, by simp, by simpa using h⟩
  | cons x P ih =>
    cases Z with
    | nil => exact absurd h (List.not_lt_nil _)
    | cons y Z1 =>
      rw [List.cons_append, List.cons_lt_cons_iff] at h
      rcases h with h | ⟨rfl, h⟩
      · exact .inl ⟨[], x, P, y, Z1, rfl, rfl, h⟩
      · rcases ih Z1 h with ⟨P1, x', P2, y', Z2, h1, h2, h3⟩ | ⟨Z', h1, h2⟩
        · exact .inl ⟨x :: P1, x', P2, y', Z2, by rw [h1]; rfl, by rw [h2]; rfl, h3⟩
        · exact .inr ⟨Z', by rw [h1]; rfl, h2⟩

/-- A list in nonincreasing order is below none of its arrangements. -/
theorem not_lt_of_antitone :
    ∀ (S T : List UInt64), S.Pairwise (fun a b => b ≤ a) → T.Perm S → ¬S < T
  | [], T, _, hp, h => by
    rw [List.perm_nil] at hp
    subst hp
    exact List.not_lt_nil _ h
  | s :: S1, [], _, hp, _ => absurd hp.length_eq (by simp)
  | s :: S1, t :: T1, hs, hp, h => by
    rw [List.pairwise_cons] at hs
    have ht : t ≤ s := by
      rcases List.mem_cons.mp (hp.subset (List.mem_cons_self ..)) with rfl | ht
      · exact UInt64.le_refl _
      · exact hs.1 t ht
    rw [List.cons_lt_cons_iff] at h
    rcases h with h | ⟨rfl, h⟩
    · exact absurd ht (UInt64.not_le.mpr h)
    · exact not_lt_of_antitone S1 T1 hs.2 ((List.perm_cons _).mp hp) h

/-- A list in nondecreasing order is above none of its arrangements. -/
theorem not_lt_of_monotone :
    ∀ (S T : List UInt64), S.Pairwise (· ≤ ·) → T.Perm S → ¬T < S
  | [], T, _, hp, h => by
    rw [List.perm_nil] at hp
    subst hp
    exact List.not_lt_nil _ h
  | s :: S1, [], _, hp, _ => absurd hp.length_eq (by simp)
  | s :: S1, t :: T1, hs, hp, h => by
    rw [List.pairwise_cons] at hs
    have ht : s ≤ t := by
      rcases List.mem_cons.mp (hp.subset (List.mem_cons_self ..)) with rfl | ht
      · exact UInt64.le_refl _
      · exact hs.1 t ht
    rw [List.cons_lt_cons_iff] at h
    rcases h with h | ⟨rfl, h⟩
    · exact absurd ht (UInt64.not_le.mpr h)
    · exact not_lt_of_monotone S1 T1 hs.2 ((List.perm_cons _).mp hp) h

/-! ### The steps -/

theorem toNat_pred {i : UInt64} (h : 0 < i) : (i - 1).toNat = i.toNat - 1 :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h; simp; omega))

/-- Step L2 from `i`: the last `r ≤ i` with `a[r - 1] < a[r]`, or 0 when there is none. -/
theorem ascent_spec (a : Array UInt64) :
    ∀ (n : Nat) (i : UInt64), i.toNat = n →
      (ascent a i = 0 ∧ ∀ k, 0 < k → k ≤ i.toNat → ¬a[k - 1]! < a[k]!) ∨
      (0 < (ascent a i).toNat ∧ (ascent a i).toNat ≤ i.toNat ∧
        a[(ascent a i).toNat - 1]! < a[(ascent a i).toNat]! ∧
        ∀ k, (ascent a i).toNat < k → k ≤ i.toNat → ¬a[k - 1]! < a[k]!) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have h0 : ¬0 < i := by rw [UInt64.lt_iff_toNat_lt]; simp [hi]
    rw [ascent, ite_eq_right h0]
    exact .inl ⟨rfl, fun k hk hki => by omega⟩
  | succ m ih =>
    intro i hi
    have h0 : 0 < i := by rw [UInt64.lt_iff_toNat_lt]; simp [hi]
    have hp := toNat_pred h0
    rw [ascent, ite_eq_left h0]
    by_cases hlt : a[(i - 1).toNat]! < a[i.toNat]!
    · rw [ite_eq_left hlt]
      rw [hp] at hlt
      exact .inr ⟨by omega, le_refl _, hlt, fun k hk hki => by omega⟩
    · rw [ite_eq_right hlt]
      rw [hp] at hlt
      rcases ih (i - 1) (by rw [hp]; omega) with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · refine .inl ⟨h1, fun k hk hki => ?_⟩
        rcases Nat.lt_or_ge k i.toNat with hk' | hk'
        · exact h2 k hk (by rw [hp]; omega)
        · rw [show k = i.toNat by omega]; exact hlt
      · refine .inr ⟨h1, by rw [hp] at h2; omega, h3, fun k hk hki => ?_⟩
        rcases Nat.lt_or_ge k i.toNat with hk' | hk'
        · exact h4 k hk (by rw [hp]; omega)
        · rw [show k = i.toNat by omega]; exact hlt

/-- Step L3 from `l` down to `lo`: the last position up to `l` whose word exceeds `v`, or `lo`. -/
theorem lastAbove_spec (a : Array UInt64) (v lo : UInt64) :
    ∀ (n : Nat) (l : UInt64), l.toNat = n → lo ≤ l →
      lo.toNat ≤ (lastAbove a v lo l).toNat ∧ (lastAbove a v lo l).toNat ≤ l.toNat ∧
        (lastAbove a v lo l = lo ∨ v < a[(lastAbove a v lo l).toNat]!) ∧
        ∀ m, (lastAbove a v lo l).toNat < m → m ≤ l.toNat → ¬v < a[m]! := by
  intro n
  induction n with
  | zero =>
    intro l hl hlo
    have h0 : ¬lo < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [lastAbove, ite_eq_right h0]
    have := UInt64.le_iff_toNat_le.mp hlo
    exact ⟨le_refl _, by omega, .inl rfl, fun m hm hml => by omega⟩
  | succ k ih =>
    intro l hl hlo
    rw [lastAbove]
    by_cases h0 : lo < l
    · rw [ite_eq_left h0]
      have h0' := UInt64.lt_iff_toNat_lt.mp h0
      have hp : (l - 1).toNat = l.toNat - 1 := toNat_pred (by
        rw [UInt64.lt_iff_toNat_lt]; simp; omega)
      by_cases hv : v < a[l.toNat]!
      · rw [ite_eq_left hv]
        exact ⟨by omega, le_refl _, .inr hv, fun m hm hml => by omega⟩
      · rw [ite_eq_right hv]
        obtain ⟨h1, h2, h3, h4⟩ := ih (l - 1) (by rw [hp]; omega)
          (UInt64.le_iff_toNat_le.mpr (by rw [hp]; omega))
        refine ⟨h1, by rw [hp] at h2; omega, h3, fun m hm hml => ?_⟩
        rcases Nat.lt_or_ge m l.toNat with hm' | hm'
        · exact h4 m hm (by rw [hp]; omega)
        · rw [show m = l.toNat by omega]; exact hv
    · rw [ite_eq_right h0]
      have := UInt64.le_iff_toNat_le.mp hlo
      have : lo = l := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.lt_iff_toNat_lt] at h0
        omega
      subst this
      exact ⟨le_refl _, le_refl _, .inl rfl, fun m hm hml => by omega⟩

/-- The words of positions `lo` to `hi` in reverse order, for `hi` below the size: step L4, and the
reversal of the whole array at the greatest arrangement. -/
theorem reverseRange_spec (a : Array UInt64) (lo hi : UInt64) (hhi : hi.toNat < a.size) :
    (reverseRange a lo hi).size = a.size ∧
      (reverseRange a lo hi).toList.Perm a.toList ∧
      ∀ k, (reverseRange a lo hi)[k]! =
        if lo.toNat ≤ k ∧ k ≤ hi.toNat then a[lo.toNat + hi.toNat - k]! else a[k]! := by
  fun_induction reverseRange a lo hi with
  | case1 a lo hi h ih =>
    have h' := UInt64.lt_iff_toNat_lt.mp h
    have e1 : (hi - 1).toNat = hi.toNat - 1 := toNat_pred (by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega)
    have e2 : (lo + 1).toNat = lo.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]
      have := UInt64.toNat_lt hi
      omega
    have hs : (swap lo hi a).size = a.size := by unfold swap; simp
    obtain ⟨r1, r2, r3⟩ := ih (by rw [e1, hs]; omega)
    refine ⟨r1.trans hs, r2.trans (swap_perm a lo hi (by omega) hhi), fun k => ?_⟩
    rw [r3 k, e1, e2]
    have sg := swap_get a lo hi (by omega) hhi
    split_ifs with c1 c2 c2
    · rw [sg]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
      omega
    · omega
    · rcases Nat.lt_or_ge k (lo.toNat + 1) with hk | hk
      · rw [sg, show k = lo.toNat by omega, ite_eq_right (by omega), ite_eq_left rfl]
        congr 1
        omega
      · rw [sg, show k = hi.toNat by omega, ite_eq_left rfl]
        congr 1
        omega
    · rw [sg, ite_eq_right (by omega), ite_eq_right (by omega)]
  | case2 a lo hi h =>
    refine ⟨rfl, List.Perm.refl _, fun k => ?_⟩
    split_ifs with c
    · rw [UInt64.lt_iff_toNat_lt] at h
      congr 1
      omega
    · rfl

/-! ### Positions and lists -/

/-- Adjacent positions from `lo` to `hi` that do not rise give a nonincreasing run. -/
theorem antitone_steps (a : Array UInt64) (lo hi : Nat)
    (h : ∀ k, lo < k → k ≤ hi → ¬a[k - 1]! < a[k]!) (m : Nat) (hm : lo ≤ m) :
    ∀ d, m + d ≤ hi → a[m + d]! ≤ a[m]!
  | 0, _ => wle_refl _
  | d + 1, hd => by
    have h1 := h (m + d + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at h1
    rw [← Nat.add_assoc]
    exact wle_trans (wle_of_not_lt h1) (antitone_steps a lo hi h m hm d (by omega))

theorem antitone_run (a : Array UInt64) (lo hi : Nat)
    (h : ∀ k, lo < k → k ≤ hi → ¬a[k - 1]! < a[k]!) :
    ∀ m m', lo ≤ m → m ≤ m' → m' ≤ hi → a[m']! ≤ a[m]! := by
  intro m m' hm hmm' hm'
  have := antitone_steps a lo hi h m hm (m' - m) (by omega)
  rwa [Nat.add_sub_of_le hmm'] at this

theorem toList_split (c : Array UInt64) (j : Nat) (h : j < c.size) :
    c.toList = c.toList.take j ++ c[j]! :: c.toList.drop (j + 1) := by
  have hl : j < c.toList.length := by simpa using h
  rw [getElem!_pos c j h]
  conv_lhs => rw [← List.take_append_drop j c.toList, List.drop_eq_getElem_cons hl]
  simp

theorem take_eq_take (b c : Array UInt64) (j : Nat) (hb : j ≤ b.size) (hc : j ≤ c.size)
    (h : ∀ k, k < j → b[k]! = c[k]!) : b.toList.take j = c.toList.take j := by
  apply List.ext_getElem
  · simp only [List.length_take, Array.length_toList]; omega
  · intro k h1 h2
    simp only [List.length_take, Array.length_toList] at h1 h2
    have := h k (by omega)
    rw [getElem!_pos b k (by omega), getElem!_pos c k (by omega)] at this
    simpa using this

theorem pairwise_drop (c : Array UInt64) (i : Nat) (R : UInt64 → UInt64 → Prop)
    (h : ∀ k k', i ≤ k → k < k' → k' < c.size → R c[k]! c[k']!) :
    (c.toList.drop i).Pairwise R := by
  rw [List.pairwise_iff_getElem]
  intro k k' hk hk' hkk
  simp only [List.length_drop, Array.length_toList] at hk hk'
  have := h (i + k) (i + k') (by omega) (by omega) (by omega)
  rw [getElem!_pos c (i + k) (by omega), getElem!_pos c (i + k') (by omega)] at this
  simpa using this

theorem mem_drop_get (c : Array UInt64) (i : Nat) (z : UInt64) (h : z ∈ c.toList.drop i) :
    ∃ m, i ≤ m ∧ m < c.size ∧ c[m]! = z := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_drop, Array.length_toList] at hk
  exact ⟨i + k, by omega, by omega, by rw [getElem!_pos c (i + k) (by omega)]; simp⟩

/-! ### The next arrangement -/

/-- With `S` nonincreasing, no arrangement above `P ++ p :: S` lies below `P ++ q :: S'`, when
`P ++ q :: S'` is an arrangement of `P ++ p :: S`, `q` is at most every word of `S` above `p`, and
`S'` is nondecreasing. -/
theorem least_above (P S S' : List UInt64) (p q : UInt64)
    (hS : S.Pairwise (fun x y => y ≤ x)) (hS' : S'.Pairwise (· ≤ ·))
    (hq : ∀ z ∈ S, p < z → q ≤ z) (hperm : (P ++ q :: S').Perm (P ++ p :: S)) :
    ∀ zs, Greater (P ++ p :: S) zs → ¬zs < P ++ q :: S' := by
  intro zs hg hzlt
  obtain ⟨hz, hlt⟩ := hg
  rcases lt_split P (p :: S) zs hlt with ⟨P1, x, P2, y, Z2, h1, h2, h3⟩ | ⟨Z', h1, h2⟩
  · subst h1 h2
    simp only [List.append_assoc, List.cons_append] at hzlt
    rcases List.cons_lt_cons_iff.mp (lt_of_append_lt_append P1 _ _ hzlt) with h | ⟨rfl, _⟩
    · exact absurd h (UInt64.not_lt.mpr (wle_of_lt h3))
    · exact UInt64.lt_irrefl _ h3
  · subst h1
    have hz' : Z'.Perm (p :: S) := (List.perm_append_left_iff P).mp hz
    cases Z' with
    | nil => exact absurd hz'.length_eq (by simp)
    | cons z Z2 =>
      have hlt2 := List.cons_lt_cons_iff.mp (lt_of_append_lt_append P _ _ hzlt)
      rcases List.cons_lt_cons_iff.mp h2 with h | ⟨rfl, h⟩
      · have hzS : z ∈ S := by
          rcases List.mem_cons.mp (hz'.subset (List.mem_cons_self ..)) with e | e
          · exact absurd h (by rw [e]; exact UInt64.lt_irrefl _)
          · exact e
        have hqz := hq z hzS h
        rcases hlt2 with h' | ⟨rfl, h'⟩
        · exact absurd h' (UInt64.not_lt.mpr hqz)
        · have hp2 : Z2.Perm S' :=
            (List.perm_cons _).mp ((List.perm_append_left_iff P).mp (hz.trans hperm.symm))
          exact not_lt_of_monotone S' Z2 hS' hp2 h'
      · exact not_lt_of_antitone S Z2 hS ((List.perm_cons _).mp hz') h

/-- An input in nonincreasing order has no greater arrangement, so a flag of 0 with a
nondecreasing arrangement of the input is the result that `IsNext` states. -/
theorem isNext_of_greatest (a : Array UInt64) (r : UInt64 × Array UInt64)
    (ha : a.toList.Pairwise (fun x y => y ≤ x)) (h1 : r.1 = 0)
    (hs : r.2.toList.Pairwise (· ≤ ·)) (hp : r.2.toList.Perm a.toList) : IsNext a r := by
  have hno : ¬∃ zs, Greater a.toList zs := by
    intro ⟨zs, hg⟩
    obtain ⟨hz, hlt⟩ := hg
    exact not_lt_of_antitone a.toList zs ha hz hlt
  exact And.intro (fun h => absurd h hno)
    (fun _ => ⟨h1, Library.Sorting.eq_mergeSort_of_sorted_perm hs hp⟩)

/-- For an array of fewer than `2^64` words, `nextPerm` returns the flag and the array that
`IsNext` states. -/
theorem nextPerm_isNext (a : Array UInt64) (hsize : a.size < 2 ^ 64) :
    IsNext a (nextPerm a) := by
  have hN : a.size.toUInt64.toNat = a.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [nextPerm]
  by_cases h1 : a.size.toUInt64 ≤ 1
  · rw [ite_eq_left h1]
    have hle : a.size ≤ 1 := by have := UInt64.le_iff_toNat_le.mp h1; simpa [hN] using this
    have hall : ∀ R : UInt64 → UInt64 → Prop, a.toList.Pairwise R := fun R => by
      rw [List.pairwise_iff_getElem]; intro i j hi hj hij; simp at hi hj; omega
    exact isNext_of_greatest a (0, a) (hall _) rfl (hall _) (List.Perm.refl _)
  rw [ite_eq_right h1]
  have h2 : 2 ≤ a.size := by
    have : ¬a.size.toUInt64.toNat ≤ 1 := fun h =>
      h1 (UInt64.le_iff_toNat_le.mpr (by simpa using h))
    omega
  have hn1 : (a.size.toUInt64 - 1).toNat = a.size - 1 := by
    simp only [UInt64.toNat_sub, hN, UInt64.reduceToNat]; omega
  rcases ascent_spec a _ (a.size.toUInt64 - 1) rfl with ⟨h0, hno⟩ | ⟨hpos, hle, hasc, hrest⟩
  · rw [ite_eq_left h0]
    rw [hn1] at hno
    have hanti := antitone_run a 0 (a.size - 1) hno
    have ha : a.toList.Pairwise (fun x y => y ≤ x) := by
      have := pairwise_drop a 0 (fun x y => y ≤ x)
        (fun k k' _ hkk hk' => hanti k k' (by omega) (by omega) (by omega))
      rwa [List.drop_zero] at this
    obtain ⟨r1, r2, r3⟩ := reverseRange_spec a 0 (a.size.toUInt64 - 1) (by rw [hn1]; omega)
    simp only [hn1, UInt64.reduceToNat, Nat.zero_le, true_and, Nat.zero_add] at r3
    refine isNext_of_greatest a _ ha rfl ?_ r2
    have hs := pairwise_drop (reverseRange a 0 (a.size.toUInt64 - 1)) 0 (· ≤ ·)
      (fun k k' _ hkk hk' => by
        rw [r1] at hk'
        rw [r3 k, r3 k', ite_eq_left (by omega), ite_eq_left (by omega)]
        exact hanti _ _ (by omega) (by omega) (by omega))
    rwa [List.drop_zero] at hs
  have h0 : ¬ascent a (a.size.toUInt64 - 1) = 0 := fun h => by rw [h] at hpos; simp at hpos
  rw [ite_eq_right h0]
  generalize ascent a (a.size.toUInt64 - 1) = i at hpos hle hasc hrest ⊢
  rw [hn1] at hle hrest
  have hj : (i - 1).toNat = i.toNat - 1 :=
    toNat_pred (UInt64.lt_iff_toNat_lt.mpr (by simpa using hpos))
  obtain ⟨l1, l2, l3, l4⟩ := lastAbove_spec a a[(i - 1).toNat]! i _ (a.size.toUInt64 - 1) rfl
    (UInt64.le_iff_toNat_le.mpr (by rw [hn1]; exact hle))
  generalize lastAbove a a[(i - 1).toNat]! i (a.size.toUInt64 - 1) = l at l1 l2 l3 l4 ⊢
  rw [hn1] at l2 l4
  rw [hj] at l3 l4
  have hvL : a[i.toNat - 1]! < a[l.toNat]! := by
    rcases l3 with rfl | h
    · exact hasc
    · exact h
  have aAnti := antitone_run a i.toNat (a.size - 1) hrest
  have hiL : (i - 1).toNat < a.size := by rw [hj]; omega
  have hlL : l.toNat < a.size := by omega
  have sg := swap_get a (i - 1) l hiL hlL
  have hbp := swap_perm a (i - 1) l hiL hlL
  rw [hj] at sg
  have hbs : (swap (i - 1) l a).size = a.size := by unfold swap; simp
  have bAnti : ∀ m' m, i.toNat ≤ m' → m' < m → m ≤ a.size - 1 →
      (swap (i - 1) l a)[m]! ≤ (swap (i - 1) l a)[m']! := by
    intro m' m hm' hmm hm
    rw [sg m, sg m']
    by_cases e : m = l.toNat
    · rw [ite_eq_left e, ite_eq_right (by omega : ¬m' = l.toNat),
        ite_eq_right (by omega : ¬m' = i.toNat - 1)]
      exact wle_trans (wle_of_lt hvL) (aAnti m' l.toNat hm' (by omega) (by omega))
    · rw [ite_eq_right e, ite_eq_right (by omega : ¬m = i.toNat - 1)]
      by_cases e' : m' = l.toNat
      · rw [ite_eq_left e']
        exact wle_of_not_lt (l4 m (by omega) hm)
      · rw [ite_eq_right e', ite_eq_right (by omega : ¬m' = i.toNat - 1)]
        exact aAnti m' m hm' (by omega) hm
  obtain ⟨c1, c2, c3⟩ := reverseRange_spec (swap (i - 1) l a) i (a.size.toUInt64 - 1)
    (by rw [hn1, hbs]; omega)
  rw [hn1] at c3
  generalize reverseRange (swap (i - 1) l a) i (a.size.toUInt64 - 1) = c at c1 c2 c3 ⊢
  have hA := toList_split a (i.toNat - 1) (by omega)
  have hC := toList_split c (i.toNat - 1) (by rw [c1, hbs]; omega)
  rw [show i.toNat - 1 + 1 = i.toNat by omega] at hA hC
  have hP : c.toList.take (i.toNat - 1) = a.toList.take (i.toNat - 1) :=
    take_eq_take c a _ (by rw [c1, hbs]; omega) (by omega) (fun k hk => by
      rw [c3 k, ite_eq_right (by omega), sg k, ite_eq_right (by omega),
        ite_eq_right (by omega)])
  have hq : c[i.toNat - 1]! = a[l.toNat]! := by
    rw [c3, ite_eq_right (by omega), sg, ite_eq_right (by omega), ite_eq_left rfl]
  have hCeq : c.toList = a.toList.take (i.toNat - 1) ++ a[l.toNat]! :: c.toList.drop i.toNat := by
    rw [← hP, ← hq]; exact hC
  have hS : (a.toList.drop i.toNat).Pairwise (fun x y => y ≤ x) :=
    pairwise_drop a _ _ (fun k k' hk hkk hk' => aAnti k k' hk (by omega) (by omega))
  have hS' : (c.toList.drop i.toNat).Pairwise (· ≤ ·) :=
    pairwise_drop c _ _ (fun k k' hk hkk hk' => by
      rw [c1, hbs] at hk'
      rw [c3 k, c3 k', ite_eq_left (by omega), ite_eq_left (by omega)]
      exact bAnti _ _ (by omega) (by omega) (by omega))
  have hqmin : ∀ z ∈ a.toList.drop i.toNat, a[i.toNat - 1]! < z → a[l.toNat]! ≤ z := by
    intro z hz hlt
    obtain ⟨m, hm1, hm2, rfl⟩ := mem_drop_get a _ z hz
    exact aAnti m l.toNat hm1 (Nat.le_of_not_lt fun hgt => l4 m hgt (by omega) hlt) (by omega)
  have hcp : c.toList.Perm a.toList := c2.trans hbp
  generalize c.toList.drop i.toNat = S' at hCeq hS'
  generalize a.toList.drop i.toNat = S at hA hS hqmin
  generalize a.toList.take (i.toNat - 1) = P at hA hCeq
  have hperm : (P ++ a[l.toNat]! :: S').Perm (P ++ a[i.toNat - 1]! :: S) := by
    rw [← hA, ← hCeq]; exact hcp
  have hG : Greater a.toList c.toList := by
    rw [hA, hCeq]
    exact And.intro hperm (append_lt_append P _ _ (List.cons_lt_cons_iff.mpr (.inl hvL)))
  have hmin : ∀ zs, Greater a.toList zs → ¬zs < c.toList := by
    rw [hA, hCeq]
    exact least_above P S S' _ _ hS hS' hqmin hperm
  exact And.intro (fun _ => ⟨rfl, hG, hmin⟩) (fun h => (h ⟨_, hG⟩).elim)

/-- Lean's order on lists of words is total. -/
theorem list_lt_trichotomy : ∀ (A B : List UInt64), A < B ∨ A = B ∨ B < A
  | [], [] => .inr (.inl rfl)
  | [], _ :: _ => .inl (List.nil_lt_cons ..)
  | _ :: _, [] => .inr (.inr (List.nil_lt_cons ..))
  | x :: A, y :: B => by
    simp only [List.cons_lt_cons_iff, List.cons.injEq]
    rcases Nat.lt_trichotomy x.toNat y.toNat with h | h | h
    · exact .inl (.inl (UInt64.lt_iff_toNat_lt.mpr h))
    · have e : x = y := UInt64.toNat_inj.mp h
      subst e
      rcases list_lt_trichotomy A B with h' | h' | h'
      · exact .inl (.inr ⟨rfl, h'⟩)
      · exact .inr (.inl ⟨rfl, h'⟩)
      · exact .inr (.inr (.inr ⟨rfl, h'⟩))
    · exact .inr (.inr (.inl (UInt64.lt_iff_toNat_lt.mpr h)))

/-- `IsNext xs` determines the flag and the array. -/
theorem isNext_unique {xs : Array UInt64} {r r' : UInt64 × Array UInt64} (h : IsNext xs r)
    (h' : IsNext xs r') : r = r' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  by_cases hg : ∃ zs, Greater xs.toList zs
  · obtain ⟨f, g, m⟩ := h1 hg
    obtain ⟨f', g', m'⟩ := h1' hg
    have e : r.2.toList = r'.2.toList := by
      rcases list_lt_trichotomy r.2.toList r'.2.toList with lt | e | lt
      · exact absurd lt (m' _ g)
      · exact e
      · exact absurd lt (m _ g')
    exact Prod.ext (f.trans f'.symm) (Array.toList_inj.mp e)
  · obtain ⟨f, e⟩ := h2 hg
    obtain ⟨f', e'⟩ := h2' hg
    exact Prod.ext (f.trans f'.symm) (Array.toList_inj.mp (e.trans e'.symm))

end Library.Combinatorics.NextPermutation
