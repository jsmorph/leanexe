import Library.Sorting.MergeSort.Program
import Library.Sorting.MergeSort.Spec
import LeanExe.Dialect.Lemmas

/-! The proof that merge sort returns the array's elements in nondecreasing order.  `passList w l`
states one pass of width `w` on a list: it merges each pair of adjacent runs of width `w` with
`List.merge`.  `merge_toList` and `pass_toList` show that the array program computes it, and
`sortLoop_toList` that the passes compute `sortList`.  On lists, a pass permutes its input
(`passList_perm`) and turns runs of width `w` that are sorted into sorted runs of width `2w`
(`passList_runs`), so the last pass leaves a sorted permutation, which is unique. -/

namespace Library.Sorting.MergeSort

open LeanExe.Dialect

/-! ### The order of words -/

theorem wle_trans {a b c : UInt64} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  UInt64.le_iff_toNat_le.mpr
    (Nat.le_trans (UInt64.le_iff_toNat_le.mp h1) (UInt64.le_iff_toNat_le.mp h2))

theorem wle_antisymm {a b : UInt64} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  UInt64.toNat_inj.mp
    (Nat.le_antisymm (UInt64.le_iff_toNat_le.mp h1) (UInt64.le_iff_toNat_le.mp h2))

theorem wle_total (a b : UInt64) : a ≤ b ∨ b ≤ a := by
  rcases Nat.le_total a.toNat b.toNat with h | h
  · exact Or.inl (UInt64.le_iff_toNat_le.mpr h)
  · exact Or.inr (UInt64.le_iff_toNat_le.mpr h)

theorem le_trans_bool (a b c : UInt64) :
    decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
  simp only [decide_eq_true_eq]; exact wle_trans

theorem le_total_bool (a b : UInt64) : (decide (a ≤ b) || decide (b ≤ a)) = true := by
  rcases wle_total a b with h | h <;> simp [h]

/-! ### Segments -/

/-- The segment `a[lo, hi)` as a list. -/
def seg (a : Array UInt64) (lo hi : Nat) : List UInt64 := (a.toList.drop lo).take (hi - lo)

theorem seg_cons (a : Array UInt64) {lo hi : Nat} (h : lo < hi) (h2 : hi ≤ a.size) :
    seg a lo hi = a[lo]! :: seg a (lo + 1) hi := by
  unfold seg
  have hlt : lo < a.toList.length := by simp; omega
  rw [List.drop_eq_getElem_cons hlt, show hi - lo = (hi - (lo + 1)) + 1 by omega,
    List.take_succ_cons, getElem!_pos a lo (by omega)]
  simp

theorem seg_nil (a : Array UInt64) {lo hi : Nat} (h : hi ≤ lo) : seg a lo hi = [] := by
  simp [seg, Nat.sub_eq_zero_of_le h]

theorem seg_length (a : Array UInt64) {lo hi : Nat} (h : lo ≤ hi) (h2 : hi ≤ a.size) :
    (seg a lo hi).length = hi - lo := by
  simp [seg]; omega

/-! ### Merging -/

theorem set_take_drop (L : List UInt64) (K m : Nat) (v : UInt64) (h : K < L.length) :
    (L.set K v).take (K + 1) = L.take K ++ [v] ∧
      (L.set K v).drop (K + 1 + m) = L.drop (K + 1 + m) := by
  rw [List.set_eq_take_append_cons_drop, if_pos h]
  have hlen : (L.take K).length = K := by simp; omega
  constructor
  · rw [List.take_append, hlen, show K + 1 - K = 1 by omega,
      List.take_of_length_le (by rw [hlen]; omega)]
    simp
  · rw [List.drop_append, hlen, List.drop_eq_nil_of_le (by rw [hlen]; omega),
      show K + 1 + m - K = m + 1 by omega, List.nil_append, List.drop_succ_cons, List.drop_drop]

/-- The merge writes the merged runs at `k` and keeps the rest of `out`. -/
theorem merge_toList (src : Array UInt64) (k i iEnd j jEnd : UInt64) (out : Array UInt64)
    (hsize : out.size < 2 ^ 64)
    (hi : i.toNat ≤ iEnd.toNat) (hiE : iEnd.toNat ≤ src.size)
    (hj : j.toNat ≤ jEnd.toNat) (hjE : jEnd.toNat ≤ src.size)
    (hk : k.toNat + (iEnd.toNat - i.toNat) + (jEnd.toNat - j.toNat) ≤ out.size) :
    (merge src k i iEnd j jEnd out).toList =
      out.toList.take k.toNat ++
        (seg src i.toNat iEnd.toNat).merge (seg src j.toNat jEnd.toNat) (fun a b => a ≤ b) ++
        out.toList.drop (k.toNat + (iEnd.toNat - i.toNat) + (jEnd.toNat - j.toNat)) := by
  rw [merge]
  by_cases c1 : i < iEnd ∧ (jEnd ≤ j ∨ src[i.toNat]! ≤ src[j.toNat]!)
  · rw [if_pos c1]
    have hI := UInt64.lt_iff_toNat_lt.mp c1.1
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      have := UInt64.toNat_lt iEnd
      simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
    have hKlt : k.toNat < out.toList.length := by simp; omega
    rw [merge_toList src (k + 1) (i + 1) iEnd j jEnd (out.set! k.toNat src[i.toNat]!)
      (by simp; omega) (by rw [hi1]; omega) hiE hj hjE
      (by simp only [Array.size_set!]; rw [hi1, hk1]; omega)]
    rw [hi1, hk1, Array.toList_set!]
    obtain ⟨ht, hd⟩ := set_take_drop out.toList k.toNat
      ((iEnd.toNat - (i.toNat + 1)) + (jEnd.toNat - j.toNat)) src[i.toNat]! hKlt
    rw [ht, show k.toNat + 1 + (iEnd.toNat - (i.toNat + 1)) + (jEnd.toNat - j.toNat) =
      k.toNat + 1 + ((iEnd.toNat - (i.toNat + 1)) + (jEnd.toNat - j.toNat)) by omega, hd,
      seg_cons src hI hiE]
    have hm : (src[i.toNat]! :: seg src (i.toNat + 1) iEnd.toNat).merge
        (seg src j.toNat jEnd.toNat) (fun a b => a ≤ b) =
        src[i.toNat]! :: (seg src (i.toNat + 1) iEnd.toNat).merge
          (seg src j.toNat jEnd.toNat) (fun a b => a ≤ b) := by
      rcases c1.2 with hje | hle
      · rw [seg_nil src (UInt64.le_iff_toNat_le.mp hje), List.merge_right, List.merge_right]
      · by_cases hjj : j.toNat < jEnd.toNat
        · rw [seg_cons src hjj hjE, List.cons_merge_cons, if_pos (by simpa using hle)]
        · rw [seg_nil src (lo := j.toNat) (hi := jEnd.toNat) (by omega), List.merge_right,
            List.merge_right]
    rw [hm, show k.toNat + (iEnd.toNat - i.toNat) + (jEnd.toNat - j.toNat) =
      k.toNat + 1 + ((iEnd.toNat - (i.toNat + 1)) + (jEnd.toNat - j.toNat)) by omega]
    simp
  · rw [if_neg c1]
    by_cases c2 : j < jEnd
    · rw [if_pos c2]
      have hJ := UInt64.lt_iff_toNat_lt.mp c2
      have hj1 : (j + 1).toNat = j.toNat + 1 := by
        have := UInt64.toNat_lt jEnd
        simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := by
        simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
      have hKlt : k.toNat < out.toList.length := by simp; omega
      rw [merge_toList src (k + 1) i iEnd (j + 1) jEnd (out.set! k.toNat src[j.toNat]!)
        (by simp; omega) hi hiE (by rw [hj1]; omega) hjE
        (by simp only [Array.size_set!]; rw [hj1, hk1]; omega)]
      rw [hj1, hk1, Array.toList_set!]
      obtain ⟨ht, hd⟩ := set_take_drop out.toList k.toNat
        ((iEnd.toNat - i.toNat) + (jEnd.toNat - (j.toNat + 1))) src[j.toNat]! hKlt
      rw [ht, show k.toNat + 1 + (iEnd.toNat - i.toNat) + (jEnd.toNat - (j.toNat + 1)) =
        k.toNat + 1 + ((iEnd.toNat - i.toNat) + (jEnd.toNat - (j.toNat + 1))) by omega, hd,
        seg_cons src hJ hjE]
      have hm : (seg src i.toNat iEnd.toNat).merge
          (src[j.toNat]! :: seg src (j.toNat + 1) jEnd.toNat) (fun a b => a ≤ b) =
          src[j.toNat]! :: (seg src i.toNat iEnd.toNat).merge
            (seg src (j.toNat + 1) jEnd.toNat) (fun a b => a ≤ b) := by
        by_cases hii : i.toNat < iEnd.toNat
        · have hnle : ¬ src[i.toNat]! ≤ src[j.toNat]! := fun h =>
            c1 ⟨UInt64.lt_iff_toNat_lt.mpr hii, Or.inr h⟩
          rw [seg_cons src hii hiE, List.cons_merge_cons, if_neg (by simpa using hnle)]
        · rw [seg_nil src (lo := i.toNat) (hi := iEnd.toNat) (by omega), List.nil_merge,
            List.nil_merge]
      rw [hm, show k.toNat + (iEnd.toNat - i.toNat) + (jEnd.toNat - j.toNat) =
        k.toNat + 1 + ((iEnd.toNat - i.toNat) + (jEnd.toNat - (j.toNat + 1))) by omega]
      simp
    · rw [if_neg c2]
      have hjj : jEnd.toNat ≤ j.toNat := by
        by_contra h
        exact c2 (UInt64.lt_iff_toNat_lt.mpr (by omega))
      have hii : iEnd.toNat ≤ i.toNat := by
        by_contra h
        exact c1 ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), Or.inl (UInt64.le_iff_toNat_le.mpr hjj)⟩
      rw [seg_nil src hii, seg_nil src hjj, List.nil_merge,
        show iEnd.toNat - i.toNat = 0 by omega, show jEnd.toNat - j.toNat = 0 by omega]
      simp
termination_by (iEnd - i).toNat + (jEnd - j).toNat
decreasing_by
  · have := UInt64.lt_iff_toNat_lt.mp c1.1
    have := UInt64.toNat_lt iEnd
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  · have := UInt64.lt_iff_toNat_lt.mp c2
    have := UInt64.toNat_lt jEnd
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    omega

/-! ### A pass -/

/-- One pass of width `w` on a list: merge each pair of adjacent runs of width `w`. -/
def passList (w : Nat) (l : List UInt64) : List UInt64 :=
  if h : w = 0 ∨ l = [] then l
  else (l.take w).merge ((l.drop w).take w) (fun a b => a ≤ b) ++ passList w (l.drop (w + w))
termination_by l.length
decreasing_by
  have h1 : w ≠ 0 := (not_or.mp h).1
  have h2 : l ≠ [] := (not_or.mp h).2
  have : l.length ≠ 0 := fun h' => h2 (List.length_eq_zero_iff.mp h')
  simp only [List.length_drop]
  omega

theorem passList_step {w : Nat} {l : List UInt64} (hw : w ≠ 0) (hl : l ≠ []) :
    passList w l =
      (l.take w).merge ((l.drop w).take w) (fun a b => a ≤ b) ++ passList w (l.drop (w + w)) := by
  rw [passList, dif_neg (not_or.mpr ⟨hw, hl⟩)]

theorem passList_nil (w : Nat) : passList w [] = [] := by
  rw [passList]; simp

/-- The pass writes `passList` of the segment `[lo, n)` of `src` after the first `lo` words of
`out`. -/
theorem pass_toList (src : Array UInt64) (w n lo : UInt64) (out : Array UInt64)
    (hw : 0 < w.toNat) (hsrc : src.size = n.toNat) (hout : out.size = n.toNat)
    (hlo : lo.toNat ≤ n.toNat) :
    (pass src w n lo out).toList =
      out.toList.take lo.toNat ++ passList w.toNat (seg src lo.toNat n.toNat) := by
  have hn := UInt64.toNat_lt n
  rw [pass]
  by_cases c : 0 < w ∧ lo < n
  · rw [if_pos c]
    have hl := UInt64.lt_iff_toNat_lt.mp c.2
    have hm := runEnd_toNat (lo := lo) (w := w) (UInt64.le_iff_toNat_le.mpr hlo)
    have hmn : (runEnd lo w n).toNat ≤ n.toNat := by omega
    have hh := runEnd_toNat (lo := runEnd lo w n) (w := w) (UInt64.le_iff_toNat_le.mpr hmn)
    have hmerge := merge_toList src lo lo (runEnd lo w n) (runEnd lo w n)
      (runEnd (runEnd lo w n) w n) out (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    set LO := lo.toNat with hLO
    set M := (runEnd lo w n).toNat with hM
    set H := (runEnd (runEnd lo w n) w n).toNat with hH
    set W := w.toNat with hW
    set N := n.toNat with hN
    have hsz : (merge src lo lo (runEnd lo w n) (runEnd lo w n) (runEnd (runEnd lo w n) w n)
        out).size = N := by
      rw [← Array.length_toList, hmerge, List.length_append, List.length_append, List.length_take,
        List.length_merge, List.length_drop, seg_length src (lo := LO) (hi := M) (by omega)
        (by omega), seg_length src (lo := M) (hi := H) (by omega) (by omega), Array.length_toList]
      omega
    rw [pass_toList src w n (runEnd (runEnd lo w n) w n) _ hw hsrc hsz (by omega), hmerge]
    have hlen1 : (out.toList.take LO).length = LO := by simp; omega
    have hlen2 : ((seg src LO M).merge (seg src M H) (fun a b => a ≤ b)).length = H - LO := by
      rw [List.length_merge, seg_length src (by omega) (by omega),
        seg_length src (by omega) (by omega)]
      omega
    have hseg : seg src LO N ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [seg_length src (by omega) (by omega)] at this
      simp at this
      omega
    rw [passList_step (by omega) hseg]
    have e1 : (seg src LO N).take W = seg src LO M := by
      simp only [seg, List.take_take]
      congr 1
      omega
    have e2 : ((seg src LO N).drop W).take W = seg src M H := by
      simp only [seg, List.drop_take, List.take_take, List.drop_drop]
      by_cases hc : W ≤ N - LO
      · have : M = LO + W := by omega
        rw [this]
        congr 1
        omega
      · rw [show min W (N - LO - W) = 0 by omega, show H - M = 0 by omega]
        simp
    have e3 : (seg src LO N).drop (W + W) = seg src H N := by
      simp only [seg, List.drop_take, List.drop_drop]
      by_cases hc : W + W ≤ N - LO
      · have : H = LO + (W + W) := by omega
        rw [this]
        congr 1
        omega
      · rw [show N - LO - (W + W) = 0 by omega, show N - H = 0 by omega]
        simp
    rw [e1, e2, e3, List.take_left' (by rw [List.length_append, hlen1, hlen2]; omega),
      List.append_assoc]
  · rw [if_neg c]
    have hge : n.toNat ≤ lo.toNat := by
      by_contra h
      exact c ⟨UInt64.lt_iff_toNat_lt.mpr (by simpa using hw), UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
    rw [seg_nil src hge, passList_nil, List.append_nil,
      List.take_of_length_le (by simp; omega)]
termination_by (n - lo).toNat
decreasing_by
  have hw' := UInt64.lt_iff_toNat_lt.mp c.1
  have hl := UInt64.lt_iff_toNat_lt.mp c.2
  have h1 := runEnd_toNat (lo := lo) (w := w) (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hl))
  have h2 := runEnd_toNat (lo := runEnd lo w n) (w := w) (n := n)
    (UInt64.le_iff_toNat_le.mpr (by omega))
  simp only [UInt64.reduceToNat] at hw'
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt n
  omega

/-! ### Sortedness and permutation on lists -/

theorem passList_perm (w : Nat) (l : List UInt64) : (passList w l).Perm l := by
  by_cases h : w = 0 ∨ l = []
  · rw [passList, dif_pos h]
  · rw [passList_step (not_or.mp h).1 (not_or.mp h).2]
    have ih := passList_perm w (l.drop (w + w))
    have e : l.take w ++ (l.drop w).take w ++ l.drop (w + w) = l := by
      rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
    exact ((List.merge_perm_append _).append ih).trans (List.Perm.of_eq e)
termination_by l.length
decreasing_by
  have h1 : w ≠ 0 := (not_or.mp h).1
  have h2 : l ≠ [] := (not_or.mp h).2
  have : l.length ≠ 0 := fun h' => h2 (List.length_eq_zero_iff.mp h')
  simp only [List.length_drop]
  omega

/-- Every run of width `w` of the list, `l[t * w, (t + 1) * w)`, is sorted. -/
def RunsSorted (w : Nat) (l : List UInt64) : Prop :=
  ∀ t, ((l.drop (t * w)).take w).Pairwise (· ≤ ·)

theorem runsSorted_one (l : List UInt64) : RunsSorted 1 l := by
  intro t
  rcases h : (l.drop (t * 1)) with _ | ⟨a, r⟩
  · simp
  · simp

theorem sorted_of_runsSorted {w : Nat} {l : List UInt64} (h : RunsSorted w l)
    (hl : l.length ≤ w) : l.Pairwise (· ≤ ·) := by
  have := h 0
  rwa [Nat.zero_mul, List.drop_zero, List.take_of_length_le hl] at this

theorem runsSorted_of_sorted (w : Nat) {l : List UInt64} (h : l.Pairwise (· ≤ ·)) :
    RunsSorted w l :=
  fun t => h.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))

theorem pairwise_bool {l : List UInt64} :
    l.Pairwise (fun a b => decide (a ≤ b) = true) ↔ l.Pairwise (· ≤ ·) := by
  simp

theorem passList_runs (w : Nat) (hw : w ≠ 0) (l : List UInt64) (h : RunsSorted w l) :
    RunsSorted (w + w) (passList w l) := by
  by_cases hl : l = []
  · subst hl; rw [passList_nil]; intro t; simp
  rw [passList_step hw hl]
  have hA : (l.take w).Pairwise (· ≤ ·) := by simpa using h 0
  have hB : ((l.drop w).take w).Pairwise (· ≤ ·) := by simpa using h 1
  have hM : ((l.take w).merge ((l.drop w).take w) (fun a b => a ≤ b)).Pairwise (· ≤ ·) :=
    pairwise_bool.mp (List.pairwise_merge le_trans_bool le_total_bool _ _
      (pairwise_bool.mpr hA) (pairwise_bool.mpr hB))
  have hrest : RunsSorted w (l.drop (w + w)) := by
    intro t
    have := h (t + 2)
    rwa [List.drop_drop, show w + w + t * w = (t + 2) * w by rw [Nat.add_mul]; omega]
  have ih := passList_runs w hw (l.drop (w + w)) hrest
  have hlenM : ((l.take w).merge ((l.drop w).take w) (fun a b => a ≤ b)).length =
      min w l.length + min w (l.length - w) := by
    rw [List.length_merge]; simp
  intro t
  by_cases hbig : w + w ≤ l.length
  · have hlen : ((l.take w).merge ((l.drop w).take w) (fun a b => a ≤ b)).length = w + w := by
      rw [hlenM]; omega
    rcases t with _ | t
    · rw [Nat.zero_mul, List.drop_zero, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
      exact hM
    · rw [List.drop_append, hlen,
        List.drop_eq_nil_of_le (by rw [hlen]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos t)),
        List.nil_append, show (t + 1) * (w + w) - (w + w) = t * (w + w) by
          rw [Nat.add_mul, Nat.one_mul]; omega]
      exact ih t
  · have hnil : l.drop (w + w) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hnil, passList_nil, List.append_nil]
    exact runsSorted_of_sorted (w + w) hM t
termination_by l.length
decreasing_by
  have : l.length ≠ 0 := fun h' => hl (List.length_eq_zero_iff.mp h')
  simp only [List.length_drop]
  omega

/-! ### The passes -/

/-- The passes on a list, as `sortLoop` performs them on an array of length `n`. -/
def sortList (w n : Nat) (l : List UInt64) : List UInt64 :=
  if 0 < w ∧ w < n then sortList (if w < n - w then w + w else n) n (passList w l) else l
termination_by n - w
decreasing_by
  split <;> omega

theorem sortLoop_toList (w n : UInt64) (xs : Array UInt64) (hxs : xs.size = n.toNat) :
    (sortLoop w n xs).toList = sortList w.toNat n.toNat xs.toList := by
  have hn := UInt64.toNat_lt n
  rw [sortLoop, sortList]
  by_cases c : 0 < w ∧ w < n
  · have hw := UInt64.lt_iff_toNat_lt.mp c.1
    have hl := UInt64.lt_iff_toNat_lt.mp c.2
    simp only [UInt64.reduceToNat] at hw
    rw [if_pos c, if_pos (show 0 < w.toNat ∧ w.toNat < n.toNat from ⟨hw, hl⟩)]
    have hb : (LeanExe.build n fun _ => (0 : UInt64)).size = n.toNat := by
      rw [build_size]
    have hpass := pass_toList xs w n 0 (LeanExe.build n fun _ => 0) (by omega) hxs hb (by simp)
    have hps : (pass xs w n 0 (LeanExe.build n fun _ => 0)).size = n.toNat := by
      rw [← Array.length_toList, hpass]
      simp [(passList_perm _ _).length_eq, seg]
      omega
    have hseg : seg xs 0 n.toNat = xs.toList := by
      simp [seg, ← hxs]
    have hs : (n - w).toNat = n.toNat - w.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    by_cases h2 : w < n - w
    · have h2' : w.toNat < n.toNat - w.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp h2; rwa [hs] at this
      rw [if_pos h2, if_pos h2', sortLoop_toList (w + w) n _ hps, hpass]
      simp only [UInt64.toNat_zero, List.take_zero, List.nil_append, hseg]
      congr 1
      simp only [UInt64.toNat_add]; omega
    · have h2' : ¬ w.toNat < n.toNat - w.toNat := fun h' =>
        h2 (UInt64.lt_iff_toNat_lt.mpr (by rw [hs]; exact h'))
      rw [if_neg h2, if_neg h2', sortLoop_toList n n _ hps, hpass]
      simp only [UInt64.toNat_zero, List.take_zero, List.nil_append, hseg]
  · rw [if_neg c, if_neg]
    intro ⟨hw, hl⟩
    exact c ⟨UInt64.lt_iff_toNat_lt.mpr (by simpa using hw), UInt64.lt_iff_toNat_lt.mpr hl⟩
termination_by (n - w).toNat
decreasing_by
  all_goals
    have hw := UInt64.lt_iff_toNat_lt.mp c.1
    have hl := UInt64.lt_iff_toNat_lt.mp c.2
    have := UInt64.toNat_lt n
    simp only [UInt64.reduceToNat] at hw
  · have := UInt64.lt_iff_toNat_lt.mp h2
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat] at *
    omega
  · simp only [UInt64.toNat_sub, UInt64.reduceToNat]
    omega

theorem sortList_spec (w n : Nat) (l : List UInt64) (hw : 0 < w) (hl : l.length = n)
    (hr : RunsSorted w l) : (sortList w n l).Pairwise (· ≤ ·) ∧ (sortList w n l).Perm l := by
  rw [sortList]
  by_cases c : 0 < w ∧ w < n
  · rw [if_pos c]
    have hp := passList_perm w l
    have hr2 := passList_runs w (by omega) l hr
    split
    · obtain ⟨h1, h2⟩ := sortList_spec (w + w) n (passList w l) (by omega)
        (by rw [hp.length_eq, hl]) hr2
      exact ⟨h1, h2.trans hp⟩
    · have hs : (passList w l).Pairwise (· ≤ ·) :=
        sorted_of_runsSorted hr2 (by rw [hp.length_eq]; omega)
      obtain ⟨h1, h2⟩ := sortList_spec n n (passList w l) (by omega)
        (by rw [hp.length_eq, hl]) (runsSorted_of_sorted n hs)
      exact ⟨h1, h2.trans hp⟩
  · rw [if_neg c]
    exact ⟨sorted_of_runsSorted hr (by omega), List.Perm.refl _⟩
termination_by n - w
decreasing_by all_goals omega

/-- Merge sort computes the specification on every array that memory can hold. -/
theorem mergeSort_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    mergeSort xs = expected xs := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  have hl := sortLoop_toList 1 xs.size.toUInt64 xs hN.symm
  obtain ⟨hsorted, hperm⟩ := sortList_spec 1 xs.size xs.toList (by omega) (by simp)
    (runsSorted_one _)
  rw [hN] at hl
  simp only [UInt64.reduceToNat] at hl
  have hms := List.pairwise_mergeSort le_trans_bool le_total_bool xs.toList
  have heq := List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun a b _ _ hab hba => wle_antisymm hab hba) hsorted (pairwise_bool.mp hms)
    (hperm.trans (List.mergeSort_perm _ _).symm)
  unfold mergeSort expected
  rw [← heq, ← hl, Array.toArray_toList]

end Library.Sorting.MergeSort
