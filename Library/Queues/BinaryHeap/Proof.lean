import Library.Queues.BinaryHeap.Program
import Library.Queues.BinaryHeap.Spec
import Library.Sorting.Heapsort.Proof
import LeanExe.Dialect.ArrayLemmas

/-! The proof that the binary heap computes the outputs of the list queue.  `Agrees` states the
invariant of the loop: the prefix `h[0, n)` of the array is a heap, `HeapFrom` of heapsort's proof,
whose words are a permutation of the list queue's words, and the outputs are equal.  `siftUp_spec`
states the invariant of an insertion: the heap order holds at every node except between the moving
node and its parent, and the children of the moving node are at most its parent.  A removal reuses
heapsort's `siftDown_spec`.  The root of a heap is its largest word, `heap_root`, so it is `largest`
of the list queue. -/

namespace Library.Queues.BinaryHeap

open Library.Sorting.Heapsort LeanExe.Dialect

/-! ### The largest word of a list -/

theorem max_eq (a b : UInt64) : max a b = if a ≤ b then b else a := rfl

theorem wle_of_not_le {a b : UInt64} (h : ¬ a ≤ b) : b ≤ a :=
  UInt64.le_iff_toNat_le.mpr
    (Nat.le_of_lt (Nat.lt_of_not_le fun h' => h (UInt64.le_iff_toNat_le.mpr h')))

theorem foldl_max_le {l : List UInt64} {a m : UInt64} (ha : a ≤ m) (hl : ∀ x ∈ l, x ≤ m) :
    l.foldl max a ≤ m := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    rw [max_eq]; split
    · exact hl x List.mem_cons_self
    · exact ha

theorem le_foldl_max (l : List UInt64) (a : UInt64) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact wle_refl a
  | cons x xs ih =>
    simp only [List.foldl_cons]
    refine wle_trans ?_ (ih _)
    rw [max_eq]; split
    · assumption
    · exact wle_refl a

theorem mem_le_foldl_max {l : List UInt64} {m : UInt64} (hm : m ∈ l) (a : UInt64) :
    m ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hm
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · refine wle_trans ?_ (le_foldl_max _ _)
      rw [max_eq]; split
      · exact wle_refl _
      · rename_i h; exact wle_of_not_le h
    · exact ih hm _

/-- A word of the list that is at least every word of the list is its largest word. -/
theorem largest_eq {l : List UInt64} {m : UInt64} (hm : m ∈ l) (hle : ∀ x ∈ l, x ≤ m) :
    largest l = m :=
  wle_antisymm (foldl_max_le (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _)) hle)
    (mem_le_foldl_max hm 0)

/-! ### Prefixes of arrays -/

theorem take_succ_of_get {b : Array UInt64} {n : Nat} (hn : n < b.size) :
    b.toList.take (n + 1) = b.toList.take n ++ [b[n]!] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hn), Option.toList_some,
    get_toList b hn]

theorem take_eq_of_agree {a b : Array UInt64} {n : Nat} (ha : n ≤ a.size) (hb : n ≤ b.size)
    (h : ∀ k, k < n → a[k]! = b[k]!) : a.toList.take n = b.toList.take n := by
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.length_take, Array.length_toList] at h1 h2
  have := h k (by omega)
  rw [get_toList a (by omega), get_toList b (by omega)] at this
  simpa using this

/-- Two permutations of each other that agree at `m` and beyond have prefixes `[0, m)` that are
permutations of each other. -/
theorem take_perm_of_frame {a b : Array UInt64} {m : Nat} (hs : a.size = b.size)
    (hp : a.toList.Perm b.toList) (ho : ∀ k, m ≤ k → a[k]! = b[k]!) :
    (a.toList.take m).Perm (b.toList.take m) := by
  have hd : a.toList.drop m = b.toList.drop m := by
    apply List.ext_getElem (by simp [hs])
    intro k h1 h2
    simp only [List.length_drop, Array.length_toList] at h1 h2
    have := ho (m + k) (by omega)
    rw [get_toList a (by omega), get_toList b (by omega)] at this
    simpa using this
  have h := hp
  rw [← List.take_append_drop m a.toList, ← List.take_append_drop m b.toList, hd] at h
  exact (List.perm_append_right_iff _).mp h

/-- The words of `h[0, j + 1)` are the root and the words of `h[0, j)` after the word at `j`
replaces the root. -/
theorem remove_perm (h : Array UInt64) (j : UInt64) (hj : j.toNat < h.size) :
    (h.toList.take (j.toNat + 1)).Perm (h[0]! :: (h.set! 0 h[j.toNat]!).toList.take j.toNat) := by
  have h0 : (0 : UInt64).toNat < h.size := by simp only [UInt64.reduceToNat]; omega
  have hs := swap_get h 0 j h0 hj
  simp only [UInt64.reduceToNat] at hs
  have hf : ((swap 0 j h).toList.take (j.toNat + 1)).Perm (h.toList.take (j.toNat + 1)) :=
    take_perm_of_frame (swap_size h 0 j) (swap_perm h 0 j h0 hj) fun k hk => by
      have h1 : k ≠ j.toNat := by omega
      have h2 : k ≠ 0 := by omega
      rw [hs k, ite_eq_right h1, ite_eq_right h2]
  have heq : (swap 0 j h).toList.take j.toNat = (h.set! 0 h[j.toNat]!).toList.take j.toNat :=
    take_eq_of_agree (by rw [swap_size]; omega) (by simp; omega) fun k hk => by
      have h1 : k ≠ j.toNat := by omega
      rw [hs k, ite_eq_right h1, get_set h 0 _ k (by omega)]
  rw [take_succ_of_get (by rw [swap_size]; exact hj), hs j.toNat, ite_eq_left rfl, heq] at hf
  exact hf.symm.trans (List.perm_append_singleton _ _)

/-! ### Moving a word up -/

theorem sub_one_toNat {n : UInt64} (h : 0 < n.toNat) : (n - 1).toNat = n.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat]; omega))]
  simp only [UInt64.reduceToNat]

theorem parent_toNat {i : UInt64} (h : 0 < i) :
    ((i - 1) / 2).toNat = (i.toNat - 1) / 2 ∧ 0 < i.toNat := by
  have h0 : 0 < i.toNat := by simpa using UInt64.lt_iff_toNat_lt.mp h
  refine ⟨?_, h0⟩
  rw [UInt64.toNat_div, sub_one_toNat h0]
  simp only [UInt64.reduceToNat]

/-- The sift up keeps the size, permutes the words, and leaves the words after `i`. -/
theorem siftUp_frame (i : UInt64) (a : Array UInt64) (hi : i.toNat < a.size) :
    (siftUp i a).size = a.size ∧ (siftUp i a).toList.Perm a.toList ∧
      ∀ k, i.toNat < k → (siftUp i a)[k]! = a[k]! := by
  rw [siftUp]
  by_cases h : 0 < i ∧ a[((i - 1) / 2).toNat]! < a[i.toNat]!
  · rw [ite_eq_left h]
    obtain ⟨hP, hi0⟩ := parent_toNat h.1
    have hpa : ((i - 1) / 2).toNat < a.size := by omega
    obtain ⟨hs, hp, ho⟩ := siftUp_frame ((i - 1) / 2) (swap ((i - 1) / 2) i a)
      (by rw [swap_size]; exact hpa)
    refine ⟨by rw [hs, swap_size], hp.trans (swap_perm a _ _ hpa hi), fun k hk => ?_⟩
    have h1 : k ≠ i.toNat := by omega
    have h2 : k ≠ ((i - 1) / 2).toNat := by omega
    rw [ho k (by omega), swap_get a _ _ hpa hi, ite_eq_right h1, ite_eq_right h2]
  · rw [ite_eq_right h]
    exact ⟨rfl, List.Perm.refl _, fun _ _ => rfl⟩
termination_by i.toNat
decreasing_by
  obtain ⟨_, _⟩ := parent_toNat h.1
  omega

/-- The invariant of an insertion: when the heap order on `a[0, m)` holds at every node except
between `i` and its parent, and the children of `i` are at most the parent of `i`, the sift up
makes `a[0, m)` a heap. -/
theorem siftUp_spec (m : Nat) (i : UInt64) (a : Array UInt64) (hm : m ≤ a.size)
    (hi : i.toNat < m)
    (hok : ∀ j, 0 < j → j < m → j ≠ i.toNat → a[j]! ≤ a[(j - 1) / 2]!)
    (hbr : 0 < i.toNat → ∀ j, 0 < j → j < m → (j - 1) / 2 = i.toNat →
      a[j]! ≤ a[(i.toNat - 1) / 2]!) :
    HeapFrom (siftUp i a) m 0 := by
  rw [siftUp]
  by_cases h : 0 < i ∧ a[((i - 1) / 2).toNat]! < a[i.toNat]!
  · rw [ite_eq_left h]
    obtain ⟨hP, hi0⟩ := parent_toNat h.1
    have hlt := h.2
    rw [hP] at hlt
    have hpa : ((i - 1) / 2).toNat < a.size := by omega
    have hia : i.toNat < a.size := by omega
    apply siftUp_spec m ((i - 1) / 2) (swap ((i - 1) / 2) i a) (by rw [swap_size]; exact hm)
      (by omega)
    · intro j hj0 hjm hjp
      rw [swap_get a _ _ hpa hia j, swap_get a _ _ hpa hia ((j - 1) / 2), hP]
      rw [hP] at hjp
      by_cases h1 : j = i.toNat
      · subst h1
        have h2 : ¬ (i.toNat - 1) / 2 = i.toNat := by omega
        rw [ite_eq_left rfl, ite_eq_right h2, ite_eq_left rfl]
        exact wle_of_lt hlt
      · rw [ite_eq_right h1, ite_eq_right hjp]
        by_cases h2 : (j - 1) / 2 = i.toNat
        · rw [ite_eq_left h2]
          exact hbr hi0 j hj0 hjm h2
        · rw [ite_eq_right h2]
          by_cases h3 : (j - 1) / 2 = (i.toNat - 1) / 2
          · rw [ite_eq_left h3]
            have := hok j hj0 hjm h1
            rw [h3] at this
            exact wle_trans this (wle_of_lt hlt)
          · rw [ite_eq_right h3]
            exact hok j hj0 hjm h1
    · intro hp0 j hj0 hjm hjp
      rw [swap_get a _ _ hpa hia j, swap_get a _ _ hpa hia ((((i - 1) / 2).toNat - 1) / 2), hP]
      rw [hP] at hjp hp0
      have hg1 : ¬ ((i.toNat - 1) / 2 - 1) / 2 = i.toNat := by omega
      have hg2 : ¬ ((i.toNat - 1) / 2 - 1) / 2 = (i.toNat - 1) / 2 := by omega
      have hjp' : ¬ j = (i.toNat - 1) / 2 := by omega
      rw [ite_eq_right hg1, ite_eq_right hg2]
      have hpg := hok ((i.toNat - 1) / 2) hp0 (by omega) (by omega)
      by_cases h1 : j = i.toNat
      · rw [ite_eq_left h1]
        exact hpg
      · rw [ite_eq_right h1, ite_eq_right hjp']
        have := hok j hj0 hjm h1
        rw [hjp] at this
        exact wle_trans this hpg
  · rw [ite_eq_right h]
    intro j hj0 hjm _
    by_cases hji : j = i.toNat
    · subst hji
      have hi0 : 0 < i := UInt64.lt_iff_toNat_lt.mpr (by simpa using hj0)
      obtain ⟨hP, -⟩ := parent_toNat hi0
      have := wle_of_not_lt fun hlt => h ⟨hi0, hlt⟩
      rwa [hP] at this
    · exact hok j hj0 hjm hji
termination_by i.toNat
decreasing_by
  obtain ⟨_, _⟩ := parent_toNat h.1
  omega

/-! ### Operations -/

/-- An insertion: the array `b` holds `h[0, n)` and then `v` at `n`.  The sift up makes
`[0, n + 1)` a heap whose words are those of the queue with `v` added. -/
theorem insert_spec (h b : Array UInt64) (n v : UInt64) (bag : List UInt64)
    (hnh : n.toNat ≤ h.size) (hheap : HeapFrom h n.toNat 0)
    (hp : (h.toList.take n.toNat).Perm bag) (hbs : n.toNat < b.size) (hbn : b[n.toNat]! = v)
    (hbk : ∀ k, k < n.toNat → b[k]! = h[k]!) :
    n.toNat + 1 ≤ (siftUp n b).size ∧ (siftUp n b).size = b.size ∧
      HeapFrom (siftUp n b) (n.toNat + 1) 0 ∧
      ((siftUp n b).toList.take (n.toNat + 1)).Perm (v :: bag) := by
  obtain ⟨hs, hperm, ho⟩ := siftUp_frame n b hbs
  refine ⟨by omega, hs, ?_, ?_⟩
  · apply siftUp_spec (n.toNat + 1) n b (by omega) (by omega)
    · intro j hj0 hjm hjn
      rw [hbk j (by omega), hbk ((j - 1) / 2) (by omega)]
      exact hheap j hj0 (by omega) (Nat.zero_le _)
    · intro _ j _ hjm hjp
      omega
  · have h1 := take_perm_of_frame (m := n.toNat + 1) hs hperm fun k hk => ho k (by omega)
    rw [take_succ_of_get hbs, hbn, take_eq_of_agree (by omega) hnh hbk] at h1
    exact h1.trans ((List.perm_append_singleton v _).trans (hp.cons v))

/-- A removal from a heap of `n > 0` words: the root is the largest word of the queue, and the
sift down of the last word from the root makes `[0, n - 1)` a heap whose words are those of the
queue with one copy of the root removed. -/
theorem remove_spec (h h2 : Array UInt64) (n : UInt64) (bag : List UInt64)
    (hh2 : h2 = h.set! 0 h[(n - 1).toNat]!) (hn0 : 0 < n.toNat) (hnh : n.toNat ≤ h.size)
    (hheap : HeapFrom h n.toNat 0) (hp : (h.toList.take n.toNat).Perm bag) :
    bag ≠ [] ∧ largest bag = h[0]! ∧ (n - 1).toNat ≤ (siftDown 0 (n - 1) h2).size ∧
      (siftDown 0 (n - 1) h2).size = h.size ∧
      HeapFrom (siftDown 0 (n - 1) h2) (n - 1).toNat 0 ∧
      ((siftDown 0 (n - 1) h2).toList.take (n - 1).toNat).Perm (bag.erase (largest bag)) := by
  have hn1 := sub_one_toNat hn0
  have h2s : h2.size = h.size := by simp [hh2]
  have hrm := remove_perm h (n - 1) (by omega)
  rw [← hh2, hn1, Nat.sub_add_cancel hn0] at hrm
  have hmem : h[0]! ∈ bag := hp.mem_iff.mp (hrm.mem_iff.mpr List.mem_cons_self)
  have hle : ∀ x ∈ bag, x ≤ h[0]! := fun x hx => by
    obtain ⟨k, hk, -, rfl⟩ := take_get_mem (hp.mem_iff.mpr hx)
    exact heap_root h n.toNat hheap k hk
  have hlarge : largest bag = h[0]! := largest_eq hmem hle
  obtain ⟨hs, hperm, ho, -⟩ := siftDown_frame (n - 1) 0 0 h2 (by omega)
  refine ⟨List.ne_nil_of_mem hmem, hlarge, by omega, by rw [hs, h2s], ?_, ?_⟩
  · apply siftDown_spec (n - 1) 0 0 h2 (by omega) (Nat.zero_le _)
    · intro j hj0 hjn _ hjp
      simp only [UInt64.reduceToNat] at hjp
      have hj : j ≠ 0 := by omega
      rw [hh2, get_set h 0 _ j (by omega), get_set h 0 _ ((j - 1) / 2) (by omega), ite_eq_right hj,
        ite_eq_right hjp]
      exact hheap j hj0 (by omega) (Nat.zero_le _)
    · intro h0
      simp at h0
  · rw [hlarge]
    have h3 := (hp.symm.trans hrm).erase h[0]!
    rw [List.erase_cons_head] at h3
    rw [hn1] at ho ⊢
    exact (take_perm_of_frame hs hperm ho).trans h3.symm

/-! ### The loop -/

/-- One operation of the list queue on its words and its outputs. -/
def specStep (st : List UInt64 × List UInt64) (o : UInt64 × UInt64) :
    List UInt64 × List UInt64 :=
  if o.1 = 0 then (o.2 :: st.1, st.2)
  else if st.1 = [] then st
  else (st.1.erase (largest st.1), st.2 ++ [largest st.1])

theorem runOps_eq (ops : List (UInt64 × UInt64)) (bag out : List UInt64) :
    runOps ops bag out = (ops.foldl specStep (bag, out)).2 := by
  induction ops generalizing bag out with
  | nil => rfl
  | cons o rest ih =>
    obtain ⟨op, v⟩ := o
    by_cases h0 : op = 0
    · simp [runOps, specStep, h0, ih]
    · by_cases hb : bag = []
      · simp [runOps, specStep, h0, hb, ih]
      · simp [runOps, specStep, h0, hb, ih]

/-- The state of the loop, the outputs, the heap's size, and the array, agrees with the state of
the list queue: `h[0, n)` is a heap whose words are a permutation of the queue's words, and the
outputs are equal. -/
def Agrees (s : Array UInt64 × UInt64 × Array UInt64) (st : List UInt64 × List UInt64) : Prop :=
  s.2.1.toNat ≤ s.2.2.size ∧ HeapFrom s.2.2 s.2.1.toNat 0 ∧
    (s.2.2.toList.take s.2.1.toNat).Perm st.1 ∧ s.1.toList = st.2

/-- One operation keeps the agreement and adds at most one word to the heap and to the array. -/
theorem step_agrees (op v : UInt64) (o h : Array UInt64) (n : UInt64) (bag out : List UInt64)
    (hA : Agrees (o, n, h) (bag, out)) (hh : h.size < 2 ^ 63) (hn : n.toNat < 2 ^ 63) :
    Agrees (step op v (o, n, h)) (specStep (bag, out) (op, v)) ∧
      (step op v (o, n, h)).2.1.toNat ≤ n.toNat + 1 ∧
      (step op v (o, n, h)).2.2.size ≤ h.size + 1 := by
  obtain ⟨hnh, hheap, hp, hout⟩ := hA
  dsimp only at hnh hheap hp hout
  unfold step specStep Agrees
  dsimp only
  by_cases hop : op = 0
  · subst hop
    have hS : h.size.toUInt64.toNat = h.size := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
    have hN1 : (n + 1).toNat = n.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
    have hc0 : ¬ (0 < (0 : UInt64) ∧ 0 < n) := fun hc => absurd hc.1 (by decide)
    obtain ⟨b, hb, hbs, hbn, hbk, hbsz⟩ : ∃ b,
        (if n < h.size.toUInt64 then h.set! n.toNat v else h.push v) = b ∧ n.toNat < b.size ∧
          b[n.toNat]! = v ∧ (∀ k, k < n.toNat → b[k]! = h[k]!) ∧ b.size ≤ h.size + 1 := by
      by_cases hc : n < h.size.toUInt64
      · have hc' : n.toNat < h.size := by rw [UInt64.lt_iff_toNat_lt, hS] at hc; exact hc
        rw [ite_eq_left hc]
        refine ⟨_, rfl, by simp; omega, by rw [get_set h _ v _ hc', ite_eq_left rfl], fun k hk => ?_,
          by simp⟩
        rw [get_set h _ v _ hc', ite_eq_right (Nat.ne_of_lt hk)]
      · have hc' : n.toNat = h.size := by
          rw [UInt64.lt_iff_toNat_lt, hS] at hc; omega
        rw [ite_eq_right hc]
        exact ⟨_, rfl, by simp; omega, by rw [hc', push_get_size],
          fun k hk => push_get_lt h v (by omega), by simp⟩
    rw [ite_eq_right hc0, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, hb]
    obtain ⟨h1, h2, h3, h4⟩ := insert_spec h b n v bag hnh hheap hp hbs hbn hbk
    rw [hN1]
    exact ⟨⟨h1, h3, h4, hout⟩, le_refl _, by omega⟩
  · have hop' : 0 < op := by
      rcases Nat.eq_zero_or_pos op.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hop
      · exact UInt64.lt_iff_toNat_lt.mpr (by simpa using h0)
    by_cases hn0 : 0 < n
    · have hn0' : 0 < n.toNat := by simpa using UInt64.lt_iff_toNat_lt.mp hn0
      have hn1 := sub_one_toNat hn0'
      obtain ⟨hne, hlarge, h1, h2, h3, h4⟩ := remove_spec h _ n bag rfl hn0' hnh hheap hp
      rw [ite_eq_left (show 0 < op ∧ 0 < n from ⟨hop', hn0⟩), ite_eq_right hop, ite_eq_left hn0, ite_eq_right hop, ite_eq_left hn0, ite_eq_right hop,
        ite_eq_right hne]
      simp only [UInt64.reduceToNat]
      refine ⟨⟨h1, h3, h4, ?_⟩, by omega, by omega⟩
      rw [Array.toList_push, hout, hlarge]
    · have hn0' : n.toNat = 0 := by
        have : ¬ (0 : UInt64).toNat < n.toNat := fun hc => hn0 (UInt64.lt_iff_toNat_lt.mpr hc)
        simp only [UInt64.reduceToNat] at this; omega
      have hb : bag = [] := List.nil_perm.mp (by rw [hn0', List.take_zero] at hp; exact hp)
      rw [ite_eq_right (show ¬ (0 < op ∧ 0 < n) from fun hc => hn0 hc.2), ite_eq_right hop, ite_eq_right hn0, ite_eq_right hop, ite_eq_right hn0, ite_eq_right hop,
        ite_eq_left hb]
      exact ⟨⟨hnh, hheap, hp, hout⟩, by omega, by omega⟩

theorem heapQueue_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    heapQueue xs = expected xs := by
  have hN : (xs.size.toUInt64 / 2).toNat = xs.size / 2 := by
    rw [UInt64.toNat_div]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have h := loop_induction (n := xs.size.toUInt64 / 2)
    (init := ((#[] : Array UInt64), (0 : UInt64), (#[] : Array UInt64)))
    (f := fun i s => step xs[(i + i).toNat]! xs[(i + i + 1).toNat]! s)
    (P := fun k s => Agrees s (((operations xs).take k).foldl specStep ([], [])) ∧
      s.2.1.toNat ≤ k ∧ s.2.2.size ≤ k)
    ⟨⟨by simp, fun j _ hj _ => absurd hj (by simp), by simp, by simp⟩, by simp, by simp⟩
    (by
      intro k s hk ⟨hA, hn, hh⟩
      rw [hN] at hk
      have hkk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
      have h1 : (UInt64.ofNat k + UInt64.ofNat k).toNat = 2 * k := by
        simp only [UInt64.toNat_add, hkk]; omega
      have h2 : (UInt64.ofNat k + UInt64.ofNat k + 1).toNat = 2 * k + 1 := by
        simp only [UInt64.toNat_add, hkk, UInt64.reduceToNat]; omega
      have htake : (operations xs).take (k + 1) =
          (operations xs).take k ++ [(xs[2 * k]!, xs[2 * k + 1]!)] := by
        rw [List.take_add_one]
        simp [operations, hk]
      rw [h1, h2, htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize ((operations xs).take k).foldl specStep ([], []) = st at hA
      obtain ⟨bag, out⟩ := st
      obtain ⟨o, n, a⟩ := s
      dsimp only at hn hh
      obtain ⟨hA', h1', h2'⟩ := step_agrees _ _ o a n bag out hA (by omega) (by omega)
      exact ⟨hA', by omega, by omega⟩)
  rw [hN, List.take_of_length_le (by simp [operations])] at h
  obtain ⟨⟨-, -, -, hout⟩, -, -⟩ := h
  unfold heapQueue expected
  rw [runOps_eq, ← hout, Array.toArray_toList]

end Library.Queues.BinaryHeap
