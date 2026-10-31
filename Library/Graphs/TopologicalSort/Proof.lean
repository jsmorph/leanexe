import Library.Graphs.TopologicalSort.Program
import Library.Graphs.TopologicalSort.Spec
import LeanExe.Dialect.Lemmas
import Mathlib.Data.Finset.Card

/-! The proof that topological sorting returns a topological order, or the empty array when none
exists.  `count r P` counts the indices below `r` that satisfy `P`, and `pend xs done k` counts the
relations into `k` whose first vertex is not among the words of `done`.  The invariant of the main
loop, `OuterInv`, states that the queue holds distinct vertices, that every relation into a queued
vertex starts at an earlier queued vertex, that the count of each vertex is `pend` of the processed
prefix of the queue, and that a vertex is queued exactly when its count is 0.  When the queue holds
every vertex it is a topological order.  Otherwise every vertex outside the queue has a predecessor
outside it, and the first such vertex in any order would follow its predecessor, so no topological
order exists. -/

namespace Library.Graphs.TopologicalSort

open LeanExe.Dialect

/-! ### Arrays and counts -/

theorem get_set (c : Array UInt64) (i : Nat) (v : UInt64) (k : Nat) (hi : i < c.size) :
    (c.set! i v)[k]! = if k = i then v else c[k]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hk : k < c.size
  · rw [getElem!_pos _ k (by simpa using hk), Array.getElem_setIfInBounds hk, getElem!_pos c k hk]
    by_cases h : k = i <;> simp_all [eq_comm]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg c k hk]
    have : k ≠ i := by omega
    simp [this]

/-- The number of indices below `r` that satisfy `P`. -/
def count (r : Nat) (P : Nat → Bool) : Nat := ((List.range r).filter P).length

theorem count_zero (P : Nat → Bool) : count 0 P = 0 := by simp [count]

theorem count_succ (r : Nat) (P : Nat → Bool) :
    count (r + 1) P = count r P + (if P r then 1 else 0) := by
  unfold count
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : P r <;> simp [h]

theorem count_le_count (r : Nat) {P Q : Nat → Bool} (h : ∀ e, e < r → P e = true → Q e = true) :
    count r P ≤ count r Q := by
  induction r with
  | zero => simp [count_zero]
  | succ r ih =>
    rw [count_succ, count_succ]
    have := ih fun e he => h e (by omega)
    by_cases hp : P r = true
    · rw [if_pos hp, if_pos (h r (by omega) hp)]; omega
    · rw [if_neg hp]; split <;> omega

theorem count_le_succ (r : Nat) (P : Nat → Bool) : count r P ≤ count (r + 1) P := by
  rw [count_succ]; omega

theorem count_mono {r r' : Nat} (h : r ≤ r') (P : Nat → Bool) : count r P ≤ count r' P := by
  induction r' with
  | zero => rw [Nat.le_zero.mp h]
  | succ r' ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (count_le_succ r' P)
    · rw [h]

theorem count_pos {r : Nat} {P : Nat → Bool} (h : 0 < count r P) : ∃ e, e < r ∧ P e = true := by
  induction r with
  | zero => simp [count_zero] at h
  | succ r ih =>
    rw [count_succ] at h
    by_cases hp : P r = true
    · exact ⟨r, by omega, hp⟩
    · rw [if_neg hp] at h
      obtain ⟨e, he, hpe⟩ := ih (by omega)
      exact ⟨e, by omega, hpe⟩

/-- When every index that satisfies `P` satisfies `Q` and the counts agree, every index that
satisfies `Q` satisfies `P`. -/
theorem count_eq_imp {r : Nat} {P Q : Nat → Bool} (h : ∀ e, e < r → P e = true → Q e = true)
    (heq : count r Q = count r P) : ∀ e, e < r → Q e = true → P e = true := by
  induction r with
  | zero => intro e he; omega
  | succ r ih =>
    rw [count_succ, count_succ] at heq
    have hle := count_le_count r (P := P) (Q := Q) fun e he => h e (by omega)
    intro e he hq
    by_cases hr : e = r
    · subst hr
      by_contra hp
      rw [if_pos hq, if_neg hp] at heq
      omega
    · have hPQ : (if P r = true then 1 else 0) ≤ (if Q r = true then 1 else 0) := by
        by_cases hp : P r = true
        · rw [if_pos hp, if_pos (h r (by omega) hp)]
        · rw [if_neg hp]; omega
      exact ih (fun e' he' => h e' (by omega)) (by omega) e (by omega) hq

/-! ### Relations and the input -/

/-- The relations into `k` whose first vertex is not a word of `done`. -/
def pend (xs : Array UInt64) (done : List UInt64) (k : Nat) : Nat :=
  count (relationCount xs) fun e => decide (target xs e = k) && !(done.contains xs[2 * e + 1]!)

theorem n_eq (xs : Array UInt64) : (xs[(0 : UInt64).toNat]!).toNat = vertexCount xs := rfl

theorem m_eq (xs : Array UInt64) (h0 : 0 < xs.size) (hsize : xs.size < 2 ^ 64) :
    ((xs.size.toUInt64 - 1) / 2).toNat = relationCount xs := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [UInt64.toNat_div, UInt64.toNat_sub, hN, UInt64.reduceToNat, relationCount]
  congr 1
  omega

theorem index1 {e : Nat} (he : 2 * e + 2 < 2 ^ 64) :
    (UInt64.ofNat e + UInt64.ofNat e + 1).toNat = 2 * e + 1 := by
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

theorem index2 {e : Nat} (he : 2 * e + 2 < 2 ^ 64) :
    (UInt64.ofNat e + UInt64.ofNat e + 2).toNat = 2 * e + 2 := by
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

theorem count_le (r : Nat) (P : Nat → Bool) : count r P ≤ r := by
  induction r with
  | zero => simp [count_zero]
  | succ r ih => rw [count_succ]; split <;> omega

/-- A count splits over a predicate that is the disjunction of two disjoint ones. -/
theorem count_split (r : Nat) {P Q R : Nat → Bool} (h : ∀ e, Q e = (P e || R e))
    (hdis : ∀ e, ¬ (P e = true ∧ R e = true)) : count r Q = count r P + count r R := by
  induction r with
  | zero => simp [count_zero]
  | succ r ih =>
    rw [count_succ, count_succ, count_succ, ih, h r]
    have := hdis r
    by_cases hp : P r = true <;> by_cases hr : R r = true <;> simp_all <;> omega

/-- For `v` outside `L`, the relations into `k` from outside `L` are those from outside `L ++ [v]`
and those from `v`. -/
theorem pend_append (xs : Array UInt64) (L : List UInt64) (v : UInt64) (hv : v ∉ L) (k : Nat) :
    pend xs (L ++ [v]) k +
      count (relationCount xs) (fun e => decide (target xs e = k) && xs[2 * e + 1]! == v) =
      pend xs L k := by
  unfold pend
  rw [count_split (relationCount xs)
    (Q := fun e => decide (target xs e = k) && !(L.contains xs[2 * e + 1]!))
    (P := fun e => decide (target xs e = k) && !((L ++ [v]).contains xs[2 * e + 1]!))
    (R := fun e => decide (target xs e = k) && xs[2 * e + 1]! == v)]
  · intro e
    by_cases ht : target xs e = k <;> by_cases hs : xs[2 * e + 1]! = v
    · subst hs; simp [ht, hv]
    · simp [ht, hs]
    · simp [ht]
    · simp [ht]
  · intro e ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1 h2
    have : (L ++ [v]).contains xs[2 * e + 1]! = true := by simp [h2.2]
    rw [this] at h1
    exact absurd h1.2 (by decide)

/-! ### Lists of distinct vertices -/

theorem nodup_length_le (l : List UInt64) (N : Nat) (hn : l.Nodup)
    (hb : ∀ x ∈ l, x.toNat < N) : l.length ≤ N := by
  have hmap : (l.map UInt64.toNat).Nodup := hn.map fun a b h => UInt64.toNat_inj.mp h
  have hsub : (l.map UInt64.toNat).toFinset ⊆ Finset.range N := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simpa using hb a ha
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hmap, List.length_map, Finset.card_range] at this
  exact this

theorem nodup_covers (l : List UInt64) (N : Nat) (hn : l.Nodup)
    (hb : ∀ x ∈ l, x.toNat < N) (hl : l.length = N) : ∀ k, k < N → ∃ x ∈ l, x.toNat = k := by
  have hmap : (l.map UInt64.toNat).Nodup := hn.map fun a b h => UInt64.toNat_inj.mp h
  have hsub : (l.map UInt64.toNat).toFinset ⊆ Finset.range N := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simpa using hb a ha
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hmap, List.length_map, Finset.card_range, hl])
  intro k hk
  have : k ∈ (l.map UInt64.toNat).toFinset := by rw [heq]; simpa using hk
  simp only [List.mem_toFinset, List.mem_map] at this
  exact this

theorem mem_iff_get (q : Array UInt64) (x : UInt64) :
    x ∈ q.toList ↔ ∃ p, p < q.size ∧ q[p]! = x := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
    simp only [Array.length_toList] at hp
    exact ⟨p, hp, by rw [getElem!_pos q p hp]; simp⟩
  · rintro ⟨p, hp, rfl⟩
    rw [getElem!_pos q p hp]
    exact Array.getElem_mem_toList hp

/-! ### The counts and the initial queue -/

theorem countPredecessors_spec (xs : Array UInt64) (hv : Valid xs) (hsize : xs.size < 2 ^ 64) :
    (countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2)).size =
        vertexCount xs ∧
      ∀ k, k < vertexCount xs →
        (countPredecessors xs xs[(0 : UInt64).toNat]!
          ((xs.size.toUInt64 - 1) / 2))[k]!.toNat = pend xs [] k := by
  have hm := m_eq xs hv.1 hsize
  have hM : relationCount xs = (xs.size - 1) / 2 := rfl
  unfold countPredecessors
  have h := loop_induction (n := (xs.size.toUInt64 - 1) / 2)
    (init := LeanExe.build xs[(0 : UInt64).toNat]! fun _ => (0 : UInt64))
    (f := fun e cnt => cnt.set! (xs[(e + e + 2).toNat]!).toNat
      (cnt[(xs[(e + e + 2).toNat]!).toNat]! + 1))
    (P := fun e cnt => cnt.size = vertexCount xs ∧
      ∀ k, k < vertexCount xs → cnt[k]!.toNat = count e (fun e' => decide (target xs e' = k)))
    ⟨by rw [build_size]; rfl,
      fun k hk => by rw [build_get (by rw [n_eq]; exact hk), count_zero]; rfl⟩
    (by
      intro e cnt he ⟨hs, hk⟩
      rw [hm] at he
      have h2 : 2 * e + 2 < 2 ^ 64 := by omega
      have ht := (hv.2.2 e he).2
      refine ⟨by rw [Array.size_set!, hs], fun k hkN => ?_⟩
      show (cnt.set! (xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat
        (cnt[(xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat]! + 1))[k]!.toNat = _
      rw [index2 h2]
      have htw : (xs[2 * e + 2]!).toNat = target xs e := rfl
      rw [htw, get_set _ _ _ _ (by rw [hs]; exact ht), count_succ]
      by_cases hke : k = target xs e
      · rw [if_pos hke, ← hke, UInt64.toNat_add, hk k hkN,
          if_pos (show decide (k = k) = true by simp)]
        have := count_le e (fun e' => decide (target xs e' = k))
        simp only [UInt64.reduceToNat]
        omega
      · rw [if_neg hke, hk k hkN]
        have : ¬ (decide (target xs e = k) = true) := by simp; omega
        rw [if_neg this]; omega)
  rw [hm] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [h.2 k hk]
  unfold pend
  simp

theorem initialQueue_spec (c : Array UInt64) (n : UInt64) :
    (initialQueue c n).toList =
      ((List.range n.toNat).filter fun v => c[v]! == 0).map UInt64.ofNat := by
  unfold initialQueue
  exact loop_induction (n := n) (init := (#[] : Array UInt64))
    (f := fun v q => if c[v.toNat]! == 0 then q.push v else q)
    (P := fun v q => q.toList = ((List.range v).filter fun u => c[u]! == 0).map UInt64.ofNat)
    (by simp)
    (by
      intro v q hv hq
      have hvv : (UInt64.ofNat v).toNat = v :=
        UInt64.toNat_ofNat_of_lt' (show v < 2 ^ 64 by have := UInt64.toNat_lt n; omega)
      show (if c[(UInt64.ofNat v).toNat]! == 0 then q.push (UInt64.ofNat v) else q).toList = _
      rw [hvv, List.range_succ, List.filter_append, List.map_append]
      by_cases h0 : (c[v]! == 0) = true
      · rw [if_pos h0, Array.toList_push, hq]; simp [h0]
      · rw [if_neg h0, hq]; simp [h0])

/-! ### Queues -/

/-- Vertex `k` is in the queue `q`. -/
def InQueue (q : Array UInt64) (k : Nat) : Prop := ∃ x ∈ q.toList, x.toNat = k

theorem get_toList (q : Array UInt64) {p : Nat} (hp : p < q.size) :
    q[p]! = q.toList[p]'(by simpa using hp) := by
  rw [getElem!_pos q p hp]; simp

theorem get_prefix {q Q0 : Array UInt64} {R : List UInt64} (h : q.toList = Q0.toList ++ R)
    {p : Nat} (hp : p < Q0.size) : q[p]! = Q0[p]! := by
  have hq : p < q.size := by
    have := congrArg List.length h; simp at this; omega
  rw [get_toList q hq, get_toList Q0 hp]
  simp only [h]
  rw [List.getElem_append_left]

theorem push_get_lt (q : Array UInt64) (x : UInt64) {p : Nat} (hp : p < q.size) :
    (q.push x)[p]! = q[p]! := by
  rw [getElem!_pos _ p (by simp; omega), getElem!_pos q p hp, Array.getElem_push_lt]

theorem push_get_size (q : Array UInt64) (x : UInt64) : (q.push x)[q.size]! = x := by
  rw [getElem!_pos _ q.size (by simp), Array.getElem_push_eq]

theorem take_get_mem {Q0 : Array UInt64} {f : Nat} {x : UInt64}
    (h : x ∈ Q0.toList.take f) : ∃ p, p < f ∧ p < Q0.size ∧ Q0[p]! = x := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_take, Array.length_toList] at hp
  refine ⟨p, by omega, by omega, ?_⟩
  rw [get_toList Q0 (by omega)]
  simp

theorem not_mem_take {Q0 : Array UInt64} (hnd : Q0.toList.Nodup) {f : Nat} (hf : f < Q0.size) :
    Q0[f]! ∉ Q0.toList.take f := by
  intro h
  obtain ⟨p, hpf, hp, heq⟩ := take_get_mem h
  rw [get_toList Q0 hp, get_toList Q0 hf] at heq
  have := (List.Nodup.getElem_inj_iff hnd).mp heq
  omega

theorem take_succ_prefix {Q0 : Array UInt64} {R : List UInt64} {f : Nat} (hf : f < Q0.size) :
    (Q0.toList ++ R).take (f + 1) = Q0.toList.take f ++ [Q0[f]!] := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hf), get_toList Q0 hf]
  rfl

/-- The facts about the queue that both loops keep. -/
structure QueueInv (xs q : Array UInt64) : Prop where
  lt : ∀ x ∈ q.toList, x.toNat < vertexCount xs
  nodup : q.toList.Nodup
  topo : ∀ e, e < relationCount xs → ∀ p, p < q.size → q[p]!.toNat = target xs e →
    ∃ p', p' < p ∧ q[p']! = xs[2 * e + 1]!

/-- The invariant of the main loop after `f` steps. -/
def OuterInv (xs : Array UInt64) (f : Nat) (c q : Array UInt64) : Prop :=
  c.size = vertexCount xs ∧ QueueInv xs q ∧
    (∀ k, k < vertexCount xs → c[k]!.toNat = pend xs (q.toList.take f) k) ∧
    (∀ k, k < vertexCount xs → (InQueue q k ↔ c[k]! = 0))

/-- The relations into `k` from `v` among the first `e`. -/
def fromV (xs : Array UInt64) (v : UInt64) (e k : Nat) : Nat :=
  count e fun e' => decide (target xs e' = k) && xs[2 * e' + 1]! == v

/-- The invariant of the scan for the vertex `Q0[f]` after `e` relations. -/
def InnerInv (xs : Array UInt64) (f : Nat) (Q0 : Array UInt64) (e : Nat) (c q : Array UInt64) :
    Prop :=
  c.size = vertexCount xs ∧ QueueInv xs q ∧ (∃ R, q.toList = Q0.toList ++ R) ∧
    (∀ k, k < vertexCount xs →
      c[k]!.toNat + fromV xs Q0[f]! e k = pend xs (Q0.toList.take f) k) ∧
    (∀ k, k < vertexCount xs → (InQueue q k ↔ c[k]! = 0))

theorem fromV_succ (xs : Array UInt64) (v : UInt64) (e k : Nat) :
    fromV xs v (e + 1) k =
      fromV xs v e k + (if target xs e = k ∧ xs[2 * e + 1]! = v then 1 else 0) := by
  unfold fromV
  rw [count_succ]
  by_cases h : target xs e = k ∧ xs[2 * e + 1]! = v
  · rw [if_pos (by simp [h.1, h.2]), if_pos h]
  · rw [if_neg (by simp; intro h1 h2; exact h ⟨h1, h2⟩), if_neg h]

theorem fromV_le_pend (xs : Array UInt64) (hv : Valid xs) (v : UInt64) (L : List UInt64)
    (hvL : v ∉ L) (k : Nat) : fromV xs v (relationCount xs) k ≤ pend xs L k := by
  unfold fromV pend
  apply count_le_count
  intro e _ h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨h.1, ?_⟩
  simp only [List.contains_eq_mem, decide_eq_false_iff_not]
  rw [h.2]; exact hvL

/-- One step of the scan keeps its invariant. -/
theorem inner_step (xs : Array UInt64) (hv : Valid xs) (f : Nat) (Q0 : Array UInt64)
    (hf : f < Q0.size) (hQ0 : Q0.toList.Nodup) (e : Nat) (he : e < relationCount xs)
    (c q : Array UInt64) (h : InnerInv xs f Q0 e c q) :
    InnerInv xs f Q0 (e + 1)
      (if xs[2 * e + 1]! == q[f]! then
        (if c[(xs[2 * e + 2]!).toNat]! == 1 then
          (c.set! (xs[2 * e + 2]!).toNat 0, q.push xs[2 * e + 2]!)
        else (c.set! (xs[2 * e + 2]!).toNat (c[(xs[2 * e + 2]!).toNat]! - 1), q))
      else (c, q)).1
      (if xs[2 * e + 1]! == q[f]! then
        (if c[(xs[2 * e + 2]!).toNat]! == 1 then
          (c.set! (xs[2 * e + 2]!).toNat 0, q.push xs[2 * e + 2]!)
        else (c.set! (xs[2 * e + 2]!).toNat (c[(xs[2 * e + 2]!).toNat]! - 1), q))
      else (c, q)).2 := by
  obtain ⟨hcs, hq, ⟨R, hR⟩, hcnt, hzero⟩ := h
  have hv' : q[f]! = Q0[f]! := get_prefix hR hf
  have hvL := not_mem_take hQ0 hf
  have hkN := (hv.2.2 e he).2
  have hkw : (xs[2 * e + 2]!).toNat = target xs e := rfl
  rw [hkw]
  by_cases hsrc : xs[2 * e + 1]! = Q0[f]!
  · rw [if_pos (by simp [hsrc, hv'])]
    have hbound := fromV_le_pend xs hv Q0[f]! _ hvL (target xs e)
    have hmono := count_mono (show e + 1 ≤ relationCount xs by omega)
      (fun e' => decide (target xs e' = target xs e) && xs[2 * e' + 1]! == Q0[f]!)
    have hsucc := fromV_succ xs Q0[f]! e (target xs e)
    rw [if_pos ⟨rfl, hsrc⟩] at hsucc
    have hck := hcnt _ hkN
    unfold fromV at hbound hsucc
    have hc1 : 1 ≤ (c[target xs e]!).toNat := by unfold fromV at hck; omega
    by_cases h1 : c[target xs e]! = 1
    · rw [if_pos (by simp [h1])]
      have hc0 : pend xs (Q0.toList.take f) (target xs e) =
          fromV xs Q0[f]! (e + 1) (target xs e) := by
        have : (c[target xs e]!).toNat = 1 := by rw [h1]; rfl
        unfold fromV at hck ⊢; omega
      -- every relation into the vertex from outside the processed prefix starts at `Q0[f]`
      have hall : ∀ e', e' < relationCount xs → target xs e' = target xs e →
          xs[2 * e' + 1]! ∉ Q0.toList.take f → xs[2 * e' + 1]! = Q0[f]! := by
        intro e' he' ht' hn'
        have heq : count (relationCount xs)
            (fun e' => decide (target xs e' = target xs e) &&
              !((Q0.toList.take f).contains xs[2 * e' + 1]!)) =
            count (relationCount xs)
              (fun e' => decide (target xs e' = target xs e) && xs[2 * e' + 1]! == Q0[f]!) := by
          unfold pend fromV at *; omega
        have := count_eq_imp (P := fun e' => decide (target xs e' = target xs e) &&
            xs[2 * e' + 1]! == Q0[f]!) (Q := fun e' => decide (target xs e' = target xs e) &&
            !((Q0.toList.take f).contains xs[2 * e' + 1]!))
          (fun e'' _ h'' => by
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h''
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              List.contains_eq_mem, decide_eq_false_iff_not]
            exact ⟨h''.1, by rw [h''.2]; exact hvL⟩) heq e' he'
          (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
                List.contains_eq_mem, decide_eq_false_iff_not]; exact ⟨ht', hn'⟩)
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
        exact this.2
      have hnotin : ¬ InQueue q (target xs e) := fun hin =>
        absurd ((hzero _ hkN).mp hin) (by rw [h1]; decide)
      refine ⟨by rw [Array.size_set!, hcs], ⟨?_, ?_, ?_⟩, ⟨R ++ [xs[2 * e + 2]!], ?_⟩, ?_, ?_⟩
      · intro x hx
        rw [Array.toList_push, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hq.lt x hx
        · simp at hx; rw [hx]; exact hkN
      · rw [Array.toList_push, List.nodup_append]
        refine ⟨hq.nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
        simp at hb
        intro hab
        exact hnotin ⟨a, ha, by rw [hab, hb]; rfl⟩
      · intro e' he' p hp ht'
        simp only [Array.size_push] at hp
        by_cases hpq : p < q.size
        · rw [push_get_lt q _ hpq] at ht'
          obtain ⟨p', hp', hget⟩ := hq.topo e' he' p hpq ht'
          exact ⟨p', hp', by rw [push_get_lt q _ (by omega)]; exact hget⟩
        · have hpe : p = q.size := by omega
          subst hpe
          rw [push_get_size] at ht'
          have ht'' : target xs e' = target xs e := by rw [← ht']; rfl
          have hQq : Q0.size ≤ q.size := by
            have := congrArg List.length hR; simp at this; omega
          by_cases hmem : xs[2 * e' + 1]! ∈ Q0.toList.take f
          · obtain ⟨p', hpf, hp', hget⟩ := take_get_mem hmem
            exact ⟨p', by omega, by rw [push_get_lt q _ (by omega), get_prefix hR hp']; exact hget⟩
          · have := hall e' he' ht'' hmem
            exact ⟨f, by omega, by rw [push_get_lt q _ (by omega), hv']; exact this.symm⟩
      · rw [Array.toList_push, hR, List.append_assoc]
      · intro k hk
        rw [get_set _ _ _ _ (by rw [hcs]; exact hkN), fromV_succ]
        by_cases hke : k = target xs e
        · subst hke
          rw [if_pos rfl, if_pos ⟨rfl, hsrc⟩]
          have := hcnt _ hk
          unfold fromV at this ⊢
          simp only [UInt64.toNat_zero]
          have : (c[target xs e]!).toNat = 1 := by rw [h1]; rfl
          omega
        · rw [if_neg hke, if_neg (fun h' => hke h'.1.symm)]
          exact hcnt k hk
      · intro k hk
        rw [get_set _ _ _ _ (by rw [hcs]; exact hkN)]
        by_cases hke : k = target xs e
        · rw [if_pos hke]
          refine ⟨fun _ => rfl, fun _ => ⟨xs[2 * e + 2]!, by simp, hke.symm⟩⟩
        · rw [if_neg hke, ← hzero k hk]
          constructor
          · rintro ⟨x, hx, hxk⟩
            rw [Array.toList_push, List.mem_append] at hx
            rcases hx with hx | hx
            · exact ⟨x, hx, hxk⟩
            · simp at hx; subst hx; exact absurd hxk.symm hke
          · rintro ⟨x, hx, hxk⟩
            exact ⟨x, by rw [Array.toList_push]; exact List.mem_append_left _ hx, hxk⟩
    · rw [if_neg (by simp [h1])]
      have hc2 : 2 ≤ (c[target xs e]!).toNat := by
        have : (c[target xs e]!).toNat ≠ 1 := fun h' => h1 (UInt64.toNat_inj.mp (by rw [h']; rfl))
        omega
      have hsub : (c[target xs e]! - 1).toNat = (c[target xs e]!).toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      refine ⟨by rw [Array.size_set!, hcs], hq, ⟨R, hR⟩, ?_, ?_⟩
      · intro k hk
        rw [get_set _ _ _ _ (by rw [hcs]; exact hkN), fromV_succ]
        by_cases hke : k = target xs e
        · subst hke
          rw [if_pos rfl, if_pos ⟨rfl, hsrc⟩, hsub]
          have := hcnt _ hk
          omega
        · rw [if_neg hke, if_neg (fun h' => hke h'.1.symm)]
          exact hcnt k hk
      · intro k hk
        rw [get_set _ _ _ _ (by rw [hcs]; exact hkN)]
        by_cases hke : k = target xs e
        · subst hke
          rw [if_pos rfl]
          constructor
          · intro hin
            exact absurd ((hzero _ hk).mp hin)
              (fun h0 => by rw [h0] at hc2; simp at hc2)
          · intro h0
            have := congrArg UInt64.toNat h0
            rw [hsub] at this
            simp at this; omega
        · rw [if_neg hke]; exact hzero k hk
  · rw [if_neg (by simp [hv']; exact hsrc)]
    refine ⟨hcs, hq, ⟨R, hR⟩, fun k hk => ?_, hzero⟩
    rw [fromV_succ, if_neg (fun h' => hsrc h'.2)]
    exact hcnt k hk

theorem vertexCount_lt (xs : Array UInt64) : vertexCount xs < 2 ^ 64 := UInt64.toNat_lt _

theorem loop_zero {α : Type} (s : α) (g : UInt64 → α → α) : LeanExe.loop 0 s g = s :=
  loop_induction (n := 0) (init := s) (f := g) (P := fun _ t => t = s) rfl
    (fun k _ hk _ => absurd hk (by simp))

theorem queue_size_le (xs q : Array UInt64) (hq : QueueInv xs q) : q.size ≤ vertexCount xs := by
  have := nodup_length_le q.toList (vertexCount xs) hq.nodup hq.lt
  simpa using this

/-- One step of the main loop keeps its invariant. -/
theorem outer_step (xs : Array UInt64) (hv : Valid xs) (hsize : xs.size < 2 ^ 64) (f : Nat)
    (hf : f < vertexCount xs) (c q : Array UInt64) (h : OuterInv xs f c q) :
    let s := LeanExe.loop (if UInt64.ofNat f < q.size.toUInt64 then (xs.size.toUInt64 - 1) / 2
        else 0) (c, q) fun e t =>
      if xs[(e + e + 1).toNat]! == t.2[(UInt64.ofNat f).toNat]! then
        if t.1[(xs[(e + e + 2).toNat]!).toNat]! == 1 then
          (t.1.set! (xs[(e + e + 2).toNat]!).toNat 0, t.2.push xs[(e + e + 2).toNat]!)
        else
          (t.1.set! (xs[(e + e + 2).toNat]!).toNat (t.1[(xs[(e + e + 2).toNat]!).toNat]! - 1),
            t.2)
      else t
    OuterInv xs (f + 1) s.1 s.2 := by
  intro s
  obtain ⟨hcs, hq, hcnt, hzero⟩ := h
  have hN := UInt64.toNat_lt (xs[(0 : UInt64).toNat]!)
  have hqN := queue_size_le xs q hq
  have hff : (UInt64.ofNat f).toNat = f :=
    UInt64.toNat_ofNat_of_lt' (show f < 2 ^ 64 by have := vertexCount_lt xs; omega)
  have hqs : q.size.toUInt64.toNat = q.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; have := vertexCount_lt xs; omega
  by_cases hfq : f < q.size
  · have hc : UInt64.ofNat f < q.size.toUInt64 := by
      rw [UInt64.lt_iff_toNat_lt, hff, hqs]; exact hfq
    have hm := m_eq xs hv.1 hsize
    have hM : relationCount xs = (xs.size - 1) / 2 := rfl
    have hinner := loop_induction (n := (xs.size.toUInt64 - 1) / 2) (init := (c, q))
      (f := fun e t =>
        if xs[(e + e + 1).toNat]! == t.2[(UInt64.ofNat f).toNat]! then
          if t.1[(xs[(e + e + 2).toNat]!).toNat]! == 1 then
            (t.1.set! (xs[(e + e + 2).toNat]!).toNat 0, t.2.push xs[(e + e + 2).toNat]!)
          else
            (t.1.set! (xs[(e + e + 2).toNat]!).toNat (t.1[(xs[(e + e + 2).toNat]!).toNat]! - 1),
              t.2)
        else t)
      (P := fun e t => InnerInv xs f q e t.1 t.2)
      ⟨hcs, hq, ⟨[], by simp⟩, fun k hk => by rw [hcnt k hk]; unfold fromV; simp [count_zero],
        hzero⟩
      (by
        intro e t he ht
        rw [hm] at he
        have h2 : 2 * e + 2 < 2 ^ 64 := by omega
        show InnerInv xs f q (e + 1)
          (if xs[(UInt64.ofNat e + UInt64.ofNat e + 1).toNat]! == t.2[(UInt64.ofNat f).toNat]! then
            if t.1[(xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat]! == 1 then
              (t.1.set! (xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat 0,
                t.2.push xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!)
            else
              (t.1.set! (xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat
                (t.1[(xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat]! - 1), t.2)
          else t).1
          (if xs[(UInt64.ofNat e + UInt64.ofNat e + 1).toNat]! == t.2[(UInt64.ofNat f).toNat]! then
            if t.1[(xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat]! == 1 then
              (t.1.set! (xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat 0,
                t.2.push xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!)
            else
              (t.1.set! (xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat
                (t.1[(xs[(UInt64.ofNat e + UInt64.ofNat e + 2).toNat]!).toNat]! - 1), t.2)
          else t).2
        rw [index1 h2, index2 h2, hff]
        exact inner_step xs hv f q hfq hq.nodup e he t.1 t.2 ht)
    rw [hm] at hinner
    show OuterInv xs (f + 1) (LeanExe.loop (if UInt64.ofNat f < q.size.toUInt64 then
      (xs.size.toUInt64 - 1) / 2 else 0) (c, q) _).1 (LeanExe.loop (if UInt64.ofNat f <
      q.size.toUInt64 then (xs.size.toUInt64 - 1) / 2 else 0) (c, q) _).2
    rw [if_pos hc]
    obtain ⟨hcs', hq', ⟨R, hR⟩, hcnt', hzero'⟩ := hinner
    refine ⟨hcs', hq', fun k hk => ?_, hzero'⟩
    have hpa := pend_append xs (q.toList.take f) q[f]! (not_mem_take hq.nodup hfq) k
    have := hcnt' k hk
    unfold fromV at this
    rw [hR, take_succ_prefix hfq]
    omega
  · have hc : ¬ UInt64.ofNat f < q.size.toUInt64 := by
      rw [UInt64.lt_iff_toNat_lt, hff, hqs]; exact hfq
    show OuterInv xs (f + 1) (LeanExe.loop (if UInt64.ofNat f < q.size.toUInt64 then
      (xs.size.toUInt64 - 1) / 2 else 0) (c, q) _).1 (LeanExe.loop (if UInt64.ofNat f <
      q.size.toUInt64 then (xs.size.toUInt64 - 1) / 2 else 0) (c, q) _).2
    rw [if_neg hc, loop_zero]
    refine ⟨hcs, hq, fun k hk => ?_, hzero⟩
    rw [hcnt k hk, List.take_of_length_le (by simp; omega),
      List.take_of_length_le (by simp; omega)]

/-- The invariant holds at the start of the main loop. -/
theorem outer_init (xs : Array UInt64) (hv : Valid xs) (hsize : xs.size < 2 ^ 64) :
    OuterInv xs 0 (countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2))
      (initialQueue (countPredecessors xs xs[(0 : UInt64).toNat]!
        ((xs.size.toUInt64 - 1) / 2)) xs[(0 : UInt64).toNat]!) := by
  obtain ⟨hcs, hcnt⟩ := countPredecessors_spec xs hv hsize
  set c := countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2)
  have hq := initialQueue_spec c xs[(0 : UInt64).toNat]!
  have hN := UInt64.toNat_lt (xs[(0 : UInt64).toNat]!)
  have hnN : (xs[(0 : UInt64).toNat]!).toNat = vertexCount xs := rfl
  rw [hnN] at hq
  have hmem : ∀ x, x ∈ (initialQueue c xs[(0 : UInt64).toNat]!).toList ↔
      ∃ v, (v < vertexCount xs ∧ c[v]! = 0) ∧ UInt64.ofNat v = x := by
    intro x; rw [hq]; simp
  have hofNat : ∀ v, v < vertexCount xs → (UInt64.ofNat v).toNat = v := fun v hv' =>
    UInt64.toNat_ofNat_of_lt' (show v < 2 ^ 64 by have := vertexCount_lt xs; omega)
  have hinq : ∀ k, k < vertexCount xs →
      (InQueue (initialQueue c xs[(0 : UInt64).toNat]!) k ↔ c[k]! = 0) := by
    intro k hk
    constructor
    · rintro ⟨x, hx, hxk⟩
      obtain ⟨v, ⟨hvN, hv0⟩, rfl⟩ := (hmem x).mp hx
      rw [hofNat v hvN] at hxk; subst hxk; exact hv0
    · intro h0
      exact ⟨UInt64.ofNat k, (hmem _).mpr ⟨k, ⟨hk, h0⟩, rfl⟩, hofNat k hk⟩
  refine ⟨hcs, ⟨?_, ?_, ?_⟩, fun k hk => by rw [hcnt k hk]; simp, hinq⟩
  · intro x hx
    obtain ⟨v, ⟨hvN, _⟩, rfl⟩ := (hmem x).mp hx
    rw [hofNat v hvN]; exact hvN
  · rw [hq]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_range.filter _)
    simp only [List.mem_filter, List.mem_range] at ha hb
    rw [← hofNat a ha.1, ← hofNat b hb.1, hab]
  · intro e he p hp ht
    exfalso
    have hx : (initialQueue c xs[(0 : UInt64).toNat]!)[p]! ∈
        (initialQueue c xs[(0 : UInt64).toNat]!).toList := by
      rw [get_toList _ hp]; exact List.getElem_mem _
    have hzero := (hinq (target xs e) (hv.2.2 e he).2).mp ⟨_, hx, ht⟩
    have hpos := hcnt (target xs e) (hv.2.2 e he).2
    rw [hzero] at hpos
    have : 0 < pend xs [] (target xs e) := by
      unfold pend
      have := count_mono (show e + 1 ≤ relationCount xs by omega)
        (fun e' => decide (target xs e' = target xs e) && !(([] : List UInt64).contains xs[2 * e' + 1]!))
      rw [count_succ] at this
      simp at this ⊢
      omega
    simp at hpos; omega

/-- At the end of the main loop the invariant holds with every step taken. -/
theorem process_spec (xs : Array UInt64) (hv : Valid xs) (hsize : xs.size < 2 ^ 64) :
    OuterInv xs (vertexCount xs)
      (process xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2)
        (countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2))
        (initialQueue (countPredecessors xs xs[(0 : UInt64).toNat]!
          ((xs.size.toUInt64 - 1) / 2)) xs[(0 : UInt64).toNat]!)).1
      (process xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2)
        (countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2))
        (initialQueue (countPredecessors xs xs[(0 : UInt64).toNat]!
          ((xs.size.toUInt64 - 1) / 2)) xs[(0 : UInt64).toNat]!)).2 := by
  unfold process
  exact loop_induction (P := fun f (s : Array UInt64 × Array UInt64) => OuterInv xs f s.1 s.2)
    (outer_init xs hv hsize) (fun f s hf hs => outer_step xs hv hsize f hf s.1 s.2 hs)

/-- On a well-formed input, the result is a topological order, or it is the empty array and no
topological order exists. -/
theorem topoSort_spec (xs : Array UInt64) (hv : Valid xs) (hsize : xs.size < 2 ^ 64) :
    IsTopologicalOrder xs (topoSort xs) ∨
      (topoSort xs = #[] ∧ ∀ order, ¬ IsTopologicalOrder xs order) := by
  have hpos : xs.size.toUInt64 ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', UInt64.toNat_zero] at this
    have := hv.1; omega
  have hspec := process_spec xs hv hsize
  unfold topoSort
  rw [if_neg hpos]
  simp only []
  generalize process xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2)
    (countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2))
    (initialQueue (countPredecessors xs xs[(0 : UInt64).toNat]! ((xs.size.toUInt64 - 1) / 2))
      xs[(0 : UInt64).toNat]!) = st at hspec ⊢
  obtain ⟨hcs, hq, hcnt, hzero⟩ := hspec
  have hqN := queue_size_le xs st.2 hq
  have hN := UInt64.toNat_lt (xs[(0 : UInt64).toNat]!)
  have hnN : (xs[(0 : UInt64).toNat]!).toNat = vertexCount xs := rfl
  have hqs : st.2.size.toUInt64.toNat = st.2.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; have := vertexCount_lt xs; omega
  have htake : st.2.toList.take (vertexCount xs) = st.2.toList :=
    List.take_of_length_le (by simp; omega)
  by_cases hfull : st.2.size.toUInt64 = xs[(0 : UInt64).toNat]!
  · rw [if_pos hfull]
    left
    have hsz : st.2.size = vertexCount xs := by
      rw [← hqs, ← hnN, hfull]
    refine ⟨hsz, fun p hp => hq.lt _ (by rw [get_toList _ hp]; exact List.getElem_mem _),
      fun p p' hpp hp' hsame => ?_, fun e he p p' hp hp' hps hpt => ?_⟩
    · rw [get_toList _ (by omega), get_toList _ hp'] at hsame
      have := (List.Nodup.getElem_inj_iff hq.nodup).mp hsame
      omega
    · obtain ⟨p'', hp'', hget⟩ := hq.topo e he p' hp' hpt
      have hw : st.2[p]! = xs[2 * e + 1]! := UInt64.toNat_inj.mp hps
      rw [← hw, get_toList _ (by omega), get_toList _ hp] at hget
      have := (List.Nodup.getElem_inj_iff hq.nodup).mp hget
      omega
  · rw [if_neg hfull]
    right
    refine ⟨rfl, fun O ⟨hOs, hOlt, hOd, hOrel⟩ => ?_⟩
    have hsz : st.2.size ≠ vertexCount xs := fun h =>
      hfull (UInt64.toNat_inj.mp (by rw [hqs, hnN, h]))
    -- every vertex outside the queue has a predecessor outside it
    have hpred : ∀ u, u < vertexCount xs → ¬ InQueue st.2 u →
        ∃ e, e < relationCount xs ∧ target xs e = u ∧ ¬ InQueue st.2 (source xs e) := by
      intro u hu hnot
      have hc : st.1[u]! ≠ 0 := fun h0 => hnot ((hzero u hu).mpr h0)
      have hcu := hcnt u hu
      rw [htake] at hcu
      have : 0 < pend xs st.2.toList u := by
        rw [← hcu]
        have : (st.1[u]!).toNat ≠ 0 := fun h' => hc (UInt64.toNat_inj.mp (by rw [h']; rfl))
        omega
      obtain ⟨e, he, hP⟩ := count_pos this
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hP
      refine ⟨e, he, hP.1, fun ⟨x, hx, hxs⟩ => hP.2 ?_⟩
      have : x = xs[2 * e + 1]! := UInt64.toNat_inj.mp hxs
      rw [← this]; exact hx
    -- the order covers every vertex
    have hOnd : O.toList.Nodup := by
      rw [List.nodup_iff_injective_get]
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [List.get_eq_getElem, Array.length_toList] at hij hi hj
      by_contra hne
      have hne' : i ≠ j := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact hOd i j h hj (by rw [get_toList O hi, get_toList O hj]; exact hij)
      · exact hOd j i h hi (by rw [get_toList O hi, get_toList O hj] at *; exact hij.symm)
    have hcov := nodup_covers O.toList (vertexCount xs) hOnd
      (fun x hx => by
        obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
        simp only [Array.length_toList] at hp
        have := hOlt p hp
        rwa [get_toList O hp] at this) (by simpa using hOs)
    have hpos : ∀ k, k < vertexCount xs → ∃ p, p < O.size ∧ O[p]!.toNat = k := by
      intro k hk
      obtain ⟨x, hx, hxk⟩ := hcov k hk
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
      simp only [Array.length_toList] at hp
      exact ⟨p, hp, by rw [get_toList O hp]; exact hxk⟩
    -- some vertex is outside the queue
    have hmiss : ∃ u, u < vertexCount xs ∧ ¬ InQueue st.2 u := by
      by_contra hall
      push_neg at hall
      have hsub : Finset.range (vertexCount xs) ⊆ (st.2.toList.map UInt64.toNat).toFinset := by
        intro u hu
        obtain ⟨x, hx, hxu⟩ := hall u (by simpa using hu)
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨x, hx, hxu⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      have := Nat.le_trans this (List.toFinset_card_le _)
      simp at this
      omega
    -- the first vertex outside the queue in the order would follow its predecessor
    have key : ∀ p, p < O.size → ¬ InQueue st.2 O[p]!.toNat → False := by
      intro p
      induction p using Nat.strong_induction_on with
      | _ p ih =>
        intro hp hnot
        obtain ⟨e, he, ht, hs⟩ := hpred _ (by have := hOlt p hp; exact this) hnot
        obtain ⟨p1, hp1, hO1⟩ := hpos (source xs e) (hv.2.2 e he).1
        have hlt := hOrel e he p1 p hp1 hp hO1 ht.symm
        exact ih p1 hlt hp1 (by rw [hO1]; exact hs)
    obtain ⟨u, hu, hnot⟩ := hmiss
    obtain ⟨p, hp, hOp⟩ := hpos u hu
    exact key p hp (by rw [hOp]; exact hnot)

end Library.Graphs.TopologicalSort
