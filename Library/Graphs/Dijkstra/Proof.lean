import Library.Graphs.Dijkstra.Heap
import Library.Graphs.Dijkstra.Spec
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas

/-! The proof that `dijkstra` returns the least walk lengths.  A tentative length below `2^64 - 1`
is the length of a walk, every vertex that is not done and has a tentative length below `2^64 - 1`
has an entry with that length in the heap, every entry's key is at least the tentative length of its
vertex, the vertices that are done have their least lengths, and the arcs out of them are relaxed.
When the entry with the least key leaves the heap and its vertex is not done, every walk to that
vertex shorter than `2^64 - 1` leaves the done vertices by a relaxed arc to a vertex whose entry is
in the heap with a key at most the walk's length, so the vertex's tentative length is the least.
Each vertex is done once and pushes at most one entry for each position of its range, so the
`first[n]` steps of the loop empty the heap, and then a vertex that is not done has no walk shorter
than `2^64 - 1`. -/

namespace Library.Graphs.Dijkstra

open LeanExe.Dialect

/-- `x`, or `2^64 - 1` when `x` is `2^64 - 1` or more. -/
def sat (x : Nat) : Nat := if x < 2 ^ 64 - 1 then x else 2 ^ 64 - 1

theorem INF_toNat : INF.toNat = 2 ^ 64 - 1 := by unfold INF; rfl

theorem addSat_toNat (a b : UInt64) : (addSat a b).toNat = sat (a.toNat + b.toNat) := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hsub : (INF - b).toNat = 2 ^ 64 - 1 - b.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [INF_toNat]; omega)),
      INF_toNat]
  unfold addSat sat
  by_cases h : a < INF - b
  · rw [ite_eq_left h]
    have h' := UInt64.lt_iff_toNat_lt.mp h
    rw [hsub] at h'
    rw [ite_eq_left (show a.toNat + b.toNat < 2 ^ 64 - 1 by omega), UInt64.toNat_add]
    omega
  · rw [ite_eq_right h, INF_toNat]
    have h' : ¬a.toNat < 2 ^ 64 - 1 - b.toNat := fun h'' =>
      h (UInt64.lt_iff_toNat_lt.mpr (by rw [hsub]; exact h''))
    rw [ite_eq_right (show ¬a.toNat + b.toNat < 2 ^ 64 - 1 by omega)]

theorem sat_le (x : Nat) : sat x ≤ x := by unfold sat; split <;> omega

theorem sat_lt {x : Nat} (h : sat x < 2 ^ 64 - 1) : sat x = x := by
  unfold sat at *; split at h <;> simp_all

/-- The tentative length of `v`. -/
abbrev D (dist : Array UInt64) (v : Nat) : Nat := dist[v]!.toNat

/-- The number of positions in the range of `u`, at least the number of arcs out of `u`. -/
abbrev deg (first : Array UInt64) (u : Nat) : Nat := first[u + 1]!.toNat - first[u]!.toNat

/-! ### Walks -/

section Walks

variable {N : Nat} {first heads lens : Array UInt64} {s : Nat}

theorem walk_lt {v L : Nat} (h : Walk N first heads lens s v L) : v < N := by
  cases h with
  | start hs => exact hs
  | step _ ha => exact ha.2.1

theorem walk_src {v L : Nat} (h : Walk N first heads lens s v L) : s < N := by
  induction h with
  | start hs => exact hs
  | step _ _ ih => exact ih

/-- A walk from a done vertex to a vertex that is not done leaves the done vertices by an arc from
a done vertex `y` to a vertex `x` that is not done, at a length `Ly + w` at most the walk's. -/
theorem walk_exit (done : Nat → Prop) {v L : Nat} (h : Walk N first heads lens s v L)
    (hs : done s) (hv : ¬done v) :
    ∃ y x w Ly, Walk N first heads lens s y Ly ∧ done y ∧ Arc N first heads lens y x w ∧
      ¬done x ∧ Ly + w ≤ L := by
  induction h with
  | start _ => exact absurd hs hv
  | @step u v w L hw ha ih =>
    by_cases hu : done u
    · exact ⟨u, v, w, L, hw, hu, ha, hv, le_rfl⟩
    · obtain ⟨y, x, w', Ly, h1, h2, h3, h4, h5⟩ := ih hu
      exact ⟨y, x, w', Ly, h1, h2, h3, h4, by omega⟩

end Walks

/-! ### The forward star -/

theorem first_mono {N : Nat} {first heads lens : Array UInt64}
    (hwf : WellFormed N first heads lens) :
    ∀ d u, u + d ≤ N → first[u]!.toNat ≤ first[u + d]!.toNat
  | 0, _, _ => le_rfl
  | d + 1, u, h => by
    have := first_mono hwf d u (by omega)
    have h2 := UInt64.le_iff_toNat_le.mp (hwf.2.1 (u + d) (by omega))
    rw [← Nat.add_assoc]
    omega

/-- Under the request's form, an arc out of `u` is a position of `u`'s range. -/
theorem arc_iff {N : Nat} {first heads lens : Array UInt64} (hwf : WellFormed N first heads lens)
    {u v w : Nat} (hu : u < N) :
    Arc N first heads lens u v w ↔ v < N ∧ ∃ j, j < deg first u ∧
      heads[first[u]!.toNat + j]!.toNat = v ∧ lens[first[u]!.toNat + j]!.toNat = w := by
  have hm := first_mono hwf (N - (u + 1)) (u + 1) (by omega)
  rw [show u + 1 + (N - (u + 1)) = N by omega] at hm
  have hle := UInt64.le_iff_toNat_le.mp (hwf.2.1 u hu)
  have hh1 := hwf.2.2.1
  have hl1 := hwf.2.2.2
  simp only [deg]
  constructor
  · rintro ⟨_, hv, k, hk1, hk2, _, _, hh, hl⟩
    have e : first[u]!.toNat + (k - first[u]!.toNat) = k := by omega
    exact ⟨hv, k - first[u]!.toNat, by omega, by rw [e]; exact hh, by rw [e]; exact hl⟩
  · rintro ⟨hv, j, hj, hh, hl⟩
    exact ⟨hu, hv, first[u]!.toNat + j, by omega, by omega, by omega, by omega, hh, hl⟩

/-! ### Relaxation -/

/-- The state of `relax` for `u` after `t` positions of its range, from the tentative lengths
`dist` and the heap `hk`, `hv` of `h` entries: the arrays keep their sizes, the heap is in order
and holds at most `h + t` entries, the lengths only fall, the length of `u` stays, the arcs at the
first `t` positions are relaxed, a fallen length is the length of `u` plus an arc, and the heap
holds its old entries and new entries `E`.  Each entry of `E` has a vertex below `N` and a key below
`2^64 - 1`, at least the tentative length of its vertex and at least the length of `u`, and `E`
holds the fallen length of each fallen vertex. -/
def RelaxInv (N : Nat) (first heads lens dist hk hv : Array UInt64) (h : UInt64) (u t : Nat)
    (st : Array UInt64 × Array UInt64 × Array UInt64 × UInt64) : Prop :=
  st.1.size = N ∧ st.2.1.size = hk.size ∧ st.2.2.1.size = hv.size ∧
    MinHeap st.2.1 st.2.2.2.toNat ∧ st.2.2.2.toNat ≤ h.toNat + t ∧
    (∀ v, D st.1 v ≤ D dist v) ∧ D st.1 u = D dist u ∧
    (∀ j < t, heads[first[u]!.toNat + j]!.toNat < N →
      D st.1 heads[first[u]!.toNat + j]!.toNat ≤
        sat (D dist u + lens[first[u]!.toNat + j]!.toNat)) ∧
    (∀ v, D st.1 v < D dist v → ∃ w, Arc N first heads lens u v w ∧ D st.1 v = D dist u + w) ∧
    ∃ E : List (UInt64 × UInt64),
      (pairs st.2.1 st.2.2.1 st.2.2.2.toNat).Perm (pairs hk hv h.toNat ++ E) ∧
      (∀ e ∈ E, e.2.toNat < N ∧ D st.1 e.2.toNat ≤ e.1.toNat ∧ e.1.toNat < 2 ^ 64 - 1 ∧
        D dist u ≤ e.1.toNat) ∧
      ∀ v, D st.1 v < D dist v → (st.1[v]!, UInt64.ofNat v) ∈ E

theorem sat_ge {x y : Nat} (hxy : x ≤ y) (hx : x ≤ 2 ^ 64 - 1) : x ≤ sat y := by
  unfold sat; split <;> omega

/-- `relax` for `u` relaxes the arcs out of `u`. -/
theorem relax_spec (n u : UInt64) (first heads lens dist hk hv : Array UInt64) (h : UInt64)
    (hwf : WellFormed n.toNat first heads lens) (hu : u.toNat < n.toNat)
    (hds : dist.size = n.toNat) (hh : MinHeap hk h.toNat)
    (hcap : h.toNat + deg first u.toNat ≤ hk.size)
    (hcap' : h.toNat + deg first u.toNat ≤ hv.size) (hks : hk.size < 2 ^ 64) :
    RelaxInv n.toNat first heads lens dist hk hv h u.toNat (deg first u.toNat)
      (relax n u first heads lens dist hk hv h) := by
  have hn := UInt64.toNat_lt n
  have hu1 : (u + 1).toNat = u.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  have hab := hwf.2.1 u.toNat hu
  have hab' := UInt64.le_iff_toNat_le.mp hab
  have hb64 := UInt64.toNat_lt first[u.toNat + 1]!
  have hcount : (if first[u.toNat]! ≤ first[(u + 1).toNat]! then
      first[(u + 1).toNat]! - first[u.toNat]! else 0).toNat = deg first u.toNat := by
    rw [hu1, ite_eq_left hab, UInt64.toNat_sub_of_le _ _ hab]
  have hloop := loop_induction
    (n := if first[u.toNat]! ≤ first[(u + 1).toNat]! then first[(u + 1).toNat]! - first[u.toNat]!
      else 0)
    (init := (dist, hk, hv, h))
    (f := fun t s =>
      let v := heads[(first[u.toNat]! + t).toNat]!
      let nd := addSat s.1[u.toNat]! lens[(first[u.toNat]! + t).toNat]!
      if v < n ∧ nd < s.1[v.toNat]! then
        let hu := siftUp s.2.2.2 (s.2.1.set! s.2.2.2.toNat nd) (s.2.2.1.set! s.2.2.2.toNat v)
        (s.1.set! v.toNat nd, hu.1, hu.2, s.2.2.2 + 1)
      else s)
    (fun t st => RelaxInv n.toNat first heads lens dist hk hv h u.toNat t st)
    ⟨hds, rfl, rfl, hh, Nat.le_add_right _ _, fun _ => le_rfl, rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun v hv' => absurd hv' (lt_irrefl _), [],
      by simp, by simp, fun v hv' => absurd hv' (lt_irrefl _)⟩
    (by
      intro t st ht hinv
      rw [hcount] at ht
      have ht' : t < first[u.toNat + 1]!.toNat - first[u.toNat]!.toNat := ht
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, E, sE1, sE2, sE3⟩ := hinv
      have hkt : (first[u.toNat]! + UInt64.ofNat t).toNat = first[u.toNat]!.toNat + t := by
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
        omega
      dsimp only
      rw [hkt]
      generalize hvdef : heads[first[u.toNat]!.toNat + t]! = v at *
      generalize hwdef : lens[first[u.toNat]!.toNat + t]! = w at *
      have hnd : (addSat st.1[u.toNat]! w).toNat = sat (D dist u.toNat + w.toNat) := by
        rw [addSat_toNat]
        simp only [D] at s7
        rw [s7]
      by_cases hc : v < n ∧ addSat st.1[u.toNat]! w < st.1[v.toNat]!
      · rw [ite_eq_left hc]
        have hvn := UInt64.lt_iff_toNat_lt.mp hc.1
        have hlt : sat (D dist u.toNat + w.toNat) < D st.1 v.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp hc.2
          rw [hnd] at this
          exact this
        have hdv := UInt64.toNat_lt st.1[v.toNat]!
        have hdu := UInt64.toNat_lt dist[u.toNat]!
        have hsatlt : sat (D dist u.toNat + w.toNat) < 2 ^ 64 - 1 := by
          simp only [D] at hlt ⊢; omega
        have hsat := sat_lt hsatlt
        have hvu : v.toNat ≠ u.toNat := by
          intro e
          have h1 := sat_ge (show D dist u.toNat ≤ D dist u.toNat + w.toNat by omega)
            (by simp only [D]; omega)
          have h2 : D st.1 v.toNat = D dist u.toNat := by rw [e]; exact s7
          omega
        have hc1 : h.toNat + (first[u.toNat + 1]!.toNat - first[u.toNat]!.toNat) ≤ hk.size := hcap
        have hc2 : h.toNat + (first[u.toNat + 1]!.toNat - first[u.toNat]!.toNat) ≤ hv.size :=
          hcap'
        have hcapt : st.2.2.2.toNat < st.2.1.size := by rw [s2]; omega
        have hcapt' : st.2.2.2.toNat < st.2.2.1.size := by rw [s3]; omega
        obtain ⟨p1, p2, p3, p4⟩ := push_spec st.2.1 st.2.2.1 st.2.2.2 (addSat st.1[u.toNat]! w) v
          s4 hcapt hcapt'
        have hh1 : (st.2.2.2 + 1).toNat = st.2.2.2.toNat + 1 := by
          simp only [UInt64.toNat_add, UInt64.reduceToNat]
          have := UInt64.toNat_lt st.2.2.2
          omega
        have hD : ∀ x, D (st.1.set! v.toNat (addSat st.1[u.toNat]! w)) x =
            if x = v.toNat then sat (D dist u.toNat + w.toNat) else D st.1 x := by
          intro x
          simp only [D]
          rw [get_set st.1 _ _ x (by rw [s1]; exact hvn)]
          split
          · exact hnd
          · rfl
        have hDle : ∀ x, D (st.1.set! v.toNat (addSat st.1[u.toNat]! w)) x ≤ D st.1 x := by
          intro x
          rw [hD]
          split
          · rename_i e
            rw [e]
            exact le_of_lt hlt
          · exact le_rfl
        refine ⟨by rw [Array.size_set!, s1], by rw [p1, s2], by rw [p2, s3], by rw [hh1]; exact p3,
          by rw [hh1]; omega, fun x => le_trans (hDle x) (s6 x), ?_, fun j hj hjn => ?_,
          fun x hx => ?_, E ++ [(addSat st.1[u.toNat]! w, v)], ?_, fun e he => ?_,
          fun x hx => ?_⟩
        · rw [hD, ite_eq_right (Ne.symm hvu)]
          exact s7
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact le_trans (hDle _) (s8 j hj hjn)
          · refine le_of_eq ?_
            rw [hvdef, hwdef, hD, ite_eq_left rfl]
        · rw [hD] at hx ⊢
          split at hx
          · rename_i e
            rw [ite_eq_left e]
            refine ⟨w.toNat, ?_, hsat⟩
            rw [e]
            exact (arc_iff hwf hu).mpr ⟨hvn, t, ht, by rw [hvdef], by rw [hwdef]⟩
          · rename_i e
            rw [ite_eq_right e]
            exact s9 x hx
        · rw [hh1]
          exact p4.trans ((sE1.append_right _).trans (List.Perm.of_eq (List.append_assoc _ _ _)))
        · rcases List.mem_append.mp he with he | he
          · obtain ⟨e1, e2, e3, e4⟩ := sE2 e he
            exact ⟨e1, le_trans (hDle _) e2, e3, e4⟩
          · rw [List.mem_singleton] at he
            subst he
            refine ⟨hvn, by rw [hD, ite_eq_left rfl, hnd], by rw [hnd]; exact hsatlt,
              by rw [hnd, hsat]; omega⟩
        · rw [hD] at hx
          split at hx
          · rename_i e
            subst e
            refine List.mem_append_right _ (List.mem_singleton.mpr ?_)
            rw [UInt64.ofNat_toNat, get_set st.1 _ _ _ (by rw [s1]; exact hvn), ite_eq_left rfl]
          · rename_i e
            refine List.mem_append_left _ ?_
            rw [get_set st.1 _ _ x (by rw [s1]; exact hvn), ite_eq_right e]
            exact sE3 x hx
      · rw [ite_eq_right hc]
        refine ⟨s1, s2, s3, s4, by omega, s6, s7, fun j hj hjn => ?_, s9, E, sE1, sE2, sE3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact s8 j hj hjn
        · rw [hvdef] at hjn
          rw [hvdef, hwdef]
          have hvn : v < n := UInt64.lt_iff_toNat_lt.mpr hjn
          have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp fun h' => hc ⟨hvn, h'⟩)
          rw [hnd] at this
          exact this)
  rw [hcount] at hloop
  exact hloop

/-- After `relax` for `u`, every arc out of `u` is relaxed. -/
theorem relax_arcs (n u : UInt64) (first heads lens dist hk hv : Array UInt64) (h : UInt64)
    (hwf : WellFormed n.toNat first heads lens) (hu : u.toNat < n.toNat)
    {st : Array UInt64 × Array UInt64 × Array UInt64 × UInt64}
    (hst : RelaxInv n.toNat first heads lens dist hk hv h u.toNat (deg first u.toNat) st) :
    ∀ v w, Arc n.toNat first heads lens u.toNat v w → D st.1 v ≤ sat (D dist u.toNat + w) := by
  intro v w ha
  obtain ⟨hv, j, hj, hh, hl⟩ := (arc_iff hwf hu).mp ha
  have := hst.2.2.2.2.2.2.2.1 j hj (by rw [hh]; exact hv)
  rwa [hh, hl] at this

/-! ### The main loop -/

/-- The number of positions in the ranges of the done vertices below `K`. -/
def degSum (first : Array UInt64) (done : Array Bool) : Nat → Nat
  | 0 => 0
  | K + 1 => degSum first done K + if done[K]! = true then deg first K else 0

theorem degSum_le {N : Nat} {first heads lens : Array UInt64}
    (hwf : WellFormed N first heads lens) (done : Array Bool) (K : Nat) (hK : K ≤ N) :
    degSum first done K ≤ first[K]!.toNat - first[0]!.toNat := by
  induction K with
  | zero => simp [degSum]
  | succ K ih =>
    have h1 := first_mono hwf K 0 (by omega)
    have h2 := UInt64.le_iff_toNat_le.mp (hwf.2.1 K (by omega))
    rw [Nat.zero_add] at h1
    have := ih (by omega)
    simp only [degSum, deg]
    split <;> omega

theorem degSum_set (first : Array UInt64) (done : Array Bool) (u : Nat) (hu : u < done.size)
    (hd : ¬done[u]! = true) (K : Nat) :
    degSum first (done.set! u true) K =
      degSum first done K + if u < K then deg first u else 0 := by
  induction K with
  | zero => simp [degSum]
  | succ K ih =>
    simp only [degSum]
    rw [ih, get_set done u true K hu]
    by_cases hK : K = u
    · subst hK
      simp [hd]
    · rw [ite_eq_right hK]
      by_cases h1 : u < K
      · rw [ite_eq_left h1, ite_eq_left (show u < K + 1 by omega)]
        omega
      · rw [ite_eq_right h1, ite_eq_right (show ¬u < K + 1 by omega)]
        omega

theorem degSum_none (first : Array UInt64) (done : Array Bool) (K : Nat)
    (h : ∀ v < K, ¬done[v]! = true) : degSum first done K = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simp [degSum, ih fun v hv => h v (by omega), h K (by omega)]

/-- The state of the main loop after `k` steps, with the tentative lengths `dist`, the heap `hk`,
`hv` of `h` entries, and the done vertices: the arrays keep their sizes, the heap is in order, the
heap is empty or its entries and the steps taken number at most the positions in the ranges of the
done vertices, the source is done, a tentative length below `2^64 - 1` is the length of a walk, the
length of a done vertex is the least, the arcs out of the done vertices are relaxed, every entry's
vertex is below `N` and its key is below `2^64 - 1` and at least the tentative length of its
vertex, and every vertex that is not done and has a tentative length below `2^64 - 1` has an entry
with that length. -/
def MainInv (N S : Nat) (first heads lens : Array UInt64) (k : Nat) (dist hk hv : Array UInt64)
    (h : UInt64) (done : Array Bool) : Prop :=
  dist.size = N ∧ hk.size = first[N]!.toNat ∧ hv.size = first[N]!.toNat ∧ done.size = N ∧
    MinHeap hk h.toNat ∧ (h.toNat = 0 ∨ h.toNat + k ≤ degSum first done N) ∧ done[S]! = true ∧
    (∀ v < N, D dist v < 2 ^ 64 - 1 → Walk N first heads lens S v (D dist v)) ∧
    (∀ v < N, done[v]! = true → ∀ L, Walk N first heads lens S v L → D dist v ≤ L) ∧
    (∀ y < N, done[y]! = true → ∀ x w, Arc N first heads lens y x w →
      D dist x ≤ sat (D dist y + w)) ∧
    (∀ e ∈ pairs hk hv h.toNat,
      e.2.toNat < N ∧ D dist e.2.toNat ≤ e.1.toNat ∧ e.1.toNat < 2 ^ 64 - 1) ∧
    ∀ v < N, ¬done[v]! = true → D dist v < 2 ^ 64 - 1 →
      (dist[v]!, UInt64.ofNat v) ∈ pairs hk hv h.toNat

/-- A walk shorter than `2^64 - 1` to a vertex that is not done leaves the done vertices by a
relaxed arc, so the heap holds an entry whose key is at most the walk's length. -/
theorem exit_entry {N S k : Nat} {first heads lens dist hk hv : Array UInt64} {h : UInt64}
    {done : Array Bool} (hq : MainInv N S first heads lens k dist hk hv h done) {v L : Nat}
    (hw : Walk N first heads lens S v L) (hnd : ¬done[v]! = true) (hL : L < 2 ^ 64 - 1) :
    ∃ x, D dist x ≤ L ∧ (dist[x]!, UInt64.ofNat x) ∈ pairs hk hv h.toNat := by
  obtain ⟨-, -, -, -, -, -, i7, -, i9, i10, -, i12⟩ := hq
  obtain ⟨y, x, w, Ly, hy, hyd, ha, hxd, hle⟩ :=
    walk_exit (fun v => done[v]! = true) hw i7 hnd
  have h1 := i9 y (walk_lt hy) hyd Ly hy
  have h2 := i10 y (walk_lt hy) hyd x w ha
  have h3 := sat_le (D dist y + w)
  exact ⟨x, by omega, i12 x ha.2.1 hxd (by omega)⟩

/-- One step of the main loop of `dijkstra`. -/
def settle (n : UInt64) (first heads lens : Array UInt64)
    (q : Array UInt64 × Array UInt64 × Array UInt64 × UInt64 × Array Bool) :
    Array UInt64 × Array UInt64 × Array UInt64 × UInt64 × Array Bool :=
  if 0 < q.2.2.2.1 then
    let u := q.2.2.1[(0 : UInt64).toNat]!
    let h := q.2.2.2.1 - 1
    let heap := siftDown 0 h (q.2.1.set! (0 : UInt64).toNat q.2.1[h.toNat]!)
      (q.2.2.1.set! (0 : UInt64).toNat q.2.2.1[h.toNat]!)
    if q.2.2.2.2[u.toNat]! then (q.1, heap.1, heap.2, h, q.2.2.2.2)
    else
      let r := relax n u first heads lens q.1 heap.1 heap.2 h
      (r.1, r.2.1, r.2.2.1, r.2.2.2, q.2.2.2.2.set! u.toNat true)
  else q

/-- A step of the main loop keeps `MainInv`. -/
theorem settle_inv (n : UInt64) (first heads lens : Array UInt64) (S k : Nat)
    (q : Array UInt64 × Array UInt64 × Array UInt64 × UInt64 × Array Bool)
    (hwf : WellFormed n.toNat first heads lens)
    (hq : MainInv n.toNat S first heads lens k q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
    MainInv n.toNat S first heads lens (k + 1) (settle n first heads lens q).1
      (settle n first heads lens q).2.1 (settle n first heads lens q).2.2.1
      (settle n first heads lens q).2.2.2.1 (settle n first heads lens q).2.2.2.2 := by
  obtain ⟨dist, hk, hv, h, done⟩ := q
  dsimp only at hq
  have hq' := hq
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := hq'
  have hn := UInt64.toNat_lt n
  have hM := UInt64.toNat_lt first[n.toNat]!
  have hds := degSum_le hwf done n.toNat le_rfl
  unfold settle
  dsimp only
  by_cases h0 : 0 < h
  swap
  · simp only [ite_eq_right h0]
    have hz : h.toNat = 0 := by
      have := mt UInt64.lt_iff_toNat_lt.mpr h0
      simp only [UInt64.reduceToNat] at this
      omega
    exact ⟨i1, i2, i3, i4, i5, Or.inl hz, i7, i8, i9, i10, i11, i12⟩
  simp only [ite_eq_left h0]
  have h0' : 0 < h.toNat := by simpa using UInt64.lt_iff_toNat_lt.mp h0
  have hh1 : (h - 1).toNat = h.toNat - 1 := Library.Queues.BinaryHeap.sub_one_toNat h0'
  have hcnt : h.toNat + k ≤ degSum first done n.toNat := i6.resolve_left (by omega)
  obtain ⟨p1, p2, p3, p4⟩ := pop_spec hk hv h i5 h0' (by rw [i2]; omega) (by rw [i3]; omega)
  rw [← hh1] at p3 p4
  simp only [show (0 : UInt64).toNat = 0 from rfl] at p1 p2 p3 p4 ⊢
  generalize siftDown 0 (h - 1) (hk.set! 0 hk[(h - 1).toNat]!) (hv.set! 0 hv[(h - 1).toNat]!)
    = heap at p1 p2 p3 p4 ⊢
  generalize hU : hv[0]! = u at p4 ⊢
  have hroot : (hk[0]!, u) ∈ pairs hk hv h.toNat := mem_pairs.mpr ⟨0, h0', by rw [hU]⟩
  have hun : u.toNat < n.toNat := (i11 _ hroot).1
  have hku : D dist u.toNat ≤ hk[0]!.toNat := (i11 _ hroot).2.1
  have hkf : hk[0]!.toNat < 2 ^ 64 - 1 := (i11 _ hroot).2.2
  have hmin : ∀ e ∈ pairs hk hv h.toNat, hk[0]!.toNat ≤ e.1.toNat := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := mem_pairs.mp he
    exact UInt64.le_iff_toNat_le.mp (root_min hk h.toNat i5 i hi)
  have hpop : ∀ e ∈ pairs hk hv h.toNat,
      e = (hk[0]!, u) ∨ e ∈ pairs heap.1 heap.2 (h - 1).toNat := fun e he =>
    List.mem_cons.mp (p4.mem_iff.mp he)
  have hpop' : ∀ e ∈ pairs heap.1 heap.2 (h - 1).toNat, e ∈ pairs hk hv h.toNat := fun e he =>
    p4.mem_iff.mpr (List.mem_cons_of_mem _ he)
  have hof : ∀ v < n.toNat, UInt64.ofNat v = u → v = u.toNat := by
    intro v hvn e
    rw [← e, UInt64.toNat_ofNat_of_lt' (show v < 2 ^ 64 by omega)]
  by_cases hd : done[u.toNat]! = true
  · simp only [ite_eq_left hd]
    refine ⟨i1, p1.trans i2, p2.trans i3, i4, p3, Or.inr (by omega), i7, i8, i9, i10,
      fun e he => i11 e (hpop' e he), fun v hvn hnd hf => ?_⟩
    rcases hpop _ (i12 v hvn hnd hf) with e | e
    · exact (hnd (by rw [hof v hvn (Prod.mk.inj e).2]; exact hd)).elim
    · exact e
  simp only [ite_eq_right hd]
  have hfin : D dist u.toNat < 2 ^ 64 - 1 := by omega
  have hwu := i8 _ hun hfin
  have hleast : ∀ L, Walk n.toNat first heads lens S u.toNat L → D dist u.toNat ≤ L := by
    intro L hw
    by_cases hL : L < 2 ^ 64 - 1
    · obtain ⟨x, hx, hxm⟩ := exit_entry hq hw hd hL
      have : hk[0]!.toNat ≤ D dist x := hmin _ hxm
      omega
    · omega
  have hset := degSum_set first done u.toNat (by rw [i4]; exact hun) hd n.toNat
  rw [ite_eq_left hun] at hset
  have hds2 := degSum_le hwf (done.set! u.toNat true) n.toNat le_rfl
  have hcap : (h - 1).toNat + deg first u.toNat ≤ first[n.toNat]!.toNat := by omega
  have hr := relax_spec n u first heads lens dist heap.1 heap.2 (h - 1) hwf hun i1 p3
    (by rw [p1, i2]; exact hcap) (by rw [p2, i3]; exact hcap) (by rw [p1, i2]; exact hM)
  have harcs := relax_arcs n u first heads lens dist heap.1 heap.2 (h - 1) hwf hun hr
  generalize relax n u first heads lens dist heap.1 heap.2 (h - 1) = r at hr harcs ⊢
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, E, rE1, rE2, rE3⟩ := hr
  have hdone : ∀ x, (done.set! u.toNat true)[x]! = true ↔ x = u.toNat ∨ done[x]! = true := by
    intro x
    rw [get_set done u.toNat true x (by rw [i4]; exact hun)]
    by_cases hx : x = u.toNat
    · rw [ite_eq_left hx]
      exact ⟨fun _ => Or.inl hx, fun _ => rfl⟩
    · rw [ite_eq_right hx]
      exact ⟨Or.inr, fun h' => h'.resolve_left hx⟩
  have hkeep : ∀ y, done[y]! = true → D r.1 y = D dist y := by
    intro y hy
    by_contra hne
    obtain ⟨w, ha, he⟩ := r9 y (lt_of_le_of_ne (r6 y) hne)
    have := i9 y ha.2.1 hy _ (Walk.step hwu ha)
    have := r6 y
    omega
  refine ⟨r1, r2.trans (p1.trans i2), r3.trans (p2.trans i3), by rw [Array.size_set!, i4], r4,
    Or.inr (by omega), (hdone S).mpr (Or.inr i7), fun v hvn hf => ?_, fun v hvn hvd L hw => ?_,
    fun y hy hyd x w ha => ?_, fun e he => ?_, fun v hvn hnd hf => ?_⟩
  · by_cases hlt : D r.1 v < D dist v
    · obtain ⟨w, ha, he⟩ := r9 v hlt
      rw [he]
      exact Walk.step hwu ha
    · have he : D r.1 v = D dist v := le_antisymm (r6 v) (not_lt.mp hlt)
      rw [he] at hf ⊢
      exact i8 v hvn hf
  · rcases (hdone v).mp hvd with rfl | hvd'
    · rw [r7]
      exact hleast L hw
    · rw [hkeep v hvd']
      exact i9 v hvn hvd' L hw
  · rcases (hdone y).mp hyd with rfl | hyd'
    · rw [r7]
      exact harcs x w ha
    · rw [hkeep y hyd']
      exact le_trans (r6 x) (i10 y hy hyd' x w ha)
  · rcases List.mem_append.mp (rE1.mem_iff.mp he) with he' | he'
    · obtain ⟨a, b, c⟩ := i11 e (hpop' e he')
      exact ⟨a, le_trans (r6 _) b, c⟩
    · obtain ⟨a, b, c, -⟩ := rE2 e he'
      exact ⟨a, b, c⟩
  · have hvu : v ≠ u.toNat := fun e => hnd ((hdone v).mpr (Or.inl e))
    have hnd' : ¬done[v]! = true := fun e => hnd ((hdone v).mpr (Or.inr e))
    by_cases hlt : D r.1 v < D dist v
    · exact rE1.mem_iff.mpr (List.mem_append_right _ (rE3 v hlt))
    · have he : D r.1 v = D dist v := le_antisymm (r6 v) (not_lt.mp hlt)
      have hval : r.1[v]! = dist[v]! := UInt64.toNat_inj.mp he
      rw [hval]
      rcases hpop _ (i12 v hvn hnd' (by rw [← he]; exact hf)) with e | e
      · exact absurd (hof v hvn (Prod.mk.inj e).2) hvu
      · exact rE1.mem_iff.mpr (List.mem_append_left _ e)

/-- After the source's arcs are relaxed, the state before the main loop satisfies `MainInv`. -/
theorem init_inv (n s : UInt64) (first heads lens : Array UInt64)
    (hwf : WellFormed n.toNat first heads lens) (hs : s.toNat < n.toNat) :
    let st := relax n s first heads lens ((LeanExe.build n fun _ => INF).set! s.toNat 0)
      (LeanExe.build first[n.toNat]! fun _ => 0) (LeanExe.build first[n.toNat]! fun _ => 0) 0
    MainInv n.toNat s.toNat first heads lens 0 st.1 st.2.1 st.2.2.1 st.2.2.2
      ((LeanExe.build n fun _ => false).set! s.toNat true) := by
  intro st
  have hM := UInt64.toNat_lt first[n.toNat]!
  have hz : (0 : UInt64).toNat = 0 := rfl
  have hm := first_mono hwf (n.toNat - (s.toNat + 1)) (s.toNat + 1) (by omega)
  rw [show s.toNat + 1 + (n.toNat - (s.toNat + 1)) = n.toNat by omega] at hm
  have hcap : (0 : UInt64).toNat + deg first s.toNat ≤
      (LeanExe.build first[n.toNat]! fun _ => (0 : UInt64)).size := by
    rw [build_size]
    simp only [deg]
    omega
  have hds0 : ((LeanExe.build n fun _ => INF).set! s.toNat 0).size = n.toNat := by
    rw [Array.size_set!, build_size]
  have hst : RelaxInv n.toNat first heads lens ((LeanExe.build n fun _ => INF).set! s.toNat 0)
      (LeanExe.build first[n.toNat]! fun _ => 0) (LeanExe.build first[n.toNat]! fun _ => 0) 0
      s.toNat (deg first s.toNat) st :=
    relax_spec n s first heads lens _ _ _ 0 hwf hs hds0 (fun j _ hj => absurd hj (by omega))
      hcap hcap (by rw [build_size]; exact hM)
  have harcs := relax_arcs n s first heads lens _ _ _ 0 hwf hs hst
  clear_value st
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, E, rE1, rE2, rE3⟩ := hst
  rw [build_size] at r2 r3
  have hD0 : ∀ v < n.toNat, D ((LeanExe.build n fun _ => INF).set! s.toNat 0) v =
      if v = s.toNat then 0 else 2 ^ 64 - 1 := by
    intro v hv
    simp only [D]
    rw [get_set _ _ _ v (by rw [build_size]; exact hs)]
    by_cases hvs : v = s.toNat
    · subst hvs
      simp
    · simp only [ite_eq_right hvs]
      rw [build_get hv]
      exact INF_toNat
  have hdone0 : ∀ v < n.toNat,
      ((LeanExe.build n fun _ => false).set! s.toNat true)[v]! = true ↔ v = s.toNat := by
    intro v hv
    rw [get_set _ _ _ v (by rw [build_size]; exact hs)]
    by_cases hvs : v = s.toNat
    · simp [hvs]
    · simp only [ite_eq_right hvs]
      rw [build_get hv]
      simp [hvs]
  have hset := degSum_set first (LeanExe.build n fun _ => false) s.toNat
    (by rw [build_size]; exact hs) (by rw [build_get hs]; simp) n.toNat
  rw [ite_eq_left hs, degSum_none first (LeanExe.build n fun _ => false) n.toNat
    (fun v hv => by rw [build_get hv]; simp)] at hset
  refine ⟨r1, r2, r3, by rw [Array.size_set!, build_size], r4, Or.inr (by omega),
    (hdone0 _ hs).mpr rfl, fun v hv hf => ?_, fun v hv hvd L _ => ?_,
    fun y hy hyd x w ha => ?_, fun e he => ?_, fun v hv hnd hf => ?_⟩
  · by_cases hlt : D st.1 v < D ((LeanExe.build n fun _ => INF).set! s.toNat 0) v
    · obtain ⟨w, ha, he⟩ := r9 v hlt
      rw [he, hD0 _ hs, ite_eq_left rfl]
      exact Walk.step (Walk.start hs) ha
    · have he := le_antisymm (r6 v) (not_lt.mp hlt)
      rw [hD0 v hv] at he
      by_cases hvs : v = s.toNat
      · rw [he, ite_eq_left hvs, hvs]
        exact Walk.start hs
      · rw [ite_eq_right hvs] at he
        omega
  · have := (hdone0 v hv).mp hvd
    subst this
    rw [r7, hD0 _ hs, ite_eq_left rfl]
    exact Nat.zero_le _
  · have := (hdone0 y hy).mp hyd
    subst this
    rw [r7]
    exact harcs x w ha
  · rcases List.mem_append.mp (rE1.mem_iff.mp he) with he' | he'
    · rw [hz] at he'
      simp [pairs] at he'
    · obtain ⟨a, b, c, -⟩ := rE2 e he'
      exact ⟨a, b, c⟩
  · have hvs : v ≠ s.toNat := fun e => hnd ((hdone0 v hv).mpr e)
    have h1 := hD0 v hv
    rw [ite_eq_right hvs] at h1
    exact rE1.mem_iff.mpr (List.mem_append_right _ (rE3 v (by omega)))

/-- `MainInv` after `first[N]` steps gives `Distances`: the count empties the heap, so a vertex that
is not done has no walk shorter than `2^64 - 1`. -/
theorem main_spec {N S : Nat} {first heads lens dist hk hv : Array UInt64} {h : UInt64}
    {done : Array Bool} (hwf : WellFormed N first heads lens)
    (hq : MainInv N S first heads lens first[N]!.toNat dist hk hv h done) :
    Distances N S first heads lens dist := by
  have hq' := hq
  obtain ⟨i1, -, -, -, -, i6, -, i8, i9, -, -, i12⟩ := hq'
  have hds := degSum_le hwf done N le_rfl
  have h0 : h.toNat = 0 := by omega
  have hempty : ∀ x, (dist[x]!, UInt64.ofNat x) ∉ pairs hk hv h.toNat := by
    intro x hx
    rw [h0] at hx
    simp [pairs] at hx
  refine ⟨i1, fun v hv => ⟨fun hf => ?_, fun hf L hw => ?_⟩⟩
  · by_cases hd : done[v]! = true
    · exact ⟨i8 v hv hf, i9 v hv hd⟩
    · exact absurd (i12 v hv hd hf) (hempty v)
  · by_cases hd : done[v]! = true
    · have h1 : D dist v ≤ L := i9 v hv hd L hw
      have h2 : D dist v = 2 ^ 64 - 1 := hf
      omega
    · by_contra hL
      obtain ⟨x, -, hx⟩ := exit_entry hq hw hd (by omega)
      exact hempty x hx

theorem main_loop (n : UInt64) (first heads lens : Array UInt64) (S : Nat)
    (hwf : WellFormed n.toNat first heads lens)
    (init : Array UInt64 × Array UInt64 × Array UInt64 × UInt64 × Array Bool)
    (h0 : MainInv n.toNat S first heads lens 0 init.1 init.2.1 init.2.2.1 init.2.2.2.1
      init.2.2.2.2) :
    Distances n.toNat S first heads lens
      (LeanExe.loop first[n.toNat]! init fun _ q => settle n first heads lens q).1 :=
  main_spec hwf (loop_induction (n := first[n.toNat]!) (init := init)
    (f := fun _ q => settle n first heads lens q)
    (fun k q => MainInv n.toNat S first heads lens k q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) h0
    fun k q _ hq => settle_inv n first heads lens S k q hwf hq)

theorem dijkstra_eq (n s : UInt64) (first heads lens : Array UInt64) (hs : s < n) :
    dijkstra n s first heads lens =
      let st0 := relax n s first heads lens ((LeanExe.build n fun _ => INF).set! s.toNat 0)
        (LeanExe.build first[n.toNat]! fun _ => 0) (LeanExe.build first[n.toNat]! fun _ => 0) 0
      (LeanExe.loop first[n.toNat]! (st0.1, st0.2.1, st0.2.2.1, st0.2.2.2,
        (LeanExe.build n fun _ => false).set! s.toNat true)
        fun _ q => settle n first heads lens q).1 := by
  unfold dijkstra
  exact ite_eq_left hs

/-- For a graph in the request's form, `dijkstra` returns the least walk lengths from `s`. -/
theorem dijkstra_spec (n s : UInt64) (first heads lens : Array UInt64)
    (hwf : WellFormed n.toNat first heads lens) :
    Distances n.toNat s.toNat first heads lens (dijkstra n s first heads lens) := by
  by_cases hs : s < n
  · rw [dijkstra_eq n s first heads lens hs]
    exact main_loop n first heads lens s.toNat hwf _
      (init_inv n s first heads lens hwf (UInt64.lt_iff_toNat_lt.mp hs))
  · have hS : n.toNat ≤ s.toNat := by
      have := mt UInt64.lt_iff_toNat_lt.mpr hs
      omega
    have e : dijkstra n s first heads lens = LeanExe.build n fun _ => INF := by
      unfold dijkstra
      exact ite_eq_right hs
    rw [e]
    refine ⟨build_size _ _, fun v hv =>
      ⟨fun hf => ?_, fun _ L hw => absurd (walk_src hw) (by omega)⟩⟩
    have h1 : (LeanExe.build n fun _ => INF)[v]!.toNat = 2 ^ 64 - 1 := by
      rw [build_get hv]
      exact INF_toNat
    omega

end Library.Graphs.Dijkstra
