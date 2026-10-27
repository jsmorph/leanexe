import Demos.Slew.Cost

/-! Optimality of the slew planner.  The graph is the one that the program's own checks define
(`Edge`): an edge joins node `u` to node `v` when both lie below `n`, both pass the static check
or are the start or the goal (`okNode`), `v` differs from `u`, the computed angle of the rotation
is not greater than `maxEdge` or the edge joins the start to the goal, and `edgeOk` accepts the
rotation.  Its cost (`wt`) is the computed duration in whole milliseconds plus the settling time.
`plan_optimal` states that for an input that passes `validInput` and whose start and goal pass
the static check, the output has status 1 exactly when the graph has a walk from the start to the
goal, and that its segments then form such a walk of least total cost, which the header reports.

The proof is the correctness of Dijkstra's algorithm with integer costs, as an invariant of every
state of the search (`Opt`).  A finalized node holds the least cost of a walk to it (`lower`), a
node with a finite cost holds the cost of the walk through its parent (`edge`), and every node
that is not finalized holds at most the cost through each finalized node other than the goal with
an edge to it (`relaxed`), since the search stops when it finalizes the goal.  `relax` checks an
edge only when its candidate cost improves the target, and a candidate that does not improve the
target already satisfies `relaxed`, so skipping the check leaves the invariant intact.  Edge
costs of at most `2 ^ 34` (`Cost.edge_cost_le`) keep every cost at most `(card done) 2 ^ 34`
(`bound`), so no sum wraps and no finite cost reaches `infinity`.  The search finalizes one node in
each round that does not stop, so its `n + 1` rounds end with the goal finalized or with every
open admitted node unreached (`stop`). -/

namespace Demos.Slew.Optimal

open Demos.Slew Demos.Slew.Search

section Graph

variable (xs : Array Float) (d : Dims) (n st : UInt64)

/-- Node `i` passes the static check with no slack, or is the start or the goal. -/
def okNode (i : UInt64) : Bool := i < 2 || attitudeOk xs d (nodeAt xs d i) 0.0

/-- The computed angle of the rotation from node `u` to node `v`. -/
def theta (u v : UInt64) : Float := angleOf (relative (nodeAt xs d u) (nodeAt xs d v))

/-- The cost of the edge from `u` to `v`: the duration of the rotation and the settling time
`st`, in whole milliseconds. -/
def wt (u v : UInt64) : UInt64 := slewTicks (theta xs d u v) (rd xs 4) (rd xs 5) + st

/-- The edge from `u` to `v` of the graph that the program's checks define. -/
def Edge (u v : UInt64) : Prop :=
  u.toNat < n.toNat ∧ v.toNat < n.toNat ∧ okNode xs d u = true ∧ okNode xs d v = true ∧ v ≠ u ∧
    (decide (theta xs d u v > rd xs 7) && !(u == 0 && v == 1)) = false ∧
    edgeOk xs d (nodeAt xs d u) (relative (nodeAt xs d u) (nodeAt xs d v)) = true

/-- The cost of the walk `p 0, …, p m`. -/
def pathCost (p : Nat → UInt64) (m : Nat) : Nat :=
  ∑ i ∈ Finset.range m, (wt xs d st (p i) (p (i + 1))).toNat

/-- `p 0, …, p m` is a walk of the graph from the start to `v`. -/
def Walk (p : Nat → UInt64) (m : Nat) (v : UInt64) : Prop :=
  p 0 = 0 ∧ p m = v ∧ ∀ i < m, Edge xs d n (p i) (p (i + 1))

end Graph

/-- The invariant of the search.  `pend u v` names the pairs for which `relaxed` may fail. -/
structure Opt (xs : Array Float) (d : Dims) (n st : UInt64) (W : Nat)
    (pend : UInt64 → UInt64 → Prop) (s : Search) : Prop where
  inv : Inv xs d n s
  ok : s.ok = (initial xs d n).ok
  zero : cst s 0 = 0
  first : dn s 0 = false → ∀ v : UInt64, v.toNat < n.toNat →
    dn s v = false ∧ (v ≠ 0 → cst s v = infinity)
  doneFin : ∀ v : UInt64, v.toNat < n.toNat → dn s v = true → cst s v ≠ infinity
  edge : ∀ v : UInt64, v.toNat < n.toNat → v ≠ 0 → cst s v ≠ infinity →
    Edge xs d n (par s v) v ∧
      (cst s v).toNat = (cst s (par s v)).toNat + (wt xs d st (par s v) v).toNat
  bound : ∀ v : UInt64, v.toNat < n.toNat → cst s v ≠ infinity →
    (cst s v).toNat ≤ (fin n s).card * W
  lower : ∀ v : UInt64, v.toNat < n.toNat → dn s v = true → ∀ p m, Walk xs d n p m v →
    (cst s v).toNat ≤ pathCost xs d st p m
  relaxed : ∀ u v : UInt64, dn s u = true → dn s v = false → Edge xs d n u v → ¬ pend u v →
    (cst s v).toNat ≤ (cst s u).toNat + (wt xs d st u v).toNat
  goal : dn s 1 = true → s.finished = true
  stop : s.finished = true → dn s 1 = true ∨
    ∀ v : UInt64, v.toNat < n.toNat → dn s v = false → okNode xs d v = true → cst s v = infinity

section Proofs

variable {xs : Array Float} {d : Dims} {n st : UInt64}

theorem inf_toNat : infinity.toNat = 2 ^ 62 := rfl

theorem pathCost_succ (p : Nat → UInt64) (m : Nat) :
    pathCost xs d st p (m + 1) = pathCost xs d st p m + (wt xs d st (p m) (p (m + 1))).toNat :=
  Finset.sum_range_succ _ _

theorem ok_get {s : Search} (h : s.ok = (initial xs d n).ok) {v : UInt64}
    (hv : v.toNat < n.toNat) : s.ok[v.toNat]! = okNode xs d v := by
  rw [h]
  simp only [initial]
  rw [LeanExe.IR.build_get hv, UInt64.ofNat_toNat]
  rfl

theorem initial_cost {v : UInt64} (hv : v.toNat < n.toNat) :
    cst (initial xs d n) v = if v == 0 then 0 else infinity := by
  simp only [cst, initial]
  rw [LeanExe.IR.build_get hv, UInt64.ofNat_toNat]

theorem initial_done {v : UInt64} (hv : v.toNat < n.toNat) : dn (initial xs d n) v = false := by
  simp only [dn, initial]
  rw [LeanExe.IR.build_get hv]

theorem initial_opt (W : Nat) (pend : UInt64 → UInt64 → Prop) (hn2 : 2 ≤ n.toNat) :
    Opt xs d n st W pend (initial xs d n) where
  inv := initial_inv xs d n
  ok := rfl
  zero := by
    rw [initial_cost (by simp only [UInt64.reduceToNat]; omega)]
    simp
  first := fun _ v hv => ⟨initial_done hv, fun h0 => by rw [initial_cost hv]; simp [h0]⟩
  doneFin := fun v hv hd => by rw [initial_done hv] at hd; exact absurd hd (by decide)
  edge := fun v hv h0 hc => absurd (by rw [initial_cost hv]; simp [h0]) hc
  bound := fun v hv hc => by
    by_cases h0 : v = 0
    · subst h0; rw [initial_cost hv]; simp
    · rw [initial_cost hv] at hc; simp [h0] at hc
  lower := fun v hv hd => by rw [initial_done hv] at hd; exact absurd hd (by decide)
  relaxed := fun u v hu _ he => by rw [initial_done he.1] at hu; exact absurd hu (by decide)
  goal := fun h1 => by
    rw [initial_done (by simp only [UInt64.reduceToNat]; omega)] at h1
    exact absurd h1 (by decide)
  stop := fun h => by simp [initial] at h

theorem opt_congr {W : Nat} {pend : UInt64 → UInt64 → Prop} {s s' : Search}
    (h : Opt xs d n st W pend s) (hc : s'.cost = s.cost) (hp : s'.parent = s.parent)
    (hd : s'.done = s.done) (ho : s'.ok = s.ok) (hf : s'.finished = s.finished) :
    Opt xs d n st W pend s' := by
  have ep : par s' = par s := by funext v; simp only [par, hp]
  have ed : dn s' = dn s := by funext v; simp only [dn, hd]
  have ec : cst s' = cst s := by funext v; simp only [cst, hc]
  have ef : fin n s' = fin n s := by simp only [fin, ed]
  exact ⟨inv_congr hc hp hd h.inv, by rw [ho]; exact h.ok, by rw [ec]; exact h.zero,
    by rw [ed, ec]; exact h.first, by rw [ed, ec]; exact h.doneFin,
    by rw [ec, ep]; exact h.edge, by rw [ec, ef]; exact h.bound, by rw [ed, ec]; exact h.lower,
    by rw [ed, ec]; exact h.relaxed, by rw [ed, hf]; exact h.goal,
    by rw [hf, ed, ec]; exact h.stop⟩

theorem opt_mono {W : Nat} {pend pend' : UInt64 → UInt64 → Prop} {s : Search}
    (hp : ∀ u v, Edge xs d n u v → pend' u v → pend u v) (h : Opt xs d n st W pend' s) :
    Opt xs d n st W pend s :=
  { h with
    relaxed := fun u v hu hv he hnp => h.relaxed u v hu hv he (fun hp' => hnp (hp u v he hp')) }

theorem opt_finish {W : Nat} {pend : UInt64 → UInt64 → Prop} {s : Search}
    (h : Opt xs d n st W pend s)
    (hs : dn s 1 = true ∨ ∀ v : UInt64, v.toNat < n.toNat → dn s v = false →
      okNode xs d v = true → cst s v = infinity) :
    Opt xs d n st W pend { s with finished := true } where
  inv := inv_congr (s := s) rfl rfl rfl h.inv
  ok := h.ok
  zero := h.zero
  first := h.first
  doneFin := h.doneFin
  edge := h.edge
  bound := h.bound
  lower := h.lower
  relaxed := h.relaxed
  goal := fun _ => rfl
  stop := fun _ => hs

/-! ### Selection -/

/-- `selectNext` returns `n` when every open admitted node is unreached, and otherwise an open
admitted node of least cost. -/
theorem select_spec (s : Search) (n : UInt64) :
    ((selectNext s n).1 = n ∧ ∀ i : UInt64, i.toNat < n.toNat → dn s i = false →
        s.ok[i.toNat]! = true → infinity.toNat ≤ (cst s i).toNat) ∨
      ((selectNext s n).1.toNat < n.toNat ∧ dn s (selectNext s n).1 = false ∧
        s.ok[(selectNext s n).1.toNat]! = true ∧
        (cst s (selectNext s n).1).toNat < infinity.toNat ∧
        ∀ i : UInt64, i.toNat < n.toNat → dn s i = false → s.ok[i.toNat]! = true →
          (cst s (selectNext s n).1).toNat ≤ (cst s i).toNat) := by
  unfold selectNext
  have key := LeanExe.IR.loop_induction (n := n) (init := (n, infinity))
    (f := fun i acc =>
      let c := s.cost[i.toNat]!
      if !s.done[i.toNat]! && s.ok[i.toNat]! && c < acc.2 then (i, c) else acc)
    (fun k acc => ((acc.1 = n ∧ acc.2 = infinity) ∨
        (acc.1.toNat < n.toNat ∧ dn s acc.1 = false ∧ s.ok[acc.1.toNat]! = true ∧
          cst s acc.1 = acc.2 ∧ acc.2.toNat < infinity.toNat)) ∧
      ∀ i : UInt64, i.toNat < k → dn s i = false → s.ok[i.toNat]! = true →
        acc.2.toNat ≤ (cst s i).toNat)
    ⟨Or.inl ⟨rfl, rfl⟩, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    (fun k acc hk ⟨hacc, hmin⟩ => by
      have hk' : (UInt64.ofNat k).toNat = k :=
        ofNat_toNat_lt (by have := UInt64.toNat_lt n; omega)
      dsimp only
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
        have hlt := UInt64.lt_iff_toNat_lt.mp hc.2
        refine ⟨Or.inr ⟨by show (UInt64.ofNat k).toNat < n.toNat; omega, hc.1.1, hc.1.2, rfl, ?_⟩,
          ?_⟩
        · rcases hacc with ⟨_, h2⟩ | ⟨_, _, _, _, h2⟩
          · rw [h2] at hlt; exact hlt
          · show (s.cost[(UInt64.ofNat k).toNat]!).toNat < infinity.toNat
            omega
        · intro i hi hdi hoi
          show (s.cost[(UInt64.ofNat k).toNat]!).toNat ≤ (cst s i).toNat
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · have := hmin i hi hdi hoi
            omega
          · have e : i = UInt64.ofNat k := UInt64.toNat_inj.mp (by rw [hk', hi])
            subst e
            exact le_refl _
      · rename_i hc
        refine ⟨hacc, fun i hi hdi hoi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact hmin i hi hdi hoi
        · have e : i = UInt64.ofNat k := UInt64.toNat_inj.mp (by rw [hk', hi])
          subst e
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_and] at hc
          have := hc ⟨hdi, hoi⟩
          rw [UInt64.lt_iff_toNat_lt] at this
          simp only [cst]
          omega)
  obtain ⟨hacc, hmin⟩ := key
  rcases hacc with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, fun i hi hd ho => by have := hmin i hi hd ho; rwa [h2] at this⟩
  · exact Or.inr ⟨h1, h2, h3, by rw [h4]; exact h5,
      fun i hi hd ho => by rw [h4]; exact hmin i hi hd ho⟩

/-! ### Finalization -/

theorem card_finalize {n u : UInt64} {s s1 : Search} (hu : u.toNat < n.toNat)
    (hsz : s.done.size = n.toNat) (hdu : dn s u = false)
    (hd : s1.done = s.done.set! u.toNat true) : (fin n s1).card = (fin n s).card + 1 := by
  have hun : u.toNat < s.done.size := by rw [hsz]; exact hu
  have edu : dn s1 u = true := by simp only [dn, hd]; exact get_set_eq hun true
  have edv : ∀ v, v ≠ u → dn s1 v = dn s v := by
    intro v hv; simp only [dn, hd]; exact get_set_ne (ne_iff_toNat.mp hv) true
  have hfin : fin n s1 = insert u.toNat (fin n s) := by
    ext i
    simp only [fin, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · intro ⟨hi, hd⟩
      by_cases e : UInt64.ofNat i = u
      · left; rw [← e]; exact (ofNat_toNat_lt (i := i) (by have := UInt64.toNat_lt n; omega)).symm
      · right; exact ⟨hi, by rw [← edv _ e]; exact hd⟩
    · rintro (e | ⟨hi, hd⟩)
      · refine ⟨by rw [e]; exact hu, ?_⟩
        rw [e, UInt64.ofNat_toNat]; exact edu
      · refine ⟨hi, ?_⟩
        by_cases e : UInt64.ofNat i = u
        · rw [e]; exact edu
        · rw [edv _ e]; exact hd
  have hnot : u.toNat ∉ fin n s := by
    simp only [fin, Finset.mem_filter, Finset.mem_range, UInt64.ofNat_toNat, hdu]
    simp
  rw [hfin, Finset.card_insert_of_notMem hnot]

/-- The node that `selectNext` returns has a cost at most that of every walk to it: the walk
leaves the finalized nodes at some first open node, whose cost is at most the cost of the walk
up to it, and the selected node costs at most any open admitted node. -/
theorem select_lower {W : Nat} {s : Search} {u : UInt64}
    (h : Opt xs d n st W (fun w _ => w = 1) s) (h1 : dn s 1 = false) (hn2 : 2 ≤ n.toNat)
    (hdu : dn s u = false)
    (hmin : ∀ i : UInt64, i.toNat < n.toNat → dn s i = false → s.ok[i.toNat]! = true →
      (cst s u).toNat ≤ (cst s i).toNat)
    {p : Nat → UInt64} {m : Nat} (hw : Walk xs d n p m u) :
    (cst s u).toNat ≤ pathCost xs d st p m := by
  obtain ⟨hp0, hpm, hpe⟩ := hw
  classical
  have hex : ∃ j, dn s (p j) = false := ⟨m, by rw [hpm]; exact hdu⟩
  obtain ⟨j, hj, hjm, hjmin⟩ : ∃ j, dn s (p j) = false ∧ j ≤ m ∧ ∀ i < j, dn s (p i) = true :=
    ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex (by rw [hpm]; exact hdu),
      fun i hi => by simpa using Nat.find_min hex hi⟩
  have hmono : pathCost xs d st p j ≤ pathCost xs d st p m := by
    unfold pathCost
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hjm)
  rcases j with _ | i
  · have h0r : (p 0).toNat < n.toNat := by rw [hp0]; simp only [UInt64.reduceToNat]; omega
    have hok : s.ok[(p 0).toNat]! = true := by rw [ok_get h.ok h0r, hp0]; rfl
    have := hmin (p 0) h0r hj hok
    rw [hp0, h.zero] at this
    simp only [UInt64.reduceToNat] at this
    omega
  · have hdi := hjmin i (by omega)
    have he := hpe i (by omega)
    have hpi1 : p i ≠ 1 := fun e => by rw [e, h1] at hdi; exact absurd hdi (by decide)
    have hr := h.relaxed (p i) (p (i + 1)) hdi hj he hpi1
    have hl := h.lower (p i) he.1 hdi p i ⟨hp0, rfl, fun k hk => hpe k (by omega)⟩
    have hok : s.ok[(p (i + 1)).toNat]! = true := by rw [ok_get h.ok he.2.1]; exact he.2.2.2.1
    have hm := hmin (p (i + 1)) he.2.1 hj hok
    have hsum := pathCost_succ (xs := xs) (d := d) (st := st) p i
    omega

/-- Finalizing the selected node `u` keeps the invariant, with the pairs from `u` pending. -/
theorem finalize_opt {W : Nat} {s : Search} {u : UInt64} (f : Bool)
    (h : Opt xs d n st W (fun w _ => w = 1) s) (hf : s.finished = false) (hn2 : 2 ≤ n.toNat)
    (hu : u.toNat < n.toNat) (hdu : dn s u = false)
    (hcu : (cst s u).toNat < infinity.toNat)
    (hmin : ∀ i : UInt64, i.toNat < n.toNat → dn s i = false → s.ok[i.toNat]! = true →
      (cst s u).toNat ≤ (cst s i).toNat)
    (hfu : f = true ↔ u = 1) (e : UInt64) :
    Opt xs d n st W (fun w _ => w = 1 ∨ w = u)
        { s with done := s.done.set! u.toNat true, examined := e, finished := f } ∧
      (fin n { s with done := s.done.set! u.toNat true, examined := e, finished := f }).card =
        (fin n s).card + 1 := by
  set s1 : Search := { s with done := s.done.set! u.toNat true, examined := e, finished := f }
  have hun : u.toNat < s.done.size := by rw [h.inv.doneSize]; exact hu
  have edu : dn s1 u = true := by simp only [dn, s1]; exact get_set_eq hun true
  have edv : ∀ v, v ≠ u → dn s1 v = dn s v := by
    intro v hv; simp only [dn, s1]; exact get_set_ne (ne_iff_toNat.mp hv) true
  have hcard : (fin n s1).card = (fin n s).card + 1 :=
    card_finalize hu h.inv.doneSize hdu rfl
  have hcu' : cst s u ≠ infinity := fun e' => by rw [e'] at hcu; exact lt_irrefl _ hcu
  have h1 : dn s 1 = false := by
    cases h1 : dn s 1
    · rfl
    · have := h.goal h1; rw [hf] at this; exact absurd this (by decide)
  have hinv : Inv xs d n s1 :=
    inv_congr (s := { s with done := s.done.set! u.toNat true, examined := e }) rfl rfl rfl
      (finalize_inv h.inv hu hdu hcu' e).1
  refine ⟨⟨hinv, h.ok, h.zero, ?_, ?_, h.edge, ?_, ?_, ?_, ?_, ?_⟩, hcard⟩
  · intro h0
    exfalso
    by_cases e0 : u = 0
    · rw [e0] at edu; rw [edu] at h0; exact absurd h0 (by decide)
    · have h0' : dn s 0 = false := by rw [← edv 0 (Ne.symm e0)]; exact h0
      exact hcu' ((h.first h0' u hu).2 e0)
  · intro v hv hd
    by_cases e0 : v = u
    · rw [e0]; exact hcu'
    · rw [edv v e0] at hd; exact h.doneFin v hv hd
  · intro v hv hc
    rw [hcard]
    exact (h.bound v hv hc).trans (Nat.mul_le_mul_right _ (by omega))
  · intro v hv hd p m hw
    by_cases e0 : v = u
    · rw [e0] at hw ⊢
      exact select_lower h h1 hn2 hdu hmin hw
    · rw [edv v e0] at hd; exact h.lower v hv hd p m hw
  · intro w v hw hv he hnp
    simp only [not_or] at hnp
    have hw' : dn s w = true := by rw [← edv w hnp.2]; exact hw
    have hvu : v ≠ u := fun e' => by rw [e', edu] at hv; exact absurd hv (by decide)
    have hv' : dn s v = false := by rw [← edv v hvu]; exact hv
    exact h.relaxed w v hw' hv' he hnp.1
  · intro hd1
    show f = true
    by_cases e1 : u = 1
    · exact hfu.mpr e1
    · rw [edv 1 (fun e' => e1 e'.symm), h1] at hd1; exact absurd hd1 (by decide)
  · intro hfin
    left
    rw [← hfu.mp hfin]
    exact edu

/-! ### Relaxation -/

/-- Lowering the cost of an open node `v` to the cost through a finalized node `u` with an edge
to `v` keeps the invariant, with the pair `(u, v)` no longer pending. -/
theorem update_opt {W : Nat} {pend : UInt64 → UInt64 → Prop} {t : Search} {u v c : UInt64}
    (h : Opt xs d n st W pend t) (hf : t.finished = false)
    (hv : v.toNat < n.toNat) (hdv : dn t v = false) (hu : u.toNat < n.toNat)
    (hdu : dn t u = true) (he : Edge xs d n u v)
    (hc : c.toNat = (cst t u).toNat + (wt xs d st u v).toNat) (hlt : c.toNat < (cst t v).toNat)
    (hb : c.toNat ≤ (fin n t).card * W) :
    Opt xs d n st W (fun w x => pend w x ∧ ¬(w = u ∧ x = v))
      { t with cost := t.cost.set! v.toNat c, parent := t.parent.set! v.toNat u } := by
  set t' : Search := { t with cost := t.cost.set! v.toNat c, parent := t.parent.set! v.toNat u }
  have hvc : v.toNat < t.cost.size := by rw [h.inv.costSize]; exact hv
  have hvp : v.toNat < t.parent.size := by rw [h.inv.parentSize]; exact hv
  have ecv : cst t' v = c := get_set_eq hvc c
  have ecw : ∀ w, w ≠ v → cst t' w = cst t w := fun w e => get_set_ne (ne_iff_toNat.mp e) c
  have epv : par t' v = u := get_set_eq hvp u
  have epw : ∀ w, w ≠ v → par t' w = par t w := fun w e => get_set_ne (ne_iff_toNat.mp e) u
  have hne : ∀ w, dn t w = true → w ≠ v := fun w hw e => by
    rw [e, hdv] at hw; exact absurd hw (by decide)
  have h0done : dn t 0 = true := by
    cases h0 : dn t 0
    · have := ((h.first h0) u hu).1
      rw [this] at hdu; exact absurd hdu (by decide)
    · rfl
  have hv0 : v ≠ 0 := fun e => by rw [e, h0done] at hdv; exact absurd hdv (by decide)
  have huv : u ≠ v := hne u hdu
  refine ⟨update_inv h.inv hv hdv hu hdu he.2.2.2.2.2.2 c, h.ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.goal, ?_⟩
  · rw [ecw 0 (Ne.symm hv0)]; exact h.zero
  · intro h0
    exact absurd (h0done.symm.trans h0) (by decide)
  · intro w hw hd
    rw [ecw w (hne w hd)]; exact h.doneFin w hw hd
  · intro w hw h0 hc'
    by_cases e : w = v
    · subst e
      rw [epv, ecv, ecw u huv]
      exact ⟨he, hc⟩
    · rw [ecw w e] at hc' ⊢
      rw [epw w e]
      have hl : Link xs d n t w := by
        cases hdw : dn t w
        · exact h.inv.linkOpen w hw h0 hdw hc'
        · exact h.inv.linkDone w hw h0 hdw
      rw [ecw (par t w) (hne _ hl.2.1)]
      exact h.edge w hw h0 hc'
  · intro w hw hc'
    by_cases e : w = v
    · subst e; rw [ecv]; exact hb
    · rw [ecw w e] at hc' ⊢; exact h.bound w hw hc'
  · intro w hw hd p m hwk
    rw [ecw w (hne w hd)]; exact h.lower w hw hd p m hwk
  · intro w x hw hx hex hnp
    by_cases e : x = v
    · subst x
      rw [ecv, ecw w (hne w hw)]
      by_cases ewu : w = u
      · subst w; omega
      · have := h.relaxed w v hw hdv hex (fun hp => hnp ⟨hp, fun h' => ewu h'.1⟩)
        omega
    · rw [ecw x e, ecw w (hne w hw)]
      exact h.relaxed w x hw hx hex (fun hp => hnp ⟨hp, fun h' => e h'.2⟩)
  · intro hfin
    have : t.finished = true := hfin
    rw [hf] at this; exact absurd this (by decide)

/-- `relax` of the node `u` that the round finalized relaxes every pair from `u`. -/
theorem relax_opt {W : Nat} {s1 : Search} {u : UInt64}
    (h : Opt xs d n st W (fun w _ => w = 1 ∨ w = u) s1) (hf : s1.finished = false)
    (hu : u.toNat < n.toNat) (hdu : dn s1 u = true) (hou : okNode xs d u = true)
    (hbu : (cst s1 u).toNat + W ≤ (fin n s1).card * W)
    (hW : ∀ a b : UInt64, a.toNat < n.toNat → b.toNat < n.toNat → (wt xs d st a b).toNat ≤ W)
    (hNW : (n.toNat + 1) * W < 2 ^ 62) :
    Opt xs d n st W (fun w _ => w = 1) (relax xs d n u st s1) ∧
      (relax xs d n u st s1).done = s1.done := by
  have hcard := fin_card_le n s1
  have hmul : (fin n s1).card * W ≤ n.toNat * W := Nat.mul_le_mul_right _ hcard
  have hNW' : (n.toNat + 1) * W = n.toNat * W + W := by ring
  suffices hP : Opt xs d n st W (fun w x => w = 1 ∨ (w = u ∧ n.toNat ≤ x.toNat))
      (relax xs d n u st s1) ∧ (relax xs d n u st s1).done = s1.done ∧
      cst (relax xs d n u st s1) u = cst s1 u ∧
      (relax xs d n u st s1).finished = s1.finished by
    refine ⟨opt_mono (fun w x he hp => ?_) hP.1, hP.2.1⟩
    rcases hp with hp | ⟨_, hx⟩
    · exact hp
    · have := he.2.1; omega
  unfold relax
  dsimp only
  refine LeanExe.IR.loop_induction
    (P := fun k t => Opt xs d n st W (fun w x => w = 1 ∨ (w = u ∧ k ≤ x.toNat)) t ∧
      t.done = s1.done ∧ cst t u = cst s1 u ∧ t.finished = s1.finished)
    ⟨opt_mono (fun w x _ hp => by
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr ⟨hp, Nat.zero_le _⟩) h, rfl, rfl, rfl⟩ ?_
  intro k t hk ⟨ht, htd, htu, htf⟩
  have hk64 : k < 2 ^ 64 := by have := UInt64.toNat_lt n; omega
  have hvk : (UInt64.ofNat k).toNat = k := ofNat_toNat_lt hk64
  have hvn : (UInt64.ofNat k).toNat < n.toNat := by rw [hvk]; exact hk
  have hdn : dn t = dn s1 := by funext w; simp only [dn, htd]
  have hft : fin n t = fin n s1 := by simp only [fin, hdn]
  have hdut : dn t u = true := by rw [hdn]; exact hdu
  have htf' : t.finished = false := by rw [htf]; exact hf
  have hw := hW u (UInt64.ofNat k) hu hvn
  have hcu : (cst s1 u).toNat ≤ (fin n s1).card * W := h.bound u hu (h.doneFin u hu hdu)
  have cand_eq : s1.cost[u.toNat]! + slewTicks (angleOf (relative (nodeAt xs d u)
      (nodeAt xs d (UInt64.ofNat k)))) (rd xs 4) (rd xs 5) + st =
      cst s1 u + wt xs d st u (UInt64.ofNat k) := UInt64.add_assoc _ _ _
  have cand_toNat : (cst s1 u + wt xs d st u (UInt64.ofNat k)).toNat =
      (cst s1 u).toNat + (wt xs d st u (UInt64.ofNat k)).toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  have keep : ∀ t' : Search,
      Opt xs d n st W (fun w x => w = 1 ∨ (w = u ∧ k ≤ x.toNat)) t' →
      (dn t' (UInt64.ofNat k) = false → Edge xs d n u (UInt64.ofNat k) →
        (cst t' (UInt64.ofNat k)).toNat ≤
          (cst t' u).toNat + (wt xs d st u (UInt64.ofNat k)).toNat) →
      Opt xs d n st W (fun w x => w = 1 ∨ (w = u ∧ k + 1 ≤ x.toNat)) t' :=
    by
    intro t' ht' hk'
    refine { ht' with relaxed := fun w x hw hx hex hnp => ?_ }
    by_cases hp : w = 1 ∨ (w = u ∧ k ≤ x.toNat)
    · simp only [not_or, not_and, not_le] at hnp
      rcases hp with hp | ⟨hwu, hkx⟩
      · exact absurd hp hnp.1
      · have hx' : x.toNat = k := by have := hnp.2 hwu; omega
        have ex : x = UInt64.ofNat k := by rw [← hx', UInt64.ofNat_toNat]
        subst w
        subst ex
        exact hk' hx hex
    · exact ht'.relaxed w x hw hx hex hp
  split
  · rename_i hc
    refine ⟨keep t ht (fun hdv he => ?_), htd, htu, htf⟩
    exfalso
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    rcases hc with (hc | hc) | hc
    · have : dn t (UInt64.ofNat k) = true := hc
      rw [this] at hdv; exact absurd hdv (by decide)
    · rw [ok_get ht.ok hvn, he.2.2.2.1] at hc; exact absurd hc (by decide)
    · exact he.2.2.2.2.1 hc
  · rename_i hc0
    split
    · rename_i hc
      refine ⟨keep t ht (fun _ he => ?_), htd, htu, htf⟩
      exact absurd (hc.symm.trans he.2.2.2.2.2.1) (by decide)
    · rename_i hc1
      split
      · rename_i hlt
        split
        · rename_i hacc
          simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, not_or,
            Bool.not_eq_false] at hc0
          have hdv : t.done[(UInt64.ofNat k).toNat]! = false := by simpa using hc0.1.1
          have hok : okNode xs d (UInt64.ofNat k) = true := by
            rw [← ok_get ht.ok hvn]; exact hc0.1.2
          have he : Edge xs d n u (UInt64.ofNat k) :=
            ⟨hu, hvn, hou, hok, hc0.2, Bool.eq_false_iff.mpr hc1, hacc⟩
          rw [cand_eq] at hlt
          have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
          have hb : (cst s1 u + wt xs d st u (UInt64.ofNat k)).toNat ≤ (fin n t).card * W := by
            rw [cand_toNat, hft]; omega
          have hvu : u ≠ UInt64.ofNat k := fun e => hc0.2 e.symm
          refine ⟨?_, htd, ?_, htf⟩
          · rw [cand_eq]
            refine opt_mono (fun w x _ hp => ?_)
              (update_opt ht htf' hvn hdv hu hdut he (by rw [cand_toNat, htu]) hlt' hb)
            rcases hp with ⟨hp | ⟨hwu, hkx⟩, hn⟩
            · exact Or.inl hp
            · refine Or.inr ⟨hwu, ?_⟩
              have : x.toNat ≠ k := fun e => hn ⟨hwu, by rw [← e, UInt64.ofNat_toNat]⟩
              omega
          · exact (get_set_ne (ne_iff_toNat.mp hvu) _).trans htu
        · rename_i hacc
          refine ⟨keep t ht (fun _ he => ?_), htd, htu, htf⟩
          exact absurd (he.2.2.2.2.2.2.symm.trans (Bool.eq_false_iff.mpr hacc)) (by decide)
      · rename_i hge
        refine ⟨keep t ht (fun _ _ => ?_), htd, htu, htf⟩
        rw [cand_eq, UInt64.lt_iff_toNat_lt, cand_toNat] at hge
        rw [htu]
        show (t.cost[(UInt64.ofNat k).toNat]!).toNat ≤ _
        omega

/-! ### Rounds -/

theorem round_opt {W : Nat} {s : Search} (h : Opt xs d n st W (fun w _ => w = 1) s)
    (hf : s.finished = false) (hn2 : 2 ≤ n.toNat)
    (hW : ∀ a b : UInt64, a.toNat < n.toNat → b.toNat < n.toNat → (wt xs d st a b).toNat ≤ W)
    (hNW : (n.toNat + 1) * W < 2 ^ 62) :
    Opt xs d n st W (fun w _ => w = 1) (round xs d n st s) ∧
      ((round xs d n st s).finished = true ∨
        (fin n (round xs d n st s)).card = (fin n s).card + 1) := by
  have spec := select_spec s n
  have hcardn := fin_card_le n s
  have hmul : (fin n s).card * W ≤ n.toNat * W := Nat.mul_le_mul_right _ hcardn
  have hNW' : (n.toNat + 1) * W = n.toNat * W + W := by ring
  unfold round
  generalize selectNext s n = p at spec ⊢
  obtain ⟨u, c⟩ := p
  dsimp only at spec ⊢
  by_cases hun : (u == n) = true
  · rw [ite_eq_left hun]
    have hu : u = n := by simpa using hun
    rcases spec with ⟨_, hall⟩ | ⟨hlt, _⟩
    · refine ⟨opt_finish h (Or.inr fun v hv hd ho => ?_), Or.inl rfl⟩
      have hi := hall v hv hd (by rw [ok_get h.ok hv]; exact ho)
      by_contra hc
      have := h.bound v hv hc
      rw [inf_toNat] at hi
      omega
    · rw [hu] at hlt; exact absurd hlt (lt_irrefl _)
  · rw [ite_eq_right hun]
    rcases spec with ⟨hu, _⟩ | ⟨hu, hdu, hou, hcu, hmin⟩
    · exact absurd (by simp [hu]) hun
    · have hun' : u.toNat < s.done.size := by rw [h.inv.doneSize]; exact hu
      by_cases hu1 : (u == 1) = true
      · rw [ite_eq_left hu1]
        have e1 : u = 1 := by simpa using hu1
        obtain ⟨hopt, _⟩ := finalize_opt true h hf hn2 hu hdu hcu hmin
          (by simp [e1]) (s.examined + 1)
        refine ⟨opt_mono (fun w x _ hp => ?_) (opt_congr hopt rfl rfl rfl rfl rfl), Or.inl rfl⟩
        rcases hp with hp | hp
        · exact hp
        · rw [hp, e1]
      · rw [ite_eq_right hu1]
        have hu1' : u ≠ 1 := by simpa using hu1
        obtain ⟨hopt, hcard⟩ := finalize_opt false h hf hn2 hu hdu hcu hmin
          (by simp [hu1']) (s.examined + 1)
        set s1 : Search := { s with done := s.done.set! u.toNat true, examined := s.examined + 1 }
        have hopt' := opt_congr (s' := s1) hopt rfl rfl rfl rfl hf
        have hcard' : (fin n s1).card = (fin n s).card + 1 := hcard
        have hcu' : cst s u ≠ infinity := fun e' => by rw [e'] at hcu; exact lt_irrefl _ hcu
        have hbu := h.bound u hu hcu'
        obtain ⟨hr, hrd⟩ := relax_opt hopt' hf hu (get_set_eq hun' true)
          (by rw [← ok_get h.ok hu]; exact hou)
          (by rw [hcard', Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_right hbu W) hW hNW
        refine ⟨hr, Or.inr ?_⟩
        have hdn : dn (relax xs d n u st s1) = dn s1 := by funext v; simp only [dn, hrd]
        have hfe : fin n (relax xs d n u st s1) = fin n s1 := by simp only [fin, hdn]
        rw [hfe, hcard']

theorem go_done {step : Search → Search} {s : Search} (hs : s.finished = true) :
    ∀ k, LeanExe.repeatWhile.go (fun s : Search => !s.finished) step k s = s
  | 0 => rfl
  | k + 1 => by simp [LeanExe.repeatWhile.go, hs]

theorem go_opt {W : Nat} (hn2 : 2 ≤ n.toNat)
    (hW : ∀ a b : UInt64, a.toNat < n.toNat → b.toNat < n.toNat → (wt xs d st a b).toNat ≤ W)
    (hNW : (n.toNat + 1) * W < 2 ^ 62) :
    ∀ (k : Nat) (s : Search), Opt xs d n st W (fun w _ => w = 1) s →
      n.toNat + 1 ≤ (fin n s).card + k →
      Opt xs d n st W (fun w _ => w = 1) (LeanExe.repeatWhile.go (fun s : Search => !s.finished)
          (fun s => round xs d n st s) k s) ∧
        (LeanExe.repeatWhile.go (fun s : Search => !s.finished)
          (fun s => round xs d n st s) k s).finished = true
  | 0, s, _, hk => absurd hk (by have := fin_card_le n s; omega)
  | k + 1, s, h, hk => by
    simp only [LeanExe.repeatWhile.go]
    cases hf : s.finished
    · simp only [Bool.not_false, ↓reduceIte]
      obtain ⟨h', hr⟩ := round_opt h hf hn2 hW hNW
      rcases hr with hr | hr
      · rw [go_done hr]; exact ⟨h', hr⟩
      · exact go_opt hn2 hW hNW k _ h' (by omega)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h, by simp [hf]⟩

/-- The goal is finalized when the graph has a walk to it. -/
theorem done_goal {W : Nat} {s : Search} (h : Opt xs d n st W (fun w _ => w = 1) s)
    (hfin : s.finished = true) (hn2 : 2 ≤ n.toNat)
    (hW : ∀ a b : UInt64, a.toNat < n.toNat → b.toNat < n.toNat → (wt xs d st a b).toNat ≤ W)
    (hNW : (n.toNat + 1) * W < 2 ^ 62) {p : Nat → UInt64} {m : Nat}
    (hw : Walk xs d n p m 1) : dn s 1 = true := by
  rcases h.stop hfin with h1 | hall
  · exact h1
  · by_contra h1'
    have h1 : dn s 1 = false := by simpa using h1'
    obtain ⟨hp0, hpm, hpe⟩ := hw
    classical
    have hex : ∃ j, dn s (p j) = false := ⟨m, by rw [hpm]; exact h1⟩
    obtain ⟨j, hj, hjmin⟩ : ∃ j, dn s (p j) = false ∧ ∀ i < j, dn s (p i) = true :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by simpa using Nat.find_min hex hi⟩
    have hjm : j ≤ m := by
      by_contra hc
      have := hjmin m (by omega)
      rw [hpm, h1] at this; exact absurd this (by decide)
    rcases j with _ | i
    · have h0r : (p 0).toNat < n.toNat := by rw [hp0]; simp only [UInt64.reduceToNat]; omega
      have := hall (p 0) h0r hj (by rw [hp0]; rfl)
      rw [hp0, h.zero] at this
      exact absurd this (by decide)
    · have hdi := hjmin i (by omega)
      have he := hpe i (by omega)
      have hpi1 : p i ≠ 1 := fun e => by rw [e, h1] at hdi; exact absurd hdi (by decide)
      have hr := h.relaxed (p i) (p (i + 1)) hdi hj he hpi1
      have hinf := hall (p (i + 1)) he.2.1 hj he.2.2.2.1
      have hbi := h.bound (p i) he.1 (h.doneFin (p i) he.1 hdi)
      have hwi := hW (p i) (p (i + 1)) he.1 he.2.1
      rw [hinf, inf_toNat] at hr
      have := fin_card_le n s
      have hmul : (fin n s).card * W ≤ n.toNat * W := Nat.mul_le_mul_right _ this
      have e : (n.toNat + 1) * W = n.toNat * W + W := by ring
      omega

/-- The parent chain of the goal is a walk whose cost is the goal's cost. -/
theorem chain_walk {W : Nat} {s : Search} (h : Opt xs d n st W (fun w _ => w = 1) s)
    {K : Nat} {node : Nat → UInt64} (hn0 : node 0 = 0) (hK : node K = 1)
    (hlt : ∀ g ≤ K, (node g).toNat < n.toNat)
    (hpar : ∀ g < K, node (g + 1) ≠ 0 ∧ par s (node (g + 1)) = node g)
    (hc1 : cst s 1 ≠ infinity) :
    Walk xs d n node K 1 ∧ pathCost xs d st node K = (cst s 1).toNat := by
  have hfin : ∀ i ≤ K, cst s (node (K - i)) ≠ infinity := by
    intro i hi
    induction i with
    | zero => rw [Nat.sub_zero, hK]; exact hc1
    | succ i ih =>
      have ih' := ih (by omega)
      obtain ⟨hne0, hp⟩ := hpar (K - (i + 1)) (by omega)
      have e : K - (i + 1) + 1 = K - i := by omega
      rw [e] at hne0 hp
      have hvr := hlt (K - i) (by omega)
      have hl : Link xs d n s (node (K - i)) := by
        cases hd : dn s (node (K - i))
        · exact h.inv.linkOpen _ hvr hne0 hd ih'
        · exact h.inv.linkDone _ hvr hne0 hd
      rw [← hp]
      exact h.doneFin _ hl.1 hl.2.1
  have hstep : ∀ g < K, Edge xs d n (node g) (node (g + 1)) ∧
      (cst s (node (g + 1))).toNat =
        (cst s (node g)).toNat + (wt xs d st (node g) (node (g + 1))).toNat := by
    intro g hg
    obtain ⟨hne0, hp⟩ := hpar g hg
    have := hfin (K - (g + 1)) (by omega)
    rw [show K - (K - (g + 1)) = g + 1 by omega] at this
    have he := h.edge (node (g + 1)) (hlt (g + 1) hg) hne0 this
    rw [hp] at he
    exact he
  have hcost : ∀ m ≤ K, pathCost xs d st node m = (cst s (node m)).toNat := by
    intro m hm
    induction m with
    | zero => simp [pathCost, hn0, h.zero]
    | succ m ih =>
      rw [pathCost_succ, ih (by omega), (hstep m (by omega)).2]
  refine ⟨⟨hn0, hK, fun g hg => (hstep g hg).1⟩, ?_⟩
  rw [hcost K le_rfl, hK]

end Proofs

/-! ### The plan -/

theorem output_head {xs : Array Float} {d : Dims} {s : Search} {n st : UInt64}
    (hc : s.cost[(1 : UInt64).toNat]! ≠ infinity) (hk : (pathLength s n).toNat ≤ 1026) :
    (output xs d s n st)[0]! = 1.0 ∧
      (output xs d s n st)[2]! = (s.cost[(1 : UInt64).toNat]!).toFloat := by
  have hne : (s.cost[(1 : UInt64).toNat]! == infinity) = false := by simpa using hc
  simp only [output, hne, Bool.false_eq_true, ite_false]
  have hsz : (8 + 11 * pathLength s n).toNat = 8 + 11 * (pathLength s n).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  rw [LeanExe.IR.build_get (by rw [hsz]; omega), LeanExe.IR.build_get (by rw [hsz]; omega)]
  exact ⟨rfl, rfl⟩

/-- **Optimality of the slew planner.**  Let the input pass `validInput`, and let its start and
goal pass the static check.  When the graph that the program's checks define has a walk from the
start to the goal, the output has status 1, its `K` segments join the nodes of such a walk,
`node 0 = 0` to `node K = 1`, as `segValue` gives each field of each segment, its header reports
the cost of the walk, and no walk from the start to the goal costs less.  When the graph has no
such walk, the output has status 0. -/
theorem plan_optimal {xs : Array Float} (hv : validInput xs = true)
    (h1 : attitudeOk xs (dims xs) (q4At xs 8) 0.0 = true)
    (h2 : attitudeOk xs (dims xs) (q4At xs 12) 0.0 = true) :
    ((∃ p m, Walk xs (dims xs) ((dims xs).nw + 2) p m 1) →
      (plan xs)[0]! = 1.0 ∧ ∃ K : Nat, ∃ node : Nat → UInt64,
        (plan xs).size = 8 + 11 * K ∧ Walk xs (dims xs) ((dims xs).nw + 2) node K 1 ∧
        (∀ g < K, ∀ f < 11, (plan xs)[4 + 11 * g + f]! =
          segValue xs (dims xs) (ceilMs (rd xs 6)) (node g) (node (g + 1)) (UInt64.ofNat f)) ∧
        (plan xs)[2]! =
          (UInt64.ofNat (pathCost xs (dims xs) (ceilMs (rd xs 6)) node K)).toFloat ∧
        ∀ p m, Walk xs (dims xs) ((dims xs).nw + 2) p m 1 →
          pathCost xs (dims xs) (ceilMs (rd xs 6)) node K ≤
            pathCost xs (dims xs) (ceilMs (rd xs 6)) p m) ∧
    ((¬ ∃ p m, Walk xs (dims xs) ((dims xs).nw + 2) p m 1) → (plan xs)[0]! = 0.0) := by
  have hnw := (Demos.Slew.Valid.valid_good hv).2.2
  have hn : ((dims xs).nw + 2).toNat = (dims xs).nw.toNat + 2 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  have hn2 : 2 ≤ ((dims xs).nw + 2).toNat := by omega
  have hW : ∀ a b : UInt64, a.toNat < ((dims xs).nw + 2).toNat →
      b.toNat < ((dims xs).nw + 2).toNat →
      (wt xs (dims xs) (ceilMs (rd xs 6)) a b).toNat ≤ 2 ^ 34 := fun a b ha hb =>
    Cost.edge_cost_le (a := a) (b := b) hv (by omega) (by omega)
  have hNW : (((dims xs).nw + 2).toNat + 1) * 2 ^ 34 < 2 ^ 62 := by rw [hn]; omega
  have hS : Opt xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6)) (2 ^ 34) (fun w _ => w = 1)
        (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6))) ∧
      (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6))).finished = true := by
    unfold search LeanExe.repeatWhile
    have hn1 : ((dims xs).nw + 2 + 1).toNat = ((dims xs).nw + 2).toNat + 1 := by
      rw [UInt64.toNat_add, hn]; simp only [UInt64.reduceToNat]; omega
    rw [hn1]
    exact go_opt hn2 hW hNW _ _ (initial_opt _ _ hn2) (by omega)
  obtain ⟨hopt, hfin⟩ := hS
  have hp := plan_output hv h1 h2
  have hk := pathLength_le (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6)))
    ((dims xs).nw + 2)
  have path : (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6))).cost[(1 : UInt64).toNat]!
      ≠ infinity → (plan xs)[0]! = 1.0 ∧ ∃ K : Nat, ∃ node : Nat → UInt64,
        (plan xs).size = 8 + 11 * K ∧ Walk xs (dims xs) ((dims xs).nw + 2) node K 1 ∧
        (∀ g < K, ∀ f < 11, (plan xs)[4 + 11 * g + f]! =
          segValue xs (dims xs) (ceilMs (rd xs 6)) (node g) (node (g + 1)) (UInt64.ofNat f)) ∧
        (plan xs)[2]! =
          (UInt64.ofNat (pathCost xs (dims xs) (ceilMs (rd xs 6)) node K)).toFloat ∧
        pathCost xs (dims xs) (ceilMs (rd xs 6)) node K =
          (cst (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6))) 1).toNat := by
    intro hc
    obtain ⟨h0, h2'⟩ := output_head (xs := xs) (d := dims xs) (n := (dims xs).nw + 2)
      (st := ceilMs (rd xs 6)) hc (by omega)
    have hs : (plan xs)[0]! = 1.0 := by rw [hp]; exact h0
    obtain ⟨_, K, hsz, node, hn0, hK, hlt, _, hseg, _, hpar⟩ := plan_segments hs hnw
    obtain ⟨hwalk, hcost⟩ := chain_walk hopt hn0 hK (fun g hg => by rw [hn]; exact hlt g hg)
      hpar hc
    refine ⟨hs, K, node, hsz, hwalk, hseg, ?_, hcost⟩
    rw [hp, h2', hcost]
    show _ = (UInt64.ofNat (UInt64.toNat _)).toFloat
    rw [UInt64.ofNat_toNat]
    rfl
  refine ⟨fun ⟨p, m, hw⟩ => ?_, fun hno => ?_⟩
  · have hd1 := done_goal hopt hfin hn2 hW hNW hw
    have h1r : (1 : UInt64).toNat < ((dims xs).nw + 2).toNat := by
      simp only [UInt64.reduceToNat]; omega
    have hc := hopt.doneFin 1 h1r hd1
    obtain ⟨hs, K, node, hsz, hwalk, hseg, hhead, hcost⟩ := path hc
    refine ⟨hs, K, node, hsz, hwalk, hseg, hhead, fun q r hq => ?_⟩
    rw [hcost]
    exact hopt.lower 1 h1r hd1 q r hq
  · by_cases hc :
        (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6))).cost[(1 : UInt64).toNat]! =
          infinity
    · rw [hp, output_zero hc, statusOnly_zero]
    · obtain ⟨_, K, node, _, hwalk, _⟩ := path hc
      exact absurd ⟨node, K, hwalk⟩ hno

end Demos.Slew.Optimal
