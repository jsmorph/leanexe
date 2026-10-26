import Demos.Slew.Program
import LeanExe.IR.Combinators
import LeanExe.ProofKit.F64Bits

/-! The path structure of the search.  `Inv` holds of every state of `search`: a node other than
the start that has a finite cost or is finalized has a finalized parent, and `edgeOk` accepted
the edge from that parent (`Link`); and the parent chain of a finalized node reaches the start
through finalized nodes within fewer steps than there are finalized nodes.  `relax` changes the
parent only of nodes that are not finalized, so the chains of finalized nodes persist.  The
chain from the goal therefore reaches the start within `n` steps, the fuel of `pathLength`, and
every segment of a plan joins two nodes by an accepted edge (`plan_segments`). -/

namespace Demos.Slew.Search

open Demos.Slew

/-- `edgeOk` accepts the edge from node `u` to node `v`. -/
def Accepted (xs : Array Float) (d : Dims) (u v : UInt64) : Prop :=
  edgeOk xs d (nodeAt xs d u) (relative (nodeAt xs d u) (nodeAt xs d v)) = true

def par (s : Search) (v : UInt64) : UInt64 := s.parent[v.toNat]!
def dn (s : Search) (v : UInt64) : Bool := s.done[v.toNat]!
def cst (s : Search) (v : UInt64) : UInt64 := s.cost[v.toNat]!

/-- The finalized nodes. -/
def fin (n : UInt64) (s : Search) : Finset ℕ :=
  (Finset.range n.toNat).filter fun i => dn s (UInt64.ofNat i) = true

/-- Node `v` has a finalized parent whose edge to `v` was accepted. -/
def Link (xs : Array Float) (d : Dims) (n : UInt64) (s : Search) (v : UInt64) : Prop :=
  (par s v).toNat < n.toNat ∧ dn s (par s v) = true ∧ Accepted xs d (par s v) v

structure Inv (xs : Array Float) (d : Dims) (n : UInt64) (s : Search) : Prop where
  costSize : s.cost.size = n.toNat
  parentSize : s.parent.size = n.toNat
  doneSize : s.done.size = n.toNat
  linkOpen : ∀ v : UInt64, v.toNat < n.toNat → v ≠ 0 → dn s v = false → cst s v ≠ infinity →
    Link xs d n s v
  linkDone : ∀ v : UInt64, v.toNat < n.toNat → v ≠ 0 → dn s v = true → Link xs d n s v
  reach : ∀ v : UInt64, v.toNat < n.toNat → dn s v = true →
    ∃ j, j < (fin n s).card ∧ (par s)^[j] v = 0 ∧ ∀ i < j, dn s ((par s)^[i] v) = true

/-! ### Arrays -/

theorem get_set_eq {α : Type} [Inhabited α] {a : Array α} {i : Nat} (hi : i < a.size) (v : α) :
    (a.set! i v)[i]! = v := by
  simp [Array.set!_eq_setIfInBounds, hi]

theorem get_set_ne {α : Type} [Inhabited α] {a : Array α} {i j : Nat} (h : j ≠ i) (v : α) :
    (a.set! i v)[j]! = a[j]! := by
  simp [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Ne.symm h]

theorem size_set {α : Type} (a : Array α) (i : Nat) (v : α) : (a.set! i v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

theorem ofNat_toNat_lt {i : Nat} (h : i < 2 ^ 64) : (UInt64.ofNat i).toNat = i :=
  UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; exact h)

theorem ne_iff_toNat {u v : UInt64} : u ≠ v ↔ u.toNat ≠ v.toNat :=
  not_congr UInt64.toNat_inj.symm

/-! ### States with the same arrays -/

theorem inv_congr {xs : Array Float} {d : Dims} {n : UInt64} {s s' : Search}
    (hc : s'.cost = s.cost) (hp : s'.parent = s.parent) (hd : s'.done = s.done)
    (h : Inv xs d n s) : Inv xs d n s' := by
  have ep : par s' = par s := by funext v; simp only [par, hp]
  have ed : dn s' = dn s := by funext v; simp only [dn, hd]
  have ec : cst s' = cst s := by funext v; simp only [cst, hc]
  have ef : fin n s' = fin n s := by simp only [fin, ed]
  have el : Link xs d n s' = Link xs d n s := by funext v; simp only [Link, ep, ed]
  exact ⟨by rw [hc]; exact h.costSize, by rw [hp]; exact h.parentSize,
    by rw [hd]; exact h.doneSize, by rw [el, ed, ec]; exact h.linkOpen,
    by rw [el, ed]; exact h.linkDone, by rw [ef, ep, ed]; exact h.reach⟩

/-! ### The initial state -/

theorem initial_inv (xs : Array Float) (d : Dims) (n : UInt64) : Inv xs d n (initial xs d n) where
  costSize := LeanExe.IR.build_size _ _
  parentSize := LeanExe.IR.build_size _ _
  doneSize := LeanExe.IR.build_size _ _
  linkOpen := by
    intro v hv h0 _ hc
    exfalso; apply hc
    simp only [cst, initial]
    rw [LeanExe.IR.build_get hv, UInt64.ofNat_toNat]
    simp [h0]
  linkDone := by
    intro v hv _ hd
    simp only [dn, initial] at hd
    rw [LeanExe.IR.build_get hv] at hd
    exact absurd hd (by simp)
  reach := by
    intro v hv hd
    simp only [dn, initial] at hd
    rw [LeanExe.IR.build_get hv] at hd
    exact absurd hd (by simp)

/-! ### Selection -/

theorem selectNext_spec (s : Search) (n : UInt64) :
    (selectNext s n).1 = n ∨
      ((selectNext s n).1.toNat < n.toNat ∧ dn s (selectNext s n).1 = false ∧
        cst s (selectNext s n).1 < infinity) := by
  unfold selectNext
  have key := LeanExe.IR.loop_induction (n := n) (init := (n, infinity))
    (f := fun i acc =>
      let c := s.cost[i.toNat]!
      if !s.done[i.toNat]! && s.ok[i.toNat]! && c < acc.2 then (i, c) else acc)
    (fun _ acc => (acc.1 = n ∧ acc.2 = infinity) ∨
      (acc.1.toNat < n.toNat ∧ dn s acc.1 = false ∧ cst s acc.1 = acc.2 ∧ acc.2 < infinity))
    (Or.inl ⟨rfl, rfl⟩)
    (fun k acc hk hacc => by
      dsimp only
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
        right
        have hk' : (UInt64.ofNat k).toNat = k :=
          ofNat_toNat_lt (by have := UInt64.toNat_lt n; omega)
        refine ⟨by rw [hk']; exact hk, hc.1.1, rfl, ?_⟩
        rcases hacc with ⟨_, h2⟩ | ⟨_, _, _, h2⟩
        · rw [← h2]; exact hc.2
        · exact UInt64.lt_iff_toNat_lt.mpr
            (lt_trans (UInt64.lt_iff_toNat_lt.mp hc.2) (UInt64.lt_iff_toNat_lt.mp h2))
      · exact hacc)
  rcases key with ⟨h, _⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, by rw [h3]; exact h4⟩

/-! ### Finalization -/

theorem fin_card_le (n : UInt64) (s : Search) : (fin n s).card ≤ n.toNat := by
  unfold fin
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Finalizing an open node `u` with a finite cost keeps the invariant. -/
theorem finalize_inv {xs : Array Float} {d : Dims} {n : UInt64} {s : Search} (h : Inv xs d n s)
    {u : UInt64} (hu : u.toNat < n.toNat) (hdu : dn s u = false) (hcu : cst s u ≠ infinity)
    (e : UInt64) :
    Inv xs d n { s with done := s.done.set! u.toNat true, examined := e } ∧
      dn { s with done := s.done.set! u.toNat true, examined := e } u = true := by
  set s1 : Search := { s with done := s.done.set! u.toNat true, examined := e }
  have hun : u.toNat < s.done.size := by rw [h.doneSize]; exact hu
  have ep : par s1 = par s := rfl
  have ec : cst s1 = cst s := rfl
  have edu : dn s1 u = true := by
    simp only [dn, s1]; exact get_set_eq hun true
  have edv : ∀ v, v ≠ u → dn s1 v = dn s v := by
    intro v hv
    simp only [dn, s1]
    exact get_set_ne (ne_iff_toNat.mp hv) true
  have mono : ∀ v, dn s v = true → dn s1 v = true := by
    intro v hv
    by_cases e : v = u
    · rw [e]; exact edu
    · rw [edv v e]; exact hv
  have hlink : ∀ v, Link xs d n s v → Link xs d n s1 v := by
    intro v ⟨l1, l2, l3⟩
    exact ⟨l1, by rw [ep]; exact mono _ l2, l3⟩
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
      · exact ⟨hi, mono _ hd⟩
  have hnot : u.toNat ∉ fin n s := by
    simp only [fin, Finset.mem_filter, Finset.mem_range, UInt64.ofNat_toNat, hdu]
    simp
  have hcard : (fin n s1).card = (fin n s).card + 1 := by
    rw [hfin, Finset.card_insert_of_notMem hnot]
  refine ⟨⟨h.costSize, h.parentSize, by simp only [s1]; rw [size_set]; exact h.doneSize, ?_, ?_, ?_⟩,
    edu⟩
  · intro v hv h0 hd hc
    have hvu : v ≠ u := by intro e; rw [e, edu] at hd; exact absurd hd (by simp)
    rw [edv v hvu] at hd
    exact hlink v (h.linkOpen v hv h0 hd (by rw [← ec]; exact hc))
  · intro v hv h0 hd
    by_cases e : v = u
    · rw [e] at h0 ⊢
      exact hlink u (h.linkOpen u hu h0 hdu hcu)
    · rw [edv v e] at hd
      exact hlink v (h.linkDone v hv h0 hd)
  · intro v hv hd
    rw [hcard, ep]
    by_cases e : v = u
    · rw [e]
      by_cases h0 : u = 0
      · exact ⟨0, by omega, by rw [h0]; rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · obtain ⟨l1, l2, _⟩ := h.linkOpen u hu h0 hdu hcu
        obtain ⟨j, hj, hz, hdone⟩ := h.reach (par s u) l1 l2
        refine ⟨j + 1, by omega, by rw [Function.iterate_succ_apply]; exact hz, ?_⟩
        intro i hi
        rcases i with _ | i
        · simp only [Function.iterate_zero, id]; exact edu
        · rw [Function.iterate_succ_apply]; exact mono _ (hdone i (by omega))
    · rw [edv v e] at hd
      obtain ⟨j, hj, hz, hdone⟩ := h.reach v hv hd
      exact ⟨j, by omega, hz, fun i hi => mono _ (hdone i hi)⟩

/-! ### Relaxation -/

/-- Setting the parent of an open node `v` to a finalized node `u` whose edge to `v` was
accepted keeps the invariant. -/
theorem update_inv {xs : Array Float} {d : Dims} {n : UInt64} {st : Search} (h : Inv xs d n st)
    {u v : UInt64} (hv : v.toNat < n.toNat) (hdv : dn st v = false) (hu : u.toNat < n.toNat)
    (hdu : dn st u = true) (ha : Accepted xs d u v) (c : UInt64) :
    Inv xs d n { st with cost := st.cost.set! v.toNat c, parent := st.parent.set! v.toNat u } := by
  set st' : Search := { st with cost := st.cost.set! v.toNat c, parent := st.parent.set! v.toNat u }
  have hvp : v.toNat < st.parent.size := by rw [h.parentSize]; exact hv
  have ed : dn st' = dn st := rfl
  have epv : par st' v = u := get_set_eq hvp u
  have epw : ∀ w, w ≠ v → par st' w = par st w := fun w e => get_set_ne (ne_iff_toNat.mp e) u
  have ecw : ∀ w, w ≠ v → cst st' w = cst st w := fun w e => get_set_ne (ne_iff_toNat.mp e) c
  have ef : fin n st' = fin n st := by simp only [fin, ed]
  have hne : ∀ w, dn st w = true → w ≠ v := by
    intro w hw e; rw [e, hdv] at hw; exact absurd hw (by simp)
  refine ⟨by simp only [st']; rw [size_set]; exact h.costSize,
    by simp only [st']; rw [size_set]; exact h.parentSize, h.doneSize, ?_, ?_, ?_⟩
  · intro w hw h0 hd hc
    by_cases e : w = v
    · rw [e]
      exact ⟨by rw [epv]; exact hu, by rw [epv, ed]; exact hdu, by rw [epv]; exact ha⟩
    · rw [ed] at hd
      obtain ⟨l1, l2, l3⟩ := h.linkOpen w hw h0 hd (by rw [← ecw w e]; exact hc)
      exact ⟨by rw [epw w e]; exact l1, by rw [epw w e, ed]; exact l2, by rw [epw w e]; exact l3⟩
  · intro w hw h0 hd
    rw [ed] at hd
    have e := hne w hd
    obtain ⟨l1, l2, l3⟩ := h.linkDone w hw h0 hd
    exact ⟨by rw [epw w e]; exact l1, by rw [epw w e, ed]; exact l2, by rw [epw w e]; exact l3⟩
  · intro w hw hd
    rw [ed] at hd
    obtain ⟨j, hj, hz, hdone⟩ := h.reach w hw hd
    have hiter : ∀ i ≤ j, (par st')^[i] w = (par st)^[i] w := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
        exact epw _ (hne _ (hdone i (by omega)))
    refine ⟨j, by rw [ef]; exact hj, by rw [hiter j le_rfl]; exact hz, fun i hi => ?_⟩
    rw [hiter i hi.le, ed]; exact hdone i hi

theorem relax_inv {xs : Array Float} {d : Dims} {n : UInt64} {s : Search} (h : Inv xs d n s)
    {u : UInt64} (hu : u.toNat < n.toNat) (hdu : dn s u = true) (settleTicks : UInt64) :
    Inv xs d n (relax xs d n u settleTicks s) := by
  unfold relax
  dsimp only
  refine (LeanExe.IR.loop_induction (P := fun _ st => Inv xs d n st ∧ st.done = s.done)
    ⟨h, rfl⟩ ?_).1
  intro k st hk ⟨hi, hd⟩
  have hdn : dn st = dn s := by funext w; simp only [dn, hd]
  split
  · exact ⟨hi, hd⟩
  rename_i hc
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, not_or, Bool.not_eq_false] at hc
  split
  · exact ⟨hi, hd⟩
  split
  · split
    · rename_i _ hacc
      refine ⟨update_inv hi ?_ ?_ hu (by rw [hdn]; exact hdu) hacc _, hd⟩
      · rw [ofNat_toNat_lt (by have := UInt64.toNat_lt n; omega)]; exact hk
      · simp only [dn]; simpa using hc.1.1
    · exact ⟨hi, hd⟩
  · exact ⟨hi, hd⟩

theorem round_inv {xs : Array Float} {d : Dims} {n : UInt64} {s : Search} (h : Inv xs d n s)
    (settleTicks : UInt64) : Inv xs d n (round xs d n settleTicks s) := by
  unfold round
  have spec := selectNext_spec s n
  generalize selectNext s n = p at spec ⊢
  obtain ⟨u, c⟩ := p
  dsimp only at spec ⊢
  by_cases hun : (u == n) = true
  · rw [ite_eq_left hun]; exact inv_congr (s := s) rfl rfl rfl h
  rw [ite_eq_right hun]
  have hun' : u ≠ n := by simpa using hun
  rcases spec with e | ⟨hu, hdu, hcu⟩
  · exact absurd e hun'
  have hcu' : cst s u ≠ infinity := by
    intro e; rw [e] at hcu; exact absurd hcu (by decide)
  obtain ⟨h1, hd1⟩ := finalize_inv h hu hdu hcu' (s.examined + 1)
  set s1 : Search := { s with done := s.done.set! u.toNat true, examined := s.examined + 1 }
  by_cases h1u : (u == 1) = true
  · rw [ite_eq_left h1u]; exact inv_congr (s := s1) rfl rfl rfl h1
  · rw [ite_eq_right h1u]; exact relax_inv h1 hu hd1 settleTicks

theorem repeatWhile_induction {α : Type} {P : α → Prop} {fuel : UInt64} {init : α}
    {cond : α → Bool} {step : α → α} (h0 : P init) (hs : ∀ s, P s → P (step s)) :
    P (LeanExe.repeatWhile fuel init cond step) := by
  unfold LeanExe.repeatWhile
  suffices ∀ k s, P s → P (LeanExe.repeatWhile.go cond step k s) from this _ _ h0
  intro k
  induction k with
  | zero => intro s hsP; simpa [LeanExe.repeatWhile.go] using hsP
  | succ k ih =>
    intro s hsP
    simp only [LeanExe.repeatWhile.go]
    split
    · exact ih _ (hs _ hsP)
    · exact hsP

theorem search_inv (xs : Array Float) (d : Dims) (n settleTicks : UInt64) :
    Inv xs d n (search xs d n settleTicks) :=
  repeatWhile_induction (initial_inv xs d n) (fun _ h => round_inv h settleTicks)

/-! ### The path -/

theorem loop_const {α : Type} (m : UInt64) (x : α) (g : α → α) :
    LeanExe.loop m x (fun _ y => g y) = g^[m.toNat] x := by
  unfold LeanExe.loop
  generalize m.toNat = k
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, ih, Function.iterate_succ_apply']

theorem go_path (s : Search) : ∀ (j fuel : Nat) (v c : UInt64), j ≤ fuel → j < 2 ^ 32 →
    (par s)^[j] v = 0 → (∀ i < j, (par s)^[i] v ≠ 0) →
    LeanExe.repeatWhile.go (fun p : UInt64 × UInt64 => p.1 != 0)
      (fun p => (s.parent[p.1.toNat]!, p.2 + 1)) fuel (v, c) = (0, c + UInt64.ofNat j) := by
  intro j
  induction j with
  | zero =>
    intro fuel v c _ _ hz _
    simp only [Function.iterate_zero, id] at hz
    rw [hz]
    cases fuel with
    | zero => simp [LeanExe.repeatWhile.go]
    | succ f => simp [LeanExe.repeatWhile.go]
  | succ j ih =>
    intro fuel v c hf hj hz hne
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hv : v ≠ 0 := hne 0 (by omega)
    have h1 := ih f (par s v) (c + 1) (by omega) (by omega)
      (by rw [← Function.iterate_succ_apply]; exact hz)
      (fun i hi => by rw [← Function.iterate_succ_apply]; exact hne (i + 1) (by omega))
    simp only [LeanExe.repeatWhile.go, bne_iff_ne, ne_eq, hv, not_false_eq_true, ite_true]
    rw [show s.parent[v.toNat]! = par s v from rfl, h1]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, ofNat_toNat_lt (by omega),
      ofNat_toNat_lt (by omega)]
    simp only [UInt64.reduceToNat]
    omega

/-- The output's segment fields for the segment from node `a` to node `b`, as `segmentField`
computes them. -/
def segValue (xs : Array Float) (d : Dims) (settleTicks a b f : UInt64) : Float :=
  let qa := nodeAt xs d a
  let rel := relative qa (nodeAt xs d b)
  let sn := Float.sqrt (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z)
  let big : Bool := sn ≥ axisMin
  if f == 0 then qa.w else if f == 1 then qa.x else if f == 2 then qa.y else if f == 3 then qa.z
  else if f == 4 then (if big then rel.x / sn else 1.0)
  else if f == 5 then (if big then rel.y / sn else 0.0)
  else if f == 6 then (if big then rel.z / sn else 0.0)
  else if f == 7 then angleOf rel
  else if f == 8 then (slewTicks (angleOf rel) (rd xs 4) (rd xs 5) + settleTicks).toFloat
  else if f == 9 then a.toFloat
  else b.toFloat

theorem segmentField_eq (xs : Array Float) (d : Dims) (s : Search) (k settleTicks g f : UInt64) :
    segmentField xs d s k settleTicks g f =
      segValue xs d settleTicks (pathNode s k g) (pathNode s k (g + 1)) f := rfl

theorem statusOnly_zero (status : Float) (e : UInt64) : (statusOnly status e)[0]! = status := by
  unfold statusOnly
  rw [LeanExe.IR.build_get (by decide)]
  rfl

theorem float_ne {a b : Float} (h : a.toBits ≠ b.toBits) : a ≠ b := fun e => h (by rw [e])

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl

theorem neg3_ne : (-3.0 : Float) ≠ 1.0 := float_ne (by
  rw [LeanExe.ProofKit.F64Bits.toBits_neg, show (3.0 : Float).toBits = 0x4008000000000000 from rfl, one_bits]
  decide +kernel)

theorem neg2_ne : (-2.0 : Float) ≠ 1.0 := float_ne (by
  rw [LeanExe.ProofKit.F64Bits.toBits_neg, show (2.0 : Float).toBits = 0x4000000000000000 from rfl, one_bits]
  decide +kernel)

theorem neg1_ne : (-1.0 : Float) ≠ 1.0 := float_ne (by
  rw [LeanExe.ProofKit.F64Bits.toBits_neg, one_bits]
  decide +kernel)

theorem zero_ne : (0.0 : Float) ≠ 1.0 := float_ne (by
  rw [show (0.0 : Float).toBits = 0 from rfl, one_bits]
  decide)

/-! ### The plan -/

theorem plan_invalid {xs : Array Float} (hv : validInput xs = false) :
    plan xs = statusOnly (-3.0) 0 := by
  simp only [plan, hv, Bool.not_false, ite_true]

theorem plan_start {xs : Array Float} (hv : validInput xs = true)
    (h1 : attitudeOk xs (dims xs) (q4At xs 8) 0.0 = false) : plan xs = statusOnly (-1.0) 0 := by
  simp only [plan, hv, h1, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]

theorem plan_goal {xs : Array Float} (hv : validInput xs = true)
    (h1 : attitudeOk xs (dims xs) (q4At xs 8) 0.0 = true)
    (h2 : attitudeOk xs (dims xs) (q4At xs 12) 0.0 = false) : plan xs = statusOnly (-2.0) 0 := by
  simp only [plan, hv, h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false,
    ite_true]

theorem plan_output {xs : Array Float} (hv : validInput xs = true)
    (h1 : attitudeOk xs (dims xs) (q4At xs 8) 0.0 = true)
    (h2 : attitudeOk xs (dims xs) (q4At xs 12) 0.0 = true) :
    plan xs = output xs (dims xs) (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6)))
      ((dims xs).nw + 2) (ceilMs (rd xs 6)) := by
  simp only [plan, hv, h1, h2, Bool.not_true, Bool.false_eq_true, ite_false]

theorem output_zero {xs : Array Float} {d : Dims} {s : Search} {n st : UInt64}
    (hc : s.cost[(1 : UInt64).toNat]! = infinity) : output xs d s n st = statusOnly 0.0 s.examined := by
  simp only [output, hc, beq_self_eq_true, ite_true]

/-- An output of status 1 comes from a validated input with a reached goal. -/
theorem plan_cases {xs : Array Float} (h : (plan xs)[0]! = 1.0) :
    validInput xs = true ∧
      (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6))).cost[(1 : UInt64).toNat]! ≠
        infinity ∧
      plan xs = output xs (dims xs) (search xs (dims xs) ((dims xs).nw + 2) (ceilMs (rd xs 6)))
        ((dims xs).nw + 2) (ceilMs (rd xs 6)) := by
  cases hv : validInput xs
  · rw [plan_invalid hv, statusOnly_zero] at h; exact absurd h neg3_ne
  cases h1 : attitudeOk xs (dims xs) (q4At xs 8) 0.0
  · rw [plan_start hv h1, statusOnly_zero] at h; exact absurd h neg1_ne
  cases h2 : attitudeOk xs (dims xs) (q4At xs 12) 0.0
  · rw [plan_goal hv h1 h2, statusOnly_zero] at h; exact absurd h neg2_ne
  rw [plan_output hv h1 h2] at h ⊢
  refine ⟨rfl, fun hc => ?_, rfl⟩
  rw [output_zero hc, statusOnly_zero] at h
  exact absurd h zero_ne

theorem beq_ofNat (m : Nat) (c : UInt64) (hm : m < 2 ^ 64) :
    (UInt64.ofNat m == c) = decide (m = c.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, ofNat_toNat_lt hm]

/-- The elements of an output of status 1. -/
theorem output_get {xs : Array Float} {d : Dims} {s : Search} {n st : UInt64}
    (hc : s.cost[(1 : UInt64).toNat]! ≠ infinity) {K : Nat} (hK : (pathLength s n).toNat = K)
    (hK1 : K < 2 ^ 20) :
    (output xs d s n st).size = 8 + 11 * K ∧
      (∀ g < K, ∀ f < 11, (output xs d s n st)[4 + 11 * g + f]! =
        segValue xs d st (pathNode s (pathLength s n) (UInt64.ofNat g))
          (pathNode s (pathLength s n) (UInt64.ofNat (g + 1))) (UInt64.ofNat f)) ∧
      (∀ i < 4, (output xs d s n st)[4 + 11 * K + i]! = rd xs (12 + UInt64.ofNat i)) := by
  have hne : (s.cost[(1 : UInt64).toNat]! == infinity) = false := by simpa using hc
  simp only [output, hne, Bool.false_eq_true, ite_false]
  set k := pathLength s n
  have hsz : (8 + 11 * k).toNat = 8 + 11 * K := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hK]; simp only [UInt64.reduceToNat]; omega
  have h4k : (4 + 11 * k).toNat = 4 + 11 * K := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hK]; simp only [UInt64.reduceToNat]; omega
  refine ⟨by rw [LeanExe.IR.build_size, hsz], ?_, ?_⟩
  · intro g hg f hf
    have hm : 4 + 11 * g + f < 2 ^ 64 := by omega
    rw [LeanExe.IR.build_get (by rw [hsz]; omega)]
    have e0 : (UInt64.ofNat (4 + 11 * g + f) == 0) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e1 : (UInt64.ofNat (4 + 11 * g + f) == 1) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e2 : (UInt64.ofNat (4 + 11 * g + f) == 2) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e3 : (UInt64.ofNat (4 + 11 * g + f) == 3) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e4 : UInt64.ofNat (4 + 11 * g + f) < 4 + 11 * k := by
      rw [UInt64.lt_iff_toNat_lt, ofNat_toNat_lt hm, h4k]; omega
    have hsub : (UInt64.ofNat (4 + 11 * g + f) - 4).toNat = 11 * g + f := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, ofNat_toNat_lt hm]; simp only [UInt64.reduceToNat]; omega)]
      rw [ofNat_toNat_lt hm]; simp only [UInt64.reduceToNat]; omega
    have eg : (UInt64.ofNat (4 + 11 * g + f) - 4) / 11 = UInt64.ofNat g := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, hsub, ofNat_toNat_lt (by omega)]; simp only [UInt64.reduceToNat]
      omega
    have ef : (UInt64.ofNat (4 + 11 * g + f) - 4) % 11 = UInt64.ofNat f := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, hsub, ofNat_toNat_lt (by omega)]; simp only [UInt64.reduceToNat]
      omega
    have eg1 : UInt64.ofNat g + 1 = UInt64.ofNat (g + 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
      simp only [UInt64.reduceToNat]; omega
    simp only [e0, e1, e2, e3, Bool.false_eq_true, ite_false]
    rw [ite_eq_left e4, eg, ef, segmentField_eq, eg1]
  · intro i hi
    have hm : 4 + 11 * K + i < 2 ^ 64 := by omega
    rw [LeanExe.IR.build_get (by rw [hsz]; omega)]
    have e0 : (UInt64.ofNat (4 + 11 * K + i) == 0) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e1 : (UInt64.ofNat (4 + 11 * K + i) == 1) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e2 : (UInt64.ofNat (4 + 11 * K + i) == 2) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e3 : (UInt64.ofNat (4 + 11 * K + i) == 3) = false := by
      rw [beq_ofNat _ _ hm]; simp only [UInt64.reduceToNat, decide_eq_false_iff_not]; omega
    have e4 : ¬ UInt64.ofNat (4 + 11 * K + i) < 4 + 11 * k := by
      rw [UInt64.lt_iff_toNat_lt, ofNat_toNat_lt hm, h4k]; omega
    have ei : UInt64.ofNat (4 + 11 * K + i) - 4 - 11 * k = UInt64.ofNat i := by
      apply UInt64.toNat_inj.mp
      have h11 : (11 * k).toNat = 11 * K := by
        rw [UInt64.toNat_mul, hK]; simp only [UInt64.reduceToNat]; omega
      rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_, ofNat_toNat_lt hm, h11,
        ofNat_toNat_lt (by omega)]
      · simp only [UInt64.reduceToNat]; omega
      · rw [UInt64.le_iff_toNat_le, ofNat_toNat_lt hm]; simp only [UInt64.reduceToNat]; omega
      · rw [UInt64.le_iff_toNat_le, h11, UInt64.toNat_sub_of_le _ _ ?_, ofNat_toNat_lt hm]
        · simp only [UInt64.reduceToNat]; omega
        · rw [UInt64.le_iff_toNat_le, ofNat_toNat_lt hm]; simp only [UInt64.reduceToNat]; omega
    simp only [e0, e1, e2, e3, Bool.false_eq_true, ite_false]
    rw [ite_eq_right e4, ei]

/-! ### The segments of a plan -/

/-- Node 1 has a link, and so does every node of its parent chain before the start. -/
theorem chain_links {xs : Array Float} {d : Dims} {n : UInt64} {s : Search} (h : Inv xs d n s)
    (h1n : 1 < n.toNat) (hc : cst s 1 ≠ infinity) {m : Nat}
    (hmin : ∀ i < m, (par s)^[i] 1 ≠ 0) :
    ∀ i < m, ((par s)^[i] 1).toNat < n.toNat ∧ Link xs d n s ((par s)^[i] 1) := by
  intro i hi
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id]
    refine ⟨by simpa using h1n, ?_⟩
    cases hd : dn s 1
    · exact h.linkOpen 1 (by simpa using h1n) (by decide) hd hc
    · exact h.linkDone 1 (by simpa using h1n) (by decide) hd
  | succ i ih =>
    obtain ⟨_, l1, l2, _⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨l1, h.linkDone _ l1 ?_ l2⟩
    have := hmin (i + 1) hi
    rwa [Function.iterate_succ_apply'] at this

/-- The segments of an output of status 1: `K` segments join nodes `node 0 = 0` (the start) to
`node K = 1` (the goal), each by an edge that `edgeOk` accepted. -/
theorem plan_segments {xs : Array Float} (h : (plan xs)[0]! = 1.0)
    (hnw : (dims xs).nw.toNat ≤ 1024) :
    validInput xs = true ∧ ∃ K : Nat, (plan xs).size = 8 + 11 * K ∧ ∃ node : Nat → UInt64,
      node 0 = 0 ∧ node K = 1 ∧ (∀ g ≤ K, (node g).toNat < (dims xs).nw.toNat + 2) ∧
      (∀ g < K, Accepted xs (dims xs) (node g) (node (g + 1))) ∧
      (∀ g < K, ∀ f < 11, (plan xs)[4 + 11 * g + f]! =
        segValue xs (dims xs) (ceilMs (rd xs 6)) (node g) (node (g + 1)) (UInt64.ofNat f)) ∧
      (∀ i < 4, (plan xs)[4 + 11 * K + i]! = rd xs (12 + UInt64.ofNat i)) := by
  obtain ⟨hv, hc, hp⟩ := plan_cases h
  refine ⟨hv, ?_⟩
  set d := dims xs
  set n := d.nw + 2
  set S := search xs d n (ceilMs (rd xs 6))
  have hn : n.toNat = d.nw.toNat + 2 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  have hinv : Inv xs d n S := search_inv xs d n (ceilMs (rd xs 6))
  have hc' : cst S 1 ≠ infinity := hc
  have h1n : 1 < n.toNat := by omega
  -- the chain from the goal reaches the start
  have hl1 : Link xs d n S 1 := by
    cases hd : dn S 1
    · exact hinv.linkOpen 1 (by simpa using h1n) (by decide) hd hc'
    · exact hinv.linkDone 1 (by simpa using h1n) (by decide) hd
  obtain ⟨j, hj, hz, _⟩ := hinv.reach (par S 1) hl1.1 hl1.2.1
  have hex : ∃ m, (par S)^[m] 1 = 0 := ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hz⟩
  classical
  set K := Nat.find hex
  have hK0 : (par S)^[K] 1 = 0 := Nat.find_spec hex
  have hKmin : ∀ i < K, (par S)^[i] 1 ≠ 0 := fun i hi => Nat.find_min hex hi
  have hKle : K ≤ n.toNat := by
    have := Nat.find_min' hex (show (par S)^[j + 1] 1 = 0 by
      rw [Function.iterate_succ_apply]; exact hz)
    have := fin_card_le n S
    omega
  have hpl : pathLength S n = UInt64.ofNat K := by
    unfold pathLength LeanExe.repeatWhile
    rw [go_path S K n.toNat 1 0 hKle (by omega) hK0 hKmin]
    simp
  have hpK : (pathLength S n).toNat = K := by rw [hpl, ofNat_toNat_lt (by omega)]
  have hnode : ∀ g ≤ K, pathNode S (pathLength S n) (UInt64.ofNat g) = (par S)^[K - g] 1 := by
    intro g hg
    unfold pathNode
    rw [loop_const, UInt64.toNat_sub_of_le _ _ ?_, hpK, ofNat_toNat_lt (by omega)]
    · rfl
    · rw [UInt64.le_iff_toNat_le, hpK, ofNat_toNat_lt (by omega)]; exact hg
  have links := chain_links hinv h1n hc' hKmin
  obtain ⟨hsz, hseg, hgoal⟩ := output_get (xs := xs) (d := d) (st := ceilMs (rd xs 6)) hc hpK
    (by omega)
  rw [hp]
  refine ⟨K, hsz, fun g => pathNode S (pathLength S n) (UInt64.ofNat g), ?_, ?_, ?_, ?_, ?_,
    hgoal⟩
  · simp only; rw [hnode 0 (by omega), Nat.sub_zero, hK0]
  · simp only; rw [hnode K le_rfl, Nat.sub_self]; rfl
  · intro g hg
    simp only; rw [hnode g hg, ← hn]
    rcases Nat.eq_zero_or_pos (K - g) with e | e
    · rw [e]; exact h1n
    · rw [show K - g = (K - g - 1) + 1 by omega, Function.iterate_succ_apply']
      exact (links (K - g - 1) (by omega)).2.1
  · intro g hg
    simp only; rw [hnode g hg.le, hnode (g + 1) hg]
    rw [show K - g = (K - (g + 1)) + 1 by omega, Function.iterate_succ_apply']
    exact (links (K - (g + 1)) (by omega)).2.2.2
  · intro g hg f hf
    exact hseg g hg f hf

end Demos.Slew.Search
