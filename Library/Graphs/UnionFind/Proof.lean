import Library.Graphs.UnionFind.Program
import Library.Graphs.UnionFind.Spec
import LeanExe.Dialect.Lemmas

/-! The proof that `classes` labels each element with the least element of its class.  `Forest`
states that the parent links form a forest: a rank rises along every link from an element that is
not a root, so the elements on a path are distinct, and `n` steps from an element below `n` reach
its root, `rootOf`.  `Inv` adds that every link joins equivalent elements and that the two elements
of every pair taken so far that lie below `n` have the same root.  `merge_inv` shows that steps E3
and E4 keep `Inv`, `equivalent_iff` turns it into the statement that two elements are equivalent
exactly when they have the same root, and the loop of `classes` records the least element of each
root. -/

namespace Library.Graphs.UnionFind

open LeanExe.Dialect

theorem set_get (a : Array UInt64) (i : Nat) (v : UInt64) (hi : i < a.size) (k : Nat) :
    (a.set! i v)[k]! = if k = i then v else a[k]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hk : k < a.size
  · rw [getElem!_pos _ k (by simpa using hk), Array.getElem_setIfInBounds (by simpa using hk),
      getElem!_pos a k hk]
    by_cases h : k = i <;> simp_all [eq_comm]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg a k hk]
    have : k ≠ i := by omega
    simp [this]

theorem set_size (a : Array UInt64) (i : Nat) (v : UInt64) : (a.set! i v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (UInt64.ofNat x).toNat = x := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- The parent of `x` in `p`, as a natural number. -/
def up (p : Array UInt64) (x : Nat) : Nat := p[x]!.toNat

/-- The element that `n` steps along the links of `p` reach from `x`, which on a forest of `n`
elements is the root of the tree that holds `x`. -/
def rootOf (n : Nat) (p : Array UInt64) (x : Nat) : Nat := (up p)^[n] x

/-- The links of `p` form a forest on the elements below `n`: every link stays below `n`, and a
rank rises along the link of every element that is not a root. -/
structure Forest (n : Nat) (p : Array UInt64) : Prop where
  size : p.size = n
  bound : ∀ x < n, up p x < n
  rank : ∃ h : Nat → Nat, ∀ x < n, up p x ≠ x → h x < h (up p x)

theorem iter_lt {n : Nat} {p : Array UInt64} (hb : ∀ x < n, up p x < n) {x : Nat} (hx : x < n) :
    ∀ k, (up p)^[k] x < n
  | 0 => hx
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact hb _ (iter_lt hb hx k)

theorem iter_stay {p : Array UInt64} {x d m : Nat} (hr : up p ((up p)^[d] x) = (up p)^[d] x)
    (hdm : d ≤ m) : (up p)^[m] x = (up p)^[d] x := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdm
  rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_fixed hr]

/-- On a forest of `n` elements, fewer than `n` steps from an element reach a root: the ranks of
the first `n + 1` elements of a path without a root would rise, so the elements would be
distinct, and only `n` exist. -/
theorem exists_root {n : Nat} {p : Array UInt64} (hf : Forest n p) {x : Nat} (hx : x < n) :
    ∃ d < n, up p ((up p)^[d] x) = (up p)^[d] x := by
  obtain ⟨h, hh⟩ := hf.rank
  by_contra hne
  push Not at hne
  have mono : ∀ b a, a < b → b ≤ n → h ((up p)^[a] x) < h ((up p)^[b] x) := by
    intro b
    induction b with
    | zero => intro a hab; omega
    | succ b ih =>
      intro a hab hb
      have step : h ((up p)^[b] x) < h ((up p)^[b + 1] x) := by
        rw [Function.iterate_succ_apply']
        exact hh _ (iter_lt hf.bound hx b) (hne b (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hab | rfl
      · exact lt_trans (ih a hab (by omega)) step
      · exact step
  obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (n + 1)) (t := Finset.range n) (f := fun d => (up p)^[d] x)
    (by simp) (by intro d _; simpa using iter_lt hf.bound hx d)
  simp only [Finset.mem_range] at ha hb
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have := mono b a hlt (by omega)
    rw [heq] at this
    exact lt_irrefl _ this
  · have := mono a b hlt (by omega)
    rw [heq] at this
    exact lt_irrefl _ this

theorem rootOf_eq_of_root {n : Nat} {p : Array UInt64} (hf : Forest n p) {x d : Nat} (hx : x < n)
    (hr : up p ((up p)^[d] x) = (up p)^[d] x) : rootOf n p x = (up p)^[d] x := by
  obtain ⟨d0, hd0, hr0⟩ := exists_root hf hx
  unfold rootOf
  rw [iter_stay hr0 hd0.le]
  rcases le_total d d0 with h | h
  · exact iter_stay hr h
  · exact (iter_stay hr0 h).symm

theorem rootOf_root {n : Nat} {p : Array UInt64} (hf : Forest n p) {x : Nat} (hx : x < n) :
    up p (rootOf n p x) = rootOf n p x := by
  obtain ⟨d0, _, hr0⟩ := exists_root hf hx
  rw [rootOf_eq_of_root hf hx hr0]
  exact hr0

theorem rootOf_lt {n : Nat} {p : Array UInt64} (hf : Forest n p) {x : Nat} (hx : x < n) :
    rootOf n p x < n :=
  iter_lt hf.bound hx n

theorem rootOf_up {n : Nat} {p : Array UInt64} (hf : Forest n p) {x : Nat} (hx : x < n) :
    rootOf n p (up p x) = rootOf n p x := by
  unfold rootOf
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact rootOf_root hf hx

theorem root_at_root (p : Array UInt64) {x : Nat} (hx : x < 2 ^ 64) (hr : up p x = x)
    (F : UInt64) : (root p (UInt64.ofNat x) F).toNat = x := by
  have hp : p[x]! = UInt64.ofNat x := by
    apply UInt64.toNat_inj.mp
    rw [toNat_ofNat_lt hx]
    exact hr
  rw [root]
  simp [toNat_ofNat_lt hx, hp]

/-- Step E3 with a count of at least `d` steps returns the root `d` steps above `x`. -/
theorem root_iter {n : Nat} {p : Array UInt64} (hb : ∀ x < n, up p x < n) (hn : n < 2 ^ 64) :
    ∀ d x (F : UInt64), x < n → d ≤ F.toNat → up p ((up p)^[d] x) = (up p)^[d] x →
      (root p (UInt64.ofNat x) F).toNat = (up p)^[d] x := by
  intro d
  induction d with
  | zero =>
    intro x F hx _ hr
    rw [Function.iterate_zero_apply] at hr ⊢
    exact root_at_root p (by omega) hr F
  | succ d ih =>
    intro x F hx hdF hr
    by_cases hxr : up p x = x
    · rw [Function.iterate_fixed hxr]
      exact root_at_root p (by omega) hxr F
    · have hF : 0 < F := by
        rw [UInt64.lt_iff_toNat_lt]
        simp only [UInt64.reduceToNat]
        omega
      have hpx : p[x]! = UInt64.ofNat (up p x) := by rw [up, UInt64.ofNat_toNat]
      have hne : ¬p[x]! = UInt64.ofNat x := fun e => hxr (by rw [up, e, toNat_ofNat_lt (by omega)])
      have hsub : d ≤ (F - 1).toNat := by
        have := UInt64.toNat_lt F
        simp only [UInt64.toNat_sub, UInt64.reduceToNat]
        omega
      rw [root]
      simp only [hF, ↓reduceIte, toNat_ofNat_lt (show x < 2 ^ 64 by omega), hne]
      rw [hpx, ih (up p x) (F - 1) (hb x hx) hsub (by rwa [← Function.iterate_succ_apply]),
        ← Function.iterate_succ_apply]

/-- Step E3 with the count `n` returns the root. -/
theorem root_eq {n : Nat} {p : Array UInt64} (hf : Forest n p) (hn : n < 2 ^ 64) {x : Nat}
    (hx : x < n) (F : UInt64) (hF : n ≤ F.toNat) :
    (root p (UInt64.ofNat x) F).toNat = rootOf n p x := by
  obtain ⟨d0, hd0, hr0⟩ := exists_root hf hx
  rw [rootOf_eq_of_root hf hx hr0]
  exact root_iter hf.bound hn d0 x F hx (by omega) hr0

/-- The forest after a link from the root `ra` to the root `rb`: the ranks of the trees other than
that of `ra` rise above the rank of `ra`. -/
theorem forest_link {n : Nat} {p q : Array UInt64} (hf : Forest n p) (hsize : q.size = n)
    {ra rb : Nat} (hra : ra < n) (hrb : rb < n) (hroota : up p ra = ra) (hrootb : up p rb = rb)
    (hne : ra ≠ rb) (hup : ∀ x, up q x = if x = ra then rb else up p x) : Forest n q := by
  obtain ⟨h, hh⟩ := hf.rank
  refine ⟨hsize, fun x hx => ?_,
    ⟨fun x => if rootOf n p x = ra then h x else h x + h ra + 1, fun x hx hxq => ?_⟩⟩
  · rw [hup]
    split
    · exact hrb
    · exact hf.bound x hx
  · by_cases hxa : x = ra
    · subst hxa
      have h1 : rootOf n p x = x := rootOf_eq_of_root hf hra (d := 0) hroota
      have h2 : rootOf n p rb = rb := rootOf_eq_of_root hf hrb (d := 0) hrootb
      simp only [hup, ↓reduceIte, h1, h2, Ne.symm hne]
      omega
    · simp only [hup, hxa, ↓reduceIte] at hxq ⊢
      rw [rootOf_up hf hx]
      split
      · exact hh x hx hxq
      · have := hh x hx hxq
        omega

/-- After the link from `ra` to `rb`, the root of an element of the tree of `ra` is `rb`, and the
root of every other element stays. -/
theorem rootOf_link {n : Nat} {p q : Array UInt64} (hf : Forest n p) (hq : Forest n q)
    {ra rb : Nat} (hroota : up p ra = ra) (hrootb : up p rb = rb) (hne : ra ≠ rb)
    (hup : ∀ x, up q x = if x = ra then rb else up p x) {y : Nat} (hy : y < n) :
    rootOf n q y = if rootOf n p y = ra then rb else rootOf n p y := by
  obtain ⟨d0, _, hr0⟩ := exists_root hf hy
  have hR : rootOf n p y = (up p)^[d0] y := rootOf_eq_of_root hf hy hr0
  have agree : ∀ k, (∀ i < k, (up p)^[i] y ≠ ra) → (up q)^[k] y = (up p)^[k] y := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih (fun i hi => hk i (by omega)), hup, ite_eq_right (hk k (by omega))]
  by_cases hroot : rootOf n p y = ra
  · rw [ite_eq_left hroot]
    have hex : ∃ k, (up p)^[k] y = ra := ⟨d0, hR ▸ hroot⟩
    have hk : (up p)^[Nat.find hex] y = ra := Nat.find_spec hex
    have h1 : (up q)^[Nat.find hex + 1] y = rb := by
      rw [Function.iterate_succ_apply', agree _ (fun i hi => Nat.find_min hex hi), hk, hup,
        ite_eq_left rfl]
    rw [rootOf_eq_of_root hq hy (d := Nat.find hex + 1)
      (by rw [h1, hup, ite_eq_right (Ne.symm hne), hrootb]), h1]
  · rw [ite_eq_right hroot]
    have hav : ∀ i < d0, (up p)^[i] y ≠ ra := by
      intro i hi heq
      have := iter_stay (x := y) (d := i) (m := d0) (by rw [heq]; exact hroota) hi.le
      exact hroot (by rw [hR, this, heq])
    have hq0 : (up q)^[d0] y = (up p)^[d0] y := agree d0 hav
    have hd0 : (up p)^[d0] y ≠ ra := fun e => hroot (by rw [hR, e])
    rw [rootOf_eq_of_root hq hy (d := d0) (by rw [hq0, hup, ite_eq_right hd0, hr0]), hq0, hR]

/-- Pair `s`, for `s` below `t`, relates `a` and `b`. -/
def PairedBelow (n : Nat) (js ks : Array UInt64) (t a b : Nat) : Prop :=
  ∃ s < t, s < js.size ∧ s < ks.size ∧ js[s]!.toNat = a ∧ ks[s]!.toNat = b ∧ a < n ∧
    b < n

theorem pairedBelow_mono {n : Nat} {js ks : Array UInt64} {t u : Nat} (htu : t ≤ u) {a b : Nat}
    (h : PairedBelow n js ks t a b) : PairedBelow n js ks u a b := by
  obtain ⟨s, hs, rest⟩ := h
  exact ⟨s, by omega, rest⟩

/-- The state of the loop of `forest` after the pairs below `t`: the links form a forest, every
link joins two equivalent elements, and the two elements of every pair taken so far whose elements
are below `n` have the same root. -/
structure Inv (n : Nat) (js ks : Array UInt64) (t : Nat) (p : Array UInt64) : Prop where
  forest : Forest n p
  link : ∀ x < n, Relation.EqvGen (PairedBelow n js ks t) x (up p x)
  pairs : ∀ s < t, s < js.size → s < ks.size → js[s]!.toNat < n → ks[s]!.toNat < n →
    rootOf n p js[s]!.toNat = rootOf n p ks[s]!.toNat

theorem eqv_iter {n : Nat} {js ks : Array UInt64} {t : Nat} {p : Array UInt64}
    (hi : Inv n js ks t p) {x : Nat} (hx : x < n) :
    ∀ k, Relation.EqvGen (PairedBelow n js ks t) x ((up p)^[k] x)
  | 0 => .refl x
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact .trans _ _ _ (eqv_iter hi hx k) (hi.link _ (iter_lt hi.forest.bound hx k))

theorem eqv_mono {n : Nat} {js ks : Array UInt64} {t u : Nat} (htu : t ≤ u) {a b : Nat}
    (h : Relation.EqvGen (PairedBelow n js ks t) a b) :
    Relation.EqvGen (PairedBelow n js ks u) a b :=
  Relation.EqvGen.mono (fun _ _ h' => pairedBelow_mono htu h') _ _ h

theorem inv_init (N : UInt64) (js ks : Array UInt64) :
    Inv N.toNat js ks 0 (LeanExe.build N fun i => i) := by
  have hup : ∀ x < N.toNat, up (LeanExe.build N fun i => i) x = x := by
    intro x hx
    rw [up, build_get hx, toNat_ofNat_lt (lt_trans hx (UInt64.toNat_lt N))]
  refine ⟨⟨build_size N _, fun x hx => by rw [hup x hx]; exact hx,
    ⟨fun _ => 0, fun x hx hne => absurd (hup x hx) hne⟩⟩, fun x hx => ?_,
    fun s hs => absurd hs (by omega)⟩
  rw [hup x hx]
  exact .refl x

/-- `Inv` for the pairs below `t + 1` holds for links that satisfy it for the pairs below `t`, when
pair `t` has an element of `n` or more or has both elements in one tree. -/
theorem inv_keep {n : Nat} {js ks : Array UInt64} {t : Nat} {p : Array UInt64}
    (hi : Inv n js ks t p)
    (hpair : ¬js[t]!.toNat < n ∨ ¬ks[t]!.toNat < n ∨
      rootOf n p js[t]!.toNat = rootOf n p ks[t]!.toNat) :
    Inv n js ks (t + 1) p := by
  refine ⟨hi.forest, fun x hx => eqv_mono (by omega) (hi.link x hx),
    fun s hs hsj hsk ha hb => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
  · exact hi.pairs s hs hsj hsk ha hb
  · rcases hpair with h | h | h
    · exact absurd ha h
    · exact absurd hb h
    · exact h

/-- A link from the root of one element of pair `t` to the root of the other, in either direction,
takes `Inv` from the pairs below `t` to the pairs below `t + 1`. -/
theorem link_inv {n : Nat} {js ks : Array UInt64} {t : Nat} {p q : Array UInt64}
    (hi : Inv n js ks t p) (htj : t < js.size) (htk : t < ks.size) (ha : js[t]!.toNat < n)
    (hb : ks[t]!.toNat < n) {ra rb : Nat}
    (hr : (ra = rootOf n p js[t]!.toNat ∧ rb = rootOf n p ks[t]!.toNat) ∨
      (ra = rootOf n p ks[t]!.toNat ∧ rb = rootOf n p js[t]!.toNat))
    (hne : ra ≠ rb) (hsize : q.size = n) (hup : ∀ x, up q x = if x = ra then rb else up p x) :
    Inv n js ks (t + 1) q := by
  have hf := hi.forest
  have hra : ra < n ∧ up p ra = ra := by
    rcases hr with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
    · exact ⟨rootOf_lt hf ha, rootOf_root hf ha⟩
    · exact ⟨rootOf_lt hf hb, rootOf_root hf hb⟩
  have hrb : rb < n ∧ up p rb = rb := by
    rcases hr with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e]
    · exact ⟨rootOf_lt hf hb, rootOf_root hf hb⟩
    · exact ⟨rootOf_lt hf ha, rootOf_root hf ha⟩
  have hq : Forest n q := forest_link hf hsize hra.1 hrb.1 hra.2 hrb.2 hne hup
  have hpair : PairedBelow n js ks (t + 1) js[t]!.toNat ks[t]!.toNat :=
    ⟨t, by omega, htj, htk, rfl, rfl, ha, hb⟩
  have h1 := eqv_mono (Nat.le_succ t) (eqv_iter hi ha n)
  have h2 := eqv_mono (Nat.le_succ t) (eqv_iter hi hb n)
  refine ⟨hq, fun x hx => ?_, fun s hs hsj hsk hsa hsb => ?_⟩
  · rw [hup]
    by_cases hx' : x = ra
    · rw [ite_eq_left hx', hx']
      rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]
        exact .trans _ _ _ (.symm _ _ h1) (.trans _ _ _ (.rel _ _ hpair) h2)
      · rw [e1, e2]
        exact .trans _ _ _ (.symm _ _ h2) (.trans _ _ _ (.symm _ _ (.rel _ _ hpair)) h1)
    · rw [ite_eq_right hx']
      exact eqv_mono (Nat.le_succ t) (hi.link x hx)
  · rw [rootOf_link hf hq hra.2 hrb.2 hne hup hsa, rootOf_link hf hq hra.2 hrb.2 hne hup hsb]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · rw [hi.pairs s hs hsj hsk hsa hsb]
    · rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> split_ifs <;> omega

/-- Steps E3 and E4 for pair `t` keep `Inv`. -/
theorem merge_inv (N : UInt64) (js ks : Array UInt64) {t : Nat} (htj : t < js.size)
    (htk : t < ks.size) {p : Array UInt64} (hi : Inv N.toNat js ks t p) :
    Inv N.toNat js ks (t + 1) (merge N js[t]! ks[t]! p) := by
  have hN := UInt64.toNat_lt N
  have hf := hi.forest
  unfold merge
  by_cases hj : js[t]! < N
  · by_cases hk : ks[t]! < N
    · have ha : js[t]!.toNat < N.toNat := UInt64.lt_iff_toNat_lt.mp hj
      have hb : ks[t]!.toNat < N.toNat := UInt64.lt_iff_toNat_lt.mp hk
      have hrj : (root p js[t]! N).toNat = rootOf N.toNat p js[t]!.toNat := by
        conv => lhs; rw [← UInt64.ofNat_toNat (x := js[t]!)]
        exact root_eq hf hN ha N le_rfl
      have hrk : (root p ks[t]! N).toNat = rootOf N.toNat p ks[t]!.toNat := by
        conv => lhs; rw [← UInt64.ofNat_toNat (x := ks[t]!)]
        exact root_eq hf hN hb N le_rfl
      simp only [hj, hk, ↓reduceIte]
      by_cases he : root p js[t]! N = root p ks[t]! N
      · rw [ite_eq_left he]
        exact inv_keep hi (.inr (.inr (by rw [← hrj, ← hrk, he])))
      · rw [ite_eq_right he]
        have hne : rootOf N.toNat p js[t]!.toNat ≠ rootOf N.toNat p ks[t]!.toNat :=
          fun e => he (UInt64.toNat_inj.mp (by rw [hrj, hrk, e]))
        refine link_inv hi htj htk ha hb (.inl ⟨rfl, rfl⟩) hne (by rw [set_size, hf.size])
          fun x => ?_
        rw [up, set_get p _ _ (by rw [hrj, hf.size]; exact rootOf_lt hf ha), hrj]
        split
        · exact hrk
        · rfl
    · simp only [hj, hk, ↓reduceIte]
      exact inv_keep hi (.inr (.inl fun h => hk (UInt64.lt_iff_toNat_lt.mpr h)))
  · simp only [hj, ↓reduceIte]
    exact inv_keep hi (.inl fun h => hj (UInt64.lt_iff_toNat_lt.mpr h))

theorem size_toUInt64 {s : Nat} (h : s < 2 ^ 64) : s.toUInt64.toNat = s := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  omega

/-- Steps E1 and E2 over all pairs keep `Inv` for the pairs of both arrays. -/
theorem forest_inv (N : UInt64) (js ks : Array UInt64) (hjs : js.size < 2 ^ 64)
    (hks : ks.size < 2 ^ 64) : Inv N.toNat js ks (min js.size ks.size) (forest N js ks) := by
  have hm : (if js.size.toUInt64 ≤ ks.size.toUInt64 then js.size.toUInt64
      else ks.size.toUInt64).toNat = min js.size ks.size := by
    split
    · rename_i h
      rw [UInt64.le_iff_toNat_le, size_toUInt64 hjs, size_toUInt64 hks] at h
      rw [size_toUInt64 hjs]
      omega
    · rename_i h
      rw [UInt64.le_iff_toNat_le, size_toUInt64 hjs, size_toUInt64 hks] at h
      rw [size_toUInt64 hks]
      omega
  unfold forest
  simp only
  rw [← hm]
  apply loop_induction (P := fun t p => Inv N.toNat js ks t p) (inv_init N js ks)
  intro t p ht hp
  rw [hm] at ht
  have h64 : (UInt64.ofNat t).toNat = t := toNat_ofNat_lt (by omega)
  rw [h64]
  exact merge_inv N js ks (by omega) (by omega) hp

theorem pairedBelow_min (n : Nat) (js ks : Array UInt64) :
    PairedBelow n js ks (min js.size ks.size) = Paired n js ks := by
  funext a b
  apply propext
  constructor
  · rintro ⟨s, _, hsj, hsk, rest⟩
    exact ⟨s, hsj, hsk, rest⟩
  · rintro ⟨s, hsj, hsk, rest⟩
    exact ⟨s, by omega, hsj, hsk, rest⟩

theorem equivalent_lt {n : Nat} {js ks : Array UInt64} {x y : Nat}
    (h : Equivalent n js ks x y) : x = y ∨ (x < n ∧ y < n) := by
  induction h with
  | rel a b hab =>
    obtain ⟨_, _, _, _, _, ha, hb⟩ := hab
    exact .inr ⟨ha, hb⟩
  | refl => exact .inl rfl
  | symm _ _ _ ih =>
    rcases ih with h | h
    · exact .inl h.symm
    · exact .inr ⟨h.2, h.1⟩
  | trans _ _ _ _ _ ih1 ih2 =>
    rcases ih1 with rfl | h1
    · exact ih2
    · rcases ih2 with rfl | h2
      · exact .inr h1
      · exact .inr ⟨h1.1, h2.2⟩

/-- After all pairs, two elements are equivalent exactly when they have the same root. -/
theorem equivalent_iff {n : Nat} {js ks : Array UInt64} {p : Array UInt64}
    (hi : Inv n js ks (min js.size ks.size) p) {x y : Nat} (hx : x < n) (hy : y < n) :
    Equivalent n js ks x y ↔ rootOf n p x = rootOf n p y := by
  have hrel : PairedBelow n js ks (min js.size ks.size) = Paired n js ks := pairedBelow_min n js ks
  constructor
  · intro h
    clear hx hy
    induction h with
    | rel a b hab =>
      obtain ⟨s, hsj, hsk, rfl, rfl, ha, hb⟩ := hab
      exact hi.pairs s (by omega) hsj hsk ha hb
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    have h1 := eqv_iter hi hx n
    have h2 := eqv_iter hi hy n
    rw [hrel] at h1 h2
    change Equivalent n js ks x (rootOf n p x) at h1
    change Equivalent n js ks y (rootOf n p y) at h2
    rw [h] at h1
    exact .trans _ _ _ h1 (.symm _ _ h2)

/-- The state of the loop of `classes` after the elements below `i`: `first` holds at each root the
least element below `i` with that root, or `n` when there is none, and `out` holds at each
element below `i` the least element with its root. -/
def LabelInv (N : UInt64) (p : Array UInt64) (i : Nat) (s : Array UInt64 × Array UInt64) : Prop :=
  s.1.size = N.toNat ∧ s.2.size = N.toNat ∧
    (∀ r < N.toNat, (s.1[r]! = N ∧ ∀ y < i, rootOf N.toNat p y ≠ r) ∨
      (s.1[r]!.toNat < i ∧ rootOf N.toNat p s.1[r]!.toNat = r ∧
        ∀ y < s.1[r]!.toNat, rootOf N.toNat p y ≠ r)) ∧
    ∀ x < i, s.2[x]!.toNat ≤ x ∧ rootOf N.toNat p s.2[x]!.toNat = rootOf N.toNat p x ∧
      ∀ y < s.2[x]!.toNat, rootOf N.toNat p y ≠ rootOf N.toNat p x

theorem label_step (N : UInt64) {p : Array UInt64} (hf : Forest N.toNat p) {i : Nat}
    (hiN : i < N.toNat) (s : Array UInt64 × Array UInt64) (hs : LabelInv N p i s) :
    LabelInv N p (i + 1)
      (let r := root p (UInt64.ofNat i) N
       let least := if s.1[r.toNat]! = N then UInt64.ofNat i else s.1[r.toNat]!
       (s.1.set! r.toNat least, s.2.set! (UInt64.ofNat i).toNat least)) := by
  obtain ⟨h1, h2, hfirst, hout⟩ := hs
  have hN := UInt64.toNat_lt N
  have hi64 : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
  have hR : (root p (UInt64.ofNat i) N).toNat = rootOf N.toNat p i := root_eq hf hN hiN N le_rfl
  have hRn : rootOf N.toNat p i < N.toNat := rootOf_lt hf hiN
  simp only [hR, hi64]
  set R := rootOf N.toNat p i with hR_def
  by_cases hfR : s.1[R]! = N
  · simp only [hfR, ↓reduceIte]
    have hnone : ∀ y < i, rootOf N.toNat p y ≠ R := by
      rcases hfirst R hRn with ⟨_, h⟩ | ⟨h, _, _⟩
      · exact h
      · rw [hfR] at h
        omega
    refine ⟨by rw [set_size, h1], by rw [set_size, h2], fun r hr => ?_, fun x hx => ?_⟩
    · rw [set_get _ _ _ (by rw [h1]; exact hRn)]
      by_cases hrR : r = R
      · rw [ite_eq_left hrR, hi64]
        exact .inr ⟨by omega, by rw [hrR], fun y hy => by rw [hrR]; exact hnone y hy⟩
      · rw [ite_eq_right hrR]
        rcases hfirst r hr with ⟨he, hy⟩ | ⟨hl, hroot, hmin⟩
        · refine .inl ⟨he, fun y hy' => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hy' with hy' | rfl
          · exact hy y hy'
          · exact fun e => hrR e.symm
        · exact .inr ⟨by omega, hroot, hmin⟩
    · rw [set_get _ _ _ (by rw [h2]; exact hiN)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · rw [ite_eq_right (by omega)]
        exact hout x hx
      · rw [ite_eq_left rfl, hi64]
        exact ⟨le_rfl, rfl, hnone⟩
  · simp only [hfR, ↓reduceIte]
    obtain ⟨hl, hroot, hmin⟩ : s.1[R]!.toNat < i ∧ rootOf N.toNat p s.1[R]!.toNat = R ∧
        ∀ y < s.1[R]!.toNat, rootOf N.toNat p y ≠ R := by
      rcases hfirst R hRn with ⟨he, _⟩ | h
      · exact absurd he hfR
      · exact h
    refine ⟨by rw [set_size, h1], by rw [set_size, h2], fun r hr => ?_, fun x hx => ?_⟩
    · rw [set_get _ _ _ (by rw [h1]; exact hRn)]
      by_cases hrR : r = R
      · rw [ite_eq_left hrR]
        subst hrR
        exact .inr ⟨by omega, hroot, hmin⟩
      · rw [ite_eq_right hrR]
        rcases hfirst r hr with ⟨he, hy⟩ | ⟨hl', hroot', hmin'⟩
        · refine .inl ⟨he, fun y hy' => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hy' with hy' | rfl
          · exact hy y hy'
          · exact fun e => hrR e.symm
        · exact .inr ⟨by omega, hroot', hmin'⟩
    · rw [set_get _ _ _ (by rw [h2]; exact hiN)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · rw [ite_eq_right (by omega)]
        exact hout x hx
      · rw [ite_eq_left rfl]
        exact ⟨by omega, hroot, hmin⟩

/-- The loop of `classes`, on any parent links that satisfy `Inv` for all the pairs, labels each
element below `n` with the least element of its class. -/
theorem labels_spec (N : UInt64) (js ks p : Array UInt64)
    (hi : Inv N.toNat js ks (min js.size ks.size) p) :
    LeastLabels N.toNat js ks
      (LeanExe.loop N (LeanExe.build N fun _ => N, LeanExe.build N fun _ => (0 : UInt64))
        fun i s =>
          let r := root p i N
          let least := if s.1[r.toNat]! = N then i else s.1[r.toNat]!
          (s.1.set! r.toNat least, s.2.set! i.toNat least)).2 := by
  have hf := hi.forest
  have hN := UInt64.toNat_lt N
  have hloop := loop_induction (n := N)
    (init := (LeanExe.build N fun _ => N, LeanExe.build N fun _ => (0 : UInt64)))
    (f := fun i s =>
      let r := root p i N
      let least := if s.1[r.toNat]! = N then i else s.1[r.toNat]!
      (s.1.set! r.toNat least, s.2.set! i.toNat least))
    (fun i s => LabelInv N p i s)
    ⟨build_size N _, build_size N _,
      fun r hr => .inl ⟨build_get hr, fun _ h => absurd h (by omega)⟩,
      fun _ h => absurd h (by omega)⟩
    (fun i s hiN hs => label_step N hf hiN s hs)
  obtain ⟨_, hsize, _, hout⟩ := hloop
  refine ⟨hsize, fun i hiN => ⟨?_, fun j hj => ?_⟩⟩
  · obtain ⟨hle, hroot, _⟩ := hout i hiN
    exact (equivalent_iff hi hiN (by omega)).mpr hroot.symm
  · obtain ⟨hle, hroot, hmin⟩ := hout i hiN
    rcases equivalent_lt hj with rfl | ⟨_, hjn⟩
    · exact hle
    · by_contra hlt
      exact hmin j (by omega) ((equivalent_iff hi hiN hjn).mp hj).symm

/-- For arrays of fewer than `2^64` words, `classes` labels each element below `n` with the least
element of its class. -/
theorem classes_spec (N : UInt64) (js ks : Array UInt64) (hjs : js.size < 2 ^ 64)
    (hks : ks.size < 2 ^ 64) : LeastLabels N.toNat js ks (classes N js ks) :=
  labels_spec N js ks (forest N js ks) (forest_inv N js ks hjs hks)

end Library.Graphs.UnionFind
