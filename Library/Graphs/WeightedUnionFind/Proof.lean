import Library.Graphs.WeightedUnionFind.Program
import Library.Graphs.WeightedUnionFind.Spec
import Library.Graphs.UnionFind.Proof

/-! The proof that `classes` labels each element with the least element of its class, with the
invariant `Inv` of the module of Algorithm E.  A link from an element `j` to the root of its tree
keeps a forest, since the rank of the forest rises from `j` to its root, and it keeps the root of
every element, so path compression keeps `Inv`.  `unite` then links one root to the other in either
direction, which `link_inv` covers, and the labeling loop is the one of the module of Algorithm E,
which `labels_spec` covers for any links that satisfy `Inv`.  The sizes decide only the direction of
a link, so the proof does not use them. -/

namespace Library.Graphs.WeightedUnionFind

open LeanExe.Dialect
open Library.Graphs.UnionFind

/-- Along the links of a forest the rank does not fall. -/
theorem rank_mono {n : Nat} {p : Array UInt64} (hb : ∀ x < n, up p x < n) {h : Nat → Nat}
    (hh : ∀ x < n, up p x ≠ x → h x < h (up p x)) {y : Nat} (hy : y < n) :
    ∀ k, h y ≤ h ((up p)^[k] y)
  | 0 => le_rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    have hz := iter_lt hb hy k
    by_cases e : up p ((up p)^[k] y) = (up p)^[k] y
    · rw [e]; exact rank_mono hb hh hy k
    · exact le_trans (rank_mono hb hh hy k) (Nat.le_of_lt (hh _ hz e))

/-- An element that is not a root has a lower rank than its root. -/
theorem rank_lt_root {n : Nat} {p : Array UInt64} (hf : Forest n p) {h : Nat → Nat}
    (hh : ∀ x < n, up p x ≠ x → h x < h (up p x)) {x : Nat} (hx : x < n) (hr : up p x ≠ x) :
    h x < h (rootOf n p x) := by
  have hn : 0 < n := by omega
  have e : rootOf n p x = (up p)^[n - 1] (up p x) := by
    unfold rootOf
    rw [← Function.iterate_succ_apply, show (n - 1).succ = n by omega]
  rw [e]
  exact lt_of_lt_of_le (hh x hx hr) (rank_mono hf.bound hh (hf.bound x hx) (n - 1))

/-- On a forest where `R` takes the same value at every element below `n` and at its parent, and
where `R` fixes every root below `n`, the root of every element below `n` is its value under `R`. -/
theorem rootOf_eq_of {n : Nat} {q : Array UInt64} (hq : Forest n q) (R : Nat → Nat)
    (hstep : ∀ y < n, R (up q y) = R y) (hfix : ∀ z < n, up q z = z → R z = z) {y : Nat}
    (hy : y < n) : rootOf n q y = R y := by
  have hk : ∀ k, R ((up q)^[k] y) = R y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', hstep _ (iter_lt hq.bound hy k), ih]
  rw [← hfix _ (rootOf_lt hq hy) (rootOf_root hq hy)]
  exact hk n

theorem up_set (p : Array UInt64) (i : Nat) (v : UInt64) (hi : i < p.size) (x : Nat) :
    up (p.set! i v) x = if x = i then v.toNat else up p x := by
  rw [up, set_get p i v hi]
  split <;> rfl

/-- A link from `j` to its root keeps a forest and the root of every element. -/
theorem link_root {n : Nat} {p : Array UInt64} (hf : Forest n p) {j : Nat} (hj : j < n)
    (r : UInt64) (hr : rootOf n p j = r.toNat) (hjr : j ≠ r.toNat) :
    Forest n (p.set! j r) ∧ ∀ y < n, rootOf n (p.set! j r) y = rootOf n p y := by
  have hs : j < p.size := by rw [hf.size]; exact hj
  have hup := up_set p j r hs
  have hjroot : up p j ≠ j := fun e => hjr (by rw [← hr, rootOf_eq_of_root hf hj (d := 0) e]; rfl)
  obtain ⟨h, hh⟩ := hf.rank
  have hq : Forest n (p.set! j r) := by
    refine ⟨by rw [set_size, hf.size], fun x hx => ?_, ⟨h, fun x hx hxq => ?_⟩⟩
    · rw [hup]
      split
      · rw [← hr]; exact rootOf_lt hf hj
      · exact hf.bound x hx
    · rw [hup] at hxq ⊢
      split
      · rename_i e
        subst e
        rw [← hr]
        exact rank_lt_root hf hh hx hjroot
      · rw [ite_eq_right (by assumption)] at hxq
        exact hh x hx hxq
  refine ⟨hq, fun y hy => rootOf_eq_of hq (rootOf n p) (fun z hz => ?_) (fun z hz hzq => ?_) hy⟩
  · rw [hup]
    split
    · rename_i e
      subst e
      rw [← hr, rootOf_eq_of_root hf (rootOf_lt hf hz) (d := 0) (rootOf_root hf hz)]
      rfl
    · exact rootOf_up hf hz
  · rw [hup] at hzq
    split at hzq
    · rename_i e
      exact absurd (hzq.trans e).symm hjr
    · exact rootOf_eq_of_root hf hz (d := 0) hzq

/-- Path compression from `j` to its root `r` keeps a forest and the root of every element, and
gives each element its old parent or its root as parent. -/
theorem compress_spec {n : Nat} (r : UInt64) :
    ∀ (m : Nat) (F : UInt64) (p : Array UInt64) (j : UInt64), F.toNat = m → Forest n p →
      j.toNat < n → rootOf n p j.toNat = r.toNat →
      Forest n (compress p j r F) ∧
        (∀ y < n, rootOf n (compress p j r F) y = rootOf n p y) ∧
        ∀ x < n, up (compress p j r F) x = up p x ∨ up (compress p j r F) x = rootOf n p x := by
  intro m
  induction m with
  | zero =>
    intro F p j hF hf _ _
    rw [compress, ite_eq_right (by rw [UInt64.lt_iff_toNat_lt]; simp [hF])]
    exact ⟨hf, fun _ _ => rfl, fun _ _ => .inl rfl⟩
  | succ m ih =>
    intro F p j hF hf hj hr
    have h0 : 0 < F := by rw [UInt64.lt_iff_toNat_lt]; simp [hF]
    rw [compress, ite_eq_left h0]
    by_cases hjr : j = r
    · rw [ite_eq_left hjr]
      exact ⟨hf, fun _ _ => rfl, fun _ _ => .inl rfl⟩
    rw [ite_eq_right hjr]
    dsimp only
    have hjr' : j.toNat ≠ r.toNat := fun e => hjr (UInt64.toNat_inj.mp e)
    obtain ⟨hq, hroots⟩ := link_root hf hj r hr hjr'
    have hnext : p[j.toNat]!.toNat < n := hf.bound _ hj
    have hF1 : (F - 1).toNat = m := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp; omega
    obtain ⟨f1, f2, f3⟩ := ih (F - 1) (p.set! j.toNat r) p[j.toNat]! hF1 hq hnext
      (by rw [hroots _ hnext]; exact (rootOf_up hf hj).trans hr)
    refine ⟨f1, fun y hy => (f2 y hy).trans (hroots y hy), fun x hx => ?_⟩
    have hup := up_set p j.toNat r (by rw [hf.size]; exact hj) x
    rcases f3 x hx with e | e
    · rw [e, hup]
      split
      · rename_i e'
        subst e'
        exact .inr hr.symm
      · exact .inl rfl
    · rw [e, hroots x hx]
      exact .inr rfl

theorem root_toNat {n : Nat} {p : Array UInt64} (hf : Forest n p) (hn : n < 2 ^ 64)
    (N : UInt64) (hN : N.toNat = n) (j : UInt64) (hj : j.toNat < n) :
    (root p j N).toNat = rootOf n p j.toNat := by
  conv => lhs; rw [← UInt64.ofNat_toNat (x := j)]
  exact root_eq hf hn hj N (by omega)

/-- `unite` for pair `t` keeps `Inv`. -/
theorem unite_inv (N : UInt64) (js ks : Array UInt64) {t : Nat} (htj : t < js.size)
    (htk : t < ks.size) {p : Array UInt64} (size : Array UInt64) (hi : Inv N.toNat js ks t p) :
    Inv N.toNat js ks (t + 1) (unite N js[t]! ks[t]! p size).1 := by
  have hN := UInt64.toNat_lt N
  have hf := hi.forest
  unfold unite
  by_cases hc : js[t]! < N ∧ ks[t]! < N
  swap
  · rw [ite_eq_right hc]
    refine inv_keep hi ?_
    by_cases ha : js[t]!.toNat < N.toNat
    · exact .inr (.inl fun hb => hc ⟨UInt64.lt_iff_toNat_lt.mpr ha, UInt64.lt_iff_toNat_lt.mpr hb⟩)
    · exact .inl ha
  rw [ite_eq_left hc]
  dsimp only
  have ha : js[t]!.toNat < N.toNat := UInt64.lt_iff_toNat_lt.mp hc.1
  have hb : ks[t]!.toNat < N.toNat := UInt64.lt_iff_toNat_lt.mp hc.2
  have hrj := root_toNat hf hN N rfl js[t]! ha
  have hrk := root_toNat hf hN N rfl ks[t]! hb
  obtain ⟨c1, c2, c3⟩ := compress_spec (root p js[t]! N) _ N p js[t]! rfl hf ha hrj.symm
  obtain ⟨d1, d2, d3⟩ := compress_spec (root p ks[t]! N) _ N
    (compress p js[t]! (root p js[t]! N) N) ks[t]! rfl c1 hb (by rw [c2 _ hb]; exact hrk.symm)
  generalize compress (compress p js[t]! (root p js[t]! N) N) ks[t]! (root p ks[t]! N) N = q
    at d1 d2 d3 ⊢
  have hroots : ∀ y < N.toNat, rootOf N.toNat q y = rootOf N.toNat p y :=
    fun y hy => (d2 y hy).trans (c2 y hy)
  have hq : Inv N.toNat js ks t q := by
    refine ⟨d1, fun x hx => ?_, fun s hs hsj hsk hsa hsb => ?_⟩
    · have hlink : ∀ z, z = up p x ∨ z = rootOf N.toNat p x →
          Relation.EqvGen (PairedBelow N.toNat js ks t) x z := by
        rintro z (rfl | rfl)
        · exact hi.link x hx
        · exact eqv_iter hi hx N.toNat
      rcases d3 x hx with e | e
      · rcases c3 x hx with e' | e'
        · exact hlink _ (.inl (e.trans e'))
        · exact hlink _ (.inr (e.trans e'))
      · exact hlink _ (.inr (e.trans (c2 x hx)))
    · rw [hroots _ hsa, hroots _ hsb]
      exact hi.pairs s hs hsj hsk hsa hsb
  by_cases he : root p js[t]! N = root p ks[t]! N
  · rw [ite_eq_left he]
    exact inv_keep hq (.inr (.inr (by rw [hroots _ ha, hroots _ hb, ← hrj, ← hrk, he])))
  rw [ite_eq_right he]
  have hne : rootOf N.toNat p js[t]!.toNat ≠ rootOf N.toNat p ks[t]!.toNat :=
    fun e => he (UInt64.toNat_inj.mp (by rw [hrj, hrk, e]))
  have hqs : q.size = N.toNat := d1.size
  split <;> dsimp only
  · refine link_inv hq htj htk ha hb (.inl ⟨by rw [hroots _ ha], by rw [hroots _ hb]⟩) hne
      (by rw [set_size, hqs]) fun x => ?_
    rw [up_set q _ _ (by rw [hqs, hrj]; exact rootOf_lt hf ha), hrj, hrk]
  · refine link_inv hq htj htk ha hb (.inr ⟨by rw [hroots _ hb], by rw [hroots _ ha]⟩)
      (Ne.symm hne) (by rw [set_size, hqs]) fun x => ?_
    rw [up_set q _ _ (by rw [hqs, hrk]; exact rootOf_lt hf hb), hrj, hrk]

/-- The loop of `forest` over all pairs keeps `Inv` for the pairs of both arrays. -/
theorem forest_inv (N : UInt64) (js ks : Array UInt64) (hjs : js.size < 2 ^ 64)
    (hks : ks.size < 2 ^ 64) : Inv N.toNat js ks (min js.size ks.size) (forest N js ks) := by
  have hm : (if js.size.toUInt64 ≤ ks.size.toUInt64 then js.size.toUInt64
      else ks.size.toUInt64).toNat = min js.size ks.size := by
    split
    · rename_i h
      rw [UInt64.le_iff_toNat_le, Library.Graphs.UnionFind.size_toUInt64 hjs,
        Library.Graphs.UnionFind.size_toUInt64 hks] at h
      rw [Library.Graphs.UnionFind.size_toUInt64 hjs]
      omega
    · rename_i h
      rw [UInt64.le_iff_toNat_le, Library.Graphs.UnionFind.size_toUInt64 hjs,
        Library.Graphs.UnionFind.size_toUInt64 hks] at h
      rw [Library.Graphs.UnionFind.size_toUInt64 hks]
      omega
  unfold forest
  simp only
  rw [← hm]
  apply loop_induction (P := fun t (st : Array UInt64 × Array UInt64) => Inv N.toNat js ks t st.1)
    (inv_init N js ks)
  intro t st ht hp
  rw [hm] at ht
  have h64 : (UInt64.ofNat t).toNat = t := toNat_ofNat_lt (by omega)
  rw [h64]
  exact unite_inv N js ks (by omega) (by omega) st.2 hp

/-- For arrays of fewer than `2^64` words, `classes` labels each element below `n` with the least
element of its class. -/
theorem classes_spec (N : UInt64) (js ks : Array UInt64) (hjs : js.size < 2 ^ 64)
    (hks : ks.size < 2 ^ 64) : LeastLabels N.toNat js ks (classes N js ks) :=
  labels_spec N js ks (forest N js ks) (forest_inv N js ks hjs hks)

end Library.Graphs.WeightedUnionFind
