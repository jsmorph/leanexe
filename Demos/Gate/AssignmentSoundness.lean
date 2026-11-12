import Demos.Gate.Assignment
import LeanExe.Dialect.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
Soundness of the assignment check.  `weak_duality` states, for integer costs, that an assignment
whose pairs are tight under a dual certificate feasible on every allowed pair has the cost
`Σ u + Σ v`, and that every permutation through allowed pairs costs at least as much.
`check_sound` states that an accepted result of `check` meets the premises of `weak_duality` for
the integers of the `Int64` values, so the proposed assignment has the least cost.
-/

namespace Demos.Gate.Assignment

open Finset

/-! ### The model -/

/-- `f` maps `{0, …, n - 1}` into itself without repeating a value, so it permutes it. -/
def IsPerm (n : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ i < n, f i < n) ∧ ∀ i < n, ∀ j < n, f i = f j → i = j

/-- The pair `(i, j)` of the `n × n` costs `c` is allowed: its cost is not `2⁶³ - 1`. -/
def Allowed (c : Array Int64) (n i j : ℕ) : Prop := c[i * n + j]! ≠ forbidden

/-- The total cost of the assignment `f`, in the integers. -/
def cost (c : Array Int64) (n : ℕ) (f : ℕ → ℕ) : ℤ := ∑ i ∈ range n, (c[i * n + f i]!).toInt

theorem sum_perm {n : ℕ} {f : ℕ → ℕ} (hf : IsPerm n f) (v : ℕ → ℤ) :
    ∑ i ∈ range n, v (f i) = ∑ j ∈ range n, v j := by
  have hinj : Set.InjOn f (range n : Set ℕ) := fun i hi j hj h =>
    hf.2 i (mem_range.mp hi) j (mem_range.mp hj) h
  have himg : (range n).image f = range n := by
    refine eq_of_subset_of_card_le (fun j hj => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      exact mem_range.mpr (hf.1 i (mem_range.mp hi))
    · rw [card_image_of_injOn hinj]
  calc ∑ i ∈ range n, v (f i) = ∑ j ∈ (range n).image f, v j := (sum_image hinj).symm
    _ = ∑ j ∈ range n, v j := by rw [himg]

/-- Weak duality for integer costs. -/
theorem weak_duality {n : ℕ} {C : ℕ → ℕ → ℤ} {A : ℕ → ℕ → Prop} {u v : ℕ → ℤ} {π f : ℕ → ℕ}
    (hπ : IsPerm n π) (htight : ∀ i < n, u i + v (π i) = C i (π i))
    (hfeas : ∀ i < n, ∀ j < n, A i j → u i + v j ≤ C i j)
    (hf : IsPerm n f) (hfa : ∀ i < n, A i (f i)) :
    ∑ i ∈ range n, C i (π i) = ∑ i ∈ range n, u i + ∑ j ∈ range n, v j ∧
      ∑ i ∈ range n, C i (π i) ≤ ∑ i ∈ range n, C i (f i) := by
  have e1 : ∑ i ∈ range n, C i (π i) = ∑ i ∈ range n, (u i + v (π i)) :=
    sum_congr rfl fun i hi => (htight i (mem_range.mp hi)).symm
  have e2 : ∑ i ∈ range n, (u i + v (f i)) ≤ ∑ i ∈ range n, C i (f i) :=
    sum_le_sum fun i hi => hfeas i (mem_range.mp hi) (f i) (hf.1 i (mem_range.mp hi))
      (hfa i (mem_range.mp hi))
  rw [sum_add_distrib, sum_perm hπ v] at e1
  rw [sum_add_distrib, sum_perm hf v] at e2
  exact ⟨e1, e1 ▸ e2⟩

/-! ### The passes -/

theorem inRange_toInt {w : Int64} (h : inRange w = true) :
    -2 ^ 62 < w.toInt ∧ w.toInt < 2 ^ 62 := by
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Int64.lt_iff_toInt_lt, Int64.lt_iff_toInt_lt] at h
  have a : (-4611686018427387904 : Int64).toInt = -2 ^ 62 := by decide
  have b : (4611686018427387904 : Int64).toInt = 2 ^ 62 := by decide
  rw [a, b] at h
  exact h

theorem add_toInt {a b : Int64} (ha : -2 ^ 62 < a.toInt ∧ a.toInt < 2 ^ 62)
    (hb : -2 ^ 62 < b.toInt ∧ b.toInt < 2 ^ 62) : (a + b).toInt = a.toInt + b.toInt := by
  rw [Int64.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem status_of_ne {r : Check} (h : ¬ (r.status == 0) = true) : r.status ≠ 0 := by
  simpa using h

theorem ofNat_toNat {k : ℕ} (h : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' h

theorem toNat_lt64 (n : UInt64) : n.toNat < 2 ^ 64 := n.toNat_lt_size

theorem ranges_sound {u v : Array Int64} {n : UInt64} (h : (ranges u v n).status = 0) :
    ∀ i < n.toNat, inRange u[i]! = true ∧ inRange v[i]! = true := by
  have key := LeanExe.Dialect.loop_induction (n := n) (init := (⟨0, 0, 0⟩ : Check))
    (f := fun i r => if r.status == 0 then
      if inRange u[i.toNat]! && inRange v[i.toNat]! then r else ⟨2, i, 0⟩ else r)
    (P := fun k r => r.status = 0 → ∀ i < k, inRange u[i]! = true ∧ inRange v[i]! = true)
    (fun _ i hi => absurd hi (Nat.not_lt_zero i)) ?_
  · exact key h
  · intro k r hk ih hs
    have hk' : (UInt64.ofNat k).toNat = k := ofNat_toNat (by have := toNat_lt64 n; omega)
    by_cases g1 : (r.status == 0) = true
    · rw [ite_eq_left g1] at hs
      by_cases g2 : (inRange u[(UInt64.ofNat k).toNat]! && inRange v[(UInt64.ofNat k).toNat]!) = true
      · rw [ite_eq_left g2] at hs
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact ih hs i hi
        · rw [hk'] at g2
          rw [hi]
          simpa using g2
      · rw [ite_eq_right g2] at hs
        exact absurd hs (by simp)
    · rw [ite_eq_right g1] at hs
      exact absurd hs (status_of_ne g1)

theorem index_toNat {i j n : UInt64} (hn : n.toNat ≤ 65536) (hi : i.toNat < n.toNat)
    (hj : j.toNat < n.toNat) : (i * n + j).toNat = i.toNat * n.toNat + j.toNat := by
  have h1 : i.toNat * n.toNat < 2 ^ 32 := by nlinarith
  rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Row `i` of an accepted pass 2: its column lies below `n`, and its pair is allowed and tight. -/
def RowOk (c : Array Int64) (perm : Array UInt64) (u v : Array Int64) (n i : ℕ) : Prop :=
  (perm[i]!).toNat < n ∧ c[i * n + (perm[i]!).toNat]! ≠ forbidden ∧
    u[i]! + v[(perm[i]!).toNat]! = c[i * n + (perm[i]!).toNat]!

theorem rows_sound {c : Array Int64} {perm : Array UInt64} {u v : Array Int64} {n : UInt64}
    {r : Check} (hn : n.toNat ≤ 65536) (h : (rows c perm u v n r).status = 0) :
    r.status = 0 ∧ ∀ i < n.toNat, RowOk c perm u v n.toNat i := by
  unfold rows at h
  refine LeanExe.Dialect.loop_induction (n := n) (init := r)
    (P := fun k (q : Check) => q.status = 0 → r.status = 0 ∧ ∀ i < k, RowOk c perm u v n.toNat i)
    (fun hs => ⟨hs, fun i hi => absurd hi (Nat.not_lt_zero i)⟩) ?_ h
  intro k q hk ih hs
  have hk' : (UInt64.ofNat k).toNat = k := ofNat_toNat (by omega)
  simp only at hs
  by_cases g1 : (q.status == 0) = true
  · rw [ite_eq_left g1] at hs
    by_cases g2 : perm[(UInt64.ofNat k).toNat]! < n
    · rw [ite_eq_left g2] at hs
      have hj := UInt64.lt_iff_toNat_lt.mp g2
      rw [hk'] at hj
      have hidx := index_toNat (i := UInt64.ofNat k) (j := perm[k]!) hn (by rw [hk']; exact hk) hj
      rw [hk'] at hs
      by_cases g3 : (c[(UInt64.ofNat k * n + perm[k]!).toNat]! != forbidden) = true
      · rw [ite_eq_left g3] at hs
        by_cases g4 : (u[k]! + v[(perm[k]!).toNat]! == c[(UInt64.ofNat k * n + perm[k]!).toNat]!) = true
        · rw [ite_eq_left g4] at hs
          obtain ⟨h0, hrows⟩ := ih hs
          refine ⟨h0, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · exact hrows i hi
          · rw [hidx, hk'] at g3 g4
            rw [hi]
            exact ⟨hj, by simpa using g3, by simpa using g4⟩
        · rw [ite_eq_right g4] at hs
          exact absurd hs (by simp)
      · rw [ite_eq_right g3] at hs
        exact absurd hs (by simp)
    · rw [ite_eq_right g2] at hs
      exact absurd hs (by simp)
  · rw [ite_eq_right g1] at hs
    exact absurd hs (status_of_ne g1)

/-- Index `t = i·n + j` of an accepted pass 3: rows `i < j` have different columns, and the pair
satisfies the dual inequality. -/
def PairOk (c : Array Int64) (perm : Array UInt64) (u v : Array Int64) (n t : ℕ) : Prop :=
  (t / n < t % n → perm[t / n]! ≠ perm[t % n]!) ∧ ¬ c[t]! < u[t / n]! + v[t % n]!

theorem pairs_sound {c : Array Int64} {perm : Array UInt64} {u v : Array Int64} {n : UInt64}
    {r : Check} (hn : n.toNat ≤ 65536) (h : (pairs c perm u v n r).status = 0) :
    r.status = 0 ∧ ∀ t < n.toNat * n.toNat, PairOk c perm u v n.toNat t := by
  unfold pairs at h
  have hnn : (n * n).toNat = n.toNat * n.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by nlinarith)]
  rw [← hnn]
  refine LeanExe.Dialect.loop_induction (n := n * n) (init := r)
    (P := fun k (q : Check) => q.status = 0 → r.status = 0 ∧ ∀ t < k, PairOk c perm u v n.toNat t)
    (fun hs => ⟨hs, fun i hi => absurd hi (Nat.not_lt_zero i)⟩) ?_ h
  intro k q hk ih hs
  have hk' : (UInt64.ofNat k).toNat = k := ofNat_toNat (by have := toNat_lt64 (n * n); omega)
  have hdiv : (UInt64.ofNat k / n).toNat = k / n.toNat := by rw [UInt64.toNat_div, hk']
  have hmod : (UInt64.ofNat k % n).toNat = k % n.toNat := by rw [UInt64.toNat_mod, hk']
  simp only at hs
  by_cases g1 : (q.status == 0) = true
  · rw [ite_eq_left g1] at hs
    by_cases g2 : (UInt64.ofNat k / n < UInt64.ofNat k % n &&
        perm[(UInt64.ofNat k / n).toNat]! == perm[(UInt64.ofNat k % n).toNat]!) = true
    · rw [ite_eq_left g2] at hs
      exact absurd hs (by simp)
    · rw [ite_eq_right g2] at hs
      by_cases g3 : c[(UInt64.ofNat k).toNat]! < u[(UInt64.ofNat k / n).toNat]! +
            v[(UInt64.ofNat k % n).toNat]!
      · rw [ite_eq_left g3] at hs
        exact absurd hs (by simp)
      · rw [ite_eq_right g3] at hs
        obtain ⟨h0, hpairs⟩ := ih hs
        refine ⟨h0, fun t ht => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
        · exact hpairs t ht
        · rw [ht]
          rw [hk', hdiv, hmod] at g3
          refine ⟨fun hlt heq => g2 ?_, g3⟩
          have hlt' : UInt64.ofNat k / n < UInt64.ofNat k % n := by
            rw [UInt64.lt_iff_toNat_lt, hdiv, hmod]
            exact hlt
          rw [hdiv, hmod]
          simp [hlt', heq]
  · rw [ite_eq_right g1] at hs
    exact absurd hs (status_of_ne g1)

/-- An accepted check: the sizes are those of an `n × n` instance with `1 ≤ n ≤ 16,384`, the
proposed assignment is a permutation through allowed pairs whose cost is `Σ u + Σ v`, and every
permutation through allowed pairs costs at least as much, in the integers of the `Int64` values. -/
theorem check_sound {c : Array Int64} {perm : Array UInt64} {u v : Array Int64}
    (hsize : perm.size < 2 ^ 64 ∧ c.size < 2 ^ 64 ∧ u.size < 2 ^ 64 ∧ v.size < 2 ^ 64)
    (h : (check c perm u v).status = 0) :
    1 ≤ perm.size ∧ perm.size ≤ 16384 ∧ c.size = perm.size * perm.size ∧ u.size = perm.size ∧
      v.size = perm.size ∧ IsPerm perm.size (fun i => (perm[i]!).toNat) ∧
      (∀ i < perm.size, Allowed c perm.size i (perm[i]!).toNat) ∧
      cost c perm.size (fun i => (perm[i]!).toNat) =
        ∑ i ∈ range perm.size, (u[i]!).toInt + ∑ j ∈ range perm.size, (v[j]!).toInt ∧
      ∀ f, IsPerm perm.size f → (∀ i < perm.size, Allowed c perm.size i (f i)) →
        cost c perm.size (fun i => (perm[i]!).toNat) ≤ cost c perm.size f := by
  unfold check at h
  simp only at h
  by_cases g : 1 ≤ perm.size.toUInt64 ∧ perm.size.toUInt64 ≤ 16384 ∧
      c.size.toUInt64 = perm.size.toUInt64 * perm.size.toUInt64 ∧
      u.size.toUInt64 = perm.size.toUInt64 ∧ v.size.toUInt64 = perm.size.toUInt64
  · rw [ite_eq_left g] at h
    obtain ⟨g1, g2, g3, g4, g5⟩ := g
    set n := perm.size
    have hnt : n.toUInt64.toNat = n := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsize.1]
    have hn1 : 1 ≤ n := by have := UInt64.le_iff_toNat_le.mp g1; simpa [hnt] using this
    have hn2 : n ≤ 16384 := by have := UInt64.le_iff_toNat_le.mp g2; simpa [hnt] using this
    have hc : c.size = n * n := by
      have := congrArg UInt64.toNat g3
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsize.2.1, UInt64.toNat_mul, hnt,
        Nat.mod_eq_of_lt (by nlinarith)] at this
      exact this
    have hu : u.size = n := by
      have := congrArg UInt64.toNat g4
      rwa [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsize.2.2.1, hnt] at this
    have hv : v.size = n := by
      have := congrArg UInt64.toNat g5
      rwa [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsize.2.2.2, hnt] at this
    have hn65 : n.toUInt64.toNat ≤ 65536 := by rw [hnt]; omega
    obtain ⟨hr, hpairs⟩ := pairs_sound hn65 h
    obtain ⟨hq, hrows⟩ := rows_sound hn65 hr
    have hranges := ranges_sound hq
    rw [hnt] at hpairs hrows hranges
    -- the assignment is a permutation through allowed pairs
    have hperm : IsPerm n (fun i => (perm[i]!).toNat) := by
      refine ⟨fun i hi => (hrows i hi).1, fun i hi j hj hij => ?_⟩
      by_contra hne
      have key : ∀ a < n, ∀ b < n, a < b → perm[a]! ≠ perm[b]! := by
        intro a ha b hb hab
        have ht : a * n + b < n * n := by nlinarith
        have hd : (a * n + b) / n = a := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
        have hm : (a * n + b) % n = b := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
        have := (hpairs (a * n + b) ht).1
        rw [hd, hm] at this
        exact this hab
      have heq : perm[i]! = perm[j]! := UInt64.toNat_inj.mp hij
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact key i hi j hj hlt heq
      · exact key j hj i hi hlt heq.symm
    have hallow : ∀ i < n, Allowed c n i (perm[i]!).toNat := fun i hi => (hrows i hi).2.1
    have hU : ∀ i < n, -2 ^ 62 < (u[i]!).toInt ∧ (u[i]!).toInt < 2 ^ 62 :=
      fun i hi => inRange_toInt (hranges i hi).1
    have hV : ∀ i < n, -2 ^ 62 < (v[i]!).toInt ∧ (v[i]!).toInt < 2 ^ 62 :=
      fun i hi => inRange_toInt (hranges i hi).2
    have htight : ∀ i < n, (u[i]!).toInt + (v[(perm[i]!).toNat]!).toInt =
        (c[i * n + (perm[i]!).toNat]!).toInt := by
      intro i hi
      rw [← add_toInt (hU i hi) (hV _ (hrows i hi).1), (hrows i hi).2.2]
    have hfeas : ∀ i < n, ∀ j < n, Allowed c n i j →
        (u[i]!).toInt + (v[j]!).toInt ≤ (c[i * n + j]!).toInt := by
      intro i hi j hj ha
      have ht : i * n + j < n * n := by nlinarith
      have hd : (i * n + j) / n = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
      have hm : (i * n + j) % n = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have := (hpairs (i * n + j) ht).2
      rw [hd, hm] at this
      rw [Int64.lt_iff_toInt_lt, add_toInt (hU i hi) (hV j hj)] at this
      exact not_lt.mp this
    have wd := fun f (hf : IsPerm n f) (hfa : ∀ i < n, Allowed c n i (f i)) =>
      weak_duality (C := fun i j => (c[i * n + j]!).toInt) (A := Allowed c n)
        (u := fun i => (u[i]!).toInt) (v := fun j => (v[j]!).toInt)
        (π := fun i => (perm[i]!).toNat) hperm htight hfeas hf hfa
    exact ⟨hn1, hn2, hc, hu, hv, hperm, hallow, (wd _ hperm hallow).1,
      fun f hf hfa => (wd f hf hfa).2⟩
  · rw [ite_eq_right g] at h
    exact absurd h (by decide)

#print axioms weak_duality
#print axioms check_sound

end Demos.Gate.Assignment
