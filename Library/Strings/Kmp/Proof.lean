import Library.Strings.Kmp.Program
import Library.Strings.Kmp.Spec
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas
import Mathlib.Data.List.Sort

/-! The proof that `occurrences` returns the positions of the occurrences of the pattern.  `Pre P T
s i` states that the first `s` bytes of `P` equal the `s` bytes of `T` that end before position `i`.
A border of `P[0, k)` is a length `b < k` with `Pre P P b k`, and `PiOk` states that `pi[j]` is the
longest border of `P[0, j + 1)`.  From a length `k` with `Pre P T k i`, the shorter lengths `s` with
`Pre P T s i` are the borders of `P[0, k)`, so the fall-back through `pi` visits them in decreasing
order until the next byte extends one, and from the longest such `k`, `step` returns the longest
prefix of the pattern that ends after byte `i`.  The scan keeps in `q` the longest prefix shorter
than `m` that ends at the current position, the failure function applies the same step to the
pattern's own bytes from position 1, with each length below its position, and a scan reports
position `i + 1 - m` exactly when the pattern ends after byte `i`. -/

namespace Library.Strings.Kmp

open LeanExe.Dialect Library.Bytes

/-! ### Bytes -/

theorem byte_toNat (ws : Array UInt64) (i : Nat) (hi : i < 2 ^ 64) :
    (byte ws (UInt64.ofNat i)).toNat = (byteAt ws i).toNat := by
  have hi' : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' hi
  have h8 : 8 * (i % 8) < 64 := by omega
  have e1 : (UInt64.ofNat i / 8).toNat = i / 8 := by
    rw [UInt64.toNat_div, hi']; simp only [UInt64.reduceToNat]
  have e2 : (8 * (UInt64.ofNat i % 8)).toNat = 8 * (i % 8) := by
    rw [UInt64.toNat_mul, UInt64.toNat_mod, hi']; simp only [UInt64.reduceToNat]; omega
  have e3 : (8 * (i % 8)).toUInt64.toNat = 8 * (i % 8) := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold byte byteAt
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, e1, e2, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, e3]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt h8, show (255 : Nat) = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

theorem byte_eq_iff (a b : Array UInt64) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    byte a (UInt64.ofNat i) = byte b (UInt64.ofNat j) ↔ byteAt a i = byteAt b j := by
  rw [← UInt64.toNat_inj, byte_toNat a i hi, byte_toNat b j hj, UInt8.toNat_inj]

/-- Byte `k` of the packed words `ws`, indexed by a natural number. -/
def pb (ws : Array UInt64) (k : Nat) : UInt64 := byte ws (UInt64.ofNat k)

theorem byte_eq_pb (ws : Array UInt64) (k : UInt64) : byte ws k = pb ws k.toNat := by
  unfold pb
  rw [UInt64.ofNat_toNat]

/-! ### Borders -/

/-- The first `s` bytes of `P` equal the `s` bytes of `T` that end before position `i`. -/
def Pre (P T : Nat → UInt64) (s i : Nat) : Prop := s ≤ i ∧ ∀ j < s, P j = T (i - s + j)

instance (P T : Nat → UInt64) (s i : Nat) : Decidable (Pre P T s i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem pre_zero (P T : Nat → UInt64) (i : Nat) : Pre P T 0 i :=
  ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem pre_succ {P T : Nat → UInt64} {s i : Nat} (h : Pre P T s i) (hc : P s = T i) :
    Pre P T (s + 1) (i + 1) := by
  refine ⟨by have := h.1; omega, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [h.2 j hj]; congr 1; have := h.1; omega
  · rw [hc]; congr 1; have := h.1; omega

theorem pre_pred {P T : Nat → UInt64} {s i : Nat} (h : Pre P T (s + 1) (i + 1)) :
    Pre P T s i ∧ P s = T i := by
  refine ⟨⟨by have := h.1; omega, fun j hj => ?_⟩, ?_⟩
  · rw [h.2 j (by omega)]; congr 1; have := h.1; omega
  · rw [h.2 s (by omega)]; congr 1; have := h.1; omega

/-- A border of `P[0, k)` occurs in `T` ending before `i` when `P[0, k)` does. -/
theorem pre_trans {P T : Nat → UInt64} {b k i : Nat} (hb : Pre P P b k) (hk : Pre P T k i) :
    Pre P T b i := by
  refine ⟨le_trans hb.1 hk.1, fun j hj => ?_⟩
  rw [hb.2 j hj, hk.2 (k - b + j) (by have := hb.1; omega)]
  congr 1
  have := hb.1; have := hk.1; omega

/-- Of two prefixes of `P` that occur in `T` ending before `i`, the shorter is a border of the
longer. -/
theorem pre_border {P T : Nat → UInt64} {s k i : Nat} (hs : Pre P T s i) (hk : Pre P T k i)
    (hsk : s ≤ k) : Pre P P s k := by
  refine ⟨hsk, fun j hj => ?_⟩
  rw [hs.2 j hj, hk.2 (k - s + j) (by omega)]
  congr 1
  have := hs.1; have := hk.1; omega

/-- `pi[j]` is the longest border of `P[0, j + 1)` for every `j` below `q`. -/
def PiOk (P : Nat → UInt64) (pi : Array UInt64) (q : Nat) : Prop :=
  ∀ j < q, pi[j]!.toNat < j + 1 ∧ Pre P P pi[j]!.toNat (j + 1) ∧
    ∀ b < j + 1, Pre P P b (j + 1) → b ≤ pi[j]!.toNat

/-! ### The fall-back and one step -/

/-- From a length `k` with `Pre P T k i`, a count of steps of at least `k`, and a table that
holds the longest proper borders below `k`, the fall-back before the byte `c` returns a length `r`
with `Pre P T r i`, and either `r = 0` or byte `r` of the pattern is `c`, and every positive length
up to `k` with these properties is at most `r`. -/
theorem fall_spec (pat pi : Array UInt64) (c : UInt64) (T : Nat → UInt64) (i : Nat) :
    ∀ (f : Nat) (F k : UInt64), F.toNat = f → k.toNat ≤ f → Pre (pb pat) T k.toNat i →
      PiOk (pb pat) pi k.toNat →
      (fall pat pi c k F).toNat ≤ k.toNat ∧ Pre (pb pat) T (fall pat pi c k F).toNat i ∧
        ((fall pat pi c k F).toNat = 0 ∨ pb pat (fall pat pi c k F).toNat = c) ∧
        ∀ s, s ≤ k.toNat → 0 < s → Pre (pb pat) T s i → pb pat s = c →
          s ≤ (fall pat pi c k F).toNat := by
  intro f
  induction f with
  | zero =>
    intro F k hF hk hpre _
    have hk0 : k.toNat = 0 := by omega
    rw [fall, ite_eq_right (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp h.1; simp at this; omega)]
    exact ⟨le_rfl, hpre, .inl hk0, fun s hs hs0 => by omega⟩
  | succ f ih =>
    intro F k hF hk hpre hpi
    rw [fall]
    by_cases hc : 0 < F ∧ 0 < k ∧ byte pat k ≠ c
    · rw [ite_eq_left hc]
      have hk0 : 0 < k.toNat := UInt64.lt_iff_toNat_lt.mp hc.2.1
      have hkm1 : (k - 1).toNat = k.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      obtain ⟨hb1, hb2, hb3⟩ := hpi (k.toNat - 1) (by omega)
      rw [show k.toNat - 1 + 1 = k.toNat by omega] at hb1 hb2 hb3
      have hF1 : (F - 1).toNat = f := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
        simp
        omega
      rw [hkm1]
      obtain ⟨r1, r2, r3, r4⟩ := ih (F - 1) pi[k.toNat - 1]! hF1 (by omega) (pre_trans hb2 hpre)
        (fun j hj => hpi j (by omega))
      refine ⟨by omega, r2, r3, fun s hs hs0 hps hsc => ?_⟩
      rcases Nat.lt_or_ge s k.toNat with hsk | hsk
      · exact r4 s (hb3 s hsk (pre_border hps hpre hsk.le)) hs0 hps hsc
      · have : s = k.toNat := by omega
        subst this
        exact absurd (by rw [byte_eq_pb]; exact hsc) hc.2.2
    · rw [ite_eq_right hc]
      refine ⟨le_rfl, hpre, ?_, fun s hs _ _ _ => hs⟩
      by_cases hk0 : k.toNat = 0
      · exact .inl hk0
      · refine .inr ?_
        rw [← byte_eq_pb]
        by_contra hne
        exact hc ⟨UInt64.lt_iff_toNat_lt.mpr (by simp; omega),
          UInt64.lt_iff_toNat_lt.mpr (by simp; omega), hne⟩

/-- For `L ≤ m`, from the longest prefix `k` shorter than `L` that ends before `i`, with a table
that holds the longest proper borders below `k`, `step` returns the longest prefix of length at
most `L` that ends after byte `i`. -/
theorem step_spec (pat pi : Array UInt64) (m : UInt64) (T : Nat → UInt64) (i L : Nat)
    (hL : L ≤ m.toNat) (k : UInt64) (hkL : k.toNat < L) (hpre : Pre (pb pat) T k.toNat i)
    (hmax : ∀ s < L, Pre (pb pat) T s i → s ≤ k.toNat) (hpi : PiOk (pb pat) pi k.toNat) :
    (step pat pi m (T i) k).toNat ≤ L ∧ Pre (pb pat) T (step pat pi m (T i) k).toNat (i + 1) ∧
      ∀ s ≤ L, Pre (pb pat) T s (i + 1) → s ≤ (step pat pi m (T i) k).toNat := by
  obtain ⟨r1, r2, r3, r4⟩ := fall_spec pat pi (T i) T i m.toNat m k rfl (by omega) hpre hpi
  have hm := UInt64.toNat_lt m
  unfold step
  generalize fall pat pi (T i) k m = j at r1 r2 r3 r4
  by_cases hj : byte pat j = T i
  · rw [ite_eq_left hj]
    rw [byte_eq_pb] at hj
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
    rw [hj1]
    refine ⟨by omega, pre_succ r2 hj, fun s hs hps => ?_⟩
    rcases s with _ | s
    · omega
    · obtain ⟨hp, hc⟩ := pre_pred hps
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · omega
      · have := r4 s (hmax s (by omega) hp) hs0 hp hc
        omega
  · rw [ite_eq_right hj]
    rw [byte_eq_pb] at hj
    have hj0 : j.toNat = 0 := by
      rcases r3 with h | h
      · exact h
      · exact absurd h hj
    refine ⟨by omega, by rw [hj0]; exact pre_zero _ _ _, fun s hs hps => ?_⟩
    rcases s with _ | s
    · omega
    · obtain ⟨hp, hc⟩ := pre_pred hps
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · rw [← hj0] at hc; exact absurd hc hj
      · have := r4 s (hmax s (by omega) hp) hs0 hp hc
        omega

/-! ### The failure function -/

theorem failure_spec (pat : Array UInt64) (m : UInt64) :
    (failure pat m).size = m.toNat ∧ PiOk (pb pat) (failure pat m) m.toNat := by
  have hm := UInt64.toNat_lt m
  unfold failure
  dsimp only
  by_cases h1 : m ≤ 1
  · rw [ite_eq_left h1]
    have h1' := UInt64.le_iff_toNat_le.mp h1
    simp only [UInt64.reduceToNat] at h1'
    refine ⟨build_size _ _, fun j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    rw [build_get hj]
    simp only [UInt64.reduceToNat]
    exact ⟨by omega, pre_zero _ _ _, fun b hb _ => by omega⟩
  rw [ite_eq_right h1]
  have h2 : 2 ≤ m.toNat := by
    have := mt UInt64.le_iff_toNat_le.mpr h1; simp at this; omega
  have hcount : (m - 1).toNat = m.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  obtain ⟨g1, g2, _⟩ := loop_induction (n := m - 1)
    (init := (LeanExe.build m fun _ => (0 : UInt64), (0 : UInt64)))
    (f := fun t st =>
      (st.1.set! (t + 1).toNat (step pat st.1 m (byte pat (t + 1)) st.2),
        step pat st.1 m (byte pat (t + 1)) st.2))
    (fun t (st : Array UInt64 × UInt64) => st.1.size = m.toNat ∧ PiOk (pb pat) st.1 (t + 1) ∧
      st.2 = st.1[t]!)
    ⟨build_size _ _, fun j hj => by
      have hj0 : j = 0 := by omega
      subst hj0
      rw [build_get (by omega)]
      simp only [UInt64.reduceToNat]
      exact ⟨by omega, pre_zero _ _ _, fun b hb _ => by omega⟩,
      by rw [build_get (by omega)]⟩
    (by
      intro t st ht ⟨s1, s2, s3⟩
      rw [hcount] at ht
      have ht' : (UInt64.ofNat t).toNat = t := UInt64.toNat_ofNat_of_lt' (show t < 2 ^ 64 by omega)
      have hq : (UInt64.ofNat t + 1).toNat = t + 1 := by
        simp only [UInt64.toNat_add, ht', UInt64.reduceToNat]; omega
      have hc : byte pat (UInt64.ofNat t + 1) = pb pat (t + 1) := by rw [byte_eq_pb, hq]
      rw [hc, hq]
      obtain ⟨k1, k2, k3⟩ := s2 t (by omega)
      rw [← s3] at k1 k2 k3
      obtain ⟨q1, q2, q3⟩ := step_spec pat st.1 m (pb pat) (t + 1) (t + 1) (by omega) st.2 k1 k2
        k3 (fun j hj => s2 j (by omega))
      generalize step pat st.1 m (pb pat (t + 1)) st.2 = q at q1 q2 q3
      have hlt : t + 1 < st.1.size := by rw [s1]; omega
      refine ⟨by rw [Array.size_set!]; exact s1, fun j hj => ?_, ?_⟩
      · rw [get_set _ _ _ j hlt]
        by_cases e : j = t + 1
        · rw [ite_eq_left e]
          subst e
          exact ⟨by omega, q2, fun b hb hpb => q3 b (by omega) hpb⟩
        · rw [ite_eq_right e]
          exact s2 j (by omega)
      · rw [get_set _ _ _ _ hlt, ite_eq_left rfl])
  rw [hcount, show m.toNat - 1 + 1 = m.toNat by omega] at g2
  exact ⟨g1, g2⟩

/-! ### The scan -/

/-- The scan's state after `i` bytes of `T`: `q` is the longest prefix of the pattern shorter than
`M` that ends before position `i`. -/
def IsState (P T : Nat → UInt64) (M i q : Nat) : Prop :=
  q < M ∧ Pre P T q i ∧ ∀ s < M, Pre P T s i → s ≤ q

theorem state_zero (P T : Nat → UInt64) (M : Nat) (hM : 0 < M) : IsState P T M 0 0 :=
  ⟨hM, pre_zero _ _ _, fun s _ h => by have := h.1; omega⟩

/-- One byte of the scan: the step reaches `m` exactly when the pattern ends after byte `i`, and
the next state is the step's length, or `pi[m - 1]` when the step reaches `m`. -/
theorem next_state (pat pi : Array UInt64) (m : UInt64) (T : Nat → UInt64) (i : Nat)
    (hm0 : 0 < m.toNat) (hpi : PiOk (pb pat) pi m.toNat) (q : UInt64)
    (hq : IsState (pb pat) T m.toNat i q.toNat) :
    (step pat pi m (T i) q = m ↔ Pre (pb pat) T m.toNat (i + 1)) ∧
      IsState (pb pat) T m.toNat (i + 1)
        (if step pat pi m (T i) q = m then pi[(m - 1).toNat]!.toNat
          else (step pat pi m (T i) q).toNat) := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨s1, s2, s3⟩ := step_spec pat pi m T i m.toNat le_rfl q hq1 hq2 hq3
    (fun j hj => hpi j (by omega))
  generalize step pat pi m (T i) q = q' at s1 s2 s3 ⊢
  have heq : q' = m ↔ q'.toNat = m.toNat := UInt64.toNat_inj.symm
  refine ⟨⟨fun h => by rw [heq] at h; rw [← h]; exact s2,
    fun h => heq.mpr (Nat.le_antisymm s1 (s3 _ le_rfl h))⟩, ?_⟩
  by_cases e : q' = m
  · rw [ite_eq_left e]
    have hm1 : (m - 1).toNat = m.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    rw [hm1]
    obtain ⟨b1, b2, b3⟩ := hpi (m.toNat - 1) (by omega)
    rw [show m.toNat - 1 + 1 = m.toNat by omega] at b1 b2 b3
    have hfull : Pre (pb pat) T m.toNat (i + 1) := by rw [heq] at e; rw [← e]; exact s2
    exact ⟨b1, pre_trans b2 hfull, fun s hs hps => b3 s hs (pre_border hps hfull hs.le)⟩
  · rw [ite_eq_right e]
    have hlt : q'.toNat < m.toNat := by
      rcases Nat.lt_or_ge q'.toNat m.toNat with h | h
      · exact h
      · exact absurd (heq.mpr (by omega)) e
    exact ⟨hlt, s2, fun s hs hps => s3 s hs.le hps⟩

/-- The ends `e` below `i` after which the pattern ends. -/
def ends (P T : Nat → UInt64) (M i : Nat) : List Nat :=
  (List.range i).filter fun e => decide (Pre P T M (e + 1))

theorem ends_succ (P T : Nat → UInt64) (M i : Nat) :
    ends P T M (i + 1) = ends P T M i ++ if Pre P T M (i + 1) then [i] else [] := by
  unfold ends
  rw [List.range_succ, List.filter_append]
  by_cases h : Pre P T M (i + 1) <;> simp [h]

theorem ends_length_le (P T : Nat → UInt64) (M i : Nat) : (ends P T M i).length ≤ i :=
  le_trans (List.length_filter_le _ _) (by simp)

theorem ends_mono (P T : Nat → UInt64) (M : Nat) {i n : Nat} (h : i ≤ n) :
    (ends P T M i).length ≤ (ends P T M n).length :=
  ((List.range_sublist.mpr h).filter _).length_le

/-- `count` counts the ends after which the pattern ends. -/
theorem count_spec (pat txt : Array UInt64) (m n : UInt64) (hm0 : 0 < m.toNat) :
    (count pat (failure pat m) txt m n).toNat =
      (ends (pb pat) (pb txt) m.toNat n.toNat).length := by
  have hn := UInt64.toNat_lt n
  obtain ⟨_, hpi⟩ := failure_spec pat m
  obtain ⟨_, h2⟩ := loop_induction (n := n) (init := ((0 : UInt64), (0 : UInt64)))
    (f := fun i st =>
      if step pat (failure pat m) m (byte txt i) st.1 = m then
        ((failure pat m)[(m - 1).toNat]!, st.2 + 1)
      else (step pat (failure pat m) m (byte txt i) st.1, st.2))
    (fun i (st : UInt64 × UInt64) => IsState (pb pat) (pb txt) m.toNat i st.1.toNat ∧
      st.2.toNat = (ends (pb pat) (pb txt) m.toNat i).length)
    ⟨state_zero _ _ _ hm0, by simp [ends]⟩ (by
      intro i st hi ⟨c1, c2⟩
      obtain ⟨e1, e2⟩ := next_state pat (failure pat m) m (pb txt) i hm0 hpi st.1 c1
      have hT : byte txt (UInt64.ofNat i) = pb txt i := rfl
      rw [hT]
      have hl := ends_length_le (pb pat) (pb txt) m.toNat i
      rw [ends_succ]
      by_cases e : step pat (failure pat m) m (pb txt i) st.1 = m
      · rw [ite_eq_left e] at e2 ⊢
        rw [ite_eq_left (e1.mp e)]
        refine ⟨e2, ?_⟩
        simp only [UInt64.toNat_add, c2, UInt64.reduceToNat, List.length_append,
          List.length_singleton]
        omega
      · rw [ite_eq_right e] at e2 ⊢
        rw [ite_eq_right (fun h => e (e1.mpr h)), List.append_nil]
        exact ⟨e2, c2⟩)
  exact h2

/-- The positions of the occurrences, from the ends after which the pattern ends. -/
def positions (P T : Nat → UInt64) (M i : Nat) : List Nat :=
  (ends P T M i).map fun e => e + 1 - M

theorem positions_spec (pat : Array UInt64) (m : UInt64) (txt : Array UInt64) (n : UInt64)
    (hm0 : 0 < m.toNat) :
    positions (pb pat) (pb txt) m.toNat n.toNat =
      (List.range (n.toNat + 1)).filter fun p => decide (OccursAt pat m.toNat txt n.toNat p) := by
  have hn := UInt64.toNat_lt n
  have hm := UInt64.toNat_lt m
  have hmem : ∀ e ∈ ends (pb pat) (pb txt) m.toNat n.toNat, m.toNat ≤ e + 1 := by
    intro e he
    simp only [ends, List.mem_filter, decide_eq_true_eq] at he
    exact he.2.1
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · unfold positions
    rw [List.pairwise_map]
    exact ((List.pairwise_lt_range).filter _).imp_of_mem fun ha hb hab => by
      have := hmem _ ha; have := hmem _ hb; omega
  · exact (List.pairwise_lt_range).filter _
  · intro p
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
    unfold positions ends
    rw [List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at he
      obtain ⟨he, hpre⟩ := he
      have h1 := hpre.1
      refine ⟨by omega, by omega, fun k hk => ?_⟩
      have h := hpre.2 k hk
      unfold pb at h
      exact ((byte_eq_iff pat txt k _ (by omega) (by omega)).mp h).symm
    · rintro ⟨hp, hpm, hb⟩
      refine ⟨p + m.toNat - 1, ?_, by omega⟩
      rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨by omega, by omega, fun k hk => ?_⟩
      unfold pb
      rw [show p + m.toNat - 1 + 1 - m.toNat + k = p + k by omega]
      exact (byte_eq_iff pat txt k (p + k) (by omega) (by omega)).mpr (hb k hk).symm

/-- For a nonempty pattern, `count` is the number of occurrences, the size of `expected`. -/
theorem count_eq_size (pat : Array UInt64) (m : UInt64) (txt : Array UInt64) (n : UInt64)
    (hm0 : 0 < m.toNat) :
    (count pat (failure pat m) txt m n).toNat = (expected pat m txt n).size := by
  rw [count_spec pat txt m n hm0]
  unfold expected
  rw [← positions_spec pat m txt n hm0]
  simp [positions]

/-- `occurrences` returns the positions of the occurrences in increasing order. -/
theorem occurrences_eq (pat : Array UInt64) (m : UInt64) (txt : Array UInt64) (n : UInt64) :
    occurrences pat m txt n = expected pat m txt n := by
  have hn := UInt64.toNat_lt n
  unfold occurrences expected
  by_cases h0 : m = 0
  · rw [ite_eq_left h0]
    subst h0
    have hall : ((List.range (n.toNat + 1)).filter fun p =>
        decide (OccursAt pat (0 : UInt64).toNat txt n.toNat p)) = List.range (n.toNat + 1) := by
      apply List.filter_eq_self.mpr
      intro p hp
      rw [List.mem_range] at hp
      rw [decide_eq_true_eq]
      exact ⟨by simp; omega, fun k hk => absurd hk (by simp)⟩
    rw [hall]
    by_cases hmax : n < 0xffffffffffffffff
    · rw [ite_eq_left hmax]
      have hn1 : (n + 1).toNat = n.toNat + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hmax
        simp only [UInt64.toNat_add, UInt64.reduceToNat] at *
        omega
      apply Array.ext
      · simp [build_size, hn1]
      · intro i h1 h2
        rw [build_size, hn1] at h1
        rw [← getElem!_pos _ i (by rw [build_size, hn1]; exact h1),
          build_get (by rw [hn1]; exact h1)]
        simp
    rw [ite_eq_right hmax]
    apply Array.ext
    · simp [build_size]
    · intro i h1 h2
      simp only [Array.size_push, build_size] at h1
      rw [Array.getElem_push]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      split
      · rename_i hlt
        rw [← getElem!_pos _ i hlt, build_get (by rw [build_size] at hlt; exact hlt)]
      · have : i = n.toNat := by rw [build_size] at *; omega
        subst this
        exact (UInt64.ofNat_toNat).symm
  rw [ite_eq_right h0]
  have hm0 : 0 < m.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) h0
    · exact h
  obtain ⟨_, hpi⟩ := failure_spec pat m
  rw [← positions_spec pat m txt n hm0]
  dsimp only
  have hcnt := count_spec pat txt m n hm0
  obtain ⟨f1, _, _, f4⟩ := loop_induction (n := n)
    (init := (LeanExe.build (count pat (failure pat m) txt m n) fun _ => (0 : UInt64),
      (0 : UInt64), (0 : UInt64)))
    (f := fun i st =>
      if step pat (failure pat m) m (byte txt i) st.2.1 = m then
        (st.1.set! st.2.2.toNat (i + 1 - m), (failure pat m)[(m - 1).toNat]!, st.2.2 + 1)
      else (st.1, step pat (failure pat m) m (byte txt i) st.2.1, st.2.2))
    (fun i (st : Array UInt64 × UInt64 × UInt64) =>
      st.1.size = (ends (pb pat) (pb txt) m.toNat n.toNat).length ∧
      IsState (pb pat) (pb txt) m.toNat i st.2.1.toNat ∧
      st.2.2.toNat = (ends (pb pat) (pb txt) m.toNat i).length ∧
      ∀ k < (ends (pb pat) (pb txt) m.toNat i).length,
        st.1[k]! = UInt64.ofNat (positions (pb pat) (pb txt) m.toNat i)[k]!)
    ⟨by rw [build_size, hcnt], state_zero _ _ _ hm0, by simp [ends],
      fun k hk => by simp [ends] at hk⟩ (by
      intro i st hi ⟨c1, c2, c3, c4⟩
      obtain ⟨e1, e2⟩ := next_state pat (failure pat m) m (pb txt) i hm0 hpi st.2.1 c2
      have hT : byte txt (UInt64.ofNat i) = pb txt i := rfl
      rw [hT]
      have hl := ends_length_le (pb pat) (pb txt) m.toNat i
      have hi' : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
      by_cases e : step pat (failure pat m) m (pb txt i) st.2.1 = m
      · rw [ite_eq_left e] at e2 ⊢
        have hfull := e1.mp e
        have hmono := ends_mono (pb pat) (pb txt) m.toNat (show i + 1 ≤ n.toNat by omega)
        rw [ends_succ, ite_eq_left hfull] at hmono
        simp only [List.length_append, List.length_singleton] at hmono
        have hlt : st.2.2.toNat < st.1.size := by omega
        have hpos : (UInt64.ofNat i + 1 - m).toNat = i + 1 - m.toNat := by
          have := hfull.1
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
            simp only [UInt64.toNat_add, hi', UInt64.reduceToNat]; omega))]
          simp only [UInt64.toNat_add, hi', UInt64.reduceToNat]
          omega
        refine ⟨by rw [Array.size_set!]; exact c1, ?_, ?_, fun k hk => ?_⟩
        · exact e2
        · simp only [UInt64.toNat_add, c3, UInt64.reduceToNat, ends_succ, ite_eq_left hfull,
            List.length_append, List.length_singleton]
          omega
        · rw [ends_succ, ite_eq_left hfull] at hk
          simp only [List.length_append, List.length_singleton] at hk
          rw [get_set _ _ _ _ hlt]
          unfold positions
          rw [ends_succ, ite_eq_left hfull, List.map_append]
          by_cases ek : k = st.2.2.toNat
          · rw [ite_eq_left ek, ek, c3]
            simp only [List.map_cons, List.map_nil]
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by simp),
              List.length_map]
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            apply UInt64.toNat_inj.mp
            rw [hpos, UInt64.toNat_ofNat_of_lt' (show i + 1 - m.toNat < 2 ^ 64 by omega)]
          · rw [ite_eq_right ek, c4 k (by omega)]
            unfold positions
            rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
              List.getElem?_append_left (by simp; omega)]
      · rw [ite_eq_right e] at e2 ⊢
        have hnot : ¬Pre (pb pat) (pb txt) m.toNat (i + 1) := fun h => e (e1.mpr h)
        refine ⟨c1, e2, by rw [ends_succ, ite_eq_right hnot, List.append_nil]; exact c3,
          fun k hk => ?_⟩
        rw [ends_succ, ite_eq_right hnot, List.append_nil] at hk
        rw [c4 k hk]
        unfold positions
        rw [ends_succ, ite_eq_right hnot, List.append_nil])
  show (LeanExe.loop n
    (LeanExe.build (count pat (failure pat m) txt m n) fun _ => (0 : UInt64), (0 : UInt64),
      (0 : UInt64))
    (fun i st =>
      if step pat (failure pat m) m (byte txt i) st.2.1 = m then
        (st.1.set! st.2.2.toNat (i + 1 - m), (failure pat m)[(m - 1).toNat]!, st.2.2 + 1)
      else (st.1, step pat (failure pat m) m (byte txt i) st.2.1, st.2.2))).1 = _
  apply Array.ext
  · rw [f1]
    simp [positions]
  · intro k h1 h2
    have hk : k < (ends (pb pat) (pb txt) m.toNat n.toNat).length := by rw [f1] at h1; exact h1
    rw [← getElem!_pos _ k h1, f4 k hk]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [getElem!_pos _ k (by simp [positions]; exact hk)]

end Library.Strings.Kmp
