import Library.Combinatorics.DancingLinks.Hide

/-! The walk around an option, which `hide`, `unhide`, `coverOthers`, and `uncoverOthers` share.
The forward walk starts at node `p + 1`, applies an operation `F` at each node of the option, and
follows `ULINK` at the spacer back to the option's first node, until it returns to `p`.  The
backward walk starts at `p - 1`, applies `F`, follows `DLINK` at the spacer before the option to
its last node, and returns to `p`.  `walkFwd` shows that the forward walk is `gfold G` of
`others`, when `F` acts as `G` on each prefix, and `walkBwd` that the backward walk undoes it, when
`F` undoes `G` at each node.  Both need only that every prefix keeps the static words, which give
each node's `TOP` and each spacer's links. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- Applies `G` at the nodes of `l` in order. -/
def gfold (G : Nat → Array UInt64 → Array UInt64) (l : List Nat) (t : Array UInt64) :
    Array UInt64 :=
  l.foldl (fun t q => G q t) t

theorem gfold_append (G : Nat → Array UInt64 → Array UInt64) (l l' : List Nat)
    (t : Array UInt64) : gfold G (l ++ l') t = gfold G l' (gfold G l t) := by
  simp [gfold, List.foldl_append]

theorem gfold_concat (G : Nat → Array UInt64 → Array UInt64) (l : List Nat) (q : Nat)
    (t : Array UInt64) : gfold G (l ++ [q]) t = G q (gfold G l t) := by
  rw [gfold_append]; rfl

theorem delAll_eq_gfold : ∀ (l : List Nat) (t : Array UInt64), delAll l t = gfold (fun q t => del t q) l t
  | [], _ => rfl
  | q :: l, t => by rw [delAll, delAll_eq_gfold l]; rfl

namespace Layout

theorem others_prefix_fwd (L : Layout) {k m p : Nat} (hp : p = L.first k + m) {a : Nat}
    (ha : a = L.len k - m - 1) :
    (∀ j ≤ a, List.range' (p + 1) j <+: L.others k m) ∧
      ∀ j ≤ m, List.range' (p + 1) a ++ List.range' (L.first k) j <+: L.others k m := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · unfold others
    rw [← hp, ← ha]
    refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    have : List.range' (p + 1) a = List.range' (p + 1) j ++ List.range' (p + 1 + j) (a - j) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [this]
    exact List.prefix_append _ _
  · unfold others
    rw [← hp, ← ha]
    apply List.prefix_append_right_inj _ |>.mpr
    have : List.range' (L.first k) m = List.range' (L.first k) j ++
        List.range' (L.first k + j) (m - j) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [this]
    exact List.prefix_append _ _

end Layout

/-- The forward walk around an option is `gfold G` of its `others`. -/
theorem walkFwd {L : Layout} (hL : L.Good) {k m : Nat} {p : UInt64} (hat : L.At p.toNat k m)
    (F : UInt64 → Array UInt64 → Array UInt64) (G : Nat → Array UInt64 → Array UInt64)
    (t : Array UInt64) (hS : ∀ l, l <+: L.others k m → Static (gfold G l t) L)
    (hF : ∀ l (q : UInt64), l ++ [q.toNat] <+: L.others k m →
      F q (gfold G l t) = G q.toNat (gfold G l t)) :
    (LeanExe.repeatWhile t.size.toUInt64 (p + 1, t) (fun s => decide (s.1 ≠ p)) fun s =>
      if s.2[(3 * s.1).toNat]! = 0 then (s.2[(3 * s.1 + 1).toNat]!, s.2)
      else (s.1 + 1, F s.1 s.2)).2 = gfold G (L.others k m) t := by
  obtain ⟨hk, hm, hp⟩ := hat
  have hs0 := hS [] (List.nil_prefix)
  have hsize : t.size < 2 ^ 60 := by have := hs0.size; simp [gfold] at this; rw [this]; exact hL.small
  have hlast := L.first_le_last hk
  rw [Layout.first_succ] at hlast
  have hbase : 3 * L.first L.os.length ≤ t.size := by
    have := hs0.size; simp [gfold] at this; rw [this, Layout.base]; omega
  set a := L.len k - m - 1 with ha
  obtain ⟨hpre1, hpre2⟩ := L.others_prefix_fwd hp ha
  have hsz : ∀ l, l <+: L.others k m → (gfold G l t).size = t.size := by
    intro l hl
    have h1 := (hS l hl).size
    have h0 := hs0.size
    simp only [gfold, List.foldl_nil] at h0
    omega
  let Inv : UInt64 × Array UInt64 → Prop := fun s =>
    (∃ j ≤ a, s.1.toNat = p.toNat + 1 + j ∧ s.2 = gfold G (List.range' (p.toNat + 1) j) t) ∨
      (∃ j ≤ m, s.1.toNat = L.first k + j ∧
        s.2 = gfold G (List.range' (p.toNat + 1) a ++ List.range' (L.first k) j) t)
  let μ : UInt64 × Array UInt64 → Nat := fun s =>
    if p.toNat < s.1.toNat then L.first k + L.len k - s.1.toNat + m + 1 else p.toNat - s.1.toNat
  have hp1 : (p + 1).toNat = p.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  have hfuel : μ (p + 1, t) < t.size.toUInt64.toNat := by
    simp only [μ, hp1]
    rw [size_toUInt64 t (by omega)]
    split <;> omega
  have hinit : Inv (p + 1, t) := Or.inl ⟨0, Nat.zero_le _, hp1, rfl⟩
  refine repeatWhile_of_inv _ _ _ _ Inv μ (fun s => s.2 = gfold G (L.others k m) t) hinit hfuel
    ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨q, t'⟩ hI hc
    simp only [Inv] at hI
    dsimp only at hI hc ⊢
    simp only [decide_eq_false_iff_not, not_not] at hc
    rcases hI with ⟨j, hj, hq, -⟩ | ⟨j, hj, hq, ht⟩
    · rw [hc] at hq; omega
    · rw [hc] at hq
      have hjm : j = m := by omega
      rw [ht, hjm]
      unfold Layout.others
      rw [← hp, ← ha]
  · rintro ⟨q, t'⟩ hI hcond
    simp only [Inv] at hI ⊢
    dsimp only at hI hcond ⊢
    simp only [ne_eq, decide_eq_true_eq] at hcond
    have hqp : q.toNat ≠ p.toNat := fun e => hcond (UInt64.toNat_inj.mp e)
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]
      have := hsize; omega
    rcases hI with ⟨j, hj, hq, ht⟩ | ⟨j, hj, hq, ht⟩
    · have hs' := hS _ (hpre1 j hj)
      by_cases hja : j < a
      · -- A node of the option after `p`.
        have htop : W t' (3 * q.toNat) = L.item k (m + 1 + j) := by
          rw [ht, hq, show p.toNat + 1 + j = L.first k + (m + 1 + j) by omega]
          exact hs'.top k hk (m + 1 + j) (by omega)
        have hitem := (hL.items k hk (m + 1 + j) (by omega)).1
        obtain ⟨e0, -, -⟩ := idx3 q (by omega)
        have hx : t'[(3 * q).toNat]! ≠ 0 := by
          rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
        have hcat : List.range' (p.toNat + 1) j ++ [q.toNat] = List.range' (p.toNat + 1) (j + 1) := by
          rw [List.range'_1_concat, hq]
        refine ⟨?_, ?_⟩
        · left
          refine ⟨j + 1, by omega, by simp only [ite_eq_right hx, hq1]; omega, ?_⟩
          simp only [ite_eq_right hx]
          rw [ht, hF _ q (by rw [hcat]; exact hpre1 (j + 1) (by omega)), ← gfold_concat G, hcat]
        · simp only [μ, ite_eq_right hx, hq1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          omega
      · -- The spacer after the option: back to its first node.
        have hja' : j = a := by omega
        have hsp : q.toNat = L.first (k + 1) - 1 := by rw [Layout.first_succ]; omega
        obtain ⟨e0, e1, -⟩ := idx3 q (by omega)
        have hx : t'[(3 * q).toNat]! = 0 := by
          have := hs'.spacer (k + 1) hk
          rw [e0, hsp, ht]
          exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; exact this)
        have hup : (t'[(3 * q + 1).toNat]!).toNat = L.first k := by
          rw [e1, hsp, ht]; exact hs'.up k hk
        refine ⟨?_, ?_⟩
        · right
          refine ⟨0, Nat.zero_le _, ?_, ?_⟩
          · simp only [ite_eq_left hx]; rw [hup]; rfl
          · simp only [ite_eq_left hx]; rw [ht, hja', List.range'_zero, List.append_nil]
        · simp only [μ, ite_eq_left hx, hup]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          omega
    · have hs' := hS _ (hpre2 j hj)
      have hjm : j < m := by
        rcases Nat.lt_or_ge j m with h' | h'
        · exact h'
        · exact absurd (by omega : q.toNat = p.toNat) hqp
      have htop : W t' (3 * q.toNat) = L.item k j := by
        rw [ht, hq]; exact hs'.top k hk j (by omega)
      have hitem := (hL.items k hk j (by omega)).1
      obtain ⟨e0, -, -⟩ := idx3 q (by omega)
      have hx : t'[(3 * q).toNat]! ≠ 0 := by
        rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
      have hcat : (List.range' (p.toNat + 1) a ++ List.range' (L.first k) j) ++ [q.toNat] =
          List.range' (p.toNat + 1) a ++ List.range' (L.first k) (j + 1) := by
        rw [List.append_assoc, List.range'_1_concat, hq]
      refine ⟨?_, ?_⟩
      · right
        refine ⟨j + 1, by omega, by simp only [ite_eq_right hx, hq1]; omega, ?_⟩
        simp only [ite_eq_right hx]
        rw [ht, hF _ q (by rw [hcat]; exact hpre2 (j + 1) (by omega)), ← gfold_concat G, hcat]
      · simp only [μ, ite_eq_right hx, hq1]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        omega

/-- The backward walk around an option, from the array that `gfold G` of its `others` leaves,
returns the array before. -/
theorem walkBwd {L : Layout} (hL : L.Good) {k m : Nat} {p : UInt64} (hat : L.At p.toNat k m)
    (F : UInt64 → Array UInt64 → Array UInt64) (G : Nat → Array UInt64 → Array UInt64)
    (t : Array UInt64) (hS : ∀ l, l <+: L.others k m → Static (gfold G l t) L)
    (hF : ∀ l (q : UInt64), l ++ [q.toNat] <+: L.others k m →
      F q (gfold G (l ++ [q.toNat]) t) = gfold G l t) :
    (LeanExe.repeatWhile (gfold G (L.others k m) t).size.toUInt64
      (p - 1, gfold G (L.others k m) t) (fun s => decide (s.1 ≠ p)) fun s =>
      if s.2[(3 * s.1).toNat]! = 0 then (s.2[(3 * s.1 + 2).toNat]!, s.2)
      else (s.1 - 1, F s.1 s.2)).2 = t := by
  obtain ⟨hk, hm, hp⟩ := hat
  have hs0 := hS [] (List.nil_prefix)
  have hsize : t.size < 2 ^ 60 := by have := hs0.size; simp [gfold] at this; rw [this]; exact hL.small
  have hlast := L.first_le_last hk
  rw [Layout.first_succ] at hlast
  have hbase : 3 * L.first L.os.length ≤ t.size := by
    have := hs0.size; simp [gfold] at this; rw [this, Layout.base]; omega
  have hn1 := L.n_lt_first k
  set a := L.len k - m - 1 with ha
  obtain ⟨hpre1, hpre2⟩ := L.others_prefix_fwd hp ha
  have hsz : ∀ l, l <+: L.others k m → (gfold G l t).size = t.size := by
    intro l hl
    have h1 := (hS l hl).size
    have h0 := hs0.size
    simp only [gfold, List.foldl_nil] at h0
    omega
  let Inv : UInt64 × Array UInt64 → Prop := fun s =>
    (∃ i ≤ m, s.1.toNat + 1 = L.first k + i ∧
      s.2 = gfold G (List.range' (p.toNat + 1) a ++ List.range' (L.first k) i) t) ∨
      (∃ i ≤ a, s.1.toNat = p.toNat + i ∧ s.2 = gfold G (List.range' (p.toNat + 1) i) t)
  let μ : UInt64 × Array UInt64 → Nat := fun s =>
    if s.1.toNat < p.toNat then s.1.toNat + 1 - L.first k + a + 1 else s.1.toNat - p.toNat
  have hp1 : (p - 1).toNat = p.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hfuel : μ (p - 1, gfold G (L.others k m) t) <
      (gfold G (L.others k m) t).size.toUInt64.toNat := by
    have e : μ (p - 1, gfold G (L.others k m) t) = (p - 1).toNat + 1 - L.first k + a + 1 := by
      show (if (p - 1).toNat < p.toNat then (p - 1).toNat + 1 - L.first k + a + 1
        else (p - 1).toNat - p.toNat) = _
      rw [ite_eq_left (by rw [hp1]; omega)]
    rw [e, hp1, hsz _ (List.prefix_refl _), size_toUInt64 t (by omega)]
    omega
  have hinit : Inv (p - 1, gfold G (L.others k m) t) := by
    left
    refine ⟨m, le_rfl, ?_, ?_⟩
    · show (p - 1).toNat + 1 = L.first k + m
      rw [hp1]; omega
    · unfold Layout.others; rw [← hp, ← ha]
  refine repeatWhile_of_inv _ _ _ _ Inv μ (fun s => s.2 = t) hinit hfuel ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨q, t'⟩ hI hc
    simp only [Inv] at hI
    dsimp only at hI hc ⊢
    simp only [decide_eq_false_iff_not, not_not] at hc
    rcases hI with ⟨i, hi, hq, -⟩ | ⟨i, hi, hq, ht⟩
    · rw [hc] at hq; omega
    · rw [hc] at hq
      have hi0 : i = 0 := by omega
      rw [ht, hi0]; rfl
  · rintro ⟨q, t'⟩ hI hcond
    simp only [Inv] at hI ⊢
    dsimp only at hI hcond ⊢
    simp only [ne_eq, decide_eq_true_eq] at hcond
    have hqp : q.toNat ≠ p.toNat := fun e => hcond (UInt64.toNat_inj.mp e)
    rcases hI with ⟨i, hi, hq, ht⟩ | ⟨i, hi, hq, ht⟩
    · by_cases hi0 : i = 0
      · -- The spacer before the option: forward to its last node.
        have hsp : q.toNat = L.first k - 1 := by omega
        have hs' := hS _ (hpre2 0 (Nat.zero_le _))
        rw [hi0] at ht
        obtain ⟨e0, -, e2⟩ := idx3 q (by omega)
        have hx : t'[(3 * q).toNat]! = 0 := by
          have := hs'.spacer k (Nat.le_of_lt hk)
          rw [e0, hsp, ht]
          exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; exact this)
        have hdn : (t'[(3 * q + 2).toNat]!).toNat = L.first k + L.len k - 1 := by
          rw [e2, hsp, ht]; exact hs'.down k hk
        refine ⟨?_, ?_⟩
        · right
          refine ⟨a, le_rfl, ?_, ?_⟩
          · simp only [ite_eq_left hx]; rw [hdn]; omega
          · simp only [ite_eq_left hx]; rw [ht, List.range'_zero, List.append_nil]
        · simp only [μ, ite_eq_left hx, hdn]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          omega
      · -- A node of the option before `p`: undo it.
        have hqn : q.toNat = L.first k + (i - 1) := by omega
        have hcat : (List.range' (p.toNat + 1) a ++ List.range' (L.first k) (i - 1)) ++ [q.toNat] =
            List.range' (p.toNat + 1) a ++ List.range' (L.first k) i := by
          rw [List.append_assoc, hqn, ← List.range'_1_concat]
          congr 2; omega
        have hs' := hS _ (hpre2 i hi)
        have htop : W t' (3 * q.toNat) = L.item k (i - 1) := by
          rw [ht, hqn]; exact hs'.top k hk (i - 1) (by omega)
        have hitem := (hL.items k hk (i - 1) (by omega)).1
        obtain ⟨e0, -, -⟩ := idx3 q (by omega)
        have hx : t'[(3 * q).toNat]! ≠ 0 := by
          rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
        have hq1 : (q - 1).toNat = q.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        refine ⟨?_, ?_⟩
        · left
          refine ⟨i - 1, by omega, by simp only [ite_eq_right hx, hq1]; omega, ?_⟩
          simp only [ite_eq_right hx]
          rw [ht, ← hcat, hF _ q (by rw [hcat]; exact hpre2 i hi)]
        · simp only [μ, ite_eq_right hx, hq1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          omega
    · -- A node of the option after `p`: undo it.
      have hi0 : i ≠ 0 := fun e => hqp (by omega)
      have hcat : List.range' (p.toNat + 1) (i - 1) ++ [q.toNat] =
          List.range' (p.toNat + 1) i := by
        rw [show q.toNat = p.toNat + 1 + (i - 1) by omega, ← List.range'_1_concat]
        congr 1; omega
      have hs' := hS _ (hpre1 i hi)
      have htop : W t' (3 * q.toNat) = L.item k (m + i) := by
        rw [ht, show q.toNat = L.first k + (m + i) by omega]
        exact hs'.top k hk (m + i) (by omega)
      have hitem := (hL.items k hk (m + i) (by omega)).1
      obtain ⟨e0, -, -⟩ := idx3 q (by omega)
      have hx : t'[(3 * q).toNat]! ≠ 0 := by
        rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
      have hq1 : (q - 1).toNat = q.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      refine ⟨?_, ?_⟩
      · right
        refine ⟨i - 1, by omega, by simp only [ite_eq_right hx, hq1]; omega, ?_⟩
        simp only [ite_eq_right hx]
        rw [ht, ← hcat, hF _ q (by rw [hcat]; exact hpre1 i hi)]
      · simp only [μ, ite_eq_right hx, hq1]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        omega

/-- Removals along a prefix of `others` keep the static words and the columns, and leave the next
node present. -/
theorem others_prefix_inv {t : Array UInt64} {L : Layout} {C P : Finset Nat} (hs : Static t L)
    (h : Cols t L C P) {k m : Nat} (hoth : ∀ q ∈ L.others k m, q ∈ P ∧ L.nodeItem q ∈ C)
    {l : List Nat} (hl : l <+: L.others k m) :
    Static (delAll l t) L ∧ Cols (delAll l t) L C (P \ l.toFinset) :=
  delAll_inv l t P hs h ((L.others_nodup k m).sublist hl.sublist) fun q hq => hoth q (hl.subset hq)

theorem others_next {L : Layout} {P : Finset Nat} {k m : Nat} {l : List Nat} {q : Nat}
    (hl : l ++ [q] <+: L.others k m) (hP : q ∈ P) : q ∈ P \ l.toFinset := by
  refine mem_sdiff.mpr ⟨hP, fun hin => ?_⟩
  have hnd := (L.others_nodup k m).sublist hl.sublist
  exact List.disjoint_of_nodup_append hnd (List.mem_toFinset.mp hin) (List.mem_singleton_self _)

/-- `hide p` removes the other nodes of `p`'s option, in the order of `others`. -/
theorem hide_eq {t : Array UInt64} {L : Layout} {C P : Finset Nat} (hL : L.Good) (hs : Static t L)
    (h : Cols t L C P) {p : UInt64} {k m : Nat} (hat : L.At p.toNat k m)
    (hoth : ∀ q ∈ L.others k m, q ∈ P ∧ L.nodeItem q ∈ C) :
    hide p t = delAll (L.others k m) t := by
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  unfold hide
  dsimp only
  rw [delAll_eq_gfold]
  refine walkFwd hL hat (fun q t => ((t.set! (3 * t[(3 * q + 1).toNat]! + 2).toNat
      t[(3 * q + 2).toNat]!).set! (3 * t[(3 * q + 2).toNat]! + 1).toNat t[(3 * q + 1).toNat]!).set!
      (3 * t[(3 * q).toNat]!).toNat (t[(3 * t[(3 * q).toNat]!).toNat]! - 1))
    (fun q t => del t q) t (fun l hl => ?_) (fun l q hl => ?_)
  · rw [← delAll_eq_gfold]; exact (others_prefix_inv hs h hoth hl).1
  · have hpre : l <+: L.others k m := (List.prefix_append l [q.toNat]).trans hl
    obtain ⟨-, hc⟩ := others_prefix_inv hs h hoth hpre
    have hq := hoth q.toNat (hl.subset (List.mem_append_right _ (List.mem_singleton_self _)))
    rw [← delAll_eq_gfold]
    exact hide_step hc (by rw [delAll_size]; exact hsize) (others_next hl hq.1) hq.2

/-- `unhide p`, applied to the array that `hide p` leaves, returns the array before `hide`. -/
theorem unhide_eq {t : Array UInt64} {L : Layout} {C P : Finset Nat} (hL : L.Good) (hs : Static t L)
    (h : Cols t L C P) {p : UInt64} {k m : Nat} (hat : L.At p.toNat k m)
    (hoth : ∀ q ∈ L.others k m, q ∈ P ∧ L.nodeItem q ∈ C) :
    unhide p (delAll (L.others k m) t) = t := by
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  unfold unhide
  dsimp only
  rw [delAll_eq_gfold]
  refine walkBwd hL hat (fun q t => ((t.set! (3 * t[(3 * q + 1).toNat]! + 2).toNat q).set!
      (3 * t[(3 * q + 2).toNat]! + 1).toNat q).set! (3 * t[(3 * q).toNat]!).toNat
      (t[(3 * t[(3 * q).toNat]!).toNat]! + 1))
    (fun q t => del t q) t (fun l hl => ?_) (fun l q hl => ?_)
  · rw [← delAll_eq_gfold]; exact (others_prefix_inv hs h hoth hl).1
  · have hpre : l <+: L.others k m := (List.prefix_append l [q.toNat]).trans hl
    obtain ⟨-, hc⟩ := others_prefix_inv hs h hoth hpre
    have hq := hoth q.toNat (hl.subset (List.mem_append_right _ (List.mem_singleton_self _)))
    rw [gfold_concat, ← delAll_eq_gfold]
    exact unhide_step hc (by rw [delAll_size]; exact hsize) (others_next hl hq.1) hq.2

end Library.Combinatorics.DancingLinks
