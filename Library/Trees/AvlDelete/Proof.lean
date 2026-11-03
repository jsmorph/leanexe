import Library.Trees.AvlDelete.Program
import Library.Trees.AvlDelete.Spec
import Library.Trees.Avl.Proof

/-! The proofs that `delete` computes `deleteA` and that `deleteA` satisfies `Removes` on every
balanced binary search tree.  `descendDel_eq` and `minDel_eq` state the link reversal: each loop
returns what `ascendDel` or `ascendMin` returns from the flag and the tree of `deleteA` or
`deleteMinA` below the same path, since each step with the flag set applies `shrinkLeftA` or
`shrinkRightA` to the node above, and each other step rebuilds that node.  `shrinkLeftA_props`
follows the cases of a shrunk left subtree through the heights, and `deleteA_props` and
`keys_deleteA` give the balance, the height, and the keys of the result. -/

namespace Library.Trees.AvlDelete

open Library.Trees.Avl (AvlTree height keys Ordered Balanced rootBal ordered_node searchA)

theorem isLeaf_iff (t : AvlTree) : isLeaf t = true ↔ t = .leaf := by
  cases t <;> simp [isLeaf]

theorem shrinkLeft_eq (t : AvlTree) (k b : UInt64) (c : AvlTree) :
    shrinkLeft (.node t k b c) = shrinkLeftA t k b c := by
  simp only [shrinkLeft, shrinkLeftA]
  split_ifs <;> try rfl
  cases c with
  | leaf => rfl
  | node cl ck cb cr =>
    simp only
    split_ifs <;> try rfl
    cases cl <;> rfl

theorem shrinkRight_eq (a : AvlTree) (k b : UInt64) (t : AvlTree) :
    shrinkRight (.node a k b t) = shrinkRightA a k b t := by
  simp only [shrinkRight, shrinkRightA]
  split_ifs <;> try rfl
  cases a with
  | leaf => rfl
  | node al ak ab ar =>
    simp only
    split_ifs <;> try rfl
    cases ar <;> rfl

theorem ascendDel_left {x k b : UInt64} {g : Bool} {p c t : AvlTree} (hx : x < k) :
    ascendDel x g (.node p k b c) t =
      if g then ascendDel x (shrinkLeftA t k b c).1 p (shrinkLeftA t k b c).2
      else ascendDel x false p (.node t k b c) := by
  cases g <;> simp [ascendDel, hx, shrinkLeft_eq]

theorem ascendDel_right {x k b : UInt64} {g : Bool} {p a t : AvlTree} (hx : ¬x < k) :
    ascendDel x g (.node a k b p) t =
      if g then ascendDel x (shrinkRightA a k b t).1 p (shrinkRightA a k b t).2
      else ascendDel x false p (.node a k b t) := by
  cases g <;> simp [ascendDel, hx, shrinkRight_eq]

theorem ascendMin_step {x s k b : UInt64} {g : Bool} {found i c t : AvlTree} :
    ascendMin x s g found (.node i k b c) t =
      if g then ascendMin x s (shrinkLeftA t k b c).1 found i (shrinkLeftA t k b c).2
      else ascendMin x s false found i (.node t k b c) := by
  cases g <;> simp [ascendMin, shrinkLeft_eq]

theorem ascendMin_found {x s k b : UInt64} {g : Bool} {a p t : AvlTree} :
    ascendMin x s g (.node a k b p) .leaf t =
      if g then ascendDel x (shrinkRightA a s b t).1 p (shrinkRightA a s b t).2
      else ascendDel x false p (.node a s b t) := by
  cases g <;> simp [ascendMin, shrinkRight_eq]

theorem minDel_eq (x : UInt64) (found inner t : AvlTree) :
    minDel x found inner t =
      ascendMin x (deleteMinA t).2.1 (deleteMinA t).1 found inner (deleteMinA t).2.2 := by
  induction t generalizing inner with
  | leaf => simp [minDel, deleteMinA]
  | node l k b r ihl _ =>
    cases l with
    | leaf => simp [minDel, isLeaf, deleteMinA]
    | node ll lk lb lr =>
      rw [minDel]
      simp only [isLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [ihl, ascendMin_step]
      by_cases hd : (deleteMinA (.node ll lk lb lr)).1 = true
      · simp [deleteMinA, hd]
      · simp [deleteMinA, hd]

theorem descendDel_eq (x : UInt64) (path t : AvlTree) :
    descendDel x path t = ascendDel x (deleteA x t).1 path (deleteA x t).2 := by
  induction t generalizing path with
  | leaf => simp [descendDel, deleteA]
  | node l k b r ihl ihr =>
    by_cases h : x < k
    · simp only [descendDel, h, ↓reduceIte, ihl, ascendDel_left h, deleteA]
      cases (deleteA x l).1 <;> rfl
    · by_cases h' : k < x
      · simp only [descendDel, h, h', ↓reduceIte, ihr, ascendDel_right h, deleteA]
        cases (deleteA x r).1 <;> rfl
      · cases l with
        | leaf => simp [descendDel, deleteA, h, h', isLeaf]
        | node ll lk lb lr =>
          cases r with
          | leaf => simp [descendDel, deleteA, h, h', isLeaf]
          | node rl rk rb rr =>
            simp only [descendDel, deleteA, h, h', ↓reduceIte, isLeaf, Bool.false_eq_true,
              minDel_eq, ascendMin_found]
            cases (deleteMinA (.node rl rk rb rr)).1 <;> rfl

theorem delete_eq (x : UInt64) (t : AvlTree) : delete x t = (deleteA x t).2 := by
  simp [delete, descendDel_eq, ascendDel]

theorem shrinkLeftA_props {t c : AvlTree} {k b : UInt64} {hl : Nat} (ht : Balanced t)
    (hc : Balanced c)
    (hb : height c = hl ∧ b = 0 ∨ height c = hl + 1 ∧ b = 1 ∨
      hl = height c + 1 ∧ b = 0 - 1)
    (hth : height t + 1 = hl) :
    Balanced (shrinkLeftA t k b c).2 ∧
      height (shrinkLeftA t k b c).2 + (if (shrinkLeftA t k b c).1 then 1 else 0) =
        max hl (height c) + 1 := by
  rcases hb with ⟨hh, rfl⟩ | ⟨hh, rfl⟩ | ⟨hh, rfl⟩
  · simp +decide [shrinkLeftA, Balanced, height, ht, hc]
    omega
  · cases c with
    | leaf => simp [height] at hh
    | node cl ck cb cr =>
      obtain ⟨hcl, hcr, hcb⟩ := hc
      simp only [height] at hh
      rcases hcb with ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩
      · simp +decide [shrinkLeftA, Balanced, height, ht, hcl, hcr]
        omega
      · simp +decide [shrinkLeftA, Balanced, height, ht, hcl, hcr]
        omega
      · cases cl with
        | leaf => simp [height] at hh2
        | node ul uk ub ur =>
          obtain ⟨hul, hur, hub⟩ := hcl
          simp only [height] at hh2 hh
          rcases hub with ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ <;>
            simp +decide [shrinkLeftA, Balanced, height, ht, hul, hur, hcr] <;> omega
  · simp +decide [shrinkLeftA, Balanced, height, ht, hc]
    omega

theorem shrinkRightA_props {a t : AvlTree} {k b : UInt64} {hr : Nat} (ha : Balanced a)
    (ht : Balanced t)
    (hb : hr = height a ∧ b = 0 ∨ hr = height a + 1 ∧ b = 1 ∨
      height a = hr + 1 ∧ b = 0 - 1)
    (hth : height t + 1 = hr) :
    Balanced (shrinkRightA a k b t).2 ∧
      height (shrinkRightA a k b t).2 + (if (shrinkRightA a k b t).1 then 1 else 0) =
        max (height a) hr + 1 := by
  rcases hb with ⟨hh, rfl⟩ | ⟨hh, rfl⟩ | ⟨hh, rfl⟩
  · simp +decide [shrinkRightA, Balanced, height, ha, ht]
    omega
  · simp +decide [shrinkRightA, Balanced, height, ha, ht]
    omega
  · cases a with
    | leaf => simp [height] at hh
    | node al ak ab ar =>
      obtain ⟨hal, har, hab⟩ := ha
      simp only [height] at hh
      rcases hab with ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩
      · simp +decide [shrinkRightA, Balanced, height, ht, hal, har]
        omega
      · cases ar with
        | leaf => simp [height] at hh2
        | node ul uk ub ur =>
          obtain ⟨hul, hur, hub⟩ := har
          simp only [height] at hh2 hh
          rcases hub with ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ <;>
            simp +decide [shrinkRightA, Balanced, height, ht, hal, hul, hur] <;> omega
      · simp +decide [shrinkRightA, Balanced, height, ht, hal, har]
        omega

theorem keys_shrinkLeftA (t : AvlTree) (k b : UInt64) (c : AvlTree) :
    keys (shrinkLeftA t k b c).2 = keys t ++ k :: keys c := by
  unfold shrinkLeftA
  split_ifs
  · rfl
  · rfl
  · split
    · split_ifs
      · simp [keys]
      · simp [keys]
      · split
        · simp [keys]
        · rfl
    · rfl

theorem keys_shrinkRightA (a : AvlTree) (k b : UInt64) (t : AvlTree) :
    keys (shrinkRightA a k b t).2 = keys a ++ k :: keys t := by
  unfold shrinkRightA
  split_ifs
  · rfl
  · rfl
  · split
    · split_ifs
      · simp [keys]
      · simp [keys]
      · split
        · simp [keys]
        · rfl
    · rfl

theorem keys_deleteMinA (t : AvlTree) (hne : t ≠ .leaf) :
    keys t = (deleteMinA t).2.1 :: keys (deleteMinA t).2.2 := by
  induction t with
  | leaf => exact absurd rfl hne
  | node l k b r ihl _ =>
    cases l with
    | leaf => simp [deleteMinA, keys]
    | node ll lk lb lr =>
      have hk := ihl (by simp)
      rw [keys, hk]
      by_cases hd : (deleteMinA (.node ll lk lb lr)).1 = true
      · simp [deleteMinA, hd, keys_shrinkLeftA]
      · simp [deleteMinA, hd, keys]

/-- The removal of the leftmost node of a balanced tree with at least one node keeps it balanced
and lowers it one level exactly when it reports so. -/
theorem deleteMinA_props (t : AvlTree) (hb : Balanced t) (hne : t ≠ .leaf) :
    Balanced (deleteMinA t).2.2 ∧
      height (deleteMinA t).2.2 + (if (deleteMinA t).1 then 1 else 0) = height t := by
  induction t with
  | leaf => exact absurd rfl hne
  | node l k b r ihl _ =>
    obtain ⟨hl, hr, hlr⟩ := hb
    cases l with
    | leaf =>
      show Balanced r ∧ height r + 1 = height (AvlTree.node .leaf k b r)
      refine ⟨hr, ?_⟩
      simp only [height] at hlr ⊢
      omega
    | node ll lk lb lr =>
      obtain ⟨b1, b2⟩ := ihl hl (by simp)
      by_cases hd : (deleteMinA (.node ll lk lb lr)).1 = true
      · simp only [hd, ↓reduceIte] at b2
        obtain ⟨s1, s2⟩ := shrinkLeftA_props (k := k) b1 hr hlr b2
        simp only [deleteMinA, hd, ↓reduceIte]
        exact ⟨s1, by rw [s2]; simp only [height]⟩
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at b2
        simp only [deleteMinA, hd, Bool.false_eq_true, ↓reduceIte]
        exact ⟨⟨b1, hr, by rw [show height (deleteMinA (.node ll lk lb lr)).2.2 =
          height (.node ll lk lb lr) by omega]; exact hlr⟩,
          by simp only [height] at b2 ⊢; omega⟩

/-- Deletion keeps a balanced tree balanced and lowers it one level exactly when it reports so. -/
theorem deleteA_props (x : UInt64) (t : AvlTree) (hb : Balanced t) :
    Balanced (deleteA x t).2 ∧
      height (deleteA x t).2 + (if (deleteA x t).1 then 1 else 0) = height t := by
  induction t with
  | leaf => simp [deleteA, Balanced]
  | node l k b r ihl ihr =>
    obtain ⟨hl, hr, hlr⟩ := hb
    obtain ⟨bl, hgl⟩ := ihl hl
    obtain ⟨br, hgr⟩ := ihr hr
    by_cases h : x < k
    · simp only [deleteA, h, ↓reduceIte]
      cases hg : (deleteA x l).1
      · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hgl ⊢
        exact ⟨⟨bl, hr, by rw [show height (deleteA x l).2 = height l by omega]; exact hlr⟩,
          by simp only [height]; omega⟩
      · simp only [hg, ↓reduceIte] at hgl ⊢
        obtain ⟨s1, s2⟩ := shrinkLeftA_props (k := k) bl hr hlr hgl
        exact ⟨s1, by rw [s2]; simp only [height]⟩
    · by_cases h' : k < x
      · simp only [deleteA, h, h', ↓reduceIte]
        cases hg : (deleteA x r).1
        · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hgr ⊢
          exact ⟨⟨hl, br, by rw [show height (deleteA x r).2 = height r by omega]; exact hlr⟩,
            by simp only [height]; omega⟩
        · simp only [hg, ↓reduceIte] at hgr ⊢
          obtain ⟨s1, s2⟩ := shrinkRightA_props (k := k) hl br hlr hgr
          exact ⟨s1, by rw [s2]; simp only [height]⟩
      · have := Library.Trees.Avl.eq_of_not_lt h h'
        subst this
        cases l with
        | leaf =>
          simp only [deleteA, h, ↓reduceIte]
          refine ⟨hr, ?_⟩
          simp only [height] at hlr ⊢
          omega
        | node ll lk lb lr =>
          cases r with
          | leaf =>
            simp only [deleteA, h, ↓reduceIte]
            refine ⟨hl, ?_⟩
            simp only [height] at hlr ⊢
            omega
          | node rl rk rb rr =>
            obtain ⟨d1, d2⟩ := deleteMinA_props _ hr (by simp)
            by_cases hd : (deleteMinA (.node rl rk rb rr)).1 = true
            · simp only [hd, ↓reduceIte] at d2
              obtain ⟨s1, s2⟩ := shrinkRightA_props (k := (deleteMinA (.node rl rk rb rr)).2.1)
                hl d1 hlr d2
              simp only [deleteA, h, hd, ↓reduceIte]
              exact ⟨s1, by rw [s2]; simp only [height]⟩
            · simp only [hd, Bool.false_eq_true, ↓reduceIte] at d2
              simp only [deleteA, h, hd, Bool.false_eq_true, ↓reduceIte]
              exact ⟨⟨hl, d1, by rw [show height (deleteMinA (.node rl rk rb rr)).2.2 =
                height (.node rl rk rb rr) by omega]; exact hlr⟩,
                by simp only [height] at d2 ⊢; omega⟩

theorem not_mem_of_lt {x k : UInt64} {r : AvlTree} (hkr : ∀ c ∈ keys r, k < c) (h : x < k) :
    x ∉ keys r := fun hx => UInt64.lt_irrefl _ (UInt64.lt_trans h (hkr x hx))

theorem keys_deleteA (x : UInt64) (t : AvlTree) (ht : Ordered t) :
    keys (deleteA x t).2 = (keys t).erase x := by
  induction t with
  | leaf => simp [deleteA, keys]
  | node l k b r ihl ihr =>
    obtain ⟨hl, hr, hlk, hkr⟩ := ordered_node.mp ht
    by_cases h : x < k
    · have hnode : keys (deleteA x (.node l k b r)).2 = keys (deleteA x l).2 ++ k :: keys r := by
        simp only [deleteA, h, ↓reduceIte]
        split
        · exact keys_shrinkLeftA _ _ _ _
        · rfl
      rw [hnode, ihl hl, keys]
      by_cases hx : x ∈ keys l
      · rw [List.erase_append_left _ hx]
      · rw [List.erase_of_not_mem hx, List.erase_append_right _ hx,
          List.erase_cons_tail (by simpa using fun e : k = x => UInt64.lt_irrefl x (e ▸ h)),
          List.erase_of_not_mem (not_mem_of_lt hkr h)]
    · by_cases h' : k < x
      · have hnode :
            keys (deleteA x (.node l k b r)).2 = keys l ++ k :: keys (deleteA x r).2 := by
          simp only [deleteA, h, h', ↓reduceIte]
          split
          · exact keys_shrinkRightA _ _ _ _
          · rfl
        have hxl : x ∉ keys l := fun hx => UInt64.lt_irrefl _ (UInt64.lt_trans h' (hlk x hx))
        rw [hnode, ihr hr, keys, List.erase_append_right _ hxl,
          List.erase_cons_tail
            (by simpa using fun e : k = x => UInt64.lt_irrefl x (by rw [e] at h'; exact h'))]
      · have := Library.Trees.Avl.eq_of_not_lt h h'
        subst this
        have hxl : x ∉ keys l := fun hx => UInt64.lt_irrefl _ (hlk x hx)
        rw [keys, List.erase_append_right _ hxl, List.erase_cons_head]
        simp only [deleteA, h, ↓reduceIte]
        cases l with
        | leaf => simp [keys]
        | node ll lk lb lr =>
          cases r with
          | leaf => simp [keys]
          | node rl rk rb rr =>
            have d3 := keys_deleteMinA (.node rl rk rb rr) (by simp)
            simp only
            split
            · rw [keys_shrinkRightA, d3]
            · rw [keys, d3]

theorem shrank_mem (x : UInt64) (t : AvlTree) : (deleteA x t).1 = true → x ∈ keys t := by
  induction t with
  | leaf => simp [deleteA]
  | node l k b r ihl ihr =>
    intro hg
    by_cases h : x < k
    · simp only [deleteA, h, ↓reduceIte] at hg
      cases hl : (deleteA x l).1
      · simp [hl] at hg
      · simp [keys, ihl hl]
    · by_cases h' : k < x
      · simp only [deleteA, h, h', ↓reduceIte] at hg
        cases hr : (deleteA x r).1
        · simp [hr] at hg
        · simp [keys, ihr hr]
      · have := Library.Trees.Avl.eq_of_not_lt h h'
        subst this
        simp [keys]

/-- A failed search leaves every tree as it is, factors included. -/
theorem deleteA_of_searchA (x : UInt64) (t : AvlTree) (h : searchA x t = false) :
    deleteA x t = (false, t) := by
  induction t with
  | leaf => rfl
  | node l k b r ihl ihr =>
    by_cases hl : x < k
    · simp only [searchA, hl, ↓reduceIte] at h
      simp [deleteA, hl, ihl h]
    · by_cases hr : k < x
      · simp only [searchA, hl, hr, ↓reduceIte] at h
        simp [deleteA, hl, hr, ihr h]
      · simp [searchA, hl, hr] at h

theorem searchA_of_not_mem (x : UInt64) (t : AvlTree) (h : x ∉ keys t) : searchA x t = false := by
  induction t with
  | leaf => rfl
  | node l k b r ihl ihr =>
    simp only [keys, List.mem_append, List.mem_cons, not_or] at h
    obtain ⟨hl, hk, hr⟩ := h
    by_cases h1 : x < k
    · simp [searchA, h1, ihl hl]
    · by_cases h2 : k < x
      · simp [searchA, h1, h2, ihr hr]
      · exact absurd (Library.Trees.Avl.eq_of_not_lt h1 h2) hk

/-- Deletion on a balanced binary search tree satisfies the guarantees of `Removes`. -/
theorem removes (x : UInt64) (t : AvlTree) (ho : Ordered t) (hb : Balanced t) : Removes x t := by
  have hk := keys_deleteA x t ho
  have hp := deleteA_props x t hb
  refine ⟨?_, hp.1, hk, hp.2, shrank_mem x t, fun hx => by
    rw [deleteA_of_searchA x t (searchA_of_not_mem x t hx)]⟩
  unfold Ordered
  rw [hk]
  exact ho.sublist (List.erase_sublist ..)

end Library.Trees.AvlDelete
