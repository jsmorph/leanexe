import Library.Trees.Avl.Program
import Library.Trees.Avl.Spec
import Library.Trees.Search.Proof

/-! The proofs that `search` and `insert` compute `searchA` and `algorithmA`, and that `algorithmA`
meets `SearchTree` on every balanced binary search tree.  `descend_eq` states the link reversal:
`descend x path t` returns what `ascend` returns from the flag and the tree of `algorithmA x t`
below the same `path`, since each step of `ascend` with the flag set applies `growLeft` or
`growRight` to the node above, and each other step rebuilds that node.  `growLeft_props` follows
steps A7 to A9 through the heights of the subtrees: a node that leaned right becomes balanced, a
balanced node leans left and grows, and a node that leaned left is rotated back to its height before
the insertion. -/

namespace Library.Trees.Avl

open Library.Trees.Search (orderedInsert_append_cons orderedInsert_append_of_lt)

theorem search_eq (x : UInt64) (t : AvlTree) : search x t = searchA x t := by
  induction t with
  | leaf => rfl
  | node l k b r ihl ihr => simp [search, searchA, ihl, ihr]

theorem growLeft_rotate (t : AvlTree) (k b : UInt64) (c : AvlTree) (h1 : ¬b = 1) (h0 : ¬b = 0) :
    growLeft t k b c = (false, rotateRight (.node t k b c)) := by
  simp only [growLeft, h1, h0, ↓reduceIte, rotateRight]
  cases t with
  | leaf => rfl
  | node tl tk tb tr =>
    simp only
    split
    · rfl
    · cases tr <;> rfl

theorem growRight_rotate (a : AvlTree) (k b : UInt64) (t : AvlTree) (h1 : ¬b = 0 - 1)
    (h0 : ¬b = 0) : growRight a k b t = (false, rotateLeft (.node a k b t)) := by
  simp only [growRight, h1, h0, ↓reduceIte, rotateLeft]
  cases t with
  | leaf => rfl
  | node tl tk tb tr =>
    simp only
    split
    · rfl
    · cases tl <;> rfl

theorem ascend_left {x k b : UInt64} {g : Bool} {p c t : AvlTree} (hx : x < k) :
    ascend x g (.node p k b c) t =
      if g then ascend x (growLeft t k b c).1 p (growLeft t k b c).2
      else ascend x false p (.node t k b c) := by
  cases g
  · simp [ascend, hx]
  · by_cases h1 : b = 1
    · subst h1
      simp [ascend, hx, growLeft]
    · by_cases h0 : b = 0
      · subst h0
        simp [ascend, hx, growLeft]
      · rw [growLeft_rotate t k b c h1 h0]
        simp [ascend, hx, h1, h0]

theorem ascend_right {x k b : UInt64} {g : Bool} {p a t : AvlTree} (hx : ¬x < k) :
    ascend x g (.node a k b p) t =
      if g then ascend x (growRight a k b t).1 p (growRight a k b t).2
      else ascend x false p (.node a k b t) := by
  cases g
  · simp [ascend, hx]
  · by_cases h1 : b = 0 - 1
    · subst h1
      simp +decide [ascend, hx, growRight]
    · by_cases h0 : b = 0
      · subst h0
        simp +decide [ascend, hx, growRight]
      · rw [growRight_rotate a k b t h1 h0]
        simp at h1
        simp [ascend, hx, h1, h0]

theorem descend_eq (x : UInt64) (path t : AvlTree) :
    descend x path t = ascend x (algorithmA x t).1 path (algorithmA x t).2 := by
  induction t generalizing path with
  | leaf => simp [descend, algorithmA]
  | node l k b r ihl ihr =>
    by_cases h : x < k
    · simp only [descend, h, ↓reduceIte, ihl, ascend_left h, algorithmA]
      cases (algorithmA x l).1 <;> rfl
    · by_cases h' : k < x
      · simp only [descend, h, h', ↓reduceIte, ihr, ascend_right h, algorithmA]
        cases (algorithmA x r).1 <;> rfl
      · simp [descend, algorithmA, h, h']

theorem insert_eq (x : UInt64) (t : AvlTree) : insert x t = (algorithmA x t).2 := by
  simp [insert, descend_eq, ascend]

/-- The balance factor at the root, and 0 at a leaf. -/
def rootBal : AvlTree → UInt64
  | .leaf => 0
  | .node _ _ b _ => b

theorem growLeft_props {t c : AvlTree} {k b : UInt64} {hl : Nat} (ht : Balanced t)
    (hc : Balanced c)
    (hb : height c = hl ∧ b = 0 ∨ height c = hl + 1 ∧ b = 1 ∨
      hl = height c + 1 ∧ b = 0 - 1)
    (hth : height t = hl + 1) (hlean : hl = 0 ∨ rootBal t ≠ 0) :
    Balanced (growLeft t k b c).2 ∧
      height (growLeft t k b c).2 =
        max hl (height c) + 1 + (if (growLeft t k b c).1 then 1 else 0) ∧
      ((growLeft t k b c).1 = true → rootBal (growLeft t k b c).2 ≠ 0) := by
  rcases hb with ⟨hh, rfl⟩ | ⟨hh, rfl⟩ | ⟨hh, rfl⟩
  · simp +decide [growLeft, Balanced, height, rootBal, ht, hc]
    omega
  · simp +decide [growLeft, Balanced, height, rootBal, ht, hc]
    omega
  · have hlean' : rootBal t ≠ 0 := by
      rcases hlean with h | h
      · omega
      · exact h
    cases t with
    | leaf => simp [height] at hth
    | node tl tk tb tr =>
      obtain ⟨htl, htr, htb⟩ := ht
      simp only [rootBal] at hlean'
      simp only [height] at hth
      rcases htb with ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩
      · exact absurd rfl hlean'
      · cases tr with
        | leaf => simp [height] at hh2
        | node ul uk ub ur =>
          obtain ⟨hul, hur, hub⟩ := htr
          simp only [height] at hh2 hth
          rcases hub with ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ <;>
            simp +decide [growLeft, Balanced, height, rootBal, htl, hul, hur, hc] <;> omega
      · simp +decide [growLeft, Balanced, height, rootBal, htl, htr, hc]
        omega

theorem growRight_props {a t : AvlTree} {k b : UInt64} {hr : Nat} (ha : Balanced a)
    (ht : Balanced t)
    (hb : hr = height a ∧ b = 0 ∨ hr = height a + 1 ∧ b = 1 ∨
      height a = hr + 1 ∧ b = 0 - 1)
    (hth : height t = hr + 1) (hlean : hr = 0 ∨ rootBal t ≠ 0) :
    Balanced (growRight a k b t).2 ∧
      height (growRight a k b t).2 =
        max (height a) hr + 1 + (if (growRight a k b t).1 then 1 else 0) ∧
      ((growRight a k b t).1 = true → rootBal (growRight a k b t).2 ≠ 0) := by
  rcases hb with ⟨hh, rfl⟩ | ⟨hh, rfl⟩ | ⟨hh, rfl⟩
  · simp +decide [growRight, Balanced, height, rootBal, ha, ht]
    omega
  · have hlean' : rootBal t ≠ 0 := by
      rcases hlean with h | h
      · omega
      · exact h
    cases t with
    | leaf => simp [height] at hth
    | node tl tk tb tr =>
      obtain ⟨htl, htr, htb⟩ := ht
      simp only [rootBal] at hlean'
      simp only [height] at hth
      rcases htb with ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩ | ⟨hh2, rfl⟩
      · exact absurd rfl hlean'
      · simp +decide [growRight, Balanced, height, rootBal, ha, htl, htr]
        omega
      · cases tl with
        | leaf => simp [height] at hh2
        | node ul uk ub ur =>
          obtain ⟨hul, hur, hub⟩ := htl
          simp only [height] at hh2 hth
          rcases hub with ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ | ⟨hh3, rfl⟩ <;>
            simp +decide [growRight, Balanced, height, rootBal, ha, hul, hur, htr] <;> omega
  · simp +decide [growRight, Balanced, height, rootBal, ha, ht]
    omega

/-- Algorithm A keeps a tree balanced, grows it by one level exactly when it reports growth, and
leaves a grown tree of more than one node leaning. -/
theorem algorithmA_props (x : UInt64) (t : AvlTree) (hb : Balanced t) :
    Balanced (algorithmA x t).2 ∧
      height (algorithmA x t).2 = height t + (if (algorithmA x t).1 then 1 else 0) ∧
      ((algorithmA x t).1 = true → height t = 0 ∨ rootBal (algorithmA x t).2 ≠ 0) := by
  induction t with
  | leaf => simp [algorithmA, Balanced, height]
  | node l k b r ihl ihr =>
    obtain ⟨hl, hr, hlr⟩ := hb
    obtain ⟨bl, hgl, lean⟩ := ihl hl
    obtain ⟨br, hgr, rean⟩ := ihr hr
    by_cases h : x < k
    · simp only [algorithmA, h, ↓reduceIte]
      cases hg : (algorithmA x l).1
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, Balanced, height] at hgl ⊢
        refine ⟨⟨bl, hr, by rw [hgl]; simpa using hlr⟩, by rw [hgl]; simp,
          fun h => absurd h (by simp)⟩
      · simp only [hg, ↓reduceIte] at hgl lean ⊢
        obtain ⟨b1, b2, b3⟩ := growLeft_props (k := k) bl hr hlr hgl (lean trivial)
        refine ⟨b1, by rw [b2]; simp [height], fun hg' => .inr (b3 hg')⟩
    · by_cases h' : k < x
      · simp only [algorithmA, h, h', ↓reduceIte]
        cases hg : (algorithmA x r).1
        · simp only [hg, Bool.false_eq_true, ↓reduceIte, Balanced, height] at hgr ⊢
          refine ⟨⟨hl, br, by rw [hgr]; simpa using hlr⟩, by rw [hgr]; simp,
            fun h => absurd h (by simp)⟩
        · simp only [hg, ↓reduceIte] at hgr rean ⊢
          obtain ⟨b1, b2, b3⟩ := growRight_props (k := k) hl br hlr hgr (rean trivial)
          refine ⟨b1, by rw [b2]; simp [height], fun hg' => .inr (b3 hg')⟩
      · simp only [algorithmA, h, h', ↓reduceIte, Bool.false_eq_true]
        exact ⟨⟨hl, hr, hlr⟩, by simp, fun h => absurd h (by simp)⟩

/-- The keys of the node after a growth of its left or right subtree are those of the node with the
grown subtree in place: rotations keep the symmetric order. -/
theorem keys_growLeft (t : AvlTree) (k b : UInt64) (c : AvlTree) :
    keys (growLeft t k b c).2 = keys t ++ k :: keys c := by
  unfold growLeft
  split_ifs
  · rfl
  · rfl
  · split
    · rename_i tl tk tb tr
      split_ifs
      · simp [keys]
      · split
        · simp [keys]
        · rfl
    · rfl

theorem keys_growRight (a : AvlTree) (k b : UInt64) (t : AvlTree) :
    keys (growRight a k b t).2 = keys a ++ k :: keys t := by
  unfold growRight
  split_ifs
  · rfl
  · rfl
  · split
    · rename_i tl tk tb tr
      split_ifs
      · simp [keys]
      · split
        · simp [keys]
        · rfl
    · rfl

theorem searchA_false_of_grew (x : UInt64) (t : AvlTree) :
    (algorithmA x t).1 = true → searchA x t = false := by
  induction t with
  | leaf => intro _; rfl
  | node l k b r ihl ihr =>
    intro hg
    by_cases h : x < k
    · simp only [algorithmA, h, ↓reduceIte] at hg
      cases hl : (algorithmA x l).1
      · simp [hl] at hg
      · simp [searchA, h, ihl hl]
    · by_cases h' : k < x
      · simp only [algorithmA, h, h', ↓reduceIte] at hg
        cases hr : (algorithmA x r).1
        · simp [hr] at hg
        · simp [searchA, h, h', ihr hr]
      · simp [algorithmA, h, h'] at hg

theorem eq_of_not_lt {x k : UInt64} (h : ¬x < k) (h' : ¬k < x) : x = k :=
  UInt64.le_antisymm (UInt64.not_lt.mp h') (UInt64.not_lt.mp h)

theorem ordered_node {l r : AvlTree} {k b : UInt64} :
    Ordered (.node l k b r) ↔
      Ordered l ∧ Ordered r ∧ (∀ a ∈ keys l, a < k) ∧ (∀ c ∈ keys r, k < c) := by
  simp only [Ordered, keys, List.pairwise_append, List.pairwise_cons, List.mem_cons]
  constructor
  · rintro ⟨hl, ⟨hk, hr⟩, hlr⟩
    exact ⟨hl, hr, fun a ha => hlr a ha k (.inl rfl), hk⟩
  · rintro ⟨hl, hr, hlk, hkr⟩
    refine ⟨hl, ⟨hkr, hr⟩, fun a ha c hc => ?_⟩
    rcases hc with rfl | hc
    · exact hlk a ha
    · exact UInt64.lt_trans (hlk a ha) (hkr c hc)

theorem found_searchA (x : UInt64) (t : AvlTree) (ht : Ordered t) :
    searchA x t = true ↔ x ∈ keys t := by
  induction t with
  | leaf => simp [searchA, keys]
  | node l k b r ihl ihr =>
    obtain ⟨hl, hr, hlk, hkr⟩ := ordered_node.mp ht
    by_cases h : x < k
    · simp only [searchA, h, ↓reduceIte, ihl hl, keys, List.mem_append, List.mem_cons]
      constructor
      · exact .inl
      · rintro (hx | rfl | hx)
        · exact hx
        · exact absurd h (UInt64.lt_irrefl _)
        · exact absurd (UInt64.lt_trans h (hkr x hx)) (UInt64.lt_irrefl _)
    · by_cases h' : k < x
      · simp only [searchA, h, h', ↓reduceIte, ihr hr, keys, List.mem_append, List.mem_cons]
        constructor
        · exact fun hx => .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact absurd (UInt64.lt_trans h' (hlk x hx)) (UInt64.lt_irrefl _)
          · exact absurd h' (UInt64.lt_irrefl _)
          · exact hx
      · have := eq_of_not_lt h h'
        subst this
        simp [searchA, keys, h]

theorem keys_algorithmA (x : UInt64) (t : AvlTree) (ht : Ordered t) :
    keys (algorithmA x t).2 =
      if x ∈ keys t then keys t else (keys t).orderedInsert (· ≤ ·) x := by
  induction t with
  | leaf => simp [algorithmA, keys]
  | node l k b r ihl ihr =>
    obtain ⟨hl, hr, hlk, hkr⟩ := ordered_node.mp ht
    by_cases h : x < k
    · have hmem : x ∈ keys (.node l k b r) ↔ x ∈ keys l := by
        rw [← found_searchA x _ ht, ← found_searchA x l hl]
        simp [searchA, h]
      have hnode :
          keys (algorithmA x (.node l k b r)).2 = keys (algorithmA x l).2 ++ k :: keys r := by
        simp only [algorithmA, h, ↓reduceIte]
        split
        · exact keys_growLeft _ _ _ _
        · rfl
      rw [hnode, ihl hl]
      simp only [hmem]
      by_cases hx : x ∈ keys l
      · simp [hx, keys]
      · simp [hx, keys, orderedInsert_append_cons x k (UInt64.le_of_lt h)]
    · by_cases h' : k < x
      · have hmem : x ∈ keys (.node l k b r) ↔ x ∈ keys r := by
          rw [← found_searchA x _ ht, ← found_searchA x r hr]
          simp [searchA, h, h']
        have hnode :
            keys (algorithmA x (.node l k b r)).2 = keys l ++ k :: keys (algorithmA x r).2 := by
          simp only [algorithmA, h, h', ↓reduceIte]
          split
          · exact keys_growRight _ _ _ _
          · rfl
        have hlt : ∀ a ∈ keys l ++ [k], a < x := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact UInt64.lt_trans (hlk a ha) h'
          · rw [List.mem_singleton.mp ha]
            exact h'
        have hins := orderedInsert_append_of_lt x (keys l ++ [k]) (keys r) hlt
        simp only [List.append_assoc, List.singleton_append] at hins
        rw [hnode, ihr hr]
        simp only [hmem]
        by_cases hx : x ∈ keys r
        · simp [hx, keys]
        · simp [hx, keys, hins]
      · have := eq_of_not_lt h h'
        subst this
        simp [algorithmA, keys, h]

theorem ordered_orderedInsert (x : UInt64) :
    ∀ l : List UInt64, l.Pairwise (· < ·) → x ∉ l →
      (l.orderedInsert (· ≤ ·) x).Pairwise (· < ·)
  | [], _, _ => by simp
  | a :: l, hl, hx => by
    rw [List.pairwise_cons] at hl
    have hxa : x ≠ a := fun e => hx (e ▸ List.mem_cons_self)
    by_cases h : x ≤ a
    · have hlt : x < a := by
        have h1 := UInt64.le_iff_toNat_le.mp h
        have h2 : x.toNat ≠ a.toNat := fun e => hxa (UInt64.toNat_inj.mp e)
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
      simp only [List.orderedInsert_cons, h, ↓reduceIte, List.pairwise_cons, List.mem_cons]
      refine ⟨fun y hy => ?_, hl.1, hl.2⟩
      rcases hy with rfl | hy
      · exact hlt
      · exact UInt64.lt_trans hlt (hl.1 y hy)
    · simp only [List.orderedInsert_cons, h, ↓reduceIte, List.pairwise_cons]
      refine ⟨fun y hy => ?_, ordered_orderedInsert x l hl.2 (fun e => hx (.tail _ e))⟩
      rcases (List.mem_orderedInsert (· ≤ ·)).mp hy with rfl | hy
      · exact UInt64.not_le.mp h
      · exact hl.1 y hy

/-- Algorithm A on a balanced binary search tree meets the guarantees of `SearchTree`. -/
theorem searchTree (x : UInt64) (t : AvlTree) (ho : Ordered t) (hb : Balanced t) :
    SearchTree x t := by
  have hkeys := keys_algorithmA x t ho
  have hprops := algorithmA_props x t hb
  refine ⟨found_searchA x t ho, ?_, hprops.1, hkeys, hprops.2.1, fun hg hx => ?_⟩
  · unfold Ordered
    rw [hkeys]
    split
    · exact ho
    · exact ordered_orderedInsert x _ ho (by assumption)
  · have h1 := (found_searchA x t ho).mpr hx
    rw [searchA_false_of_grew x t hg] at h1
    exact absurd h1 (by simp)

end Library.Trees.Avl
