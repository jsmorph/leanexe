import Demos.OrderBook.RefineChains

/-! The read-only helpers of [the program](Program.lean) against the chains and `toSpec`.
`findSlot` finds the slot of an order id, `freeSlot` a free slot, `predecessor` the slot before a
slot in its chain, `bestPrice` the first nonempty level of a side, `levelQty` the total quantity
of a chain, and `crosses` the post-only test.  Each `repeatWhile` gets its invariant and a measure
that its fuel bounds. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

/-! ## Words -/

/-- A word below 4,097 plus 1 is its number plus 1. -/
theorem toNat_add_one {s : UInt64} (h : s.toNat < 4097) : (s + 1).toNat = s.toNat + 1 := by
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

/-- A positive word minus 1 is its number minus 1. -/
theorem toNat_sub_one {s : UInt64} (h : 1 ≤ s.toNat) : (s - 1).toNat = s.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simpa using h))]
  simp

/-- The number of a level word of a side word of at most 1 and a price below 1,024. -/
theorem toNat_level {k p : UInt64} (hk : k ≤ 1) (hp : p.toNat < 1024) :
    (Program.level k p).toNat = k.toNat * 1024 + p.toNat := by
  have hk' : k.toNat ≤ 1 := UInt64.le_iff_toNat_le.1 hk
  simp only [Program.level, UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega : k.toNat * 1024 < 2 ^ 64)]
  omega

/-- The number of a word from a number below 2^64. -/
theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using h)

/-! ## `findSlot` -/

/-- `findSlot` gives 0 when no slot from 1 to 4,096 holds the id or the id is 0, and otherwise a
slot from 1 to 4,096 that holds it. -/
theorem findSlot_spec (oid : Array UInt64) (id : UInt64) :
    (Program.findSlot oid id = 0 →
        id = 0 ∨ ∀ t, 1 ≤ t → t ≤ 4096 → oid[t]! ≠ id) ∧
      (Program.findSlot oid id ≠ 0 → 1 ≤ (Program.findSlot oid id).toNat ∧
        (Program.findSlot oid id).toNat ≤ 4096 ∧
        oid[(Program.findSlot oid id).toNat]! = id) := by
  unfold Program.findSlot
  by_cases h0 : id = 0
  · simp [h0]
  · simp only [h0, beq_iff_eq, ite_false]
    have := repeatWhile_inv (fuel := Program.slotFuel) (init := (1 : UInt64))
      (cond := fun s => decide (s ≤ Program.slots) && oid[s.toNat]! != id)
      (step := fun s => s + 1)
      (fun s => 1 ≤ s.toNat ∧ s.toNat ≤ 4097 ∧
        ∀ t, 1 ≤ t → t < s.toNat → oid[t]! ≠ id)
      (fun s => 4097 - s.toNat) ⟨by decide, by decide, fun t h1 h2 => by simp at h2; omega⟩
      (by simp [Program.slotFuel])
      (by
        intro s ⟨h1, h2, h3⟩ hc
        simp only [Program.slots, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        have hs : s.toNat ≤ 4096 := by
          have := UInt64.le_iff_toNat_le.1 (of_decide_eq_true hc.1)
          simpa using this
        rw [toNat_add_one (by omega)]
        refine ⟨⟨by omega, by omega, fun t ht1 ht2 => ?_⟩, by omega⟩
        by_cases he : t = s.toNat
        · subst he
          exact hc.2
        · exact h3 t ht1 (by omega))
    generalize LeanExe.repeatWhile Program.slotFuel 1
      (fun s => decide (s ≤ Program.slots) && oid[s.toNat]! != id) (fun s => s + 1) = r at this
    obtain ⟨⟨h1, h2, h3⟩, hc⟩ := this
    by_cases hr : r.toNat ≤ 4096
    · have hr' : r ≤ Program.slots := by
        simp only [Program.slots]
        exact UInt64.le_iff_toNat_le.2 (by simpa using hr)
      have hz : r ≠ 0 := fun he => by rw [he] at h1; simp at h1
      have hid : oid[r.toNat]! = id := by simp [hr'] at hc; exact hc
      simp only [hr', ite_true, hz, ne_eq, not_false_eq_true, forall_const]
      exact ⟨fun h => h.elim, h1, hr, hid⟩
    · have hr' : ¬ r ≤ Program.slots := by
        simp only [Program.slots]
        exact fun h => hr (by simpa using UInt64.le_iff_toNat_le.1 h)
      simp only [hr', ite_false, ne_eq, not_true_eq_false, false_implies, and_true, forall_const]
      exact Or.inr fun t ht1 ht2 => h3 t ht1 (by omega)

/-! ## `freeSlot` -/

/-- `freeSlot` gives a free slot from 1 to 4,096 when one exists. -/
theorem freeSlot_spec {oid : Array UInt64} (hf : ∃ f, 1 ≤ f ∧ f ≤ 4096 ∧ oid[f]! = 0) :
    1 ≤ (Program.freeSlot oid).toNat ∧ (Program.freeSlot oid).toNat ≤ 4096 ∧
      oid[(Program.freeSlot oid).toNat]! = 0 := by
  obtain ⟨f, hf1, hf2, hf3⟩ := hf
  unfold Program.freeSlot
  have := repeatWhile_inv (fuel := Program.slotFuel) (init := (1 : UInt64))
    (cond := fun s => oid[s.toNat]! != 0) (step := fun s => s + 1)
    (fun s => 1 ≤ s.toNat ∧ s.toNat ≤ f) (fun s => f - s.toNat)
    ⟨by decide, by simpa using hf1⟩
    (by simp [Program.slotFuel]; omega)
    (by
      intro s ⟨h1, h2⟩ hc
      simp only [bne_iff_ne, ne_eq] at hc
      have hne : s.toNat ≠ f := fun he => hc (he ▸ hf3)
      rw [toNat_add_one (by omega)]
      exact ⟨⟨by omega, by omega⟩, by omega⟩)
  obtain ⟨⟨h1, h2⟩, hc⟩ := this
  simp only [bne_eq_false_iff_eq] at hc
  exact ⟨h1, by omega, hc⟩

/-! ## `predecessor` -/

/-- The walk of `predecessor` from the first slot of a path to `s` stops at the path's last
slot. -/
theorem predecessor_go {nxt : Array UInt64} {s : UInt64} (A' : List UInt64) (a : UInt64)
    (fuel : Nat) (t : UInt64) (hP : Path nxt t (A' ++ [a]) s) (hs : s ∉ A' ++ [a])
    (hf : A'.length < fuel) :
    LeanExe.repeatWhile.go (fun t : UInt64 => t != 0 && nxt[t.toNat]! != s)
      (fun t => nxt[t.toNat]!) fuel t = a := by
  induction A' generalizing t fuel with
  | nil =>
    obtain ⟨rfl, ha, hn⟩ := hP
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [LeanExe.repeatWhile.go]
    simp [show nxt[t.toNat]! = s from hn]
  | cons x A' ih =>
    obtain ⟨rfl, hx, hP'⟩ := hP
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hne : nxt[t.toNat]! ≠ s := by
      intro he
      cases A' with
      | nil =>
        obtain ⟨h1, -, -⟩ := hP'
        exact hs (by simp [← he, h1])
      | cons y A'' =>
        obtain ⟨h1, -, -⟩ := hP'
        exact hs (by simp [← he, h1])
    have hc : (t != 0 && nxt[t.toNat]! != s) = true := by simp [hx, hne]
    simp only [LeanExe.repeatWhile.go, hc, ↓reduceIte]
    exact ih k _ hP' (fun h => hs (List.mem_cons_of_mem _ h)) (by simp at hf; omega)

/-- The slot that a path starts from is its first slot. -/
theorem path_mem_head {nxt : Array UInt64} {t e : UInt64} {L : List UInt64} (h : Path nxt t L e)
    (hL : L ≠ []) : t ∈ L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x L => exact h.1 ▸ List.mem_cons_self

/-- `predecessor` gives 0 for the first slot of a chain and otherwise the slot before it. -/
theorem predecessor_spec {b : Book} (h : Shape b) {lv s : UInt64} {A B : List UInt64}
    (hl : BandLevel lv.toNat) (hL : levelSlots b lv.toNat = A ++ s :: B) :
    (Program.predecessor b.head b.nxt lv s = 0 ∧ A = []) ∨
      ∃ A', A = A' ++ [Program.predecessor b.head b.nxt lv s] := by
  have hP := h.path hl
  have hn := h.chainNodup _ hl
  have hlen := h.length_le hl
  rw [hL] at hP hn hlen
  unfold Program.predecessor
  rcases List.eq_nil_or_concat A with rfl | ⟨A', a, rfl⟩
  · left
    have : b.head[lv.toNat]! = s := hP.1
    simp [this]
  · right
    rw [List.concat_eq_append] at hP hn hlen ⊢
    have hsA : s ∉ A' ++ [a] := by
      rw [List.nodup_append] at hn
      exact fun hs => hn.2.2 s hs s (by simp) rfl
    obtain ⟨m, hPA, hm⟩ := path_append.1 hP
    obtain ⟨rfl, -, -⟩ := hm
    have hhs : b.head[lv.toNat]! ≠ m := fun he =>
      hsA (he ▸ path_mem_head hPA (by simp))
    refine ⟨A', ?_⟩
    simp only [beq_iff_eq, hhs, ite_false]
    unfold LeanExe.repeatWhile
    rw [predecessor_go A' a _ _ hPA hsA (by simp [Program.chainFuel] at hlen ⊢; omega)]

/-! ## `bestPrice` -/

/-- The scan of the bid levels from price `n` down stops at the first nonempty level, or at 0. -/
theorem bestPrice_go_bid (b : Book) (n : Nat) (hn : n ≤ 1023) :
    (LeanExe.repeatWhile.go
        (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1) n
        (UInt64.ofNat n) = 0 ∧ (fromLevels 0 n).flatMap (ordersAt b) = []) ∨
      (1 ≤ (LeanExe.repeatWhile.go
        (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1) n
        (UInt64.ofNat n)).toNat ∧
      (LeanExe.repeatWhile.go
        (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1) n
        (UInt64.ofNat n)).toNat ≤ n ∧
      (fromLevels 0 n).flatMap (ordersAt b) =
        ordersAt b (LeanExe.repeatWhile.go
          (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1) n
          (UInt64.ofNat n)).toNat ++
        (fromLevels 0 ((LeanExe.repeatWhile.go
          (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1) n
          (UInt64.ofNat n)).toNat - 1)).flatMap (ordersAt b) ∧
      ordersAt b (LeanExe.repeatWhile.go
        (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1) n
        (UInt64.ofNat n)).toNat ≠ []) := by
  induction n with
  | zero =>
    left
    simp [LeanExe.repeatWhile.go, fromLevels]
  | succ n ih =>
    have hn' : (UInt64.ofNat (n + 1)).toNat = n + 1 := toNat_ofNat (by omega)
    have hlv : (Program.level 0 (UInt64.ofNat (n + 1))).toNat = n + 1 := by
      rw [toNat_level (by decide) (by omega), hn']
      simp
    have hz : UInt64.ofNat (n + 1) ≠ 0 := fun he => by rw [he] at hn'; simp at hn'
    have hsub : UInt64.ofNat (n + 1) - 1 = UInt64.ofNat n :=
      UInt64.toNat_inj.1 (by rw [toNat_sub_one (by omega), hn', toNat_ofNat (by omega)]; rfl)
    have hfrom : fromLevels 0 (n + 1) = (n + 1) :: fromLevels 0 n := by
      rw [fromLevels_cons (by decide) (by omega)]
      simp [nextPrice]
    rw [hfrom, List.flatMap_cons]
    by_cases hh : b.head[n + 1]! = 0
    · have hc : (UInt64.ofNat (n + 1) != 0 &&
          b.head[(Program.level 0 (UInt64.ofNat (n + 1))).toNat]! == 0) = true := by
        rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, hlv]
        exact ⟨hz, hh⟩
      have he : ordersAt b (n + 1) = [] := by
        unfold ordersAt
        rw [levelSlots_eq_nil.2 hh]
        rfl
      simp only [LeanExe.repeatWhile.go, hc, ↓reduceIte, hsub, he, List.nil_append]
      rcases ih (by omega) with h0 | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h1, by omega, h3, h4⟩
    · have hc : (UInt64.ofNat (n + 1) != 0 &&
          b.head[(Program.level 0 (UInt64.ofNat (n + 1))).toNat]! == 0) = false := by
        rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, hlv]
        exact Or.inr hh
      have he : ordersAt b (n + 1) ≠ [] := by
        unfold ordersAt
        rw [Ne, List.map_eq_nil_iff, levelSlots_eq_nil]
        exact hh
      simp only [LeanExe.repeatWhile.go, hc, Bool.false_eq_true, ↓reduceIte, hn']
      exact Or.inr ⟨by omega, Nat.le_refl _, by simp, he⟩

/-- The scan of the ask levels from price `1024 - n` up stops at the first nonempty level, or
at 1,024. -/
theorem bestPrice_go_ask (b : Book) (n : Nat) (hn : n ≤ 1023) :
    ((LeanExe.repeatWhile.go
        (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
          b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) n
        (UInt64.ofNat (1024 - n))).toNat = 1024 ∧
        (fromLevels 1 (1024 - n)).flatMap (ordersAt b) = []) ∨
      (1024 - n ≤ (LeanExe.repeatWhile.go
        (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
          b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) n
        (UInt64.ofNat (1024 - n))).toNat ∧
      (LeanExe.repeatWhile.go
        (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
          b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) n
        (UInt64.ofNat (1024 - n))).toNat ≤ 1023 ∧
      (fromLevels 1 (1024 - n)).flatMap (ordersAt b) =
        ordersAt b (1024 + (LeanExe.repeatWhile.go
          (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
            b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) n
          (UInt64.ofNat (1024 - n))).toNat) ++
        (fromLevels 1 ((LeanExe.repeatWhile.go
          (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
            b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) n
          (UInt64.ofNat (1024 - n))).toNat + 1)).flatMap (ordersAt b) ∧
      ordersAt b (1024 + (LeanExe.repeatWhile.go
        (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
          b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) n
        (UInt64.ofNat (1024 - n))).toNat) ≠ []) := by
  induction n with
  | zero =>
    left
    simp [LeanExe.repeatWhile.go, fromLevels]
  | succ n ih =>
    have hp : (UInt64.ofNat (1024 - (n + 1))).toNat = 1023 - n := by
      rw [toNat_ofNat (by omega)]
      omega
    have hlv : (Program.level 1 (UInt64.ofNat (1024 - (n + 1)))).toNat = 1024 + (1023 - n) := by
      rw [toNat_level (by decide) (by omega), hp]
      simp
    have hle : UInt64.ofNat (1024 - (n + 1)) ≤ Program.maxPrice := by
      rw [UInt64.le_iff_toNat_le, hp]
      simp [Program.maxPrice]
    have hadd : UInt64.ofNat (1024 - (n + 1)) + 1 = UInt64.ofNat (1024 - n) :=
      UInt64.toNat_inj.1 (by rw [toNat_add_one (by omega), hp, toNat_ofNat (by omega)]; omega)
    have hfrom : fromLevels 1 (1024 - (n + 1)) =
        (1024 + (1023 - n)) :: fromLevels 1 (1024 - n) := by
      rw [fromLevels_cons (by decide) (by omega)]
      simp only [nextPrice, show ¬ (1 : UInt64) = 0 by decide, ite_false, UInt64.reduceToNat]
      congr 2
      · omega
      · omega
    rw [hfrom, List.flatMap_cons]
    by_cases hh : b.head[1024 + (1023 - n)]! = 0
    · have hc : (decide (UInt64.ofNat (1024 - (n + 1)) ≤ Program.maxPrice) &&
          b.head[(Program.level 1 (UInt64.ofNat (1024 - (n + 1)))).toNat]! == 0) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hlv]
        exact ⟨hle, hh⟩
      have he : ordersAt b (1024 + (1023 - n)) = [] := by
        unfold ordersAt
        rw [levelSlots_eq_nil.2 hh]
        rfl
      simp only [LeanExe.repeatWhile.go, hc, ↓reduceIte, hadd, he, List.nil_append]
      rcases ih (by omega) with h0 | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, h2, h3, h4⟩
    · have hc : (decide (UInt64.ofNat (1024 - (n + 1)) ≤ Program.maxPrice) &&
          b.head[(Program.level 1 (UInt64.ofNat (1024 - (n + 1)))).toNat]! == 0) = false := by
        rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, hlv]
        exact Or.inr hh
      have he : ordersAt b (1024 + (1023 - n)) ≠ [] := by
        unfold ordersAt
        rw [Ne, List.map_eq_nil_iff, levelSlots_eq_nil]
        exact hh
      simp only [LeanExe.repeatWhile.go, hc, Bool.false_eq_true, ↓reduceIte, hp]
      refine Or.inr ⟨by omega, by omega, ?_, he⟩
      rw [show 1023 - n + 1 = 1024 - n by omega]

/-- `bestPrice` of a side finds the side's first nonempty level, and gives 0 for an empty side. -/
theorem bestPrice_spec (b : Book) {k : UInt64} (hk : k ≤ 1) :
    (Program.bestPrice b.head k = 0 ∧ (levelsOf k).flatMap (ordersAt b) = []) ∨
      (1 ≤ (Program.bestPrice b.head k).toNat ∧ (Program.bestPrice b.head k).toNat ≤ 1023 ∧
        (levelsOf k).flatMap (ordersAt b) =
          ordersAt b (k.toNat * 1024 + (Program.bestPrice b.head k).toNat) ++
            (fromLevels k (nextPrice k (Program.bestPrice b.head k).toNat)).flatMap
              (ordersAt b) ∧
        ordersAt b (k.toNat * 1024 + (Program.bestPrice b.head k).toNat) ≠ []) := by
  by_cases h0 : k = 0
  · subst h0
    have e : Program.bestPrice b.head 0 = LeanExe.repeatWhile.go
        (fun p : UInt64 => p != 0 && b.head[(Program.level 0 p).toNat]! == 0) (fun p => p - 1)
        1023 (UInt64.ofNat 1023) := by
      simp only [Program.bestPrice, beq_self_eq_true, ↓reduceIte, LeanExe.repeatWhile]
      rw [show Program.bandFuel.toNat = 1023 from rfl,
        show Program.maxPrice = UInt64.ofNat 1023 from rfl]
    have hL : levelsOf 0 = fromLevels 0 1023 := by
      rw [levelsOf_eq (k := 0) (p := 1023) (by simp)]
      have : aboveLevels 0 1023 = [] := by simp [aboveLevels]
      rw [this, List.nil_append]
    rw [e, hL]
    rcases bestPrice_go_bid b 1023 (Nat.le_refl _) with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, ?_, by simpa using h4⟩
      simpa [nextPrice] using h3
  · have h1 : k = 1 := UInt64.toNat_inj.1 (by rw [side_one hk h0]; rfl)
    subst h1
    have e : Program.bestPrice b.head 1 =
        let p := LeanExe.repeatWhile.go
          (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
            b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) 1023
          (UInt64.ofNat (1024 - 1023))
        if p ≤ Program.maxPrice then p else 0 := by
      simp only [Program.bestPrice, show ((1 : UInt64) == 0) = false from rfl,
        Bool.false_eq_true, ↓reduceIte, LeanExe.repeatWhile]
      have e1 : Program.bandFuel.toNat = 1023 := rfl
      have e2 : (1 : UInt64) = UInt64.ofNat (1024 - 1023) := rfl
      simp only [e1]
      rw [← e2]
    have hL : levelsOf 1 = fromLevels 1 (1024 - 1023) := by
      rw [levelsOf_eq (k := 1) (p := 1) (by simp)]
      have : aboveLevels 1 1 = [] := by simp [aboveLevels]
      rw [this, List.nil_append]
    rw [e, hL]
    rcases bestPrice_go_ask b 1023 (Nat.le_refl _) with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · left
      have : ¬ LeanExe.repeatWhile.go
          (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
            b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) 1023
          (UInt64.ofNat (1024 - 1023)) ≤ Program.maxPrice := by
        rw [UInt64.le_iff_toNat_le, h1, show Program.maxPrice.toNat = 1023 from rfl]
        decide
      simp only [this, ite_false]
      exact ⟨by trivial, h2⟩
    · right
      have : LeanExe.repeatWhile.go
          (fun p : UInt64 => decide (p ≤ Program.maxPrice) &&
            b.head[(Program.level 1 p).toNat]! == 0) (fun p => p + 1) 1023
          (UInt64.ofNat (1024 - 1023)) ≤ Program.maxPrice := by
        rw [UInt64.le_iff_toNat_le, show Program.maxPrice.toNat = 1023 from rfl]
        exact h2
      simp only [this, ite_true]
      refine ⟨by omega, h2, ?_, by simpa using h4⟩
      simpa [nextPrice] using h3

/-- The side of word 0 is the bids. -/
theorem sideList_zero (B : Spec.Book) : sideList B 0 = B.bids := by simp [sideList]

/-- The side of word 1 is the asks. -/
theorem sideList_one (B : Spec.Book) : sideList B 1 = B.asks := by simp [sideList]

/-- An order of a level has the level's price. -/
theorem price_of_mem_ordersAt {b : Book} {l : Nat} {o : Spec.Order} (h : o ∈ ordersAt b l) :
    o.price = levelPrice l := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
  rfl

/-- The best price of a side of `toSpec` is the number of `bestPrice`. -/
theorem bestPrice_toSpec (b : Book) {k : UInt64} (hk : k ≤ 1) :
    (Program.bestPrice b.head k).toNat = Spec.bestPrice (sideList (toSpec b) k) := by
  rw [toSpec_eq, sideList_ofLevels]
  rcases bestPrice_spec b hk with ⟨h0, h1⟩ | ⟨h1, h2, h3, h4⟩
  · rw [h1, h0]
    rfl
  · rw [h3]
    obtain ⟨o, os, ho⟩ := List.exists_cons_of_ne_nil h4
    rw [ho, List.cons_append]
    have := price_of_mem_ordersAt (ho ▸ List.mem_cons_self : o ∈ ordersAt b _)
    simp only [Spec.bestPrice, this,
      (levelSide_level hk (p := (Program.bestPrice b.head k).toNat) (by omega)).2]

/-- The total quantity at the best price of a side of `toSpec` is the total of the chain of the
level that `bestPrice` finds, and 0 for an empty side. -/
theorem bestQty_toSpec (b : Book) {k : UInt64} (hk : k ≤ 1) :
    Spec.bestQty (sideList (toSpec b) k) =
      if Program.bestPrice b.head k = 0 then 0
      else ((levelSlots b (k.toNat * 1024 + (Program.bestPrice b.head k).toNat)).map
        (fun t => b.qty[t.toNat]!.toNat)).sum := by
  have hbp := bestPrice_toSpec b hk
  rw [toSpec_eq, sideList_ofLevels] at hbp ⊢
  rcases bestPrice_spec b hk with ⟨h0, h1⟩ | ⟨h1, h2, h3, h4⟩
  · simp only [h1, h0, ↓reduceIte]
    rfl
  · have hne : Program.bestPrice b.head k ≠ 0 := fun he => by rw [he] at h1; simp at h1
    simp only [hne, ↓reduceIte]
    unfold Spec.bestQty
    rw [← hbp, h3, List.filter_append]
    have hA : (ordersAt b (k.toNat * 1024 + (Program.bestPrice b.head k).toNat)).filter
        (·.price == (Program.bestPrice b.head k).toNat) =
        ordersAt b (k.toNat * 1024 + (Program.bestPrice b.head k).toNat) := by
      rw [List.filter_eq_self]
      intro o ho
      rw [price_of_mem_ordersAt ho,
        (levelSide_level hk (p := (Program.bestPrice b.head k).toNat) (by omega)).2]
      simp
    have hB : ((fromLevels k (nextPrice k (Program.bestPrice b.head k).toNat)).flatMap
        (ordersAt b)).filter (·.price == (Program.bestPrice b.head k).toNat) = [] := by
      rw [List.filter_eq_nil_iff]
      intro o ho
      obtain ⟨l, hl, hol⟩ := List.mem_flatMap.1 ho
      rw [price_of_mem_ordersAt hol]
      have hl' := mem_fromLevels.1 hl
      unfold nextPrice at hl'
      unfold levelPrice
      simp only [beq_iff_eq]
      by_cases h0 : k = 0
      · subst h0
        simp only [ite_true] at hl'
        omega
      · simp only [h0, ite_false] at hl'
        omega
    rw [hA, hB, List.append_nil]
    unfold ordersAt
    rw [List.map_map]
    rfl

/-! ## `levelQty` -/

/-- The walk of `levelQty` along a path that ends at 0 adds the path's quantities. -/
theorem levelQty_go {nxt qty : Array UInt64} {L : List UInt64} :
    ∀ {t : UInt64} (fuel : Nat) (acc : UInt64), Path nxt t L 0 → L.length ≤ fuel →
      acc.toNat + (L.map (fun u => qty[u.toNat]!.toNat)).sum < 2 ^ 64 →
      (LeanExe.repeatWhile.go (fun st : UInt64 × UInt64 => st.1 != 0)
        (fun st => (nxt[st.1.toNat]!, st.2 + qty[st.1.toNat]!)) fuel (t, acc)).2.toNat =
        acc.toNat + (L.map (fun u => qty[u.toNat]!.toNat)).sum := by
  induction L with
  | nil =>
    intro t fuel acc hP _ _
    have : t = 0 := hP
    subst this
    cases fuel <;> simp [LeanExe.repeatWhile.go]
  | cons x L ih =>
    intro t fuel acc hP hf hb
    obtain ⟨rfl, hx, hP'⟩ := hP
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hc : ((t, acc).1 != 0) = true := by simp [hx]
    simp only [LeanExe.repeatWhile.go, hc, ↓reduceIte]
    simp only [List.map_cons, List.sum_cons] at hb ⊢
    have hadd : (acc + qty[t.toNat]!).toNat = acc.toNat + qty[t.toNat]!.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [ih k _ hP' (by simp at hf; omega) (by rw [hadd]; omega), hadd]
    omega

/-- A sum of a list's values, each at most `c`, is at most the list's length times `c`. -/
theorem sum_le_length_mul {α : Type} {L : List α} {f : α → Nat} {c : Nat}
    (h : ∀ x ∈ L, f x ≤ c) : (L.map f).sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    omega

/-- `levelQty` of a level of the band gives the total quantity of its chain. -/
theorem levelQty_spec {b : Book} (h : Inv b) {lv : UInt64} (hl : BandLevel lv.toNat) :
    (Program.levelQty b.head b.nxt b.qty lv).toNat =
      ((levelSlots b lv.toNat).map (fun t => b.qty[t.toNat]!.toNat)).sum := by
  have hs := h.shape
  have hlen := hs.length_le hl
  have hb : ((levelSlots b lv.toNat).map (fun t => b.qty[t.toNat]!.toNat)).sum ≤
      4096 * Spec.maxQty := by
    have := sum_le_length_mul (c := Spec.maxQty) (L := levelSlots b lv.toNat)
      (f := fun t => b.qty[t.toNat]!.toNat) (fun t ht => (h.qty_mem hl ht).2)
    exact Nat.le_trans this (Nat.mul_le_mul_right _ hlen)
  unfold Program.levelQty LeanExe.repeatWhile
  rw [levelQty_go _ 0 (hs.path hl) (by simp [Program.chainFuel]; exact hlen)
    (by simp [Spec.maxQty] at hb ⊢; omega)]
  simp

/-! ## `crosses` -/

/-- The opposite side of an incoming order of side word `side` is the side of word `1 - side`. -/
theorem opposite_toSide (B : Spec.Book) {side : UInt64} (hs : side ≤ 1) :
    Spec.opposite B (toSide side) = sideList B (1 - side) := by
  by_cases h0 : side = 0
  · subst h0
    simp [toSide, sideList, Spec.opposite]
  · have h1 : side = 1 := UInt64.toNat_inj.1 (by rw [side_one hs h0]; rfl)
    subst h1
    simp [toSide, sideList, Spec.opposite]

/-- The word `1 - side` of a side word of at most 1 is a side word. -/
theorem one_sub_le {side : UInt64} (hs : side ≤ 1) : 1 - side ≤ 1 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hs]
  simp

/-- `acceptable` on words is the specification's `acceptable` on their numbers. -/
theorem acceptable_eq (side limit price : UInt64) :
    Program.acceptable side limit price =
      Spec.acceptable (toSide side) limit.toNat price.toNat := by
  unfold Program.acceptable Spec.acceptable toSide
  by_cases h0 : side = 0
  · simp [h0, UInt64.le_iff_toNat_le]
  · simp [h0, UInt64.le_iff_toNat_le]

/-- The post-only test of the program is the specification's `crosses`. -/
theorem crosses_spec (b : Book) {side price : UInt64} (hs : side ≤ 1) :
    Program.crosses b.head side price = Spec.crosses (toSpec b) (toSide side) price.toNat := by
  have hk := one_sub_le hs
  have hbp := bestPrice_toSpec b hk
  simp only [Program.crosses, Spec.crosses]
  rw [opposite_toSide _ hs, acceptable_eq]
  rw [toSpec_eq, sideList_ofLevels] at hbp ⊢
  rcases bestPrice_spec b hk with ⟨h0, h1⟩ | ⟨h1, h2, h3, h4⟩
  · rw [h1, h0]
    rfl
  · rw [h3]
    obtain ⟨o, os, ho⟩ := List.exists_cons_of_ne_nil h4
    rw [ho, List.cons_append]
    have hp := price_of_mem_ordersAt (ho ▸ List.mem_cons_self : o ∈ ordersAt b _)
    rw [(levelSide_level hk (by omega)).2] at hp
    have hne : Program.bestPrice b.head (1 - side) ≠ 0 := fun he => by rw [he] at h1; simp at h1
    simp [hne, hp]

/-- `top` gives the specification's top of the book. -/
theorem top_spec {b : Book} (h : Inv b) :
    ((Program.top b).1.toNat, (Program.top b).2.1.toNat, (Program.top b).2.2.1.toNat,
      (Program.top b).2.2.2.toNat) = Spec.top (toSpec b) := by
  have hq : ∀ k : UInt64, k ≤ 1 →
      (if Program.bestPrice b.head k == 0 then 0
        else Program.levelQty b.head b.nxt b.qty (Program.level k (Program.bestPrice b.head k))
          ).toNat = Spec.bestQty (sideList (toSpec b) k) := by
    intro k hk
    rw [bestQty_toSpec b hk]
    by_cases h0 : Program.bestPrice b.head k = 0
    · simp [h0]
    · have hr := bestPrice_spec b hk
      have hle : (Program.bestPrice b.head k).toNat ≤ 1023 := by
        rcases hr with ⟨h1, -⟩ | ⟨-, h2, -⟩
        · exact absurd h1 h0
        · exact h2
      have hge : 1 ≤ (Program.bestPrice b.head k).toNat := by
        rcases hr with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 h0
        · exact h1
      have hlv := toNat_level hk (p := Program.bestPrice b.head k) (by omega)
      have hband : BandLevel (Program.level k (Program.bestPrice b.head k)).toNat := by
        rw [hlv]
        have := UInt64.le_iff_toNat_le.1 hk
        simp at this
        constructor <;> omega
      simp only [beq_iff_eq, h0, ite_false]
      rw [levelQty_spec h hband, hlv]
  have h0 := bestPrice_toSpec b (k := 0) (by decide)
  have h1 := bestPrice_toSpec b (k := 1) (by decide)
  have q0 := hq 0 (by decide)
  have q1 := hq 1 (by decide)
  rw [sideList_zero] at h0 q0
  rw [sideList_one] at h1 q1
  simp only [Program.top, Spec.top, Prod.mk.injEq]
  exact ⟨h0, q0, h1, q1⟩

end Demos.OrderBook.Refinement
