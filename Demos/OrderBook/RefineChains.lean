import Demos.OrderBook.Invariant

/-! Chains of slots and the level structure of `toSpec`, for the refinement of
[the specification](Spec.lean) by [the program](Program.lean).  `Path nxt s L e` states without
fuel that `L` is the chain from slot `s` along the links `nxt` and that its last link goes to `e`.
Under the structural part of the invariant, `Shape`, each level's chain is such a path that ends
at 0, so the fuel of `slotsFrom` never runs out.  The book `toSpec b` is the concatenation of the
levels' order lists `ordersAt b l` over the bid levels and the ask levels. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

/-! ## `repeatWhile` -/

/-- A property that each step keeps while the condition holds, under a measure that each such step
lowers and that starts at most at the fuel, holds where `repeatWhile` stops, and the condition
fails there. -/
theorem repeatWhile_inv {α : Type} {fuel : UInt64} {init : α} {cond : α → Bool}
    {step : α → α}
    (P : α → Prop) (μ : α → Nat) (h0 : P init) (hμ : μ init ≤ fuel.toNat)
    (hs : ∀ s, P s → cond s = true → P (step s) ∧ μ (step s) < μ s) :
    P (LeanExe.repeatWhile fuel init cond step) ∧
      cond (LeanExe.repeatWhile fuel init cond step) = false := by
  unfold LeanExe.repeatWhile
  suffices h : ∀ k s, P s → μ s ≤ k → P (LeanExe.repeatWhile.go cond step k s) ∧
      cond (LeanExe.repeatWhile.go cond step k s) = false from h _ _ h0 hμ
  intro k
  induction k with
  | zero =>
    intro s hP hk
    refine ⟨hP, ?_⟩
    simp only [LeanExe.repeatWhile.go]
    cases hc : cond s
    · rfl
    · have := (hs s hP hc).2
      omega
  | succ k ih =>
    intro s hP hk
    simp only [LeanExe.repeatWhile.go]
    cases hc : cond s
    · exact ⟨hP, hc⟩
    · have := hs s hP hc
      simpa using ih _ this.1 (by omega)

/-! ## Arrays -/

/-- An update of an array at an index leaves every other index. -/
theorem get_set_ne {a : Array UInt64} {i j : Nat} {v : UInt64} (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! :=
  Array.getElem!_set!_ne a i j v h

/-- An update of an array at an index inside it gives the new value there. -/
theorem get_set_eq {a : Array UInt64} {i : Nat} {v : UInt64} (h : i < a.size) :
    (a.set! i v)[i]! = v :=
  Array.getElem!_set!_self a i v h

/-- Two words with different numbers differ. -/
theorem toNat_ne {s t : UInt64} (h : s ≠ t) : s.toNat ≠ t.toNat :=
  fun he => h (UInt64.toNat_inj.1 he)

/-! ## Paths -/

/-- The list `L` is the chain from slot `s` along the links `nxt`, whose last link goes to `e`. -/
def Path (nxt : Array UInt64) : UInt64 → List UInt64 → UInt64 → Prop
  | s, [], e => s = e
  | s, x :: L, e => s = x ∧ x ≠ 0 ∧ Path nxt nxt[x.toNat]! L e

/-- A path through two lists is a path through the first to some slot and a path from it through
the second. -/
theorem path_append {nxt : Array UInt64} {s e : UInt64} {L₁ L₂ : List UInt64} :
    Path nxt s (L₁ ++ L₂) e ↔ ∃ m, Path nxt s L₁ m ∧ Path nxt m L₂ e := by
  induction L₁ generalizing s with
  | nil => simp [Path]
  | cons x L ih =>
    simp only [List.cons_append, Path, ih]
    constructor
    · rintro ⟨h1, h2, m, h3, h4⟩
      exact ⟨m, ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨m, ⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, m, h3, h4⟩

/-- A path stays a path under links that agree with the old ones on its slots. -/
theorem path_congr {nxt nxt' : Array UInt64} {s e : UInt64} {L : List UInt64}
    (h : Path nxt s L e) (hn : ∀ t ∈ L, nxt'[t.toNat]! = nxt[t.toNat]!) : Path nxt' s L e := by
  induction L generalizing s with
  | nil => exact h
  | cons x L ih =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    rw [hn x (by simp)]
    exact ih h3 (fun t ht => hn t (by simp [ht]))

/-- The slots of a path that ends at 0 are not 0. -/
theorem path_ne_zero {nxt : Array UInt64} {s : UInt64} {L : List UInt64}
    (h : Path nxt s L 0) : ∀ t ∈ L, t ≠ 0 := by
  induction L generalizing s with
  | nil => simp
  | cons x L ih =>
    obtain ⟨-, h2, h3⟩ := h
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h2
    · exact ih h3 t ht

/-- A chain read with fuel to spare is a path that ends at 0. -/
theorem path_slotsFrom (b : Book) (fuel : Nat) (s : UInt64)
    (h : (slotsFrom b fuel s).length < fuel) : Path b.nxt s (slotsFrom b fuel s) 0 := by
  induction fuel generalizing s with
  | zero => simp at h
  | succ k ih =>
    simp only [slotsFrom] at h ⊢
    split
    · simp_all [Path]
    · rename_i hs
      simp only [hs, ite_false, List.length_cons] at h
      exact ⟨rfl, hs, ih _ (by omega)⟩

/-- A path that ends at 0 and is shorter than the fuel is the chain that `slotsFrom` reads. -/
theorem slotsFrom_of_path {b : Book} {fuel : Nat} {s : UInt64} {L : List UInt64}
    (h : Path b.nxt s L 0) (hl : L.length < fuel) : slotsFrom b fuel s = L := by
  induction L generalizing s fuel with
  | nil =>
    cases fuel with
    | zero => simp at hl
    | succ k => simp [slotsFrom, show s = 0 from h]
  | cons x L ih =>
    obtain ⟨h1, h2, h3⟩ := h
    subst h1
    cases fuel with
    | zero => simp at hl
    | succ k =>
      simp only [slotsFrom, h2, ite_false]
      rw [ih h3 (by simp at hl; omega)]

/-- A list of distinct slots from 1 to 4,096 has at most 4,096 slots. -/
theorem length_le_of_slots {L : List UInt64} (hn : L.Nodup)
    (hs : ∀ s ∈ L, 1 ≤ s.toNat ∧ s.toNat ≤ 4096) : L.length ≤ 4096 := by
  have hm : (L.map UInt64.toNat).Nodup := by
    exact List.Pairwise.map _ (fun a b h he => h (UInt64.toNat_inj.1 he)) hn
  have hsub : L.map UInt64.toNat ⊆ List.range' 1 4096 := by
    intro n hn'
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hn'
    have := hs s hs'
    rw [List.mem_range'_1]
    omega
  have := hm.length_le_of_subset hsub
  simpa using this

/-! ## The structure of the book -/

/-- The structural part of the invariant, with nonzero order ids on the chains: what the program's
effects keep on their own, apart from the count and the validity of the specification's book. -/
structure Shape (b : Book) : Prop where
  oidSize : b.oid.size = 4097
  acctSize : b.acct.size = 4097
  qtySize : b.qty.size = 4097
  lvlSize : b.lvl.size = 4097
  nxtSize : b.nxt.size = 4097
  headSize : b.head.size = 2048
  tailSize : b.tail.size = 2048
  chainNodup : ∀ l, BandLevel l → (levelSlots b l).Nodup
  chainSlots : ∀ l, BandLevel l → ∀ s ∈ levelSlots b l,
    1 ≤ s.toNat ∧ s.toNat ≤ 4096 ∧ b.lvl[s.toNat]!.toNat = l
  chainTail : ∀ l, BandLevel l → b.tail[l]! = (levelSlots b l).getLast?.getD 0
  used : ∀ s, 1 ≤ s → s ≤ 4096 → b.oid[s]! ≠ 0 →
    BandLevel b.lvl[s]!.toNat ∧ s.toUInt64 ∈ levelSlots b b.lvl[s]!.toNat
  oidPos : ∀ l, BandLevel l → ∀ s ∈ levelSlots b l, b.oid[s.toNat]! ≠ 0

/-- A level's chain has at most 4,096 slots. -/
theorem Shape.length_le {b : Book} (h : Shape b) {l : Nat} (hl : BandLevel l) :
    (levelSlots b l).length ≤ 4096 :=
  length_le_of_slots (h.chainNodup l hl) (fun s hs => ⟨(h.chainSlots l hl s hs).1,
    (h.chainSlots l hl s hs).2.1⟩)

/-- A level's chain is the path from the level's first slot that ends at 0. -/
theorem Shape.path {b : Book} (h : Shape b) {l : Nat} (hl : BandLevel l) :
    Path b.nxt b.head[l]! (levelSlots b l) 0 :=
  path_slotsFrom b 4097 _ (Nat.lt_succ_of_le (h.length_le hl))

/-- A path from a level's first slot that ends at 0, of at most 4,096 slots, is the level's
chain. -/
theorem levelSlots_of_path {b : Book} {l : Nat} {L : List UInt64}
    (h : Path b.nxt b.head[l]! L 0) (hl : L.length ≤ 4096) : levelSlots b l = L :=
  slotsFrom_of_path h (by omega)

/-- A level whose first slot is 0 has no slots. -/
theorem levelSlots_eq_nil {b : Book} {l : Nat} : levelSlots b l = [] ↔ b.head[l]! = 0 := by
  unfold levelSlots
  rw [slotsFrom.eq_2]
  split <;> simp_all

/-- The slots of a chain lie inside the slot arrays. -/
theorem Shape.lt_size {b : Book} (h : Shape b) {l : Nat} (hl : BandLevel l) {s : UInt64}
    (hs : s ∈ levelSlots b l) : s.toNat < 4097 := by
  have := h.chainSlots l hl s hs
  omega

/-- The chains of two levels share no slot. -/
theorem Shape.disjoint {b : Book} (h : Shape b) {l l' : Nat} (hl : BandLevel l)
    (hl' : BandLevel l') {s : UInt64} (hs : s ∈ levelSlots b l) (hs' : s ∈ levelSlots b l') :
    l = l' := by
  have h1 := (h.chainSlots l hl s hs).2.2
  have h2 := (h.chainSlots l' hl' s hs').2.2
  omega

/-! ## Levels -/

/-- The side of the orders of level `l`. -/
def levelSide (l : Nat) : Spec.Side := if l < 1024 then .buy else .sell

/-- The price of the orders of level `l`. -/
def levelPrice (l : Nat) : Nat := l % 1024

/-- The order in slot `s` of level `l`. -/
def orderAt (b : Book) (l : Nat) (s : UInt64) : Spec.Order :=
  ⟨b.oid[s.toNat]!, b.acct[s.toNat]!, levelSide l, levelPrice l, b.qty[s.toNat]!.toNat⟩

/-- The orders of level `l` in the order of its chain. -/
def ordersAt (b : Book) (l : Nat) : List Spec.Order := (levelSlots b l).map (orderAt b l)

/-- The bid levels, best first: levels 1,023 down to 1. -/
def bidLevels : List Nat := (List.range' 1 1023).reverse

/-- The ask levels, best first: levels 1,025 to 2,047. -/
def askLevels : List Nat := List.range' 1025 1023

/-- The specification's book whose levels hold the orders `F l` and whose next id is `n`. -/
def ofLevels (F : Nat → List Spec.Order) (n : UInt64) : Spec.Book :=
  ⟨bidLevels.flatMap F, askLevels.flatMap F, n⟩

/-- The slots of the chains of all levels of the band, bid levels first. -/
def allSlots (b : Book) : List UInt64 := (bidLevels ++ askLevels).flatMap (levelSlots b)

/-- The orders of a chain read with fuel are its slots' orders. -/
theorem chain_eq_map (b : Book) (side : Spec.Side) (price : Nat) (fuel : Nat) (s : UInt64) :
    chain b side price fuel s = (slotsFrom b fuel s).map
      (fun t => ⟨b.oid[t.toNat]!, b.acct[t.toNat]!, side, price, b.qty[t.toNat]!.toNat⟩) := by
  induction fuel generalizing s with
  | zero => simp [chain, slotsFrom]
  | succ k ih =>
    simp only [chain, slotsFrom]
    split <;> simp [ih]

/-- The numbers `n - i` for `i` below `n` are the numbers from `n` down to 1. -/
theorem range_map_sub (n : Nat) :
    (List.range n).map (fun i => n - i) = (List.range' 1 n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.range'_concat]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [← ih]
    congr 1
    · omega
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      omega

/-- Two functions that agree on a list's members give one concatenation. -/
theorem flatMap_congr {α β : Type} {f g : α → List β} {L : List α}
    (h : ∀ x ∈ L, f x = g x) :
    L.flatMap f = L.flatMap g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- A bid level lies from 1 to 1,023. -/
theorem mem_bidLevels {l : Nat} : l ∈ bidLevels ↔ 1 ≤ l ∧ l ≤ 1023 := by
  simp only [bidLevels, List.mem_reverse, List.mem_range'_1]
  omega

/-- An ask level lies from 1,025 to 2,047. -/
theorem mem_askLevels {l : Nat} : l ∈ askLevels ↔ 1025 ≤ l ∧ l ≤ 2047 := by
  simp only [askLevels, List.mem_range'_1]
  omega

/-- The levels of the band are the bid levels and the ask levels. -/
theorem bandLevel_iff {l : Nat} : BandLevel l ↔ l ∈ bidLevels ∨ l ∈ askLevels := by
  simp only [BandLevel, mem_bidLevels, mem_askLevels]
  omega

/-- The book that `toSpec` reads is the concatenation of the levels' orders. -/
theorem toSpec_eq (b : Book) : toSpec b = ofLevels (ordersAt b) b.nextId := by
  simp only [toSpec, ofLevels, Spec.Book.mk.injEq, and_true]
  constructor
  · rw [show bidLevels = (List.range 1023).map (fun i => 1023 - i) from (range_map_sub 1023).symm,
      List.flatMap_map]
    apply flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    have hl : 1 ≤ 1023 - i ∧ 1023 - i ≤ 1023 := by omega
    generalize 1023 - i = l at hl ⊢
    simp only [levelOrders, levelIndex, ordersAt, levelSlots, chain_eq_map]
    apply List.map_congr_left
    intro t _
    simp only [orderAt, levelSide, levelPrice, show l < 1024 by omega, ite_true,
      Nat.mod_eq_of_lt (show l < 1024 by omega)]
  · rw [askLevels, List.range'_eq_map_range, List.flatMap_map]
    apply flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    simp only [levelOrders, levelIndex, ordersAt, levelSlots, chain_eq_map,
      show 1024 + (i + 1) = 1025 + i by omega]
    apply List.map_congr_left
    intro t _
    simp only [orderAt, levelSide, levelPrice, show ¬ 1025 + i < 1024 by omega, ite_false,
      show (1025 + i) % 1024 = i + 1 by omega]

/-- The ids of the specification's book are the order ids of the slots of the chains. -/
theorem toSpec_ids (b : Book) :
    ((toSpec b).bids ++ (toSpec b).asks).map (·.id) =
      (allSlots b).map (fun t => b.oid[t.toNat]!) := by
  rw [toSpec_eq]
  simp only [ofLevels, allSlots, ← List.flatMap_append, List.map_flatMap, ordersAt, List.map_map]
  rfl

/-- The specification's book has one order for each slot of the chains. -/
theorem size_toSpec (b : Book) : Spec.size (toSpec b) = (allSlots b).length := by
  have := congrArg List.length (toSpec_ids b)
  simp only [List.length_map, List.length_append] at this
  exact this

/-- The slots of the chains are the slots of the chains of the levels of the band. -/
theorem mem_allSlots {b : Book} {t : UInt64} :
    t ∈ allSlots b ↔ ∃ l, BandLevel l ∧ t ∈ levelSlots b l := by
  simp only [allSlots, List.mem_flatMap, List.mem_append, bandLevel_iff]

/-- The order in a slot of a chain of the band belongs to the specification's book. -/
theorem mem_toSpec {b : Book} {l : Nat} (hl : BandLevel l) {t : UInt64}
    (ht : t ∈ levelSlots b l) : orderAt b l t ∈ (toSpec b).bids ++ (toSpec b).asks := by
  rw [toSpec_eq]
  simp only [ofLevels, ← List.flatMap_append, List.mem_flatMap, ordersAt, List.mem_map]
  exact ⟨l, List.mem_append.2 (bandLevel_iff.1 hl), t, ht, rfl⟩

/-- A function whose images of a list are distinct takes distinct values on its members. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} {L : List α} (h : (L.map f).Nodup)
    {x y : α} (hx : x ∈ L) (hy : y ∈ L) (he : f x = f y) : x = y := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with hxa | hxL <;> rcases List.mem_cons.1 hy with hya | hyL
    · exact hxa.trans hya.symm
    · subst hxa
      exact absurd (List.mem_map.2 ⟨y, hyL, he.symm⟩) h.1
    · subst hya
      exact absurd (List.mem_map.2 ⟨x, hxL, he⟩) h.1
    · exact ih h.2 hxL hyL

/-- The invariant gives the structural part, with nonzero ids on the chains from `Spec.Valid`. -/
theorem Inv.shape {b : Book} (h : Inv b) : Shape b where
  oidSize := h.oidSize
  acctSize := h.acctSize
  qtySize := h.qtySize
  lvlSize := h.lvlSize
  nxtSize := h.nxtSize
  headSize := h.headSize
  tailSize := h.tailSize
  chainNodup := h.chainNodup
  chainSlots := h.chainSlots
  chainTail := h.chainTail
  used := h.used
  oidPos l hl s hs := by
    have := (h.valid.ids _ (mem_toSpec hl hs)).1
    intro h0
    simp only [orderAt, h0] at this
    exact absurd this (by decide)

/-- The structural part, the count, and validity give the invariant. -/
theorem Inv.of_shape {b : Book} (h : Shape b) (hc : b.count.toNat = Spec.size (toSpec b))
    (hv : Spec.Valid (toSpec b)) : Inv b :=
  ⟨h.oidSize, h.acctSize, h.qtySize, h.lvlSize, h.nxtSize, h.headSize, h.tailSize, h.chainNodup,
    h.chainSlots, h.chainTail, h.used, hc, hv⟩

/-- Under the invariant, two slots of the chains with one order id are one slot. -/
theorem Inv.oid_inj {b : Book} (h : Inv b) {l l' : Nat} (hl : BandLevel l) (hl' : BandLevel l')
    {t t' : UInt64} (ht : t ∈ levelSlots b l) (ht' : t' ∈ levelSlots b l')
    (he : b.oid[t.toNat]! = b.oid[t'.toNat]!) : t = t' := by
  have hd := h.valid.distinct
  rw [toSpec_ids] at hd
  exact eq_of_nodup_map hd (mem_allSlots.2 ⟨l, hl, ht⟩) (mem_allSlots.2 ⟨l', hl', ht'⟩) he

/-- Under the invariant, the quantity of a slot of a chain lies from 1 to `Spec.maxQty`. -/
theorem Inv.qty_mem {b : Book} (h : Inv b) {l : Nat} (hl : BandLevel l) {t : UInt64}
    (ht : t ∈ levelSlots b l) :
    1 ≤ b.qty[t.toNat]!.toNat ∧ b.qty[t.toNat]!.toNat ≤ Spec.maxQty :=
  h.valid.qty _ (mem_toSpec hl ht)

/-- A book with fewer than 4,096 orders has a free slot from 1 to 4,096. -/
theorem Shape.exists_free {b : Book} (h : Shape b) (hc : Spec.size (toSpec b) < 4096) :
    ∃ s, 1 ≤ s ∧ s ≤ 4096 ∧ b.oid[s]! = 0 := by
  refine Classical.byContradiction fun hn => ?_
  have hsub : List.range' 1 4096 ⊆ (allSlots b).map UInt64.toNat := by
    intro n hn'
    rw [List.mem_range'_1] at hn'
    have hne : b.oid[n]! ≠ 0 := fun h0 => hn ⟨n, by omega, by omega, h0⟩
    obtain ⟨hb, hm⟩ := h.used n (by omega) (by omega) hne
    refine List.mem_map.2 ⟨n.toUInt64, mem_allSlots.2 ⟨_, hb, hm⟩, ?_⟩
    simp only [Nat.toUInt64_eq]
    exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have := (List.nodup_range' (s := 1) (n := 4096)).length_le_of_subset hsub
  rw [List.length_map, ← size_toSpec, List.length_range'] at this
  omega

/-! ## Frames -/

/-- A chain read under the same links is the same chain. -/
theorem slotsFrom_congr {b b' : Book} (h : b'.nxt = b.nxt) (fuel : Nat) (s : UInt64) :
    slotsFrom b' fuel s = slotsFrom b fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih => simp only [slotsFrom, h, ih]

/-- A level's chain under the same links and first slots is the same chain. -/
theorem levelSlots_congr {b b' : Book} (hn : b'.nxt = b.nxt) (hh : b'.head = b.head) (l : Nat) :
    levelSlots b' l = levelSlots b l := by
  simp only [levelSlots, hh, slotsFrom_congr hn]

/-- A book read from level lists that agree on the band is the same book. -/
theorem ofLevels_congr {F G : Nat → List Spec.Order} (h : ∀ l, BandLevel l → F l = G l)
    (n : UInt64) : ofLevels F n = ofLevels G n := by
  simp only [ofLevels, Spec.Book.mk.injEq, and_true]
  exact ⟨flatMap_congr fun l hl => h l (bandLevel_iff.2 (Or.inl hl)),
    flatMap_congr fun l hl => h l (bandLevel_iff.2 (Or.inr hl))⟩

/-- The reverse of a list of distinct members has distinct members. -/
theorem nodup_reverse {α : Type} {L : List α} (h : L.Nodup) : L.reverse.Nodup :=
  List.pairwise_reverse.2 (h.imp fun h' => Ne.symm h')

/-- The levels of the band, bid levels first, are distinct. -/
theorem nodup_levels : (bidLevels ++ askLevels).Nodup := by
  rw [List.nodup_append]
  refine ⟨nodup_reverse (List.nodup_range' _), List.nodup_range' _, ?_⟩
  intro a ha b hb
  rw [mem_bidLevels] at ha
  rw [mem_askLevels] at hb
  omega

/-- Replacing one level's list in a concatenation over distinct levels that holds the level
changes the length as the level's list changes. -/
theorem length_flatMap_update {α : Type} {Ls : List Nat} (hn : Ls.Nodup) {F G : Nat → List α}
    {lv : Nat} (hm : lv ∈ Ls) (hF : ∀ l ∈ Ls, l ≠ lv → G l = F l) {k k' : Nat}
    (hk : (G lv).length + k = (F lv).length + k') :
    (Ls.flatMap G).length + k = (Ls.flatMap F).length + k' := by
  induction Ls with
  | nil => simp at hm
  | cons a Ls ih =>
    rw [List.nodup_cons] at hn
    simp only [List.flatMap_cons, List.length_append]
    by_cases ha : a = lv
    · subst ha
      have : Ls.flatMap G = Ls.flatMap F :=
        flatMap_congr fun l hl => hF l (by simp [hl]) (fun he => hn.1 (he ▸ hl))
      rw [this]
      omega
    · have hm' : lv ∈ Ls := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm ha
        · exact h
      have := ih hn.2 hm' (fun l hl hne => hF l (by simp [hl]) hne)
      rw [hF a (by simp) ha]
      omega

/-! ## Sides and scans -/

/-- The specification's side of a side word: 0 for buy, and any other word for sell. -/
def toSide (k : UInt64) : Spec.Side := if k = 0 then .buy else .sell

/-- The levels of side `k`, best first. -/
def levelsOf (k : UInt64) : List Nat := if k = 0 then bidLevels else askLevels

/-- The levels of side `k` at price `p` and worse, best first. -/
def fromLevels (k : UInt64) (p : Nat) : List Nat :=
  if k = 0 then (List.range' 1 p).reverse else List.range' (1024 + p) (1024 - p)

/-- The levels of side `k` at prices better than `p`, best first. -/
def aboveLevels (k : UInt64) (p : Nat) : List Nat :=
  if k = 0 then (List.range' (p + 1) (1023 - p)).reverse else List.range' 1025 (p - 1)

/-- The price after `p` in the scan of side `k`, toward worse prices. -/
def nextPrice (k : UInt64) (p : Nat) : Nat := if k = 0 then p - 1 else p + 1

/-- The side of a book of side `k`. -/
def sideList (B : Spec.Book) (k : UInt64) : List Spec.Order := if k = 0 then B.bids else B.asks

/-- A side word of at most 1 other than 0 is 1. -/
theorem side_one {k : UInt64} (hk : k ≤ 1) (h0 : ¬k = 0) : k.toNat = 1 := by
  have h1 := UInt64.le_iff_toNat_le.1 hk
  have h2 : k.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.1 (by simpa using h))
  simp only [UInt64.reduceToNat] at h1
  omega

/-- The levels of a side are the levels above a price followed by the levels from it, for a price
from 0 to 1,023 on the bid side and from 1 to 1,024 on the ask side. -/
theorem levelsOf_eq {k : UInt64} {p : Nat}
    (hp : if k = 0 then p ≤ 1023 else 1 ≤ p ∧ p ≤ 1024) :
    levelsOf k = aboveLevels k p ++ fromLevels k p := by
  unfold levelsOf aboveLevels fromLevels
  split
  · rename_i hk
    simp only [hk, ite_true] at hp
    rw [bidLevels, ← List.reverse_append, show p + 1 = 1 + p by omega, List.range'_append_1,
      show p + (1023 - p) = 1023 by omega]
  · rename_i hk
    simp only [hk, ite_false] at hp
    rw [askLevels, show 1024 + p = 1025 + (p - 1) by omega, List.range'_append_1,
      show p - 1 + (1024 - p) = 1023 by omega]

/-- From a price of the band, the levels of a side begin with the price's level. -/
theorem fromLevels_cons {k : UInt64} (hk : k ≤ 1) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 1023) :
    fromLevels k p = (k.toNat * 1024 + p) :: fromLevels k (nextPrice k p) := by
  unfold fromLevels nextPrice
  split
  · rename_i h0
    subst h0
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.range'_1_concat, List.reverse_append, Nat.add_sub_cancel]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      UInt64.reduceToNat]
    congr 1
    omega
  · rename_i h0
    rw [side_one hk h0, show 1024 - p = (1024 - (p + 1)) + 1 by omega, List.range'_succ]
    congr 2 <;> omega

/-- Past a price of the band, the levels above the next price are the levels above the price
followed by the price's level. -/
theorem aboveLevels_next {k : UInt64} (hk : k ≤ 1) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 1023) :
    aboveLevels k (nextPrice k p) = aboveLevels k p ++ [k.toNat * 1024 + p] := by
  unfold aboveLevels nextPrice
  split
  · rename_i h0
    subst h0
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have e1 : (0 : UInt64).toNat * 1024 + (q + 1) = q + 1 := by simp
    rw [e1, Nat.add_sub_cancel, show 1023 - q = (1023 - (q + 1)) + 1 by omega, List.range'_succ,
      List.reverse_cons]
  · rename_i h0
    rw [side_one hk h0, show p + 1 - 1 = (p - 1) + 1 by omega, List.range'_1_concat]
    congr 2
    omega

/-- A side of a book read from level lists is the concatenation over the side's levels. -/
theorem sideList_ofLevels (F : Nat → List Spec.Order) (n : UInt64) (k : UInt64) :
    sideList (ofLevels F n) k = (levelsOf k).flatMap F := by
  unfold sideList levelsOf
  split <;> simp only [ofLevels]

/-- The levels of a side from a price: prices 1 to `p` on the bid side, and prices `p` to 1,023 on
the ask side. -/
theorem mem_fromLevels {k : UInt64} {p l : Nat} :
    l ∈ fromLevels k p ↔
      if k = 0 then 1 ≤ l ∧ l ≤ p else 1024 + p ≤ l ∧ l ≤ 2047 := by
  unfold fromLevels
  split
  · simp only [List.mem_reverse, List.mem_range'_1]
    omega
  · simp only [List.mem_range'_1]
    omega

/-- The levels of a side above a price: prices `p + 1` to 1,023 on the bid side, and prices 1 to
`p - 1` on the ask side. -/
theorem mem_aboveLevels {k : UInt64} {p l : Nat} :
    l ∈ aboveLevels k p ↔
      if k = 0 then p + 1 ≤ l ∧ l ≤ 1023 else 1025 ≤ l ∧ l < 1024 + p := by
  unfold aboveLevels
  split
  · simp only [List.mem_reverse, List.mem_range'_1]
    omega
  · simp only [List.mem_range'_1]
    omega

/-- A concatenation over a side's levels whose levels above a price are empty is the
concatenation over the levels from the price. -/
theorem flatMap_levelsOf {α : Type} {k : UInt64} {p : Nat}
    (hp : if k = 0 then p ≤ 1023 else 1 ≤ p ∧ p ≤ 1024) {G : Nat → List α}
    (hG : ∀ l ∈ aboveLevels k p, G l = []) :
    (levelsOf k).flatMap G = (fromLevels k p).flatMap G := by
  rw [levelsOf_eq hp, List.flatMap_append]
  have : (aboveLevels k p).flatMap G = [] := by
    rw [List.flatMap_eq_nil_iff]
    exact hG
  rw [this, List.nil_append]

/-- A side word of at most 1 gives the side of its level word. -/
theorem levelSide_level {k : UInt64} (hk : k ≤ 1) {p : Nat} (hp : p < 1024) :
    levelSide (k.toNat * 1024 + p) = toSide k ∧ levelPrice (k.toNat * 1024 + p) = p := by
  unfold levelSide levelPrice toSide
  by_cases h0 : k = 0
  · subst h0
    simp [hp, Nat.mod_eq_of_lt hp]
  · rw [side_one hk h0]
    simp only [h0, ite_false, show ¬ (1 * 1024 + p < 1024) by omega]
    exact ⟨by simp, by omega⟩

end Demos.OrderBook.Refinement
