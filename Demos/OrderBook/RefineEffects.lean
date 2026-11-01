import Demos.OrderBook.RefineChains

/-! The effects of [the program's](Program.lean) book updates on the chains and on `toSpec`.
`unlink` removes one slot from its level's chain, `place` appends a free slot to the end of a
level's chain, and an update of `qty` changes one slot's quantity.  Each keeps `Shape`, changes
the order list of one level, and changes the count by the number of orders it adds or removes. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

/-! ## Removing a slot -/

/-- Slot `s` lies in the chain of band level `lv` after the slots `A` and before the slots `B`,
and `pr` is the last slot of `A`, or 0 when `A` is empty. -/
structure UnlinkAt (b : Book) (lv pr s : UInt64) (A B : List UInt64) : Prop where
  band : BandLevel lv.toNat
  slots : levelSlots b lv.toNat = A ++ s :: B
  pred : (pr = 0 ∧ A = []) ∨ ∃ A', A = A' ++ [pr]

section Unlink

variable {b : Book} {lv pr s : UInt64} {A B : List UInt64}

/-- The links after `unlink`. -/
theorem unlink_nxt : (Program.unlink b lv pr s).nxt =
    if pr = 0 then b.nxt else b.nxt.set! pr.toNat b.nxt[s.toNat]! := by
  simp [Program.unlink]

/-- The first slots after `unlink`. -/
theorem unlink_head : (Program.unlink b lv pr s).head =
    if pr = 0 then b.head.set! lv.toNat b.nxt[s.toNat]! else b.head := by
  simp [Program.unlink]

/-- The last slots after `unlink`. -/
theorem unlink_tail : (Program.unlink b lv pr s).tail =
    if b.tail[lv.toNat]! = s then b.tail.set! lv.toNat pr else b.tail := by
  simp [Program.unlink]

/-- The slot `s` is not 0, lies inside the slot arrays, and occurs once in its chain. -/
theorem UnlinkAt.facts (h : Shape b) (hu : UnlinkAt b lv pr s A B) :
    s ≠ 0 ∧ s.toNat < 4097 ∧ s ∉ A ∧ s ∉ B ∧ (A ++ B).Nodup := by
  have hn := h.chainNodup _ hu.band
  rw [hu.slots] at hn
  have hm : s ∈ levelSlots b lv.toNat := by rw [hu.slots]; simp
  have hP := h.path hu.band
  rw [hu.slots] at hP
  refine ⟨path_ne_zero hP s (by simp), h.lt_size hu.band hm, ?_, ?_, ?_⟩
  · intro hs
    rw [List.nodup_append] at hn
    exact hn.2.2 s hs s (by simp) rfl
  · intro hs
    rw [List.nodup_append, List.nodup_cons] at hn
    exact hn.2.1.1 hs
  · exact List.Nodup.sublist ((List.sublist_cons_self s B).append_left A) hn

/-- A level's chain after `unlink`: the chain of `lv` loses `s`, and every other chain stays. -/
theorem unlink_levelSlots (h : Shape b) (hu : UnlinkAt b lv pr s A B) {l : Nat}
    (hl : BandLevel l) :
    levelSlots (Program.unlink b lv pr s) l = if l = lv.toNat then A ++ B else levelSlots b l := by
  obtain ⟨hs0, hsz, hsA, hsB, hAB⟩ := hu.facts h
  have hP := h.path hu.band
  rw [hu.slots] at hP
  have hn := h.chainNodup _ hu.band
  rw [hu.slots] at hn
  have hlv : lv.toNat < 2048 := hu.band.1
  split
  · rename_i he
    subst he
    apply levelSlots_of_path _ (by
      have := h.length_le hu.band
      rw [hu.slots] at this
      simp at this ⊢
      omega)
    rcases hu.pred with ⟨rfl, rfl⟩ | ⟨A', rfl⟩
    · rw [unlink_nxt, unlink_head]
      simp only [ite_true, List.nil_append]
      rw [get_set_eq (by rw [h.headSize]; exact hlv)]
      exact hP.2.2
    · have hpr : pr ≠ 0 := path_ne_zero hP pr (by simp)
      rw [unlink_nxt, unlink_head]
      simp only [hpr, ite_false]
      rw [List.append_assoc, List.singleton_append] at hP ⊢
      obtain ⟨m, hA', hm⟩ := path_append.1 hP
      obtain ⟨rfl, -, hm2⟩ := hm
      obtain ⟨hs1, -, hB⟩ := hm2
      have hn' : (A' ++ m :: s :: B).Nodup := by simpa using hn
      have hmA : m ∉ A' := by
        rw [List.nodup_append] at hn'
        exact fun hx => hn'.2.2 m hx m (by simp) rfl
      have hmB : m ∉ B := by
        rw [List.nodup_append, List.nodup_cons] at hn'
        exact fun hx => hn'.2.1.1 (by simp [hx])
      have hmz : m.toNat < 4097 := h.lt_size hu.band (by rw [hu.slots]; simp)
      refine path_append.2 ⟨m, path_congr hA' fun t ht => ?_, rfl, hpr, ?_⟩
      · exact get_set_ne (toNat_ne fun he => hmA (he ▸ ht))
      · rw [get_set_eq (by rw [h.nxtSize]; exact hmz)]
        exact path_congr hB fun t ht => get_set_ne (toNat_ne fun he => hmB (he ▸ ht))
  · rename_i hne
    apply levelSlots_of_path _ (h.length_le hl)
    have hP' := h.path hl
    rw [unlink_nxt, unlink_head]
    by_cases hpr : pr = 0
    · simp only [hpr, ite_true]
      rw [get_set_ne (Ne.symm hne)]
      exact hP'
    · simp only [hpr, ite_false]
      refine path_congr hP' fun t ht => get_set_ne (toNat_ne fun he => ?_)
      subst he
      rcases hu.pred with ⟨h0, -⟩ | ⟨A', hA⟩
      · exact hpr h0
      · have : pr ∈ levelSlots b lv.toNat := by rw [hu.slots, hA]; simp
        exact hne (h.disjoint hl hu.band ht this)

/-- The order ids after `unlink`. -/
theorem unlink_oid : (Program.unlink b lv pr s).oid = b.oid.set! s.toNat 0 := rfl

/-- Every slot of a chain after `unlink` is a slot of the old chain other than `s`. -/
theorem unlink_mem (h : Shape b) (hu : UnlinkAt b lv pr s A B) {l : Nat} (hl : BandLevel l)
    {t : UInt64} (ht : t ∈ levelSlots (Program.unlink b lv pr s) l) :
    t ∈ levelSlots b l ∧ t ≠ s := by
  obtain ⟨-, -, hsA, hsB, -⟩ := hu.facts h
  rw [unlink_levelSlots h hu hl] at ht
  by_cases he : l = lv.toNat
  · subst he
    simp only [ite_true] at ht
    rw [hu.slots]
    rcases List.mem_append.1 ht with ht | ht
    · exact ⟨by simp [ht], fun he => hsA (he ▸ ht)⟩
    · exact ⟨by simp [ht], fun he => hsB (he ▸ ht)⟩
  · simp only [he, ite_false] at ht
    exact ⟨ht, fun hts => he (h.disjoint hl hu.band ht (by rw [hu.slots, hts]; simp))⟩

/-- The order in a slot other than `s` is the same after `unlink`. -/
theorem unlink_orderAt (l : Nat) {t : UInt64} (ht : t ≠ s) :
    orderAt (Program.unlink b lv pr s) l t = orderAt b l t := by
  simp only [orderAt, unlink_oid]
  rw [get_set_ne (toNat_ne (Ne.symm ht))]
  rfl

/-- `unlink` keeps the structural part of the invariant. -/
theorem unlink_shape (h : Shape b) (hu : UnlinkAt b lv pr s A B) :
    Shape (Program.unlink b lv pr s) := by
  obtain ⟨hs0, hsz, hsA, hsB, hAB⟩ := hu.facts h
  have hL := fun l (hl : BandLevel l) => unlink_levelSlots h hu hl
  have hlv : lv.toNat < 2048 := hu.band.1
  refine
    { oidSize := by rw [unlink_oid, Array.size_set!, h.oidSize]
      acctSize := h.acctSize
      qtySize := h.qtySize
      lvlSize := h.lvlSize
      nxtSize := by rw [unlink_nxt]; split <;> simp [h.nxtSize]
      headSize := by rw [unlink_head]; split <;> simp [h.headSize]
      tailSize := by rw [unlink_tail]; split <;> simp [h.tailSize]
      chainNodup := ?_
      chainSlots := fun l hl t ht => h.chainSlots l hl t (unlink_mem h hu hl ht).1
      chainTail := ?_
      used := ?_
      oidPos := ?_ }
  · intro l hl
    rw [hL l hl]
    split
    · exact hAB
    · exact h.chainNodup l hl
  · intro l hl
    have ht := h.chainTail l hl
    rw [hL l hl, unlink_tail]
    by_cases he : l = lv.toNat
    · subst he
      simp only [ite_true]
      rw [hu.slots] at ht
      rcases List.eq_nil_or_concat B with rfl | ⟨B', z, rfl⟩
      · have ht' : b.tail[lv.toNat]! = s := by simpa using ht
        simp only [ht', ite_true, List.append_nil]
        rw [get_set_eq (by rw [h.tailSize]; exact hlv)]
        rcases hu.pred with ⟨rfl, rfl⟩ | ⟨A', rfl⟩ <;> simp
      · have hz : z ≠ s := fun he => hsB (by simp [he])
        have ht' : b.tail[lv.toNat]! = z := by
          have : A ++ s :: B'.concat z = (A ++ s :: B') ++ [z] := by simp [List.concat_eq_append]
          rw [ht, this, List.getLast?_concat]
          rfl
        simp only [ht', hz, ite_false]
        simp [List.concat_eq_append]
    · split
      · rw [get_set_ne (Ne.symm he)]
        simpa [he] using ht
      · simpa [he] using ht
  · intro t h1 h2 hne
    have hts : t ≠ s.toNat := by
      rintro rfl
      rw [unlink_oid, get_set_eq (show s.toNat < b.oid.size by rw [h.oidSize]; exact hsz)] at hne
      exact hne rfl
    have hne' : b.oid[t]! ≠ 0 := by
      rwa [unlink_oid, get_set_ne (Ne.symm hts)] at hne
    obtain ⟨hb, hm⟩ := h.used t h1 h2 hne'
    refine ⟨hb, ?_⟩
    show t.toUInt64 ∈ levelSlots (Program.unlink b lv pr s) b.lvl[t]!.toNat
    rw [hL _ hb]
    by_cases he : b.lvl[t]!.toNat = lv.toNat
    · simp only [he, ite_true]
      rw [he, hu.slots] at hm
      have : t.toUInt64 ≠ s := by
        intro he'
        apply hts
        rw [← he']
        simp only [Nat.toUInt64_eq]
        exact (UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)).symm
      rcases List.mem_append.1 hm with hm | hm
      · simp [hm]
      · rcases List.mem_cons.1 hm with hm | hm
        · exact absurd hm this
        · simp [hm]
    · simpa [he] using hm
  · intro l hl t ht
    obtain ⟨ht', hts⟩ := unlink_mem h hu hl ht
    rw [unlink_oid, get_set_ne (toNat_ne (Ne.symm hts))]
    exact h.oidPos l hl t ht'

/-- The orders of a level after `unlink`: level `lv` loses the order of `s`. -/
theorem unlink_ordersAt (h : Shape b) (hu : UnlinkAt b lv pr s A B) {l : Nat}
    (hl : BandLevel l) :
    ordersAt (Program.unlink b lv pr s) l =
      if l = lv.toNat then (A ++ B).map (orderAt b lv.toNat) else ordersAt b l := by
  have hm := fun t (ht : t ∈ levelSlots (Program.unlink b lv pr s) l) => unlink_mem h hu hl ht
  unfold ordersAt
  have hL := unlink_levelSlots h hu hl
  by_cases he : l = lv.toNat
  · subst he
    simp only [ite_true] at hL ⊢
    rw [← hL]
    exact List.map_congr_left fun t ht => unlink_orderAt _ (hm t ht).2
  · simp only [he, ite_false] at hL ⊢
    rw [← hL]
    exact List.map_congr_left fun t ht => unlink_orderAt _ (hm t ht).2

/-- `unlink` removes one order from the specification's book. -/
theorem unlink_size (h : Shape b) (hu : UnlinkAt b lv pr s A B) :
    Spec.size (toSpec (Program.unlink b lv pr s)) + 1 = Spec.size (toSpec b) := by
  rw [size_toSpec, size_toSpec, allSlots, allSlots]
  have := length_flatMap_update (k := 1) (k' := 0) nodup_levels
    (List.mem_append.2 (bandLevel_iff.1 hu.band))
    (G := levelSlots (Program.unlink b lv pr s)) (F := levelSlots b)
    (fun l hl hne => by
      simp [unlink_levelSlots h hu (bandLevel_iff.2 (List.mem_append.1 hl)), hne])
    (by simp only [unlink_levelSlots h hu hu.band, ite_true, hu.slots]; simp; omega)
  simpa using this

/-- `unlink` keeps the count equal to the number of orders. -/
theorem unlink_count (h : Shape b) (hu : UnlinkAt b lv pr s A B)
    (hc : b.count.toNat = Spec.size (toSpec b)) :
    (Program.unlink b lv pr s).count.toNat = Spec.size (toSpec (Program.unlink b lv pr s)) := by
  have := unlink_size h hu
  show (b.count - 1).toNat = _
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; omega))]
  simp
  omega

end Unlink

/-! ## Placing an order in a free slot -/

/-- Level `lv` lies in the band, and slot `s` is a free slot from 1 to 4,096. -/
structure PlaceAt (b : Book) (lv s : UInt64) : Prop where
  band : BandLevel lv.toNat
  lo : 1 ≤ s.toNat
  hi : s.toNat ≤ 4096
  free : b.oid[s.toNat]! = 0

/-- The book with an order of id `id`, account `account`, and quantity `q` in slot `s`, at the end
of the chain of level `lv`. -/
def placed (b : Book) (lv s id account q : UInt64) : Book :=
  { b with
    oid := b.oid.set! s.toNat id
    acct := b.acct.set! s.toNat account
    qty := b.qty.set! s.toNat q
    lvl := b.lvl.set! s.toNat lv
    nxt := (if b.head[lv.toNat]! = 0 then b.nxt
      else b.nxt.set! b.tail[lv.toNat]!.toNat s).set! s.toNat 0
    head := if b.head[lv.toNat]! = 0 then b.head.set! lv.toNat s else b.head
    tail := b.tail.set! lv.toNat s
    count := b.count + 1 }

/-- `place` puts the order in the first free slot at the end of the chain of its level. -/
theorem place_eq (b : Book) (side price id account q : UInt64) :
    Program.place b side price id account q =
      placed b (Program.level side price) (Program.freeSlot b.oid) id account q := by
  simp [Program.place, placed]

section Place

variable {b : Book} {lv s id account q : UInt64}

/-- A free slot lies in no chain. -/
theorem PlaceAt.not_mem (h : Shape b) (hp : PlaceAt b lv s) {l : Nat} (hl : BandLevel l) :
    s ∉ levelSlots b l := fun hs => h.oidPos l hl s hs hp.free

/-- A level's chain after `placed`: the chain of `lv` gains `s` at its end, and every other chain
stays. -/
theorem placed_levelSlots (h : Shape b) (hp : PlaceAt b lv s) {l : Nat} (hl : BandLevel l) :
    levelSlots (placed b lv s id account q) l =
      if l = lv.toNat then levelSlots b lv.toNat ++ [s] else levelSlots b l := by
  have hs0 : s ≠ 0 := fun he => by have := hp.lo; rw [he] at this; simp at this
  have hsz : s.toNat < b.nxt.size := by rw [h.nxtSize]; have := hp.hi; omega
  have hlv : lv.toNat < b.head.size := by rw [h.headSize]; exact hp.band.1
  have hP := h.path hp.band
  have hn := h.chainNodup _ hp.band
  by_cases he : l = lv.toNat
  · subst he
    simp only [ite_true]
    have hlen : (levelSlots b lv.toNat ++ [s]).length ≤ 4096 := by
      apply length_le_of_slots
      · rw [List.nodup_append]
        exact ⟨hn, by simp, fun a ha c hc he => by
          simp at hc; subst hc; subst he; exact hp.not_mem h hp.band ha⟩
      · intro t ht
        rcases List.mem_append.1 ht with ht | ht
        · exact ⟨(h.chainSlots _ hp.band t ht).1, (h.chainSlots _ hp.band t ht).2.1⟩
        · simp at ht; subst ht; exact ⟨hp.lo, hp.hi⟩
    apply levelSlots_of_path _ hlen
    by_cases hh : b.head[lv.toNat]! = 0
    · rw [levelSlots_eq_nil.2 hh]
      simp only [placed, hh, ite_true, List.nil_append]
      rw [get_set_eq hlv]
      exact ⟨rfl, hs0, by rw [get_set_eq hsz]; rfl⟩
    · have hne : levelSlots b lv.toNat ≠ [] := fun he => hh (levelSlots_eq_nil.1 he)
      obtain ⟨L', t, hLt⟩ := (List.eq_nil_or_concat _).resolve_left hne
      rw [List.concat_eq_append] at hLt
      have htail : b.tail[lv.toNat]! = t := by
        rw [h.chainTail _ hp.band, hLt, List.getLast?_concat]
        rfl
      have hts : t ≠ s := fun he => hp.not_mem h hp.band (by rw [hLt, ← he]; simp)
      rw [hLt] at hP hn ⊢
      obtain ⟨m, hL', hm⟩ := path_append.1 hP
      obtain ⟨rfl, ht0, -⟩ := hm
      have htz : m.toNat < b.nxt.size := by
        rw [h.nxtSize]; exact h.lt_size hp.band (by rw [hLt]; simp)
      simp only [placed, hh, ite_false, htail]
      rw [List.append_assoc]
      refine path_append.2 ⟨m, path_congr hL' fun u hu => ?_, rfl, ht0, ?_⟩
      · have hus : u ≠ s := fun he => hp.not_mem h hp.band (by rw [hLt, ← he]; simp [hu])
        have hum : u ≠ m := by
          rintro rfl
          rw [List.nodup_append] at hn
          exact hn.2.2 u hu u (by simp) rfl
        rw [get_set_ne (toNat_ne (Ne.symm hus)), get_set_ne (toNat_ne (Ne.symm hum))]
      · rw [get_set_ne (toNat_ne (Ne.symm hts)), get_set_eq htz]
        exact ⟨rfl, hs0, by rw [get_set_eq (by simp [hsz])]; rfl⟩
  · simp only [he, ite_false]
    apply levelSlots_of_path _ (h.length_le hl)
    have hP' := h.path hl
    have hhd : (placed b lv s id account q).head[l]! = b.head[l]! := by
      simp only [placed]
      split
      · exact get_set_ne (Ne.symm he)
      · rfl
    rw [hhd]
    refine path_congr hP' fun u hu => ?_
    have hus : u ≠ s := fun he' => hp.not_mem h hl (he' ▸ hu)
    simp only [placed]
    rw [get_set_ne (toNat_ne (Ne.symm hus))]
    split
    · rfl
    · rename_i hh
      have hne : levelSlots b lv.toNat ≠ [] := fun he' => hh (levelSlots_eq_nil.1 he')
      obtain ⟨L', t, hLt⟩ := (List.eq_nil_or_concat _).resolve_left hne
      rw [List.concat_eq_append] at hLt
      have htail : b.tail[lv.toNat]! = t := by
        rw [h.chainTail _ hp.band, hLt, List.getLast?_concat]
        rfl
      have hut : u ≠ t := fun he' => he (h.disjoint hl hp.band hu (by rw [hLt, ← he']; simp))
      rw [htail, get_set_ne (toNat_ne (Ne.symm hut))]

/-- Every slot of a chain after `placed` is `s` on the chain of `lv` or a slot of the old
chain. -/
theorem placed_mem (h : Shape b) (hp : PlaceAt b lv s) {l : Nat} (hl : BandLevel l)
    {t : UInt64} (ht : t ∈ levelSlots (placed b lv s id account q) l) :
    (t ∈ levelSlots b l ∧ t ≠ s) ∨ (t = s ∧ l = lv.toNat) := by
  rw [placed_levelSlots h hp hl] at ht
  by_cases he : l = lv.toNat
  · subst he
    simp only [ite_true, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact Or.inl ⟨ht, fun he => hp.not_mem h hl (he ▸ ht)⟩
    · exact Or.inr ⟨ht, rfl⟩
  · simp only [he, ite_false] at ht
    exact Or.inl ⟨ht, fun he' => hp.not_mem h hl (he' ▸ ht)⟩

/-- The order in a slot other than `s` is the same after `placed`. -/
theorem placed_orderAt_ne (l : Nat) {t : UInt64} (ht : t ≠ s) :
    orderAt (placed b lv s id account q) l t = orderAt b l t := by
  simp only [orderAt, placed]
  rw [get_set_ne (toNat_ne (Ne.symm ht)), get_set_ne (toNat_ne (Ne.symm ht)),
    get_set_ne (toNat_ne (Ne.symm ht))]

/-- The order in slot `s` after `placed` is the new order. -/
theorem placed_orderAt_eq (h : Shape b) (hp : PlaceAt b lv s) (l : Nat) :
    orderAt (placed b lv s id account q) l s =
      ⟨id, account, levelSide l, levelPrice l, q.toNat⟩ := by
  have hsz : s.toNat < 4097 := by have := hp.hi; omega
  simp only [orderAt, placed]
  rw [get_set_eq (by rw [h.oidSize]; exact hsz), get_set_eq (by rw [h.acctSize]; exact hsz),
    get_set_eq (by rw [h.qtySize]; exact hsz)]

/-- `placed` keeps the structural part of the invariant when the new id is not 0. -/
theorem placed_shape (h : Shape b) (hp : PlaceAt b lv s) (hid : id ≠ 0) :
    Shape (placed b lv s id account q) := by
  have hsz : s.toNat < 4097 := by have := hp.hi; omega
  have hL := fun l (hl : BandLevel l) => placed_levelSlots (id := id) (account := account)
    (q := q) h hp hl
  have hlvl : ∀ t : Nat, t ≠ s.toNat → (placed b lv s id account q).lvl[t]! = b.lvl[t]! :=
    fun t ht => get_set_ne (Ne.symm ht)
  have hlvs : (placed b lv s id account q).lvl[s.toNat]! = lv :=
    get_set_eq (by rw [h.lvlSize]; exact hsz)
  refine
    { oidSize := by simp [placed, h.oidSize]
      acctSize := by simp [placed, h.acctSize]
      qtySize := by simp [placed, h.qtySize]
      lvlSize := by simp [placed, h.lvlSize]
      nxtSize := by simp only [placed]; split <;> simp [h.nxtSize]
      headSize := by simp only [placed]; split <;> simp [h.headSize]
      tailSize := by simp [placed, h.tailSize]
      chainNodup := ?_
      chainSlots := ?_
      chainTail := ?_
      used := ?_
      oidPos := ?_ }
  · intro l hl
    rw [hL l hl]
    split
    · rename_i he
      subst he
      rw [List.nodup_append]
      exact ⟨h.chainNodup _ hl, by simp, fun a ha c hc he => by
        simp at hc; subst hc; subst he; exact hp.not_mem h hl ha⟩
    · exact h.chainNodup l hl
  · intro l hl t ht
    rcases placed_mem h hp hl ht with ⟨ht, hts⟩ | ⟨rfl, rfl⟩
    · have := h.chainSlots l hl t ht
      rw [hlvl _ (toNat_ne hts)]
      exact this
    · rw [hlvs]
      exact ⟨hp.lo, hp.hi, rfl⟩
  · intro l hl
    rw [hL l hl]
    simp only [placed]
    by_cases he : l = lv.toNat
    · subst he
      simp only [ite_true, List.getLast?_concat, Option.getD_some]
      exact get_set_eq (by rw [h.tailSize]; exact hl.1)
    · simp only [he, ite_false]
      rw [get_set_ne (Ne.symm he)]
      exact h.chainTail l hl
  · intro t h1 h2 hne
    by_cases hts : t = s.toNat
    · subst hts
      rw [hlvs]
      refine ⟨hp.band, ?_⟩
      rw [hL _ hp.band]
      simp only [ite_true, Nat.toUInt64_eq]
      have : UInt64.ofNat s.toNat = s := by simp
      simp [this]
    · have hne' : b.oid[t]! ≠ 0 := by
        have : (placed b lv s id account q).oid[t]! = b.oid[t]! := get_set_ne (Ne.symm hts)
        rwa [this] at hne
      obtain ⟨hb, hm⟩ := h.used t h1 h2 hne'
      rw [hlvl t hts]
      refine ⟨hb, ?_⟩
      rw [hL _ hb]
      split
      · rename_i he
        rw [he] at hm
        simp [hm]
      · exact hm
  · intro l hl t ht
    rcases placed_mem h hp hl ht with ⟨ht, hts⟩ | ⟨rfl, rfl⟩
    · have : (placed b lv s id account q).oid[t.toNat]! = b.oid[t.toNat]! :=
        get_set_ne (toNat_ne (Ne.symm hts))
      rw [this]
      exact h.oidPos l hl t ht
    · have : (placed b lv t id account q).oid[t.toNat]! = id :=
        get_set_eq (by rw [h.oidSize]; exact hsz)
      rw [this]
      exact hid

/-- The orders of a level after `placed`: level `lv` gains the new order at its end. -/
theorem placed_ordersAt (h : Shape b) (hp : PlaceAt b lv s) {l : Nat} (hl : BandLevel l) :
    ordersAt (placed b lv s id account q) l =
      if l = lv.toNat then ordersAt b lv.toNat ++
        [⟨id, account, levelSide lv.toNat, levelPrice lv.toNat, q.toNat⟩]
      else ordersAt b l := by
  unfold ordersAt
  rw [placed_levelSlots h hp hl]
  by_cases he : l = lv.toNat
  · subst he
    simp only [ite_true, List.map_append, List.map_cons, List.map_nil]
    rw [placed_orderAt_eq h hp]
    congr 1
    exact List.map_congr_left fun t ht => placed_orderAt_ne _
      (fun he => hp.not_mem h hl (he ▸ ht))
  · simp only [he, ite_false]
    exact List.map_congr_left fun t ht => placed_orderAt_ne _
      (fun he' => hp.not_mem h hl (he' ▸ ht))

/-- `placed` adds one order to the specification's book. -/
theorem placed_size (h : Shape b) (hp : PlaceAt b lv s) :
    Spec.size (toSpec (placed b lv s id account q)) = Spec.size (toSpec b) + 1 := by
  rw [size_toSpec, size_toSpec, allSlots, allSlots]
  have := length_flatMap_update (k := 0) (k' := 1) nodup_levels
    (List.mem_append.2 (bandLevel_iff.1 hp.band))
    (G := levelSlots (placed b lv s id account q)) (F := levelSlots b)
    (fun l hl hne => by
      simp [placed_levelSlots h hp (bandLevel_iff.2 (List.mem_append.1 hl)), hne])
    (by simp only [placed_levelSlots h hp hp.band, ite_true]; simp)
  simpa using this

end Place

/-! ## Changing a quantity -/

section SetQty

variable {b : Book} {s v : UInt64}

/-- The chains after a quantity update are the same. -/
theorem setQ_levelSlots (l : Nat) :
    levelSlots { b with qty := b.qty.set! s.toNat v } l = levelSlots b l := by
  apply levelSlots_congr <;> rfl

/-- A quantity update keeps the structural part of the invariant. -/
theorem setQ_shape (h : Shape b) : Shape { b with qty := b.qty.set! s.toNat v } where
  oidSize := h.oidSize
  acctSize := h.acctSize
  qtySize := by simp [h.qtySize]
  lvlSize := h.lvlSize
  nxtSize := h.nxtSize
  headSize := h.headSize
  tailSize := h.tailSize
  chainNodup l hl := by rw [setQ_levelSlots]; exact h.chainNodup l hl
  chainSlots l hl t ht := by rw [setQ_levelSlots] at ht; exact h.chainSlots l hl t ht
  chainTail l hl := by rw [setQ_levelSlots]; exact h.chainTail l hl
  used t h1 h2 hne := by rw [setQ_levelSlots]; exact h.used t h1 h2 hne
  oidPos l hl t ht := by rw [setQ_levelSlots] at ht; exact h.oidPos l hl t ht

/-- The order in a slot after a quantity update at slot `s`. -/
theorem setQ_orderAt (h : Shape b) (hs : s.toNat < 4097) (l : Nat) (t : UInt64) :
    orderAt { b with qty := b.qty.set! s.toNat v } l t =
      if t = s then { orderAt b l t with qty := v.toNat } else orderAt b l t := by
  simp only [orderAt]
  split
  · rename_i he
    subst he
    rw [get_set_eq (by rw [h.qtySize]; exact hs)]
  · rename_i hne
    rw [get_set_ne (toNat_ne (Ne.symm hne))]

/-- The orders of a level after a quantity update at slot `s`. -/
theorem setQ_ordersAt (h : Shape b) (hs : s.toNat < 4097) (l : Nat) :
    ordersAt { b with qty := b.qty.set! s.toNat v } l = (levelSlots b l).map
      (fun t => if t = s then { orderAt b l t with qty := v.toNat } else orderAt b l t) := by
  unfold ordersAt
  rw [setQ_levelSlots]
  exact List.map_congr_left fun t _ => setQ_orderAt h hs l t

/-- A quantity update keeps the number of orders. -/
theorem setQ_size :
    Spec.size (toSpec { b with qty := b.qty.set! s.toNat v }) = Spec.size (toSpec b) := by
  rw [size_toSpec, size_toSpec, allSlots, allSlots,
    show levelSlots { b with qty := b.qty.set! s.toNat v } = levelSlots b from
      funext setQ_levelSlots]

end SetQty

/-! ## The specification's updates on level lists -/

/-- Removing the orders with an id removes them from each level. -/
theorem remove_ofLevels (F : Nat → List Spec.Order) (n id : UInt64) :
    Spec.remove (ofLevels F n) id = ofLevels (fun l => (F l).filter (·.id != id)) n := by
  simp [Spec.remove, ofLevels, List.filter_flatMap]

/-- Setting the quantity of the orders with an id sets it in each level. -/
theorem setQty_ofLevels (F : Nat → List Spec.Order) (n id : UInt64) (q : Nat) :
    Spec.setQty (ofLevels F n) id q =
      ofLevels (fun l => (F l).map (fun o => if o.id = id then { o with qty := q } else o)) n := by
  simp [Spec.setQty, ofLevels, List.map_flatMap]

/-- Each level holds orders of its side and price. -/
def LevelsOK (F : Nat → List Spec.Order) : Prop :=
  ∀ l, BandLevel l → ∀ o ∈ F l, o.side = levelSide l ∧ o.price = levelPrice l

/-- The levels of a book hold orders of their sides and prices. -/
theorem levelsOK_ordersAt (b : Book) : LevelsOK (ordersAt b) := by
  intro l _ o ho
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 ho
  exact ⟨rfl, rfl⟩

/-- Placing an order behind a prefix whose prices are at least as good as its own. -/
theorem place_append (o : Spec.Order) {X : List Spec.Order} (Y : List Spec.Order)
    (hX : ∀ x ∈ X, Spec.asGood o.side x.price o.price = true) :
    Spec.place o (X ++ Y) = X ++ Spec.place o Y := by
  induction X with
  | nil => rfl
  | cons x X ih =>
    simp only [List.cons_append, Spec.place, hX x (by simp), ite_true]
    rw [ih fun y hy => hX y (by simp [hy])]

/-- Placing an order before a side whose first price is not as good as its own. -/
theorem place_front (o : Spec.Order) {Y : List Spec.Order}
    (hY : ∀ y ∈ Y.head?, Spec.asGood o.side y.price o.price = false) :
    Spec.place o Y = o :: Y := by
  cases Y with
  | nil => rfl
  | cons y Y => simp [Spec.place, hY y rfl]

/-- The price of a bid level is the level. -/
theorem levelPrice_bid {l : Nat} (h : l < 1024) : levelPrice l = l := Nat.mod_eq_of_lt h

/-- The price of an ask level is the level less 1,024. -/
theorem levelPrice_ask {l : Nat} (h1 : 1024 ≤ l) (h2 : l < 2048) : levelPrice l = l - 1024 := by
  unfold levelPrice
  omega

/-- Resting an order of a level of the band appends it to the level. -/
theorem rest_ofLevels {F : Nat → List Spec.Order} (hF : LevelsOK F) (n : UInt64) {lv : Nat}
    (hlv : BandLevel lv) {o : Spec.Order} (hos : o.side = levelSide lv)
    (hop : o.price = levelPrice lv) :
    Spec.rest (ofLevels F n) o = ofLevels (fun l => if l = lv then F l ++ [o] else F l) n := by
  have hcong : ∀ L : List Nat, lv ∉ L →
      L.flatMap (fun l => if l = lv then F l ++ [o] else F l) = L.flatMap F :=
    fun L hL => flatMap_congr fun l hl => by simp [show l ≠ lv from fun he => hL (he ▸ hl)]
  have hband : lv < 2048 ∧ lv % 1024 ≠ 0 := hlv
  by_cases hb : lv < 1024
  · have hk : (0 : UInt64) ≤ 1 := by decide
    have hp : 1 ≤ lv ∧ lv ≤ 1023 := by omega
    have hlv' : (0 : UInt64).toNat * 1024 + lv = lv := by simp
    have hL := levelsOf_eq (k := 0) (p := lv) (by simp; omega)
    rw [fromLevels_cons hk hp, hlv'] at hL
    have hside : o.side = .buy := by rw [hos]; simp [levelSide, hb]
    have hprice : o.price = lv := by rw [hop, levelPrice_bid hb]
    simp only [Spec.rest, hside, ofLevels, Spec.Book.mk.injEq, and_true]
    have hbid : bidLevels = levelsOf 0 := rfl
    have hnotask : lv ∉ askLevels := by rw [mem_askLevels]; omega
    refine ⟨?_, (hcong _ hnotask).symm⟩
    rw [hbid, hL, List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_cons]
    have hA : lv ∉ aboveLevels 0 lv := by simp [mem_aboveLevels] <;> omega
    have hB : lv ∉ fromLevels 0 (nextPrice 0 lv) := by
      simp [mem_fromLevels, nextPrice] <;> omega
    rw [hcong _ hA, hcong _ hB]
    simp only [ite_true]
    rw [← List.append_assoc, place_append, place_front]
    · simp
    · intro y hy
      obtain ⟨l, hl, hyl⟩ := List.mem_flatMap.1 (List.mem_of_mem_head? hy)
      have hl' : 1 ≤ l ∧ l ≤ lv - 1 := by simpa [mem_fromLevels, nextPrice] using hl
      have := hF l (bandLevel_iff.2 (Or.inl (mem_bidLevels.2 (by omega)))) y hyl
      rw [hside, this.2, hprice, levelPrice_bid (by omega)]
      simp only [Spec.asGood, decide_eq_false_iff_not]
      omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨l, hl, hxl⟩ := List.mem_flatMap.1 hx
        have hl' : lv + 1 ≤ l ∧ l ≤ 1023 := by simpa [mem_aboveLevels] using hl
        have := hF l (bandLevel_iff.2 (Or.inl (mem_bidLevels.2 (by omega)))) x hxl
        rw [hside, this.2, hprice, levelPrice_bid (by omega)]
        simp only [Spec.asGood, decide_eq_true_eq]
        omega
      · have := hF lv hlv x hx
        rw [hside, this.2, hprice, levelPrice_bid hb]
        simp [Spec.asGood]
  · have hk : (1 : UInt64) ≤ 1 := by decide
    have hp : 1 ≤ lv - 1024 ∧ lv - 1024 ≤ 1023 := by omega
    have hlv' : (1 : UInt64).toNat * 1024 + (lv - 1024) = lv := by simp; omega
    have hL := levelsOf_eq (k := 1) (p := lv - 1024) (by simp; omega)
    rw [fromLevels_cons hk hp, hlv'] at hL
    have hside : o.side = .sell := by rw [hos]; simp [levelSide, hb]
    have hprice : o.price = lv - 1024 := by rw [hop, levelPrice_ask (by omega) hband.1]
    simp only [Spec.rest, hside, ofLevels, Spec.Book.mk.injEq, and_true]
    have hask : askLevels = levelsOf 1 := rfl
    have hnotbid : lv ∉ bidLevels := by rw [mem_bidLevels]; omega
    refine ⟨(hcong _ hnotbid).symm, ?_⟩
    rw [hask, hL, List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_cons]
    have hA : lv ∉ aboveLevels 1 (lv - 1024) := by simp [mem_aboveLevels] <;> omega
    have hB : lv ∉ fromLevels 1 (nextPrice 1 (lv - 1024)) := by
      simp [mem_fromLevels, nextPrice] <;> omega
    rw [hcong _ hA, hcong _ hB]
    simp only [ite_true]
    rw [← List.append_assoc, place_append, place_front]
    · simp
    · intro y hy
      obtain ⟨l, hl, hyl⟩ := List.mem_flatMap.1 (List.mem_of_mem_head? hy)
      have hl' : 1024 + (lv - 1024 + 1) ≤ l ∧ l ≤ 2047 := by
        simpa [mem_fromLevels, nextPrice] using hl
      have := hF l (bandLevel_iff.2 (Or.inr (mem_askLevels.2 (by omega)))) y hyl
      rw [hside, this.2, hprice, levelPrice_ask (by omega) (by omega)]
      simp only [Spec.asGood, decide_eq_false_iff_not]
      omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨l, hl, hxl⟩ := List.mem_flatMap.1 hx
        have hl' : 1025 ≤ l ∧ l < 1024 + (lv - 1024) := by simpa [mem_aboveLevels] using hl
        have := hF l (bandLevel_iff.2 (Or.inr (mem_askLevels.2 (by omega)))) x hxl
        rw [hside, this.2, hprice, levelPrice_ask (by omega) (by omega)]
        simp only [Spec.asGood, decide_eq_true_eq]
        omega
      · have := hF lv hlv x hx
        rw [hside, this.2, hprice, levelPrice_ask (by omega) hband.1]
        simp [Spec.asGood]

end Demos.OrderBook.Refinement
