import Demos.OrderBook.Spec

/-! Theorems of [the order book's specification](Spec.lean).  `Valid` holds of the empty book and
after every step and stream, matching trades with the first orders of the opposite side at their
prices, quantities are conserved, each rejection reason occurs exactly when the requirements' table
gives it, and a stream run in two parts gives the book and the events of one run. -/

namespace Demos.OrderBook.Spec

/-- Whether an event is `accepted`. -/
def Event.isAccepted : Event → Bool
  | .accepted .. => true
  | _ => false

/-- The quantity of a trade event, and 0 for any other event. -/
def Event.tradeQty : Event → Nat
  | .trade _ _ _ q _ _ => q
  | _ => 0

/-- The maker id of a trade event. -/
def Event.maker? : Event → Option UInt64
  | .trade m .. => some m
  | _ => none

/-- The bounds of an event's fields that hold natural numbers, which `encode` writes as words. -/
def Event.Bounded : Event → Prop
  | .trade _ _ p q _ rem => 1 ≤ p ∧ p ≤ maxPrice ∧ 1 ≤ q ∧ q ≤ maxQty ∧ rem ≤ maxQty
  | .cancelled _ rem _ => 1 ≤ rem ∧ rem ≤ maxQty
  | .reduced _ q => 1 ≤ q ∧ q ≤ maxQty
  | _ => True

/-- The total quantity that a list of events trades. -/
def traded (es : List Event) : Nat := (es.map Event.tradeQty).sum

/-- The total remaining quantity of a list of orders. -/
def total (os : List Order) : Nat := (os.map (·.qty)).sum

/-- The trade that exhausts the resting order `m` against the incoming order `taker`. -/
def exhaust (taker : UInt64) (m : Order) : Event := .trade m.id taker m.price m.qty m.account 0

/-- The reference word of a seven-word command record. -/
def refWord (r : Array UInt64) : UInt64 :=
  if r[0]! = 1 then r[5]!
  else if r[0]! = 2 then r[4]!
  else if r[0]! = 3 ∨ r[0]! = 4 then r[1]!
  else 0

/-! ## Valid books -/


theorem empty_valid : Valid empty :=
  { bidsOrdered := by simp [empty, Ordered]
    asksOrdered := by simp [empty, Ordered]
    bidSide := by simp [empty]
    askSide := by simp [empty]
    price := by simp [empty]
    qty := by simp [empty]
    ids := by simp [empty]
    distinct := by simp [empty]
    bounded := by simp [empty]
    notCrossed := by simp [empty]
    nextPositive := by decide }

/-- Matching against a side that begins with `m` stops before `m`, stops at `m` for self-trade
prevention, exhausts `m` and continues with the rest of the side, or trades part of `m` and
ends. -/
theorem fill_cases (taker account : UInt64) (side : Side) (limit qty : Nat) (m : Order)
    (ms : List Order) :
    ((qty = 0 ∨ acceptable side limit m.price = false) ∧
        fill taker account side limit qty (m :: ms) = ⟨m :: ms, [], qty, false⟩) ∨
      (qty ≠ 0 ∧ acceptable side limit m.price = true ∧ m.account = account ∧
        fill taker account side limit qty (m :: ms) = ⟨m :: ms, [], qty, true⟩) ∨
      (qty ≠ 0 ∧ acceptable side limit m.price = true ∧ m.account ≠ account ∧ m.qty ≤ qty ∧
        fill taker account side limit qty (m :: ms) =
          ⟨(fill taker account side limit (qty - m.qty) ms).others,
            exhaust taker m :: (fill taker account side limit (qty - m.qty) ms).trades,
            (fill taker account side limit (qty - m.qty) ms).remaining,
            (fill taker account side limit (qty - m.qty) ms).selfTrade⟩) ∨
      (0 < qty ∧ qty < m.qty ∧ acceptable side limit m.price = true ∧ m.account ≠ account ∧
        fill taker account side limit qty (m :: ms) =
          ⟨{ m with qty := m.qty - qty } :: ms,
            [.trade m.id taker m.price qty m.account (m.qty - qty)], 0, false⟩) := by
  by_cases h1 : qty = 0 ∨ acceptable side limit m.price = false
  · left
    refine ⟨h1, ?_⟩
    rcases h1 with h | h <;> simp [fill, h]
  · have hq : qty ≠ 0 := fun h => h1 (Or.inl h)
    have ha : acceptable side limit m.price = true := by
      cases h : acceptable side limit m.price
      · exact absurd (Or.inr h) h1
      · rfl
    by_cases h2 : m.account = account
    · right; left
      exact ⟨hq, ha, h2, by simp [fill, hq, ha, h2]⟩
    · right; right
      by_cases h3 : m.qty ≤ qty
      · left
        refine ⟨hq, ha, h2, h3, ?_⟩
        have hmin : min qty m.qty = m.qty := Nat.min_eq_right h3
        simp [fill, hq, ha, h2, hmin, exhaust]
      · right
        have hmin : min qty m.qty = qty := by omega
        refine ⟨by omega, by omega, ha, h2, ?_⟩
        have hne : qty ≠ m.qty := by omega
        simp [fill, hq, ha, h2, hmin, hne]

/-- The side, price, and id of an order, which fix its place in priority order. -/
def Order.key (o : Order) : Side × Nat × UInt64 := (o.side, o.price, o.id)

/-- Whether an order with key `p` may come before an order with key `q` on `side`: its price is at
least as good, and at an equal price its id is smaller. -/
def Ahead (side : Side) (p q : Side × Nat × UInt64) : Prop :=
  asGood side p.2.1 q.2.1 = true ∧ (p.2.1 = q.2.1 → p.2.2 < q.2.2)

/-- The keys of the side that matching leaves form a sublist of the keys of the side it began
with. -/
theorem fill_keys (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order) :
    ((fill taker account side limit qty os).others.map Order.key).Sublist
      (os.map Order.key) := by
  induction os generalizing qty with
  | nil => simp [fill]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h]
    · exact List.Sublist.refl _
    · exact List.Sublist.refl _
    · exact List.Sublist.cons _ (ih (qty - m.qty))
    · exact List.Sublist.refl _

/-- Every order of the side that matching leaves has a quantity from 1 to `maxQty` when every
order of the side it began with has one. -/
theorem fill_qty (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order)
    (h : ∀ o ∈ os, 1 ≤ o.qty ∧ o.qty ≤ maxQty) :
    ∀ o ∈ (fill taker account side limit qty os).others, 1 ≤ o.qty ∧ o.qty ≤ maxQty := by
  induction os generalizing qty with
  | nil => simp [fill]
  | cons m ms ih =>
    have hms : ∀ o ∈ ms, 1 ≤ o.qty ∧ o.qty ≤ maxQty := fun o ho =>
      h o (List.mem_cons_of_mem _ ho)
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, hf⟩ | ⟨_, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ | ⟨_, hlt, _, _, hf⟩ <;> rw [hf]
    · exact h
    · exact h
    · exact ih (qty - m.qty) hms
    · intro o ho
      rcases List.mem_cons.1 ho with rfl | ho
      · have := h m (by simp)
        dsimp only
        omega
      · exact hms o ho

/-- Matching leaves at most the incoming quantity. -/
theorem fill_remaining_le (taker account : UInt64) (side : Side) (limit qty : Nat)
    (os : List Order) : (fill taker account side limit qty os).remaining ≤ qty := by
  induction os generalizing qty with
  | nil => simp [fill]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, hf⟩ | ⟨_, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ <;> rw [hf]
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih _) (Nat.sub_le _ _)
    · exact Nat.zero_le _

/-- Matching that leaves a remaining quantity without self-trade prevention leaves a side whose
first order has a price that the limit does not accept. -/
theorem fill_rest (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order)
    (hr : 0 < (fill taker account side limit qty os).remaining)
    (hs : (fill taker account side limit qty os).selfTrade = false) :
    ∀ m ∈ (fill taker account side limit qty os).others.head?,
      acceptable side limit m.price = false := by
  induction os generalizing qty with
  | nil => simp [fill]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨h1, hf⟩ | ⟨_, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ <;> rw [hf] at hr hs ⊢
    · intro x hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      rcases h1 with h1 | h1
      · simp [h1] at hr
      · exact h1
    · simp at hs
    · exact ih _ hr hs
    · simp at hr

/-- Every event that matching gives is a trade, which has a maker id. -/
theorem fill_maker (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order) :
    ∀ e ∈ (fill taker account side limit qty os).trades, ∃ id, e.maker? = some id := by
  induction os generalizing qty with
  | nil => simp [fill]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, hf⟩ | ⟨_, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ | ⟨_, _, _, _, hf⟩ <;> rw [hf]
    · simp
    · simp
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨m.id, rfl⟩
      · exact ih _ e he
    · simp [Event.maker?]

/-- A side is in priority order exactly when its keys are pairwise in priority order. -/
theorem ordered_iff (side : Side) (l : List Order) :
    Ordered side l ↔ (l.map Order.key).Pairwise (Ahead side) := by
  induction l with
  | nil => simp [Ordered]
  | cons o os ih => simp [Ordered, ih, Ahead, Order.key]

/-- Every price is at least as good as itself. -/
theorem asGood_refl (side : Side) (p : Nat) : asGood side p p = true := by
  cases side <;> simp [asGood]

/-- When `p` is at least as good as `r` but not as good as `q`, `q` is at least as good as `r` and
differs from it. -/
theorem asGood_of_not {side : Side} {p q r : Nat} (h₁ : asGood side p q = false)
    (h₂ : asGood side p r = true) : asGood side q r = true ∧ q ≠ r := by
  cases side <;> simp only [asGood, decide_eq_true_eq, decide_eq_false_iff_not] at h₁ h₂ ⊢ <;>
    exact ⟨by omega, by omega⟩

/-- Placing an order into a side permutes the side with the order in front. -/
theorem place_perm (o : Order) (l : List Order) : (place o l).Perm (o :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons r rs ih =>
    simp only [place]
    split
    · exact (ih.cons r).trans (List.Perm.swap o r rs)
    · exact List.Perm.refl _

/-- Placing an order whose id exceeds every id of a side in priority order for the order's side
keeps the side in priority order. -/
theorem ordered_place (o : Order) (l : List Order) (hl : Ordered o.side l)
    (hid : ∀ r ∈ l, r.id < o.id) : Ordered o.side (place o l) := by
  induction l with
  | nil => simp [place, Ordered]
  | cons r rs ih =>
    simp only [Ordered] at hl
    simp only [place]
    split
    · next hg =>
      simp only [Ordered]
      refine ⟨fun x hx => ?_, ih hl.2 (fun x hx => hid x (List.mem_cons_of_mem _ hx))⟩
      rcases List.mem_cons.1 ((place_perm o rs).mem_iff.1 hx) with rfl | hx
      · exact ⟨hg, fun _ => hid r (by simp)⟩
      · exact hl.1 x hx
    · next hg =>
      simp only [Ordered]
      refine ⟨fun x hx => ?_, hl⟩
      have h3 : asGood o.side r.price x.price = true := by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact asGood_refl _ _
        · exact (hl.1 x hx).1
      obtain ⟨h4, h5⟩ := asGood_of_not (by simpa using hg) h3
      exact ⟨h4, fun h => absurd h h5⟩

/-- The first order of a side in priority order has a price at least as good as every order of
the side. -/
theorem asGood_head {side : Side} {m : Order} {l : List Order} (h : Ordered side (m :: l)) :
    ∀ y ∈ m :: l, asGood side m.price y.price = true := by
  simp only [Ordered] at h
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact asGood_refl _ _
  · exact (h.1 y hy).1

/-- In a valid book, every bid's price lies below every ask's price. -/
theorem below {b : Book} (h : Valid b) : ∀ x ∈ b.bids, ∀ y ∈ b.asks, x.price < y.price := by
  intro x hx y hy
  have hbo := h.bidsOrdered
  have hao := h.asksOrdered
  have hnc := h.notCrossed
  cases hb : b.bids with
  | nil => simp [hb] at hx
  | cons bh bt =>
    cases ha : b.asks with
    | nil => simp [ha] at hy
    | cons ah ta =>
      rw [hb] at hx hbo hnc
      rw [ha] at hy hao hnc
      have h1 := hnc bh rfl ah rfl
      have h2 := asGood_head hbo x hx
      have h3 := asGood_head hao y hy
      simp only [asGood, decide_eq_true_eq] at h2 h3
      omega

/-- Sides whose every bid lies below every ask have a best bid below the best ask. -/
theorem notCrossed_of_below {bids asks : List Order}
    (h : ∀ x ∈ bids, ∀ y ∈ asks, x.price < y.price) :
    ∀ bid ∈ bids.head?, ∀ ask ∈ asks.head?, bid.price < ask.price :=
  fun x hx y hy => h x (List.mem_of_mem_head? hx) y (List.mem_of_mem_head? hy)

/-- An order of a list whose keys form a sublist of another list's keys has the side, price, and
id of an order of the other list. -/
theorem exists_key {l' l : List Order} (h : (l'.map Order.key).Sublist (l.map Order.key))
    {o : Order} (ho : o ∈ l') : ∃ x ∈ l, x.side = o.side ∧ x.price = o.price ∧ x.id = o.id := by
  obtain ⟨x, hx, hk⟩ := List.mem_map.1 (h.subset (List.mem_map_of_mem ho))
  simp only [Order.key, Prod.mk.injEq] at hk
  exact ⟨x, hx, hk⟩

/-- A book is valid when the keys of its sides form sublists of the keys of a valid book's sides,
its quantities lie from 1 to `maxQty`, and its next id is at least the valid book's. -/
theorem valid_of_keys {b b' : Book} (h : Valid b)
    (hb : (b'.bids.map Order.key).Sublist (b.bids.map Order.key))
    (ha : (b'.asks.map Order.key).Sublist (b.asks.map Order.key))
    (hq : ∀ o ∈ b'.bids ++ b'.asks, 1 ≤ o.qty ∧ o.qty ≤ maxQty)
    (hn : b.nextId.toNat ≤ b'.nextId.toNat) : Valid b' := by
  have hmem : ∀ o ∈ b'.bids ++ b'.asks, ∃ x ∈ b.bids ++ b.asks,
      x.side = o.side ∧ x.price = o.price ∧ x.id = o.id := by
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨x, hx, hk⟩ := exists_key hb ho
      exact ⟨x, List.mem_append_left _ hx, hk⟩
    · obtain ⟨x, hx, hk⟩ := exists_key ha ho
      exact ⟨x, List.mem_append_right _ hx, hk⟩
  have hids : ∀ l : List Order, l.map (·.id) = (l.map Order.key).map (fun k => k.2.2) := by
    intro l
    simp [List.map_map, Function.comp_def, Order.key]
  refine
    { bidsOrdered := (ordered_iff _ _).2 (((ordered_iff _ _).1 h.bidsOrdered).sublist hb)
      asksOrdered := (ordered_iff _ _).2 (((ordered_iff _ _).1 h.asksOrdered).sublist ha)
      bidSide := ?_
      askSide := ?_
      price := ?_
      qty := hq
      ids := ?_
      distinct := ?_
      bounded := ?_
      notCrossed := ?_
      nextPositive := by have := h.nextPositive; omega }
  · intro o ho
    obtain ⟨x, hx, hs, -, -⟩ := exists_key hb ho
    rw [← hs]
    exact h.bidSide x hx
  · intro o ho
    obtain ⟨x, hx, hs, -, -⟩ := exists_key ha ho
    rw [← hs]
    exact h.askSide x hx
  · intro o ho
    obtain ⟨x, hx, -, hp, -⟩ := hmem o ho
    rw [← hp]
    exact h.price x hx
  · intro o ho
    obtain ⟨x, hx, -, -, hi⟩ := hmem o ho
    have := h.ids x hx
    rw [hi] at this
    omega
  · have hs : ((b'.bids ++ b'.asks).map (·.id)).Sublist ((b.bids ++ b.asks).map (·.id)) := by
      have := (hb.append ha).map (fun k : Side × Nat × UInt64 => k.2.2)
      rw [← List.map_append, ← List.map_append, ← hids, ← hids] at this
      exact this
    exact hs.nodup h.distinct
  · have h1 := hb.length_le
    have h2 := ha.length_le
    simp only [List.length_map] at h1 h2
    have := h.bounded
    omega
  · apply notCrossed_of_below
    intro x hx y hy
    obtain ⟨x', hx', -, hpx, -⟩ := exists_key hb hx
    obtain ⟨y', hy', -, hpy, -⟩ := exists_key ha hy
    rw [← hpx, ← hpy]
    exact below h x' hx' y' hy'

/-- The opposite side of a book does not depend on its next id. -/
theorem opposite_nextId (b : Book) (n : UInt64) (side : Side) :
    opposite { b with nextId := n } side = opposite b side := by
  cases side <;> rfl

/-- The opposite side of a book whose opposite side is replaced is the replacement. -/
theorem opposite_setOpposite (b : Book) (side : Side) (os : List Order) :
    opposite (setOpposite b side os) side = os := by
  cases side <;> rfl

/-- Replacing the opposite side keeps the next id. -/
theorem setOpposite_nextId (b : Book) (side : Side) (os : List Order) :
    (setOpposite b side os).nextId = b.nextId := by
  cases side <;> rfl

/-- Resting an order keeps the next id. -/
theorem rest_nextId (b : Book) (o : Order) : (rest b o).nextId = b.nextId := by
  unfold rest
  split <;> rfl

/-- Every order of the opposite side belongs to the book. -/
theorem mem_of_opposite {b : Book} {side : Side} {o : Order} (h : o ∈ opposite b side) :
    o ∈ b.bids ++ b.asks := by
  cases side
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ h

/-- Every order of a book whose opposite side is replaced belongs to the book or to the new
side. -/
theorem mem_setOpposite {b : Book} {side : Side} {os : List Order} {o : Order}
    (h : o ∈ (setOpposite b side os).bids ++ (setOpposite b side os).asks) :
    o ∈ b.bids ++ b.asks ∨ o ∈ os := by
  cases side <;> simp only [setOpposite, List.mem_append] at h ⊢ <;> rcases h with h | h <;>
    simp [h]

/-- Replacing the opposite side of a valid book by a side whose keys form a sublist of its keys
and whose quantities lie from 1 to `maxQty`, with a next id at least the book's, keeps the book
valid. -/
theorem valid_setOpposite {b : Book} (h : Valid b) (side : Side) {os : List Order} {n : UInt64}
    (hk : (os.map Order.key).Sublist ((opposite b side).map Order.key))
    (hq : ∀ o ∈ os, 1 ≤ o.qty ∧ o.qty ≤ maxQty) (hn : b.nextId.toNat ≤ n.toNat) :
    Valid (setOpposite { b with nextId := n } side os) := by
  cases side
  · refine valid_of_keys h (List.Sublist.refl _) hk ?_ hn
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact h.qty o (List.mem_append_left _ ho)
    · exact hq o ho
  · refine valid_of_keys h hk (List.Sublist.refl _) ?_ hn
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hq o ho
    · exact h.qty o (List.mem_append_right _ ho)

/-- Resting an order on a valid book with room keeps it valid when the order's id exceeds every
id of the book and lies below the next id, its price and quantity lie in their ranges, and the
first opposite order has a price that the order does not accept. -/
theorem valid_rest {b : Book} {o : Order} (h : Valid b)
    (hid : ∀ x ∈ b.bids ++ b.asks, x.id.toNat < o.id.toNat) (hid0 : 0 < o.id.toNat)
    (hidn : o.id.toNat < b.nextId.toNat) (hp : 1 ≤ o.price ∧ o.price ≤ maxPrice)
    (hq : 1 ≤ o.qty ∧ o.qty ≤ maxQty) (hs : size b < capacity)
    (hc : ∀ m ∈ (opposite b o.side).head?, acceptable o.side o.price m.price = false) :
    Valid (rest b o) := by
  have hlt : ∀ x ∈ b.bids ++ b.asks, x.id < o.id := fun x hx =>
    UInt64.lt_iff_toNat_lt.2 (hid x hx)
  have hmem : ∀ x l, x ∈ place o l ↔ x = o ∨ x ∈ l := fun x l => by
    rw [(place_perm o l).mem_iff, List.mem_cons]
  have hnot : o.id ∉ (b.bids ++ b.asks).map (·.id) := by
    intro hm
    obtain ⟨x, hx, he⟩ := List.mem_map.1 hm
    have := hid x hx
    rw [he] at this
    omega
  have hperm : ((rest b o).bids ++ (rest b o).asks).Perm (o :: (b.bids ++ b.asks)) := by
    unfold rest
    split
    · exact (place_perm o b.bids).append_right b.asks
    · exact ((place_perm o b.asks).append_left b.bids).trans List.perm_middle
  have hnew : ∀ x ∈ (rest b o).bids ++ (rest b o).asks, x = o ∨ x ∈ b.bids ++ b.asks :=
    fun x hx => List.mem_cons.1 (hperm.mem_iff.1 hx)
  have hlen := hperm.length_eq
  simp only [List.length_append, List.length_cons] at hlen
  have hsides : Ordered .buy (rest b o).bids ∧ Ordered .sell (rest b o).asks ∧
      (∀ x ∈ (rest b o).bids, x.side = .buy) ∧ (∀ x ∈ (rest b o).asks, x.side = .sell) ∧
      ∀ x ∈ (rest b o).bids, ∀ y ∈ (rest b o).asks, x.price < y.price := by
    rcases hs' : o.side with _ | _
    · have hr : rest b o = { b with bids := place o b.bids } := by simp [rest, hs']
      rw [hr]
      rw [hs'] at hc
      simp only [opposite] at hc
      refine ⟨?_, h.asksOrdered, ?_, h.askSide, ?_⟩
      · have := ordered_place o b.bids (by rw [hs']; exact h.bidsOrdered)
          (fun x hx => hlt x (List.mem_append_left _ hx))
        rwa [hs'] at this
      · intro x hx
        rcases (hmem x _).1 hx with rfl | hx
        · exact hs'
        · exact h.bidSide x hx
      · intro x hx y hy
        rcases (hmem x _).1 hx with rfl | hx
        · have hao := h.asksOrdered
          cases ha : b.asks with
          | nil => rw [ha] at hy; simp at hy
          | cons ah ta =>
            rw [ha] at hy hc hao
            have h1 := hc ah rfl
            have h2 := asGood_head hao y hy
            simp only [acceptable, asGood, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2
            omega
        · exact below h x hx y hy
    · have hr : rest b o = { b with asks := place o b.asks } := by simp [rest, hs']
      rw [hr]
      rw [hs'] at hc
      simp only [opposite] at hc
      refine ⟨h.bidsOrdered, ?_, h.bidSide, ?_, ?_⟩
      · have := ordered_place o b.asks (by rw [hs']; exact h.asksOrdered)
          (fun x hx => hlt x (List.mem_append_right _ hx))
        rwa [hs'] at this
      · intro x hx
        rcases (hmem x _).1 hx with rfl | hx
        · exact hs'
        · exact h.askSide x hx
      · intro x hx y hy
        rcases (hmem y _).1 hy with rfl | hy
        · have hbo := h.bidsOrdered
          cases hb : b.bids with
          | nil => rw [hb] at hx; simp at hx
          | cons bh tb =>
            rw [hb] at hx hc hbo
            have h1 := hc bh rfl
            have h2 := asGood_head hbo x hx
            simp only [acceptable, asGood, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2
            omega
        · exact below h x hx y hy
  refine
    { bidsOrdered := hsides.1
      asksOrdered := hsides.2.1
      bidSide := hsides.2.2.1
      askSide := hsides.2.2.2.1
      price := fun x hx => ?_
      qty := fun x hx => ?_
      ids := fun x hx => ?_
      distinct := (hperm.map _).nodup_iff.2 (List.nodup_cons.2 ⟨hnot, h.distinct⟩)
      bounded := ?_
      notCrossed := notCrossed_of_below hsides.2.2.2.2
      nextPositive := by rw [rest_nextId]; exact h.nextPositive }
  · rcases hnew x hx with rfl | hx
    · exact hp
    · exact h.price x hx
  · rcases hnew x hx with rfl | hx
    · exact hq
    · exact h.qty x hx
  · rw [rest_nextId]
    rcases hnew x hx with rfl | hx
    · exact ⟨hid0, hidn⟩
    · exact h.ids x hx
  · simp only [size] at hs
    omega

/-- Removing the orders with an id keeps a valid book valid. -/
theorem valid_remove {b : Book} (h : Valid b) (id : UInt64) : Valid (remove b id) := by
  refine valid_of_keys h (List.filter_sublist.map _) (List.filter_sublist.map _) ?_
    (Nat.le_refl _)
  intro o ho
  simp only [remove, List.mem_append, List.mem_filter] at ho
  rcases ho with ho | ho
  · exact h.qty o (List.mem_append_left _ ho.1)
  · exact h.qty o (List.mem_append_right _ ho.1)

/-- Setting the quantity of the orders with an id to a quantity from 1 to `maxQty` keeps a valid
book valid. -/
theorem valid_setQty {b : Book} (h : Valid b) (id : UInt64) {q : Nat}
    (hq : 1 ≤ q ∧ q ≤ maxQty) : Valid (setQty b id q) := by
  have hk : ∀ l : List Order,
      (l.map (fun o => if o.id = id then { o with qty := q } else o)).map Order.key =
        l.map Order.key := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro o _
    simp only [Function.comp_apply]
    split <;> rfl
  refine valid_of_keys h (by simp only [setQty, hk, List.Sublist.refl])
    (by simp only [setQty, hk, List.Sublist.refl]) ?_ (Nat.le_refl _)
  intro o ho
  simp only [setQty, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · split
    · exact hq
    · exact h.qty x (List.mem_append_left _ hx)
  · split
    · exact hq
    · exact h.qty x (List.mem_append_right _ hx)

/-- Submitting an order with a price from 1 to `maxPrice` and a quantity of at most `maxQty`
keeps a valid book valid when its next id lies below 2^64 - 1. -/
theorem valid_submit {b : Book} (h : Valid b) (hn : b.nextId.toNat < 2 ^ 64 - 1) (side : Side)
    {limit qty : Nat} (account tag : UInt64) (tif : Tif) (hl : 1 ≤ limit ∧ limit ≤ maxPrice)
    (hq : qty ≤ maxQty) : Valid (submit b side limit qty account tag tif).1 := by
  have hn1 : (b.nextId + 1).toNat = b.nextId.toNat + 1 := by
    rw [UInt64.toNat_add]
    simp
    omega
  have hk := fill_keys b.nextId account side limit qty (opposite b side)
  have hqty := fill_qty b.nextId account side limit qty (opposite b side)
    (fun o ho => h.qty o (mem_of_opposite ho))
  have hle := fill_remaining_le b.nextId account side limit qty (opposite b side)
  have hst := fill_rest b.nextId account side limit qty (opposite b side)
  simp only [submit, opposite_nextId]
  generalize fill b.nextId account side limit qty (opposite b side) = F at hk hqty hle hst ⊢
  have hb2 : Valid (setOpposite { b with nextId := b.nextId + 1 } side F.others) :=
    valid_setOpposite h side hk hqty (by omega)
  split
  · exact hb2
  rename_i h0
  split
  · exact hb2
  rename_i hs
  split
  · exact hb2
  split
  · rename_i hc
    refine valid_rest hb2 ?_ h.nextPositive ?_ hl ⟨?_, ?_⟩ hc ?_
    · intro x hx
      rcases mem_setOpposite hx with hx | hx
      · exact (h.ids x hx).2
      · obtain ⟨y, hy, -, -, hid⟩ := exists_key hk hx
        rw [← hid]
        exact (h.ids y (mem_of_opposite hy)).2
    · simp only [setOpposite_nextId]
      omega
    · first | omega | (simp only; omega)
    · first | omega | (simp only; omega)
    · simp only [opposite_setOpposite]
      exact hst (by omega) (by simpa using hs)
  · exact hb2

/-- A word lies outside a range exactly when its number does not lie from the lower bound to the
upper bound. -/
theorem inRange_false (lo hi : Nat) (w : UInt64) :
    inRange lo hi w = false ↔ ¬(lo ≤ w.toNat ∧ w.toNat ≤ hi) := by
  simp [inRange]

/-- A step rejects with the book unchanged and the kind and reference words of the requirements,
submits an order with a price from 1 to `maxPrice` and a quantity of at most `maxQty`, cancels an
order that `find` returns, or reduces an order that `find` returns to a quantity from 1 to
`maxQty`. -/
theorem step_cases (b : Book) (r : Array UInt64) :
    (∃ k ref reason, step b r = (b, [.rejected k ref reason]) ∧
        if r.size = 7 then k = r[0]! ∧ ref = refWord r else k = 0 ∧ ref = 0) ∨
      (∃ side limit qty account tag tif, 1 ≤ limit ∧ limit ≤ maxPrice ∧ qty ≤ maxQty ∧
        step b r = submit b side limit qty account tag tif) ∨
      (∃ o, find b r[1]! = some o ∧
        step b r = (remove b r[1]!, [.cancelled r[1]! o.qty .requested])) ∨
      (∃ o, find b r[1]! = some o ∧ 1 ≤ r[3]!.toNat ∧ r[3]!.toNat ≤ maxQty ∧
        step b r = (setQty b r[1]! r[3]!.toNat, [.reduced r[1]! r[3]!.toNat])) := by
  generalize hp : step b r = p
  simp only [step] at hp
  repeat' split at hp
  all_goals subst hp
  all_goals first
    | exact Or.inl ⟨_, _, _, rfl, by simp_all [refWord]⟩
    | exact Or.inr (Or.inl ⟨_, _, _, _, _, _, by simp_all [inRange_false, maxPrice],
        by simp_all [inRange_false, maxPrice],
        by simp_all [inRange_false], rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, by assumption, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, by assumption, by simp_all [inRange_false],
        by simp_all [inRange_false], rfl⟩))

/-- A step keeps a book valid when the next id lies below 2^64 - 1. -/
theorem step_valid {b : Book} (h : Valid b) (hn : b.nextId.toNat < 2 ^ 64 - 1)
    (r : Array UInt64) : Valid (step b r).1 := by
  rcases step_cases b r with ⟨k, ref, reason, he, -⟩ |
      ⟨side, limit, qty, account, tag, tif, hl1, hl2, hq, he⟩ | ⟨o, -, he⟩ |
      ⟨o, -, hq1, hq2, he⟩ <;> rw [he]
  · exact h
  · exact valid_submit h hn side account tag tif ⟨hl1, hl2⟩ hq
  · exact valid_remove h _
  · exact valid_setQty h _ ⟨hq1, hq2⟩

/-- An accepted order advances the next id by 1. -/
theorem submit_nextId (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64)
    (tif : Tif) : (submit b side limit qty account tag tif).1.nextId = b.nextId + 1 := by
  simp only [submit]
  repeat' split
  all_goals simp only [rest_nextId, setOpposite_nextId]

/-- The events of an accepted order are its `accepted` event followed by events that are neither
`accepted` nor `rejected`. -/
theorem submit_events (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64)
    (tif : Tif) :
    ∃ es, (submit b side limit qty account tag tif).2 = .accepted b.nextId tag :: es ∧
      ∀ e ∈ es, e.isAccepted = false ∧ ∀ k ref reason, e ≠ .rejected k ref reason := by
  have hm := fill_maker b.nextId account side limit qty (opposite b side)
  simp only [submit, opposite_nextId]
  generalize fill b.nextId account side limit qty (opposite b side) = F at hm ⊢
  have ht : ∀ e ∈ F.trades,
      e.isAccepted = false ∧ ∀ k ref reason, e ≠ .rejected k ref reason := by
    intro e he
    obtain ⟨id, hid⟩ := hm e he
    cases e <;> simp_all [Event.maker?, Event.isAccepted]
  have hc : ∀ reason, ∀ e ∈ F.trades ++ [.cancelled b.nextId F.remaining reason],
      e.isAccepted = false ∧ ∀ k ref reason, e ≠ .rejected k ref reason := by
    intro reason e he
    rcases List.mem_append.1 he with he | he
    · exact ht e he
    · rw [List.mem_singleton] at he
      subst he
      simp [Event.isAccepted]
  repeat' split
  all_goals first
    | exact ⟨_, rfl, ht⟩
    | exact ⟨_, rfl, hc _⟩

/-- A step advances the next id by 1 exactly when its first event is `accepted`. -/
theorem step_nextId (b : Book) (r : Array UInt64) :
    (step b r).1.nextId =
      if (step b r).2.head?.any Event.isAccepted then b.nextId + 1 else b.nextId := by
  rcases step_cases b r with ⟨k, ref, reason, he, -⟩ |
      ⟨side, limit, qty, account, tag, tif, -, -, -, he⟩ | ⟨o, -, he⟩ | ⟨o, -, -, -, he⟩ <;>
    rw [he]
  · simp [Event.isAccepted]
  · obtain ⟨es, hes, -⟩ := submit_events b side limit qty account tag tif
    rw [hes, submit_nextId]
    simp [Event.isAccepted]
  · simp [remove, Event.isAccepted]
  · simp [setQty, Event.isAccepted]

/-- An `accepted` event gives the next id and comes first. -/
theorem step_accepted {b : Book} {r : Array UInt64} {id tag : UInt64}
    (he : Event.accepted id tag ∈ (step b r).2) :
    id = b.nextId ∧ (step b r).2.head? = some (.accepted id tag) := by
  rcases step_cases b r with ⟨k, ref, reason, hs, -⟩ |
      ⟨side, limit, qty, account, tag', tif, -, -, -, hs⟩ | ⟨o, -, hs⟩ | ⟨o, -, -, -, hs⟩ <;>
    rw [hs] at he ⊢
  · simp at he
  · obtain ⟨es, hes, hr⟩ := submit_events b side limit qty account tag' tif
    rw [hes] at he ⊢
    rcases List.mem_cons.1 he with he | he
    · simp only [Event.accepted.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, rfl⟩
    · have := (hr _ he).1
      simp [Event.isAccepted] at this
  · simp at he
  · simp at he

/-- One record of a run: the book after the record's step, and the events so far followed by the
step's events. -/
def runStep (acc : Book × List Event) (r : Array UInt64) : Book × List Event :=
  ((step acc.1 r).1, acc.2 ++ (step acc.1 r).2)

/-- A run folds `runStep` over the records from the book and no events. -/
theorem run_eq (b : Book) (ws : List UInt64) : run b ws = (records ws).foldl runStep (b, []) :=
  rfl

/-- Folding `runStep` over records keeps a book valid when the next id plus the number of records
is at most 2^64 - 1. -/
theorem foldl_valid (rs : List (Array UInt64)) (b : Book) (es : List Event) (h : Valid b)
    (hn : b.nextId.toNat + rs.length ≤ 2 ^ 64 - 1) : Valid (rs.foldl runStep (b, es)).1 := by
  induction rs generalizing b es with
  | nil => exact h
  | cons r rs ih =>
    simp only [List.foldl_cons, runStep]
    simp only [List.length_cons] at hn
    have hn' : b.nextId.toNat < 2 ^ 64 - 1 := by omega
    apply ih _ _ (step_valid h hn' r)
    have := step_nextId b r
    split at this <;> rw [this]
    · rw [UInt64.toNat_add]
      simp
      omega
    · omega

/-- A stream keeps a book valid when the next id plus the number of records is at most
2^64 - 1, since each record accepts at most one order. -/
theorem run_valid {b : Book} (h : Valid b) (ws : List UInt64)
    (hn : b.nextId.toNat + (records ws).length ≤ 2 ^ 64 - 1) : Valid (run b ws).1 := by
  rw [run_eq]
  exact foldl_valid _ _ _ h hn

theorem run_empty_valid (ws : List UInt64) (hn : (records ws).length < 2 ^ 64 - 1) :
    Valid (run empty ws).1 :=
  run_valid empty_valid ws (by simp [empty]; omega)

/-! ## Matching -/

/-- Matching exhausts a prefix `pre` of the opposite side and then either stops or trades part of
the next order `m`, which keeps its place with a smaller remaining quantity.  Each order that it
trades with has a price that the limit accepts and another account, and each trade takes place at
the resting order's price. -/
theorem fill_shape (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order) :
    ∃ pre post, os = pre ++ post ∧
      (∀ m ∈ pre, acceptable side limit m.price = true ∧ m.account ≠ account) ∧
      ((fill taker account side limit qty os).trades = pre.map (exhaust taker) ∧
          (fill taker account side limit qty os).others = post ∨
        ∃ m rest q, post = m :: rest ∧ 0 < q ∧ q < m.qty ∧
          acceptable side limit m.price = true ∧ m.account ≠ account ∧
          (fill taker account side limit qty os).trades =
            pre.map (exhaust taker) ++ [.trade m.id taker m.price q m.account (m.qty - q)] ∧
          (fill taker account side limit qty os).others = { m with qty := m.qty - q } :: rest) := by
  induction os generalizing qty with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl ⟨by simp [fill], by simp [fill]⟩⟩
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, ha, hacc, _, h⟩ | ⟨hpos, hlt, ha, hacc, h⟩ <;> rw [h]
    · exact ⟨[], m :: ms, rfl, by simp, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨[], m :: ms, rfl, by simp, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨pre, post, hos, hpre, hr⟩ := ih (qty - m.qty)
      refine ⟨m :: pre, post, by simp [hos], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨ha, hacc⟩
        · exact hpre x hx
      · rcases hr with ⟨ht, ho⟩ | ⟨m', rest, q, hpost, hq0, hq1, ha', hacc', ht, ho⟩
        · exact Or.inl ⟨by simp [ht], ho⟩
        · exact Or.inr ⟨m', rest, q, hpost, hq0, hq1, ha', hacc', by simp [ht], ho⟩
    · exact ⟨[], m :: ms, rfl, by simp,
        Or.inr ⟨m, ms, qty, rfl, hpos, hlt, ha, hacc, by simp, rfl⟩⟩

/-- The maker ids of the trades that exhaust a list of orders are the orders' ids. -/
theorem filterMap_exhaust (taker : UInt64) (pre : List Order) :
    (pre.map (exhaust taker)).filterMap Event.maker? = pre.map (·.id) := by
  induction pre with
  | nil => rfl
  | cons m ms ih => simp [exhaust, Event.maker?, ih]

/-- The makers of matching's trades, in order, are the first orders of the opposite side. -/
theorem fill_prefix (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order) :
    (fill taker account side limit qty os).trades.filterMap Event.maker? <+: os.map (·.id) := by
  obtain ⟨pre, post, hos, -, h⟩ := fill_shape taker account side limit qty os
  rcases h with ⟨ht, -⟩ | ⟨m, rest, q, hpost, -, -, -, -, ht, -⟩
  · rw [ht, hos, filterMap_exhaust, List.map_append]
    exact List.prefix_append _ _
  · rw [ht, hos, hpost, List.filterMap_append, filterMap_exhaust, List.map_append]
    exact List.prefix_append_right_inj _ |>.2 (by simp [Event.maker?])

/-- The incoming order's quantity is its traded quantity plus its remaining quantity. -/
theorem fill_traded (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order) :
    traded (fill taker account side limit qty os).trades +
      (fill taker account side limit qty os).remaining = qty := by
  induction os generalizing qty with
  | nil => simp [fill, traded]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, hle, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h]
    · simp [traded]
    · simp [traded]
    · have := ih (qty - m.qty)
      simp only [traded, List.map_cons, List.sum_cons] at this ⊢
      simp only [exhaust, Event.tradeQty]
      omega
    · simp [traded, Event.tradeQty]

/-- The opposite side loses exactly the traded quantity. -/
theorem fill_total (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order) :
    total (fill taker account side limit qty os).others +
      traded (fill taker account side limit qty os).trades = total os := by
  induction os generalizing qty with
  | nil => simp [fill, traded, total]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, hle, h⟩ | ⟨_, hlt, _, _, h⟩ <;> rw [h]
    · simp [traded]
    · simp [traded]
    · have := ih (qty - m.qty)
      simp only [traded, total, List.map_cons, List.sum_cons] at this ⊢
      simp only [exhaust, Event.tradeQty]
      omega
    · simp only [traded, total, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        Event.tradeQty]
      omega

/-- Matching that leaves a remaining quantity stopped at a resting order of the incoming order's
account with an acceptable price, or at an empty side or an unacceptable price. -/
theorem fill_stop (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order)
    (hr : 0 < (fill taker account side limit qty os).remaining) :
    ((fill taker account side limit qty os).selfTrade = true ∧
        ∃ m ∈ (fill taker account side limit qty os).others.head?,
          acceptable side limit m.price = true ∧ m.account = account) ∨
      ((fill taker account side limit qty os).selfTrade = false ∧
        ∀ m ∈ (fill taker account side limit qty os).others.head?,
          acceptable side limit m.price = false) := by
  induction os generalizing qty with
  | nil => simp [fill]
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨h1, h⟩ | ⟨_, ha, hacc, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h] at hr ⊢
    · right
      have : acceptable side limit m.price = false := by
        rcases h1 with h1 | h1
        · simp [h1] at hr
        · exact h1
      simp [this]
    · left
      exact ⟨rfl, m, rfl, ha, hacc⟩
    · exact ih (qty - m.qty) hr
    · simp at hr

/-- Self-trade prevention stops matching only with a remaining quantity. -/
theorem fill_selfTrade (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order)
    (hs : (fill taker account side limit qty os).selfTrade = true) :
    0 < (fill taker account side limit qty os).remaining := by
  induction os generalizing qty with
  | nil => simp [fill] at hs
  | cons m ms ih =>
    rcases fill_cases taker account side limit qty m ms with
      ⟨_, h⟩ | ⟨hq, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h] at hs ⊢
    · simp at hs
    · simp only
      omega
    · exact ih (qty - m.qty) hs
    · simp at hs

/-- The opposite side of a book with an order of `side` resting on it is the book's opposite
side. -/
theorem rest_opposite (b : Book) (id account : UInt64) (side : Side) (limit q : Nat) :
    opposite (rest b ⟨id, account, side, limit, q⟩) side = opposite b side := by
  cases side <;> rfl

/-- A resting order belongs to the book it rests on. -/
theorem mem_rest (b : Book) (o : Order) : o ∈ (rest b o).bids ++ (rest b o).asks := by
  unfold rest
  split
  · exact List.mem_append_left _ ((place_perm o b.bids).mem_iff.2 (by simp))
  · exact List.mem_append_right _ ((place_perm o b.asks).mem_iff.2 (by simp))

/-- The last event of a list that ends with an event is that event. -/
theorem getLast?_cons_append (a x : Event) (l : List Event) :
    (a :: l ++ [x]).getLast? = some x :=
  List.getLast?_concat

/-- An accepted order's quantity is its traded quantity plus its remaining quantity, and a positive
remaining quantity either rests in the book under the order's id or appears in the order's
`cancelled` event, its last event. -/
theorem submit_conserves (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64)
    (tif : Tif) :
    traded (submit b side limit qty account tag tif).2 +
        (fill b.nextId account side limit qty (opposite b side)).remaining = qty ∧
      ((fill b.nextId account side limit qty (opposite b side)).remaining = 0 ∨
        (∃ reason, (submit b side limit qty account tag tif).2.getLast? =
          some (.cancelled b.nextId
            (fill b.nextId account side limit qty (opposite b side)).remaining reason)) ∨
        ∃ o ∈ (submit b side limit qty account tag tif).1.bids ++
            (submit b side limit qty account tag tif).1.asks,
          o.id = b.nextId ∧
            o.qty = (fill b.nextId account side limit qty (opposite b side)).remaining) := by
  have ht := fill_traded b.nextId account side limit qty (opposite b side)
  simp only [submit, opposite_nextId]
  generalize fill b.nextId account side limit qty (opposite b side) = F at ht ⊢
  have h0 : traded (.accepted b.nextId tag :: F.trades) = traded F.trades := by
    simp [traded, Event.tradeQty]
  have h1 : ∀ reason, traded (.accepted b.nextId tag :: F.trades ++
      [.cancelled b.nextId F.remaining reason]) = traded F.trades := by
    intro reason
    simp [traded, Event.tradeQty, List.sum_append]
  split
  · exact ⟨by rw [h0]; exact ht, Or.inl (by assumption)⟩
  split
  · exact ⟨by rw [h1]; exact ht, Or.inr (Or.inl ⟨.selfTrade, getLast?_cons_append _ _ _⟩)⟩
  split
  · exact ⟨by rw [h1]; exact ht, Or.inr (Or.inl ⟨.ioc, getLast?_cons_append _ _ _⟩)⟩
  split
  · exact ⟨by rw [h0]; exact ht, Or.inr (Or.inr ⟨_, mem_rest _ _, rfl, rfl⟩)⟩
  · exact ⟨by rw [h1]; exact ht, Or.inr (Or.inl ⟨.bookFull, getLast?_cons_append _ _ _⟩)⟩

/-- The opposite side loses exactly the quantity that an accepted order trades. -/
theorem submit_opposite (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64)
    (tif : Tif) :
    total (opposite (submit b side limit qty account tag tif).1 side) +
      traded (submit b side limit qty account tag tif).2 = total (opposite b side) := by
  have ht := fill_total b.nextId account side limit qty (opposite b side)
  simp only [submit, opposite_nextId]
  generalize fill b.nextId account side limit qty (opposite b side) = F at ht ⊢
  have h0 : traded (.accepted b.nextId tag :: F.trades) = traded F.trades := by
    simp [traded, Event.tradeQty]
  have h1 : ∀ reason, traded (.accepted b.nextId tag :: F.trades ++
      [.cancelled b.nextId F.remaining reason]) = traded F.trades := by
    intro reason
    simp [traded, Event.tradeQty, List.sum_append]
  repeat' split
  all_goals simp only [rest_opposite, opposite_setOpposite, h0, h1]
  all_goals exact ht

/-! ## Cancel and reduce -/

/-- A list whose ids are distinct holds at most one order with each id. -/
theorem eq_of_nodup {l : List Order} (h : (l.map (·.id)).Nodup) {x y : Order} (hx : x ∈ l)
    (hy : y ∈ l) (he : x.id = y.id) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd (List.mem_map.2 ⟨y, hy, he.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨x, hx, he⟩) h.1
    · exact ih h.2 hx hy

/-- In a valid book, two orders with one id are the same order. -/
theorem eq_of_id {b : Book} (h : Valid b) {x y : Order} (hx : x ∈ b.bids ++ b.asks)
    (hy : y ∈ b.bids ++ b.asks) (he : x.id = y.id) : x = y :=
  eq_of_nodup h.distinct hx hy he

/-- In a valid book, `find` returns each order of the book under its id. -/
theorem find_of_mem {b : Book} (h : Valid b) {o : Order} (ho : o ∈ b.bids ++ b.asks) :
    find b o.id = some o := by
  unfold find
  cases hf : (b.bids ++ b.asks).find? (·.id == o.id) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf o ho)
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hxid := List.find?_some hf
    simp only [beq_iff_eq] at hxid
    rw [eq_of_id h hx ho hxid]

/-- An order that `find` returns belongs to the book and has the id. -/
theorem find_mem {b : Book} {id : UInt64} {o : Order} (h : find b id = some o) :
    o ∈ b.bids ++ b.asks ∧ o.id = id :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- Filtering out an order's id from a list with distinct ids, in which only that order has the
id, erases the order. -/
theorem filter_id_eq_erase {l : List Order} {o : Order} (hn : (l.map (·.id)).Nodup)
    (hu : ∀ x ∈ l, x.id = o.id → x = o) : l.filter (·.id != o.id) = l.erase o := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hx : x.id = o.id
    · have := hu x (by simp) hx
      subst this
      rw [List.erase_cons_head, List.filter_cons_of_neg (by simp), List.filter_eq_self]
      intro y hy
      have : y.id ≠ x.id := fun he => hn.1 (List.mem_map.2 ⟨y, hy, he⟩)
      simpa using this
    · have hne : ¬(x == o) = true := by
        simp only [beq_iff_eq]
        rintro rfl
        exact hx rfl
      rw [List.filter_cons_of_pos (by simpa using hx), List.erase_cons_tail hne,
        ih hn.2 (fun y hy => hu y (List.mem_cons_of_mem _ hy))]

/-- Setting the quantity of the orders with an order's id, in a list in which only that order has
the id, replaces that order. -/
theorem map_setQty {l : List Order} {o : Order} {q : Nat} (hu : ∀ x ∈ l, x.id = o.id → x = o) :
    l.map (fun x => if x.id = o.id then { x with qty := q } else x) =
      l.map (fun x => if x = o then { o with qty := q } else x) := by
  apply List.map_congr_left
  intro x hx
  by_cases he : x.id = o.id
  · have := hu x hx he
    subst this
    simp
  · have : x ≠ o := fun h => he (h ▸ rfl)
    simp [he, this]

/-- A cancel record whose order `find` returns with the record's account removes the order. -/
theorem step_cancel_eq {b : Book} {r : Array UInt64} (hr : r.size = 7) (hk : r[0]! = 3)
    {o : Order} (hf : find b r[1]! = some o) (ha : o.account = r[2]!) :
    step b r = (remove b r[1]!, [.cancelled r[1]! o.qty .requested]) := by
  simp_all [step]

/-- A reduce record whose order `find` returns with the record's account, and whose new quantity
lies from 1 to `maxQty` below the order's, sets the order's quantity. -/
theorem step_reduce_eq {b : Book} {r : Array UInt64} (hr : r.size = 7) (hk : r[0]! = 4)
    {o : Order} (hf : find b r[1]! = some o) (ha : o.account = r[2]!)
    (hq : inRange 1 maxQty r[3]! = true) (hle : ¬o.qty ≤ r[3]!.toNat) :
    step b r = (setQty b r[1]! r[3]!.toNat, [.reduced r[1]! r[3]!.toNat]) := by
  simp_all [step]
  intro h'
  exact absurd h' (by omega)

/-- A cancel that passes its checks removes exactly the order that it names. -/
theorem step_cancel {b : Book} (h : Valid b) {r : Array UInt64} (hr : r.size = 7)
    (hk : r[0]! = 3) {o : Order} (ho : o ∈ b.bids ++ b.asks) (hid : o.id = r[1]!)
    (ha : o.account = r[2]!) :
    step b r = ({ b with bids := b.bids.erase o, asks := b.asks.erase o },
      [.cancelled o.id o.qty .requested]) := by
  have hu : ∀ x ∈ b.bids ++ b.asks, x.id = o.id → x = o := fun x hx he => eq_of_id h hx ho he
  have hnd := h.distinct
  rw [List.map_append, List.nodup_append] at hnd
  have hb := filter_id_eq_erase hnd.1 (fun x hx => hu x (List.mem_append_left _ hx))
  have ha' := filter_id_eq_erase hnd.2.1 (fun x hx => hu x (List.mem_append_right _ hx))
  have hf := find_of_mem h ho
  rw [hid] at hf
  rw [step_cancel_eq hr hk hf ha, ← hid]
  simp only [remove, hb, ha']

/-- A reduce that passes its checks changes only the quantity of the order that it names, which
keeps its place. -/
theorem step_reduce {b : Book} (h : Valid b) {r : Array UInt64} (hr : r.size = 7)
    (hk : r[0]! = 4) {o : Order} (ho : o ∈ b.bids ++ b.asks) (hid : o.id = r[1]!)
    (ha : o.account = r[2]!) (hq : 1 ≤ r[3]!.toNat) (hlt : r[3]!.toNat < o.qty) :
    step b r = ({ b with
        bids := b.bids.map (fun x => if x = o then { o with qty := r[3]!.toNat } else x),
        asks := b.asks.map (fun x => if x = o then { o with qty := r[3]!.toNat } else x) },
      [.reduced o.id r[3]!.toNat]) := by
  have hu : ∀ x ∈ b.bids ++ b.asks, x.id = o.id → x = o := fun x hx he => eq_of_id h hx ho he
  have hf := find_of_mem h ho
  rw [hid] at hf
  have hoq := (h.qty o ho).2
  have hin : inRange 1 maxQty r[3]! = true := by
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [step_reduce_eq hr hk hf ha hin (by omega), ← hid]
  simp only [setQty]
  rw [map_setQty (fun x hx => hu x (List.mem_append_left _ hx)),
    map_setQty (fun x hx => hu x (List.mem_append_right _ hx))]

/-! ## Rejections

Each theorem states when its reason occurs, as the conjunction of the checks before it in the
requirements' table, which pass, and its own check, which fails. -/

/-- A rejection is the step's only event and leaves the book unchanged, and its kind and reference
words are those of the requirements. -/
theorem step_rejected {b : Book} {r : Array UInt64} {k ref : UInt64} {reason : RejectReason}
    (h : Event.rejected k ref reason ∈ (step b r).2) :
    step b r = (b, [.rejected k ref reason]) ∧
      if r.size = 7 then k = r[0]! ∧ ref = refWord r else k = 0 ∧ ref = 0 := by
  rcases step_cases b r with ⟨k', ref', reason', hs, hw⟩ |
      ⟨side, limit, qty, account, tag, tif, -, -, -, hs⟩ | ⟨o, -, hs⟩ | ⟨o, -, -, -, hs⟩
  · rw [hs] at h ⊢
    simp only [List.mem_singleton, Event.rejected.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, hw⟩
  · rw [hs] at h
    obtain ⟨es, hes, hr⟩ := submit_events b side limit qty account tag tif
    rw [hes] at h
    rcases List.mem_cons.1 h with h | h
    · simp at h
    · exact absurd rfl ((hr _ h).2 k ref reason)
  · rw [hs] at h
    simp at h
  · rw [hs] at h
    simp at h

/-- The events of an accepted order are never a single `rejected` event. -/
theorem submit_ne_rejected (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64)
    (tif : Tif) (k ref : UInt64) (reason : RejectReason) :
    (submit b side limit qty account tag tif).2 ≠ [.rejected k ref reason] := by
  obtain ⟨es, hes, -⟩ := submit_events b side limit qty account tag tif
  rw [hes]
  simp

/-- `sideOf` fails exactly on words above 1. -/
theorem sideOf_eq_none (w : UInt64) : sideOf w = none ↔ (1 : UInt64) < w := by
  simp only [sideOf, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  repeat' split
  all_goals simp_all
  all_goals omega

/-- `sideOf` succeeds exactly on words of at most 1. -/
theorem sideOf_isSome (w : UInt64) : (sideOf w).isSome = true ↔ w ≤ 1 := by
  simp only [sideOf, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  repeat' split
  all_goals simp_all
  all_goals omega

/-- `tifOf` fails exactly on words above 2. -/
theorem tifOf_eq_none (w : UInt64) : tifOf w = none ↔ (2 : UInt64) < w := by
  simp only [tifOf, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  repeat' split
  all_goals simp_all
  all_goals omega

/-- `tifOf` succeeds exactly on words of at most 2. -/
theorem tifOf_isSome (w : UInt64) : (tifOf w).isSome = true ↔ w ≤ 2 := by
  simp only [tifOf, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  repeat' split
  all_goals simp_all
  all_goals omega

/-- `tifOf` gives post-only exactly on the word 2. -/
theorem tifOf_eq_postOnly (w : UInt64) : tifOf w = some .postOnly ↔ w = 2 := by
  simp only [tifOf, ← UInt64.toNat_inj]
  repeat' split
  all_goals simp_all
  all_goals omega

/-- A word other than 1, 2, 3, and 4 is 0 or above 4. -/
theorem kind_unknown (k : UInt64) :
    (¬k = 1 ∧ ¬k = 2 ∧ ¬k = 3 ∧ ¬k = 4) ↔ (k = 0 ∨ (4 : UInt64) < k) := by
  simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  simp
  omega

/-- `find` fails exactly when no order of the book has the id. -/
theorem find_eq_none {b : Book} {id : UInt64} :
    find b id = none ↔ ∀ o ∈ b.bids ++ b.asks, o.id ≠ id := by
  unfold find
  rw [List.find?_eq_none]
  constructor
  · intro h o ho he
    exact h o ho (by simp [he])
  · intro h o ho he
    exact h o ho (by simpa using he)

/-- In a valid book, an order of the book with an id is the order that `find` returns. -/
theorem exists_find {b : Book} (h : Valid b) (id : UInt64) (P : Order → Prop) :
    (∃ o ∈ b.bids ++ b.asks, o.id = id ∧ P o) ↔ ∃ o, find b id = some o ∧ P o := by
  constructor
  · rintro ⟨o, ho, rfl, hp⟩
    exact ⟨o, find_of_mem h ho, hp⟩
  · rintro ⟨o, hf, hp⟩
    obtain ⟨ho, hid⟩ := find_mem hf
    exact ⟨o, ho, hid, hp⟩

/-- A post-only order crosses exactly when the first opposite order has an acceptable price. -/
theorem crosses_iff (b : Book) (side : Side) (p : Nat) :
    crosses b side p = true ↔ ∃ m ∈ (opposite b side).head?, acceptable side p m.price = true := by
  unfold crosses
  split <;> simp_all

theorem rejects_malformed (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .malformed]) ↔ r.size ≠ 7 := by
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected]
  · intro hs
    exact ⟨0, 0, by simp [step, hs, reject]⟩

theorem rejects_unknownKind (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .unknownKind]) ↔
      r.size = 7 ∧ (r[0]! = 0 ∨ (4 : UInt64) < r[0]!) := by
  rw [← kind_unknown]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected]
  · rintro ⟨hs, h1, h2, h3, h4⟩
    exact ⟨r[0]!, 0, by simp_all [step, reject]⟩

theorem rejects_badSide (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .badSide]) ↔
      r.size = 7 ∧ (r[0]! = 1 ∨ r[0]! = 2) ∧ (1 : UInt64) < r[1]! := by
  rw [← sideOf_eq_none]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected]
  · rintro ⟨hs, hk | hk, hsd⟩
    · exact ⟨r[0]!, r[5]!, by simp_all [step, reject]⟩
    · exact ⟨r[0]!, r[4]!, by simp_all [step, reject]⟩

theorem rejects_badTif (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .badTif]) ↔
      r.size = 7 ∧ r[0]! = 1 ∧ r[1]! ≤ 1 ∧ (2 : UInt64) < r[6]! := by
  rw [← sideOf_isSome, ← tifOf_eq_none]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected]
  · rintro ⟨hs, hk, hsd, htf⟩
    obtain ⟨side, hside⟩ := Option.isSome_iff_exists.1 hsd
    exact ⟨r[0]!, r[5]!, by simp_all [step, reject]⟩

theorem rejects_badPrice (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .badPrice]) ↔
      r.size = 7 ∧ r[0]! = 1 ∧ r[1]! ≤ 1 ∧ r[6]! ≤ 2 ∧
        ¬(1 ≤ r[2]!.toNat ∧ r[2]!.toNat ≤ maxPrice) := by
  rw [← sideOf_isSome, ← tifOf_isSome]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected, inRange_false]
  · rintro ⟨hs, hk, hsd, htf, hp⟩
    obtain ⟨side, hside⟩ := Option.isSome_iff_exists.1 hsd
    obtain ⟨tif, htif⟩ := Option.isSome_iff_exists.1 htf
    exact ⟨r[0]!, r[5]!, by simp_all [step, reject, inRange_false]⟩

theorem rejects_badQty {b : Book} (h : Valid b) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .badQty]) ↔
      r.size = 7 ∧
        ((r[0]! = 1 ∧ r[1]! ≤ 1 ∧ r[6]! ≤ 2 ∧ 1 ≤ r[2]!.toNat ∧ r[2]!.toNat ≤ maxPrice ∧
            ¬(1 ≤ r[3]!.toNat ∧ r[3]!.toNat ≤ maxQty)) ∨
          (r[0]! = 2 ∧ r[1]! ≤ 1 ∧ ¬(1 ≤ r[2]!.toNat ∧ r[2]!.toNat ≤ maxQty)) ∨
          (r[0]! = 4 ∧ (∃ o ∈ b.bids ++ b.asks, o.id = r[1]! ∧ o.account = r[2]!) ∧
            ¬(1 ≤ r[3]!.toNat ∧ r[3]!.toNat ≤ maxQty))) := by
  rw [← sideOf_isSome, ← tifOf_isSome, exists_find h r[1]! (fun o => o.account = r[2]!)]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected, inRange_false]
  · rintro ⟨hs, ⟨hk, hsd, htf, hp1, hp2, hq⟩ | ⟨hk, hsd, hq⟩ | ⟨hk, ⟨o, hf, ha⟩, hq⟩⟩
    · obtain ⟨side, hside⟩ := Option.isSome_iff_exists.1 hsd
      obtain ⟨tif, htif⟩ := Option.isSome_iff_exists.1 htf
      exact ⟨r[0]!, r[5]!, by simp_all [step, reject, inRange_false]⟩
    · obtain ⟨side, hside⟩ := Option.isSome_iff_exists.1 hsd
      exact ⟨r[0]!, r[4]!, by simp_all [step, reject, inRange_false]⟩
    · exact ⟨r[0]!, r[1]!, by simp_all [step, reject, inRange_false]⟩

theorem rejects_unknownOrder (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .unknownOrder]) ↔
      r.size = 7 ∧ (r[0]! = 3 ∨ r[0]! = 4) ∧ ∀ o ∈ b.bids ++ b.asks, o.id ≠ r[1]! := by
  rw [← find_eq_none]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected]
  · rintro ⟨hs, hk | hk, hf⟩
    · exact ⟨r[0]!, r[1]!, by simp_all [step, reject]⟩
    · exact ⟨r[0]!, r[1]!, by simp_all [step, reject]⟩

theorem rejects_otherAccount {b : Book} (h : Valid b) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .otherAccount]) ↔
      r.size = 7 ∧ (r[0]! = 3 ∨ r[0]! = 4) ∧
        ∃ o ∈ b.bids ++ b.asks, o.id = r[1]! ∧ o.account ≠ r[2]! := by
  rw [exists_find h r[1]! (fun o => o.account ≠ r[2]!)]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected]
  · rintro ⟨hs, hk | hk, o, hf, ha⟩
    · exact ⟨r[0]!, r[1]!, by simp_all [step, reject]⟩
    · exact ⟨r[0]!, r[1]!, by simp_all [step, reject]⟩

theorem rejects_wouldCross (b : Book) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .wouldCross]) ↔
      r.size = 7 ∧ r[0]! = 1 ∧ r[6]! = 2 ∧ 1 ≤ r[2]!.toNat ∧ r[2]!.toNat ≤ maxPrice ∧
        1 ≤ r[3]!.toNat ∧ r[3]!.toNat ≤ maxQty ∧
        ∃ side, sideOf r[1]! = some side ∧
          ∃ m ∈ (opposite b side).head?, acceptable side r[2]!.toNat m.price = true := by
  rw [← tifOf_eq_postOnly r[6]!]
  simp only [← crosses_iff]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected, inRange_false]
  · rintro ⟨hs, hk, htf, hp1, hp2, hq1, hq2, side, hside, hc⟩
    exact ⟨r[0]!, r[5]!, by simp_all [step, reject, inRange_false]⟩

theorem rejects_notReduction {b : Book} (h : Valid b) (r : Array UInt64) :
    (∃ k ref, (step b r).2 = [.rejected k ref .notReduction]) ↔
      r.size = 7 ∧ r[0]! = 4 ∧ 1 ≤ r[3]!.toNat ∧ r[3]!.toNat ≤ maxQty ∧
        ∃ o ∈ b.bids ++ b.asks, o.id = r[1]! ∧ o.account = r[2]! ∧ o.qty ≤ r[3]!.toNat := by
  rw [exists_find h r[1]! (fun o => o.account = r[2]! ∧ o.qty ≤ r[3]!.toNat)]
  constructor
  · rintro ⟨k, ref, he⟩
    simp only [step] at he
    repeat' split at he
    all_goals simp_all [reject, submit_ne_rejected, inRange_false]
  · rintro ⟨hs, hk, hq1, hq2, o, hf, ha, hle⟩
    exact ⟨r[0]!, r[1]!, by simp_all [step, reject, inRange_false]⟩

/-! ## Events and the top of the book -/

theorem encode_size (e : Event) : (encode e).size = 7 := by
  cases e <;> rfl

/-- Matching against a side whose prices and quantities lie in their ranges gives trades whose
fields lie in their bounds. -/
theorem fill_bounded (taker account : UInt64) (side : Side) (limit qty : Nat) (os : List Order)
    (h : ∀ o ∈ os, (1 ≤ o.price ∧ o.price ≤ maxPrice) ∧ 1 ≤ o.qty ∧ o.qty ≤ maxQty) :
    ∀ e ∈ (fill taker account side limit qty os).trades, e.Bounded := by
  obtain ⟨pre, post, hos, -, hf⟩ := fill_shape taker account side limit qty os
  have hpre : ∀ e ∈ pre.map (exhaust taker), e.Bounded := by
    intro e he
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    have := h m (by rw [hos]; exact List.mem_append_left _ hm)
    simp only [exhaust, Event.Bounded]
    omega
  rcases hf with ⟨ht, -⟩ | ⟨m, rest, q, hp, hq0, hq1, -, -, ht, -⟩
  · rw [ht]
    exact hpre
  · rw [ht]
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hpre e he
    · rw [List.mem_singleton] at he
      subst he
      have := h m (by rw [hos, hp]; simp)
      simp only [Event.Bounded]
      omega

/-- On a valid book, every event of an order with a quantity of at most `maxQty` has its fields
in their bounds. -/
theorem submit_bounded {b : Book} (h : Valid b) (side : Side) (limit qty : Nat)
    (account tag : UInt64) (tif : Tif) (hq : qty ≤ maxQty) :
    ∀ e ∈ (submit b side limit qty account tag tif).2, e.Bounded := by
  have ht := fill_bounded b.nextId account side limit qty (opposite b side)
    (fun o ho => ⟨h.price o (mem_of_opposite ho), h.qty o (mem_of_opposite ho)⟩)
  have hle := fill_remaining_le b.nextId account side limit qty (opposite b side)
  simp only [submit, opposite_nextId]
  generalize fill b.nextId account side limit qty (opposite b side) = F at ht hle ⊢
  have h0 : ∀ e ∈ Event.accepted b.nextId tag :: F.trades, e.Bounded := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · trivial
    · exact ht e he
  have h1 : F.remaining ≠ 0 → ∀ reason, ∀ e ∈ Event.accepted b.nextId tag :: F.trades ++
      [.cancelled b.nextId F.remaining reason], e.Bounded := by
    intro hr reason e he
    rcases List.mem_append.1 he with he | he
    · exact h0 e he
    · rw [List.mem_singleton] at he
      subst he
      simp only [Event.Bounded]
      omega
  split
  · exact h0
  rename_i hr
  repeat' split
  all_goals first
    | exact h0
    | exact h1 hr _

/-- An accepted order gives at most two events more than the opposite side holds orders. -/
theorem submit_length (b : Book) (side : Side) (limit qty : Nat) (account tag : UInt64)
    (tif : Tif) :
    (submit b side limit qty account tag tif).2.length ≤ (opposite b side).length + 2 := by
  have hl : (fill b.nextId account side limit qty (opposite b side)).trades.length ≤
      (opposite b side).length := by
    obtain ⟨pre, post, hos, -, hf⟩ :=
      fill_shape b.nextId account side limit qty (opposite b side)
    rcases hf with ⟨ht, -⟩ | ⟨m, rest, q, hp, -, -, -, -, ht, -⟩
    · rw [ht, hos]
      simp
    · rw [ht, hos, hp]
      simp
  simp only [submit, opposite_nextId]
  generalize fill b.nextId account side limit qty (opposite b side) = F at hl ⊢
  repeat' split
  all_goals simp only [List.length_append, List.length_cons, List.length_nil]
  all_goals omega

/-- On a valid book, every field of a step's events that holds a natural number lies in its
bounds, so `encode` writes it as a word without loss. -/
theorem step_bounded {b : Book} (h : Valid b) (r : Array UInt64) :
    ∀ e ∈ (step b r).2, e.Bounded := by
  rcases step_cases b r with ⟨k, ref, reason, hs, -⟩ |
      ⟨side, limit, qty, account, tag, tif, -, -, hq, hs⟩ | ⟨o, hf, hs⟩ |
      ⟨o, -, hq1, hq2, hs⟩ <;> rw [hs]
  · simp [Event.Bounded]
  · exact submit_bounded h side limit qty account tag tif hq
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact h.qty o (find_mem hf).1
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact ⟨hq1, hq2⟩

/-- A step on a valid book gives at most `capacity + 2` events: the `accepted` event, a trade with
each resting order at most, and a cancellation. -/
theorem step_events_length {b : Book} (h : Valid b) (r : Array UInt64) :
    (step b r).2.length ≤ capacity + 2 := by
  rcases step_cases b r with ⟨k, ref, reason, hs, -⟩ |
      ⟨side, limit, qty, account, tag, tif, -, -, -, hs⟩ | ⟨o, -, hs⟩ | ⟨o, -, -, -, hs⟩ <;>
    rw [hs]
  · simp
  · have h1 := submit_length b side limit qty account tag tif
    have h2 : (opposite b side).length ≤ capacity := by
      have := h.bounded
      cases side <;> simp only [opposite] <;> omega
    omega
  · simp
  · simp

/-- The best price of a side whose prices are at most `maxPrice` is at most `maxPrice`. -/
theorem bestPrice_le {os : List Order} (h : ∀ o ∈ os, o.price ≤ maxPrice) :
    bestPrice os ≤ maxPrice := by
  cases os with
  | nil => simp [bestPrice]
  | cons o os => exact h o (by simp)

/-- The total at the best price of a side whose quantities are at most `c` is at most its number
of orders times `c`. -/
theorem bestQty_le {os : List Order} {c : Nat} (h : ∀ o ∈ os, o.qty ≤ c) :
    bestQty os ≤ os.length * c := by
  have hs : ∀ l : List Order, (∀ o ∈ l, o.qty ≤ c) → (l.map (·.qty)).sum ≤ l.length * c := by
    intro l hl
    induction l with
    | nil => simp
    | cons o l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have h1 := hl o (by simp)
      have h2 := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      omega
  unfold bestQty
  exact Nat.le_trans (hs _ (fun o ho => h o (List.mem_filter.1 ho).1))
    (Nat.mul_le_mul_right _ (List.length_filter_le _ _))

/-- On a valid book, the best prices are at most `maxPrice`, and the totals at them are at most
`capacity * maxQty`. -/
theorem top_bound {b : Book} (h : Valid b) :
    (top b).1 ≤ maxPrice ∧ (top b).2.1 ≤ capacity * maxQty ∧
      (top b).2.2.1 ≤ maxPrice ∧ (top b).2.2.2 ≤ capacity * maxQty := by
  have hb := h.bounded
  have h1 : bestQty b.bids ≤ b.bids.length * maxQty :=
    bestQty_le (fun o ho => (h.qty o (List.mem_append_left _ ho)).2)
  have h2 : bestQty b.asks ≤ b.asks.length * maxQty :=
    bestQty_le (fun o ho => (h.qty o (List.mem_append_right _ ho)).2)
  refine ⟨bestPrice_le (fun o ho => (h.price o (List.mem_append_left _ ho)).2), ?_,
    bestPrice_le (fun o ho => (h.price o (List.mem_append_right _ ho)).2), ?_⟩
  · exact Nat.le_trans h1 (Nat.mul_le_mul_right _ (by omega))
  · exact Nat.le_trans h2 (Nat.mul_le_mul_right _ (by omega))

/-! ## Streams -/

/-- `records.go` gives records of one to seven words when its accumulator holds at most six
words. -/
theorem go_size (ws : List UInt64) (acc : Array UInt64) (h : acc.size ≤ 6) :
    ∀ r ∈ records.go ws acc, 0 < r.size ∧ r.size ≤ 7 := by
  induction ws generalizing acc with
  | nil =>
    intro r hr
    simp only [records.go] at hr
    split at hr
    · simp at hr
    · rename_i he
      rw [List.mem_singleton] at hr
      rw [hr]
      have : acc.size ≠ 0 := fun h0 => he (Array.isEmpty_iff_size_eq_zero.2 h0)
      omega
  | cons w ws ih =>
    intro r hr
    simp only [records.go] at hr
    split at hr
    · rcases List.mem_cons.1 hr with rfl | hr
      · simp
        omega
      · exact ih #[] (by simp) r hr
    · exact ih (acc.push w) (by simp; omega) r hr

/-- Each record holds from one to seven words. -/
theorem records_size (ws : List UInt64) : ∀ r ∈ records ws, 0 < r.size ∧ r.size ≤ 7 :=
  go_size ws #[] (by simp)

/-- `records.go` gives only records of seven words when its accumulator holds at most six words
and the accumulator and the words together hold a multiple of seven. -/
theorem go_full (ws : List UInt64) (acc : Array UInt64) (h : acc.size ≤ 6)
    (hm : (acc.size + ws.length) % 7 = 0) : ∀ r ∈ records.go ws acc, r.size = 7 := by
  induction ws generalizing acc with
  | nil =>
    intro r hr
    simp only [List.length_nil, Nat.add_zero] at hm
    have he : acc.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 (by omega)
    simp [records.go, he] at hr
  | cons w ws ih =>
    intro r hr
    simp only [records.go] at hr
    simp only [List.length_cons] at hm
    split at hr
    · rename_i h6
      rcases List.mem_cons.1 hr with rfl | hr
      · simp [h6]
      · exact ih #[] (by simp) (by simp; omega) r hr
    · exact ih (acc.push w) (by simp; omega) (by simp; omega) r hr

/-- A stream whose length is a multiple of seven has only records of seven words. -/
theorem records_full (ws : List UInt64) (h : ws.length % 7 = 0) :
    ∀ r ∈ records ws, r.size = 7 :=
  go_full ws #[] (by simp) (by simpa using h)

/-- `records.go` gives one record for each seven words of the accumulator and the words, and one
more for a shorter rest, when its accumulator holds at most six words. -/
theorem go_length (ws : List UInt64) (acc : Array UInt64) (h : acc.size ≤ 6) :
    (records.go ws acc).length = (acc.size + ws.length + 6) / 7 := by
  induction ws generalizing acc with
  | nil =>
    simp only [records.go]
    split
    · rename_i he
      have := Array.isEmpty_iff_size_eq_zero.1 he
      simp [this]
    · rename_i he
      have : acc.size ≠ 0 := fun h0 => he (Array.isEmpty_iff_size_eq_zero.2 h0)
      simp
      omega
  | cons w ws ih =>
    simp only [records.go]
    split
    · rename_i h6
      rw [List.length_cons, ih #[] (by simp)]
      simp
      omega
    · rw [ih (acc.push w) (by simp; omega)]
      simp
      omega

theorem records_length (ws : List UInt64) : (records ws).length = (ws.length + 6) / 7 := by
  rw [records, go_length ws #[] (by simp)]
  simp

/-- The records of `records.go` hold the accumulator's words and then the words, in order. -/
theorem go_flatten (ws : List UInt64) (acc : Array UInt64) :
    ((records.go ws acc).map (·.toList)).flatten = acc.toList ++ ws := by
  induction ws generalizing acc with
  | nil =>
    simp only [records.go]
    split
    · rename_i he
      have : acc = #[] :=
        Array.eq_empty_of_size_eq_zero (Array.isEmpty_iff_size_eq_zero.1 he)
      subst this
      simp
    · simp
  | cons w ws ih =>
    simp only [records.go]
    split
    · simp [ih]
    · rw [ih]
      simp

/-- The records hold the stream's words in order. -/
theorem records_flatten (ws : List UInt64) : ((records ws).map (·.toList)).flatten = ws := by
  rw [records, go_flatten]
  simp

/-- `records.go` reads two parts of a stream separately when its accumulator holds at most six
words and the accumulator and the first part hold a multiple of seven words. -/
theorem go_append (ws₁ ws₂ : List UInt64) (acc : Array UInt64) (h : acc.size ≤ 6)
    (hm : (acc.size + ws₁.length) % 7 = 0) :
    records.go (ws₁ ++ ws₂) acc = records.go ws₁ acc ++ records.go ws₂ #[] := by
  induction ws₁ generalizing acc with
  | nil =>
    have h0 : acc.size = 0 := by simp at hm; omega
    have : acc = #[] := Array.eq_empty_of_size_eq_zero h0
    subst this
    simp [records.go]
  | cons w ws ih =>
    simp only [List.cons_append, records.go]
    simp only [List.length_cons] at hm
    split
    · rw [ih #[] (by simp) (by simp; omega), List.cons_append]
    · exact ih (acc.push w) (by simp; omega) (by simp; omega)

theorem records_append (ws₁ ws₂ : List UInt64) (h : ws₁.length % 7 = 0) :
    records (ws₁ ++ ws₂) = records ws₁ ++ records ws₂ :=
  go_append ws₁ ws₂ #[] (by simp) (by simpa using h)

/-- Folding `runStep` from a book and some events gives the book of the fold from no events and
the events followed by the fold's events. -/
theorem foldl_runStep (rs : List (Array UInt64)) (b : Book) (es : List Event) :
    rs.foldl runStep (b, es) =
      ((rs.foldl runStep (b, [])).1, es ++ (rs.foldl runStep (b, [])).2) := by
  induction rs generalizing b es with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, runStep]
    rw [ih, ih (step b r).1 ([] ++ (step b r).2)]
    simp

/-- A stream run in two parts, the first a whole number of records, gives the book and the events
of one run. -/
theorem run_append (b : Book) (ws₁ ws₂ : List UInt64) (h : ws₁.length % 7 = 0) :
    run b (ws₁ ++ ws₂) =
      ((run (run b ws₁).1 ws₂).1, (run b ws₁).2 ++ (run (run b ws₁).1 ws₂).2) := by
  simp only [run_eq, records_append ws₁ ws₂ h, List.foldl_append]
  exact foldl_runStep _ _ _

end Demos.OrderBook.Spec

#print axioms Demos.OrderBook.Spec.empty_valid
#print axioms Demos.OrderBook.Spec.step_valid
#print axioms Demos.OrderBook.Spec.step_nextId
#print axioms Demos.OrderBook.Spec.step_accepted
#print axioms Demos.OrderBook.Spec.run_valid
#print axioms Demos.OrderBook.Spec.run_empty_valid
#print axioms Demos.OrderBook.Spec.fill_shape
#print axioms Demos.OrderBook.Spec.fill_prefix
#print axioms Demos.OrderBook.Spec.fill_traded
#print axioms Demos.OrderBook.Spec.fill_total
#print axioms Demos.OrderBook.Spec.fill_stop
#print axioms Demos.OrderBook.Spec.fill_selfTrade
#print axioms Demos.OrderBook.Spec.submit_conserves
#print axioms Demos.OrderBook.Spec.submit_opposite
#print axioms Demos.OrderBook.Spec.step_cancel
#print axioms Demos.OrderBook.Spec.step_reduce
#print axioms Demos.OrderBook.Spec.step_rejected
#print axioms Demos.OrderBook.Spec.rejects_malformed
#print axioms Demos.OrderBook.Spec.rejects_unknownKind
#print axioms Demos.OrderBook.Spec.rejects_badSide
#print axioms Demos.OrderBook.Spec.rejects_badTif
#print axioms Demos.OrderBook.Spec.rejects_badPrice
#print axioms Demos.OrderBook.Spec.rejects_badQty
#print axioms Demos.OrderBook.Spec.rejects_unknownOrder
#print axioms Demos.OrderBook.Spec.rejects_otherAccount
#print axioms Demos.OrderBook.Spec.rejects_wouldCross
#print axioms Demos.OrderBook.Spec.rejects_notReduction
#print axioms Demos.OrderBook.Spec.encode_size
#print axioms Demos.OrderBook.Spec.step_bounded
#print axioms Demos.OrderBook.Spec.step_events_length
#print axioms Demos.OrderBook.Spec.top_bound
#print axioms Demos.OrderBook.Spec.records_size
#print axioms Demos.OrderBook.Spec.records_full
#print axioms Demos.OrderBook.Spec.records_length
#print axioms Demos.OrderBook.Spec.records_flatten
#print axioms Demos.OrderBook.Spec.records_append
#print axioms Demos.OrderBook.Spec.run_append
