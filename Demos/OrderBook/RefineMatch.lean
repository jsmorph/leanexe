import Demos.OrderBook.RefineEffects
import Demos.OrderBook.RefineHelpers

/-! Matching and submission of [the program](Program.lean) against `Spec.fill` and `Spec.submit`.
The loop invariant `MatchInv` relates a state of the `repeatWhile` of `fill` to the outcome of
`Spec.fill` on the initial opposite side: that outcome is the trades so far followed by the
outcome that the state represents, `absOf`, which is `Spec.fill` on the orders of the levels from
the state's price on.  The measure is the number of levels left to scan plus the number of orders
left plus 1 while the loop condition holds, and 0 otherwise. -/

namespace Demos.OrderBook.Refinement

open Program (Book Matching)
open Abstract

/-! ## Event words -/

/-- Appending the words of events to an array appends their concatenation. -/
theorem encodeAll_foldl (es : List Spec.Event) (init : Array UInt64) :
    es.foldl (fun ws e => ws ++ Spec.encode e) init = init ++ Spec.encodeAll es := by
  induction es generalizing init with
  | nil => simp [Spec.encodeAll]
  | cons e es ih =>
    simp only [List.foldl_cons, Spec.encodeAll]
    rw [ih, ih (#[] ++ Spec.encode e)]
    simp

/-- The words of two lists of events are the words of the first followed by those of the
second. -/
theorem encodeAll_append (es es' : List Spec.Event) :
    Spec.encodeAll (es ++ es') = Spec.encodeAll es ++ Spec.encodeAll es' := by
  simp only [Spec.encodeAll, List.foldl_append]
  rw [encodeAll_foldl]
  rfl

/-- The words of an event followed by events. -/
theorem encodeAll_cons (e : Spec.Event) (es : List Spec.Event) :
    Spec.encodeAll (e :: es) = Spec.encode e ++ Spec.encodeAll es := by
  rw [show e :: es = [e] ++ es from rfl, encodeAll_append]
  simp [Spec.encodeAll]

/-- `emit` appends the seven words of an event. -/
theorem emit_eq (out : Array UInt64) (w0 w1 w2 w3 w4 w5 w6 : UInt64) :
    Program.emit out w0 w1 w2 w3 w4 w5 w6 = out ++ #[w0, w1, w2, w3, w4, w5, w6] := by
  rw [← Array.toList_inj]
  simp [Program.emit]

/-! ## Words -/

/-- The number of the smaller of two words is the smaller number. -/
theorem toNat_min (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split
  · rename_i h
    have := UInt64.le_iff_toNat_le.1 h
    omega
  · rename_i h
    have : ¬ a.toNat ≤ b.toNat := fun h' => h (UInt64.le_iff_toNat_le.2 h')
    omega

/-! ## Matching in the specification -/

/-- Matching with nothing remaining leaves the side and trades nothing. -/
theorem fill_zero (taker account : UInt64) (sd : Spec.Side) (limit : Nat) (L : List Spec.Order) :
    Spec.fill taker account sd limit 0 L = ⟨L, [], 0, false⟩ := by
  cases L <;> simp [Spec.fill]

/-- Matching against a side whose first order has an unacceptable price leaves the side. -/
theorem fill_stop_price (taker account : UInt64) (sd : Spec.Side) (limit qty : Nat)
    (L : List Spec.Order) (h : ∀ o ∈ L.head?, Spec.acceptable sd limit o.price = false) :
    Spec.fill taker account sd limit qty L = ⟨L, [], qty, false⟩ := by
  cases L with
  | nil => simp [Spec.fill]
  | cons o L => simp [Spec.fill, h o rfl]

/-! ## Sides -/

/-- A side word of at most 1 is 0 with opposite 1, or 1 with opposite 0. -/
theorem side_cases {side : UInt64} (hs : side ≤ 1) :
    (side = 0 ∧ 1 - side = 1) ∨ (side = 1 ∧ 1 - side = 0) := by
  by_cases h0 : side = 0
  · subst h0
    exact Or.inl ⟨rfl, rfl⟩
  · have : side = 1 := UInt64.toNat_inj.1 (by rw [side_one hs h0]; rfl)
    subst this
    exact Or.inr ⟨rfl, rfl⟩

/-- Replacing the opposite side of a book read from level lists by the opposite levels of other
level lists that agree on the own side gives the book read from the other lists. -/
theorem ofLevels_setOpposite {side : UInt64} (hs : side ≤ 1) {F G : Nat → List Spec.Order}
    (n : UInt64) (h : ∀ l ∈ levelsOf side, G l = F l) :
    ofLevels G n =
      Spec.setOpposite (ofLevels F n) (toSide side) ((levelsOf (1 - side)).flatMap G) := by
  rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · rw [h1]
    simp only [ofLevels, Spec.setOpposite, toSide, ite_true, Spec.Book.mk.injEq, and_true]
    exact ⟨flatMap_congr h, rfl⟩
  · rw [h1]
    simp only [ofLevels, Spec.setOpposite, toSide, show ¬ (1 : UInt64) = 0 by decide, ite_false,
      Spec.Book.mk.injEq, and_true]
    exact ⟨rfl, flatMap_congr h⟩

/-! ## The loop invariant -/

/-- The orders of the levels of side `k` from the price of a state of matching on, in scan
order. -/
def restOf (k : UInt64) (m : Matching) : List Spec.Order :=
  (fromLevels k m.price.toNat).flatMap (ordersAt m.book)

/-- The outcome of matching that a state represents: after self-trade prevention, the orders not
reached and no trades, and otherwise `Spec.fill` on the orders not reached. -/
def absOf (taker account side limit : UInt64) (m : Matching) : Spec.Fill :=
  if m.selfTrade then ⟨restOf (1 - side) m, [], m.rem.toNat, true⟩
  else Spec.fill taker account (toSide side) limit.toNat m.rem.toNat (restOf (1 - side) m)

/-- The condition of the `repeatWhile` of `fill`. -/
def matchCond (side limit : UInt64) (m : Matching) : Bool :=
  m.rem != 0 && !m.selfTrade && Program.acceptable side limit m.price

/-- The loop invariant of `fill` for an incoming order with id `taker`, account `account`, side
`side`, and limit `limit` on the book `b0`, with the event words `out0` before matching and the
outcome `R0` of `Spec.fill` on the initial opposite side. -/
structure MatchInv (b0 : Book) (out0 : Array UInt64) (taker account side limit : UInt64)
    (R0 : Spec.Fill) (m : Matching) : Prop where
  shape : Shape m.book
  count : m.book.count.toNat = Spec.size (toSpec m.book)
  nextId : m.book.nextId = b0.nextId
  price : if 1 - side = 0 then m.price.toNat ≤ 1023
    else 1 ≤ m.price.toNat ∧ m.price.toNat ≤ 1024
  above : ∀ l ∈ aboveLevels (1 - side) m.price.toNat, ordersAt m.book l = []
  own : ∀ l ∈ levelsOf side, ordersAt m.book l = ordersAt b0 l
  out : ∃ T, m.out = out0 ++ Spec.encodeAll T ∧
    R0 = ⟨(absOf taker account side limit m).others,
      T ++ (absOf taker account side limit m).trades,
      (absOf taker account side limit m).remaining,
      (absOf taker account side limit m).selfTrade⟩

/-- The measure of a state of matching: the levels left to scan plus the orders left plus 1 while
the loop condition holds, and 0 otherwise. -/
def matchMeasure (side limit : UInt64) (m : Matching) : Nat :=
  if matchCond side limit m then
    (fromLevels (1 - side) m.price.toNat).length + (restOf (1 - side) m).length + 1
  else 0

/-- While the loop condition holds, the price of matching lies in the band. -/
theorem cond_price {side limit : UInt64} (hs : side ≤ 1)
    (hl : 1 ≤ limit.toNat ∧ limit.toNat ≤ 1023) {m : Matching}
    (hp : if 1 - side = 0 then m.price.toNat ≤ 1023
      else 1 ≤ m.price.toNat ∧ m.price.toNat ≤ 1024)
    (ha : Program.acceptable side limit m.price = true) :
    1 ≤ m.price.toNat ∧ m.price.toNat ≤ 1023 := by
  rw [acceptable_eq] at ha
  rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · rw [h1] at hp
    simp only [show ¬ (1 : UInt64) = 0 by decide, ite_false] at hp
    simp [toSide, Spec.acceptable] at ha
    omega
  · rw [h1] at hp
    simp only [ite_true] at hp
    simp [toSide, Spec.acceptable] at ha
    omega

/-- The next price of matching is the next price of the scan of the opposite side. -/
theorem next_price {side : UInt64} (hs : side ≤ 1) {p : UInt64}
    (hp : 1 ≤ p.toNat ∧ p.toNat ≤ 1023) :
    (if side == 0 then p + 1 else p - 1).toNat = nextPrice (1 - side) p.toNat := by
  rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · rw [h1]
    simp only [beq_self_eq_true, ite_true, nextPrice, show ¬ (1 : UInt64) = 0 by decide, ite_false]
    exact toNat_add_one (by omega)
  · rw [h1]
    simp only [show ((1 : UInt64) == 0) = false by decide, Bool.false_eq_true, ite_false,
      nextPrice, ite_true]
    exact toNat_sub_one hp.1

/-- The price range of the invariant holds at the next price. -/
theorem next_price_range {side : UInt64} (hs : side ≤ 1) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 1023) :
    if 1 - side = 0 then nextPrice (1 - side) p ≤ 1023
    else 1 ≤ nextPrice (1 - side) p ∧ nextPrice (1 - side) p ≤ 1024 := by
  rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · rw [h1]
    simp only [show ¬ (1 : UInt64) = 0 by decide, ite_false, nextPrice]
    omega
  · rw [h1]
    simp only [ite_true, nextPrice]
    omega

/-- The levels of the two sides are disjoint. -/
theorem not_mem_levelsOf {side : UInt64} (hs : side ≤ 1) {l : Nat}
    (hl : l ∈ levelsOf (1 - side)) : l ∉ levelsOf side := by
  rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · rw [h1] at hl
    simp only [levelsOf, show ¬ (1 : UInt64) = 0 by decide, ite_false, ite_true,
      mem_askLevels] at hl ⊢
    rw [mem_bidLevels]
    omega
  · rw [h1] at hl
    simp only [levelsOf, show ¬ (1 : UInt64) = 0 by decide, ite_false, ite_true,
      mem_bidLevels] at hl ⊢
    rw [mem_askLevels]
    omega

/-- The levels of a side from a price lie on that side. -/
theorem mem_levelsOf_of_from {k : UInt64} {p l : Nat}
    (hp : if k = 0 then p ≤ 1023 else 1 ≤ p ∧ p ≤ 1024) (hl : l ∈ fromLevels k p) :
    l ∈ levelsOf k := by
  rw [mem_fromLevels] at hl
  unfold levelsOf
  by_cases h0 : k = 0
  · simp only [h0, ite_true] at hl hp ⊢
    rw [mem_bidLevels]
    omega
  · simp only [h0, ite_false] at hl hp ⊢
    rw [mem_askLevels]
    omega

/-- The levels of a side above a price lie on that side. -/
theorem mem_levelsOf_of_above {k : UInt64} {p l : Nat}
    (hp : if k = 0 then p ≤ 1023 else 1 ≤ p ∧ p ≤ 1024) (hl : l ∈ aboveLevels k p) :
    l ∈ levelsOf k := by
  rw [mem_aboveLevels] at hl
  unfold levelsOf
  by_cases h0 : k = 0
  · simp only [h0, ite_true] at hl ⊢
    rw [mem_bidLevels]
    omega
  · simp only [h0, ite_false] at hl hp ⊢
    rw [mem_askLevels]
    omega

/-- Every order of the levels from a price has a price at that price or worse. -/
theorem price_of_mem_rest {b : Book} {k : UInt64} {p : Nat} {o : Spec.Order}
    (ho : o ∈ (fromLevels k p).flatMap (ordersAt b)) :
    if k = 0 then o.price ≤ p else p ≤ o.price := by
  obtain ⟨l, hl, hol⟩ := List.mem_flatMap.1 ho
  rw [price_of_mem_ordersAt hol]
  rw [mem_fromLevels] at hl
  unfold levelPrice
  by_cases h0 : k = 0
  · simp only [h0, ite_true] at hl ⊢
    omega
  · simp only [h0, ite_false] at hl ⊢
    omega

/-- `emit` of a trade's words appends the trade's encoding. -/
theorem emit_trade (out : Array UInt64) (maker taker price q acct rem : UInt64) :
    Program.emit out 3 maker taker price q acct rem =
      out ++ Spec.encode (.trade maker taker price.toNat q.toNat acct rem.toNat) := by
  rw [emit_eq]
  simp [Spec.encode]

/-! ## One step of matching -/

/-- A quantity update at a slot outside a level's chain leaves the level's orders. -/
theorem setQ_ordersAt_ne {b : Book} (h : Shape b) {s v : UInt64} (hs : s.toNat < 4097) {l : Nat}
    (hl : s ∉ levelSlots b l) :
    ordersAt { b with qty := b.qty.set! s.toNat v } l = ordersAt b l := by
  rw [setQ_ordersAt h hs]
  exact List.map_congr_left fun t ht => by
    have hts : t ≠ s := fun he => hl (he ▸ ht)
    rw [ite_eq_right hts]

/-- A quantity update at the first slot of a level's chain changes the first order's
quantity. -/
theorem setQ_ordersAt_head {b : Book} (h : Shape b) {s v : UInt64} (hs : s.toNat < 4097) {l : Nat}
    {B : List UInt64} (hL : levelSlots b l = s :: B) (hn : s ∉ B) :
    ordersAt { b with qty := b.qty.set! s.toNat v } l =
      { orderAt b l s with qty := v.toNat } :: B.map (orderAt b l) := by
  rw [setQ_ordersAt h hs, hL, List.map_cons, ite_eq_left rfl]
  congr 1
  exact List.map_congr_left fun t ht => by
    have hts : t ≠ s := fun he => hn (he ▸ ht)
    rw [ite_eq_right hts]

/-- The levels of a side lie in the band. -/
theorem band_of_levelsOf {k : UInt64} {l : Nat} (h : l ∈ levelsOf k) : BandLevel l := by
  unfold levelsOf at h
  split at h
  · exact bandLevel_iff.2 (Or.inl h)
  · exact bandLevel_iff.2 (Or.inr h)

/-- The measure is at most the levels left plus the orders left plus 1. -/
theorem matchMeasure_le (side limit : UInt64) (m : Matching) :
    matchMeasure side limit m ≤
      (fromLevels (1 - side) m.price.toNat).length + (restOf (1 - side) m).length + 1 := by
  unfold matchMeasure
  split <;> omega

/-- One step of matching keeps the invariant and lowers the measure. -/
theorem matchInv_step {b0 : Book} {out0 : Array UInt64} {taker account side limit : UInt64}
    {R0 : Spec.Fill} (hs : side ≤ 1) (hl : 1 ≤ limit.toNat ∧ limit.toNat ≤ 1023)
    {m : Matching}
    (h : MatchInv b0 out0 taker account side limit R0 m) (hc : matchCond side limit m = true) :
    MatchInv b0 out0 taker account side limit R0 (Program.matchStep taker account side m) ∧
      matchMeasure side limit (Program.matchStep taker account side m) <
        matchMeasure side limit m := by
  have hc' := hc
  simp only [matchCond, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hc'
  obtain ⟨⟨hrem, hst⟩, hacc⟩ := hc'
  have hp := cond_price hs hl h.price hacc
  have hk : 1 - side ≤ 1 := one_sub_le hs
  have hlv := toNat_level hk (p := m.price) (by omega)
  generalize hN : (1 - side).toNat * 1024 + m.price.toNat = lvN at hlv
  have hband : BandLevel lvN := by
    rw [← hN]
    have := UInt64.le_iff_toNat_le.1 hk
    simp at this
    constructor <;> omega
  have hfrom := fromLevels_cons hk hp
  rw [hN] at hfrom
  have hnext := next_price hs hp
  have hrange := next_price_range hs hp
  have hmeas : matchMeasure side limit m =
      (fromLevels (1 - side) m.price.toNat).length + (restOf (1 - side) m).length + 1 := by
    simp [matchMeasure, hc]
  have habs : absOf taker account side limit m =
      Spec.fill taker account (toSide side) limit.toNat m.rem.toNat (restOf (1 - side) m) := by
    simp [absOf, hst]
  generalize hRA : (fromLevels (1 - side) (nextPrice (1 - side) m.price.toNat)).flatMap
    (ordersAt m.book) = restAfter
  have hrest : restOf (1 - side) m = ordersAt m.book lvN ++ restAfter := by
    rw [restOf, hfrom, List.flatMap_cons, hRA]
  have hnotA : lvN ∉ fromLevels (1 - side) (nextPrice (1 - side) m.price.toNat) := by
    rw [← hN, mem_fromLevels]
    rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rw [h1] <;> simp [nextPrice] <;>
      omega
  have hnotB : lvN ∉ aboveLevels (1 - side) m.price.toNat := by
    rw [← hN, mem_aboveLevels]
    rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rw [h1] <;> simp <;> omega
  have hpr : if 1 - side = 0 then m.price.toNat ≤ 1023
      else 1 ≤ m.price.toNat ∧ m.price.toNat ≤ 1024 := h.price
  have hnotC : lvN ∉ levelsOf side :=
    not_mem_levelsOf hs (mem_levelsOf_of_from hpr (by rw [hfrom]; simp))
  have hbandA : ∀ l ∈ aboveLevels (1 - side) m.price.toNat, BandLevel l ∧ l ≠ lvN :=
    fun l hl' => ⟨band_of_levelsOf (mem_levelsOf_of_above hpr hl'),
      fun he => hnotB (he ▸ hl')⟩
  have hbandF : ∀ l ∈ fromLevels (1 - side) (nextPrice (1 - side) m.price.toNat),
      BandLevel l ∧ l ≠ lvN :=
    fun l hl' => ⟨band_of_levelsOf (mem_levelsOf_of_from hrange hl'),
      fun he => hnotA (he ▸ hl')⟩
  have hbandO : ∀ l ∈ levelsOf side, BandLevel l ∧ l ≠ lvN :=
    fun l hl' => ⟨band_of_levelsOf hl', fun he => hnotC (he ▸ hl')⟩
  obtain ⟨T, hT, hR⟩ := h.out
  have hacc' : Spec.acceptable (toSide side) limit.toNat m.price.toNat = true := by
    rw [← acceptable_eq]
    exact hacc
  by_cases h0 : m.book.head[lvN]! = 0
  · have hstep : Program.matchStep taker account side m =
        { m with price := if side == 0 then m.price + 1 else m.price - 1 } := by
      simp only [Program.matchStep, hlv, h0, beq_self_eq_true, ↓reduceIte]
    have hempty : ordersAt m.book lvN = [] := by
      unfold ordersAt
      rw [levelSlots_eq_nil.2 h0]
      rfl
    have hrest' : restOf (1 - side)
        { m with price := if side == 0 then m.price + 1 else m.price - 1 } =
        restOf (1 - side) m := by
      rw [hrest, hempty, List.nil_append, ← hRA]
      simp only [restOf, hnext]
    rw [hstep]
    refine ⟨⟨h.shape, h.count, h.nextId, ?_, ?_, h.own, T, hT, ?_⟩, ?_⟩
    · simp only [hnext]
      exact hrange
    · simp only [hnext]
      rw [aboveLevels_next hk hp, hN]
      intro l hl'
      rcases List.mem_append.1 hl' with hl' | hl'
      · exact h.above l hl'
      · rw [List.mem_singleton] at hl'
        rw [hl']
        exact hempty
    · have : absOf taker account side limit
          { m with price := if side == 0 then m.price + 1 else m.price - 1 } =
          absOf taker account side limit m := by
        unfold absOf
        rw [hrest']
      rw [this]
      exact hR
    · have hlen : (fromLevels (1 - side) m.price.toNat).length =
          (fromLevels (1 - side) (nextPrice (1 - side) m.price.toNat)).length + 1 := by
        rw [hfrom]
        rfl
      have := matchMeasure_le side limit
        { m with price := if side == 0 then m.price + 1 else m.price - 1 }
      rw [hrest'] at this
      simp only [hnext] at this
      omega
  · have hne : levelSlots m.book lvN ≠ [] := fun he => h0 (levelSlots_eq_nil.1 he)
    obtain ⟨x, B, hxB⟩ := List.exists_cons_of_ne_nil hne
    have hP := h.shape.path hband
    rw [hxB] at hP
    have hx : x = m.book.head[lvN]! := hP.1.symm
    subst hx
    generalize hsdef : m.book.head[lvN]! = s at hxB hP h0
    have hnodup := h.shape.chainNodup _ hband
    rw [hxB, List.nodup_cons] at hnodup
    have hsz : s.toNat < 4097 := h.shape.lt_size hband (by rw [hxB]; simp)
    have hord : ordersAt m.book lvN = orderAt m.book lvN s :: B.map (orderAt m.book lvN) := by
      unfold ordersAt
      rw [hxB, List.map_cons]
    have hoprice : (orderAt m.book lvN s).price = m.price.toNat := by
      rw [← hN]
      exact (levelSide_level hk (by omega)).2
    have hacco : Spec.acceptable (toSide side) limit.toNat (orderAt m.book lvN s).price = true := by
      rw [hoprice]
      exact hacc'
    have hremN : m.rem.toNat ≠ 0 := fun he => hrem (UInt64.toNat_inj.1 (by simpa using he))
    have h0' : (s == 0) = false := by simp [h0]
    have hfc := Spec.fill_cases taker account (toSide side) limit.toNat m.rem.toNat
      (orderAt m.book lvN s) (B.map (orderAt m.book lvN) ++ restAfter)
    rw [← List.cons_append, ← hord, ← hrest, ← habs] at hfc
    by_cases ha : m.book.acct[s.toNat]! = account
    · have ha' : (m.book.acct[s.toNat]! == account) = true := by simp [ha]
      have hstep : Program.matchStep taker account side m = { m with selfTrade := true } := by
        simp only [Program.matchStep, hlv, hsdef, h0', ha', Bool.false_eq_true, ↓reduceIte]
      rw [hstep]
      refine ⟨⟨h.shape, h.count, h.nextId, h.price, h.above, h.own, T, hT, ?_⟩, ?_⟩
      · have : absOf taker account side limit { m with selfTrade := true } =
            absOf taker account side limit m := by
          rcases hfc with ⟨h1, -⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, -, h3, -⟩
          · rcases h1 with h1 | h1
            · exact absurd h1 hremN
            · rw [hacco] at h1
              exact absurd h1 (by simp)
          · rw [h2]
            simp only [absOf, ite_true]
            rw [show restOf (1 - side) { m with selfTrade := true } = restOf (1 - side) m from rfl,
              hrest, hord, List.cons_append]
          · exact absurd ha h3
          · exact absurd ha h3
        rw [this]
        exact hR
      · rw [hmeas]
        simp [matchMeasure, matchCond]
    · have ha' : (m.book.acct[s.toNat]! == account) = false := by simp [ha]
      generalize hmq : m.book.qty[s.toNat]! = mq
      generalize hq : min m.rem mq = q
      have hq' := toNat_min m.rem mq
      rw [hq] at hq'
      have hoqty : (orderAt m.book lvN s).qty = mq.toNat := by
        simp only [orderAt, hmq]
      have hoacct : (orderAt m.book lvN s).account = m.book.acct[s.toNat]! := rfl
      have hoid : (orderAt m.book lvN s).id = m.book.oid[s.toNat]! := rfl
      have hqle : q ≤ mq := UInt64.le_iff_toNat_le.2 (by omega)
      have hqr : q ≤ m.rem := UInt64.le_iff_toNat_le.2 (by omega)
      have hstep : Program.matchStep taker account side m =
          { m with
            book := if q = mq then Program.unlink m.book (Program.level (1 - side) m.price) 0 s
              else { m.book with qty := m.book.qty.set! s.toNat (mq - q) }
            out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
              m.book.acct[s.toNat]! (mq - q)
            rem := m.rem - q } := by
        simp only [Program.matchStep, hlv, hsdef, h0', ha', Bool.false_eq_true, ↓reduceIte, hmq,
          hq, beq_iff_eq]
      have hout : Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
          m.book.acct[s.toNat]! (mq - q) = out0 ++ Spec.encodeAll (T ++
            [.trade (orderAt m.book lvN s).id taker (orderAt m.book lvN s).price q.toNat
              (orderAt m.book lvN s).account ((orderAt m.book lvN s).qty - q.toNat)]) := by
        rw [emit_trade, hT, encodeAll_append, hoprice, hoqty, hoacct, hoid,
          UInt64.toNat_sub_of_le _ _ hqle]
        simp [Spec.encodeAll]
      rw [hstep]
      by_cases hqm : q = mq
      · subst hqm
        have hu : UnlinkAt m.book (Program.level (1 - side) m.price) 0 s [] B :=
          ⟨by rw [hlv]; exact hband, by rw [hlv]; simpa using hxB, Or.inl ⟨rfl, rfl⟩⟩
        have hord' : ∀ l, BandLevel l → ordersAt
            (Program.unlink m.book (Program.level (1 - side) m.price) 0 s) l =
            if l = lvN then B.map (orderAt m.book lvN) else ordersAt m.book l := by
          intro l hl'
          rw [unlink_ordersAt h.shape hu hl', hlv]
          simp
        have hrest' : restOf (1 - side) { m with
            book := Program.unlink m.book (Program.level (1 - side) m.price) 0 s,
            out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
              m.book.acct[s.toNat]! (q - q),
            rem := m.rem - q } = B.map (orderAt m.book lvN) ++ restAfter := by
          simp only [restOf, hfrom, List.flatMap_cons]
          rw [hord' lvN hband, ite_eq_left rfl, ← hRA]
          congr 1
          exact flatMap_congr fun l hl' => by
            rw [hord' l (hbandF l hl').1, ite_eq_right (hbandF l hl').2]
        have hlen : (restOf (1 - side) m).length = (B.map (orderAt m.book lvN) ++ restAfter).length
            + 1 := by
          rw [hrest, hord]
          simp
        have hA : absOf taker account side limit { m with
            book := Program.unlink m.book (Program.level (1 - side) m.price) 0 s,
            out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
              m.book.acct[s.toNat]! (q - q),
            rem := m.rem - q } = Spec.fill taker account (toSide side) limit.toNat
              (m.rem.toNat - q.toNat) (B.map (orderAt m.book lvN) ++ restAfter) := by
          unfold absOf
          rw [hrest']
          simp only [hst, Bool.false_eq_true, ite_false]
          rw [UInt64.toNat_sub_of_le _ _ hqr]
        simp only [ite_true]
        refine ⟨⟨unlink_shape h.shape hu, unlink_count h.shape hu h.count, h.nextId, h.price,
          ?_, ?_, T ++ [.trade (orderAt m.book lvN s).id taker (orderAt m.book lvN s).price
            q.toNat (orderAt m.book lvN s).account ((orderAt m.book lvN s).qty - q.toNat)],
          hout, ?_⟩, ?_⟩
        · intro l hl'
          rw [hord' l (hbandA l hl').1, ite_eq_right (hbandA l hl').2]
          exact h.above l hl'
        · intro l hl'
          rw [hord' l (hbandO l hl').1, ite_eq_right (hbandO l hl').2]
          exact h.own l hl'
        · rcases hfc with ⟨h1, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, -, -, h3⟩ |
            ⟨-, hlt, -, -, -⟩
          · rcases h1 with h1 | h1
            · exact absurd h1 hremN
            · rw [hacco] at h1
              exact absurd h1 (by simp)
          · exact absurd h2 ha
          · rw [hR, h3, hA]
            simp [Spec.exhaust, hoqty]
          · omega
        · have := matchMeasure_le side limit { m with
            book := Program.unlink m.book (Program.level (1 - side) m.price) 0 s,
            out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
              m.book.acct[s.toNat]! (q - q),
            rem := m.rem - q }
          rw [hrest'] at this
          rw [hmeas]
          simp only at this
          omega
      · have hqrem : q = m.rem := by
          have : q.toNat = m.rem.toNat := by
            have : q.toNat ≠ mq.toNat := fun he => hqm (UInt64.toNat_inj.1 he)
            omega
          exact UInt64.toNat_inj.1 this
        have hlt : m.rem.toNat < mq.toNat := by
          have : q.toNat ≠ mq.toNat := fun he => hqm (UInt64.toNat_inj.1 he)
          omega
        have hnotS : ∀ l, BandLevel l → l ≠ lvN → s ∉ levelSlots m.book l :=
          fun l hl' hne hm => hne (h.shape.disjoint hl' hband hm (by rw [hxB]; simp))
        have hord' : ∀ l, BandLevel l → l ≠ lvN →
            ordersAt { m.book with qty := m.book.qty.set! s.toNat (mq - q) } l =
              ordersAt m.book l :=
          fun l hl' hne => setQ_ordersAt_ne h.shape hsz (hnotS l hl' hne)
        have hrest' : restOf (1 - side) { m with
            book := { m.book with qty := m.book.qty.set! s.toNat (mq - q) },
            out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
              m.book.acct[s.toNat]! (mq - q),
            rem := m.rem - q } = { orderAt m.book lvN s with qty := (mq - q).toNat } ::
              (B.map (orderAt m.book lvN) ++ restAfter) := by
          simp only [restOf, hfrom, List.flatMap_cons]
          rw [setQ_ordersAt_head h.shape hsz hxB hnodup.1, ← hRA, List.cons_append]
          congr 2
          exact flatMap_congr fun l hl' => hord' l (hbandF l hl').1 (hbandF l hl').2
        have hA : absOf taker account side limit { m with
            book := { m.book with qty := m.book.qty.set! s.toNat (mq - q) },
            out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
              m.book.acct[s.toNat]! (mq - q),
            rem := m.rem - q } = ⟨{ orderAt m.book lvN s with qty := (mq - q).toNat } ::
              (B.map (orderAt m.book lvN) ++ restAfter), [], 0, false⟩ := by
          unfold absOf
          rw [hrest']
          simp only [hst, Bool.false_eq_true, ite_false]
          rw [UInt64.toNat_sub_of_le _ _ hqr, hqrem, Nat.sub_self, fill_zero]
        simp only [hqm, ite_false]
        refine ⟨⟨setQ_shape h.shape, by rw [setQ_size]; exact h.count, h.nextId, h.price,
          ?_, ?_, T ++ [.trade (orderAt m.book lvN s).id taker (orderAt m.book lvN s).price
            q.toNat (orderAt m.book lvN s).account ((orderAt m.book lvN s).qty - q.toNat)],
          hout, ?_⟩, ?_⟩
        · intro l hl'
          rw [hord' l (hbandA l hl').1 (hbandA l hl').2]
          exact h.above l hl'
        · intro l hl'
          rw [hord' l (hbandO l hl').1 (hbandO l hl').2]
          exact h.own l hl'
        · rcases hfc with ⟨h1, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, -, hle, -⟩ |
            ⟨-, -, -, -, h3⟩
          · rcases h1 with h1 | h1
            · exact absurd h1 hremN
            · rw [hacco] at h1
              exact absurd h1 (by simp)
          · exact absurd h2 ha
          · rw [hoqty] at hle
            omega
          · rw [hR, h3, hA, UInt64.toNat_sub_of_le _ _ hqle, hoqty, hqrem]
            simp
        · have : matchCond side limit { m with
              book := { m.book with qty := m.book.qty.set! s.toNat (mq - q) },
              out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
                m.book.acct[s.toNat]! (mq - q),
              rem := m.rem - q } = false := by
            simp [matchCond, hqrem]
          rw [show matchMeasure side limit { m with
              book := { m.book with qty := m.book.qty.set! s.toNat (mq - q) },
              out := Program.emit m.out 3 m.book.oid[s.toNat]! taker m.price q
                m.book.acct[s.toNat]! (mq - q),
              rem := m.rem - q } = 0 by unfold matchMeasure; rw [this]; rfl, hmeas]
          omega

/-! ## The whole loop -/

/-- A state where the loop condition fails represents the orders not reached, no trades, its
remaining quantity, and its self-trade flag. -/
theorem absOf_stop {b0 : Book} {out0 : Array UInt64} {taker account side limit : UInt64}
    {R0 : Spec.Fill} (hs : side ≤ 1) {m : Matching}
    (h : MatchInv b0 out0 taker account side limit R0 m) (hc : matchCond side limit m = false) :
    absOf taker account side limit m = ⟨restOf (1 - side) m, [], m.rem.toNat, m.selfTrade⟩ := by
  unfold absOf
  cases hst : m.selfTrade
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hr : m.rem = 0
    · rw [hr]
      exact fill_zero _ _ _ _ _
    · have ha : Program.acceptable side limit m.price = false := by
        simpa [matchCond, hst, hr] using hc
      apply fill_stop_price
      intro o ho
      have hpo := price_of_mem_rest (List.mem_of_mem_head? ho)
      rw [acceptable_eq] at ha
      have hpr := h.price
      rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
      · rw [h1] at hpo
        simp only [show ¬ (1 : UInt64) = 0 by decide, ite_false] at hpo
        simp [toSide, Spec.acceptable] at ha ⊢
        omega
      · rw [h1] at hpo
        simp only [ite_true] at hpo
        simp [toSide, Spec.acceptable] at ha ⊢
        omega
  · rfl

/-- The outcome of `Spec.fill` for an incoming order of side word `side` on the opposite side of
the book `b0`. -/
def fillOutcome (b0 : Book) (taker account side limit q : UInt64) : Spec.Fill :=
  Spec.fill taker account (toSide side) limit.toNat q.toNat
    (Spec.opposite (toSpec b0) (toSide side))

/-- The first state of matching satisfies the invariant. -/
theorem matchInv_init {b0 : Book} (hsh : Shape b0) (hc : b0.count.toNat = Spec.size (toSpec b0))
    (out0 : Array UInt64) (taker account : UInt64) {side limit : UInt64} (q : UInt64)
    (hs : side ≤ 1) :
    MatchInv b0 out0 taker account side limit (fillOutcome b0 taker account side limit q)
      ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩ := by
  have hstart : (if 1 - side = 0 then (if side == 0 then 1 else Program.maxPrice).toNat ≤ 1023
      else 1 ≤ (if side == 0 then 1 else Program.maxPrice).toNat ∧
        (if side == 0 then 1 else Program.maxPrice).toNat ≤ 1024) ∧
      aboveLevels (1 - side) (if side == 0 then 1 else Program.maxPrice).toNat = [] := by
    rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
    · rw [h1]
      simp [aboveLevels]
    · rw [h1]
      simp [aboveLevels, Program.maxPrice]
  have hrest :
      restOf (1 - side) ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩ =
      Spec.opposite (toSpec b0) (toSide side) := by
    rw [opposite_toSide _ hs, toSpec_eq, sideList_ofLevels, restOf]
    exact (flatMap_levelsOf hstart.1 (by rw [hstart.2]; simp)).symm
  refine ⟨hsh, hc, rfl, hstart.1, by rw [hstart.2]; simp, fun _ _ => rfl, [],
    by simp [Spec.encodeAll], ?_⟩
  simp only [absOf, Bool.false_eq_true, ite_false, hrest, List.nil_append]
  rfl

/-- `fill` keeps the structural invariant and the count, and gives the book, the remaining
quantity, the self-trade flag, and the trade words of `Spec.fill` on the opposite side. -/
theorem fill_refines {b0 : Book} (hsh : Shape b0) (hc : b0.count.toNat = Spec.size (toSpec b0))
    (hb : Spec.size (toSpec b0) ≤ 4096) (out0 : Array UInt64) (taker account : UInt64)
    {side limit : UInt64} (q : UInt64) (hs : side ≤ 1)
    (hl : 1 ≤ limit.toNat ∧ limit.toNat ≤ 1023) :
    Shape (Program.fill b0 out0 taker account side limit q).book ∧
      (Program.fill b0 out0 taker account side limit q).book.count.toNat =
        Spec.size (toSpec (Program.fill b0 out0 taker account side limit q).book) ∧
      toSpec (Program.fill b0 out0 taker account side limit q).book =
        Spec.setOpposite (toSpec b0) (toSide side)
          (fillOutcome b0 taker account side limit q).others ∧
      (Program.fill b0 out0 taker account side limit q).rem.toNat =
        (fillOutcome b0 taker account side limit q).remaining ∧
      (Program.fill b0 out0 taker account side limit q).selfTrade =
        (fillOutcome b0 taker account side limit q).selfTrade ∧
      (Program.fill b0 out0 taker account side limit q).out =
        out0 ++ Spec.encodeAll (fillOutcome b0 taker account side limit q).trades := by
  have hI0 := matchInv_init hsh hc out0 taker account (limit := limit) q hs
  have hμ : matchMeasure side limit
      ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩ ≤
        Program.matchFuel.toNat := by
    have h1 := matchMeasure_le side limit
      ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩
    have h2 : (fromLevels (1 - side) (if side == 0 then 1 else Program.maxPrice).toNat).length =
        1023 := by
      rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
      · rw [h1]
        simp [fromLevels]
      · rw [h1]
        simp [fromLevels, Program.maxPrice]
    have h3 : (restOf (1 - side)
        ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩).length ≤ 4096 := by
      obtain ⟨T, -, hR⟩ := hI0.out
      have hrest : restOf (1 - side)
          ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩ =
          Spec.opposite (toSpec b0) (toSide side) := by
        have := congrArg Spec.Fill.others hR
        simp only [absOf, Bool.false_eq_true, ite_false] at this
        rw [opposite_toSide _ hs, toSpec_eq, sideList_ofLevels, restOf]
        rcases side_cases hs with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
        · rw [h1]
          exact (flatMap_levelsOf (by simp) (by simp [aboveLevels])).symm
        · rw [h1]
          exact (flatMap_levelsOf (by simp [Program.maxPrice])
            (by simp [aboveLevels, Program.maxPrice])).symm
      rw [hrest]
      have : (Spec.opposite (toSpec b0) (toSide side)).length ≤ Spec.size (toSpec b0) := by
        rcases side_cases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
          simp [Spec.opposite, toSide, Spec.size]
      omega
    rw [h2] at h1
    simp only [Program.matchFuel, UInt64.reduceToNat]
    omega
  have hloop := repeatWhile_inv (fuel := Program.matchFuel)
    (init := ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩)
    (cond := matchCond side limit) (step := Program.matchStep taker account side)
    (MatchInv b0 out0 taker account side limit (fillOutcome b0 taker account side limit q))
    (matchMeasure side limit) hI0 hμ (fun m hm hcm => matchInv_step hs hl hm hcm)
  have hfill : Program.fill b0 out0 taker account side limit q =
      LeanExe.repeatWhile Program.matchFuel
        ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩
        (matchCond side limit) (Program.matchStep taker account side) := rfl
  rw [hfill]
  generalize LeanExe.repeatWhile Program.matchFuel
    ⟨b0, out0, if side == 0 then 1 else Program.maxPrice, q, false⟩
    (matchCond side limit) (Program.matchStep taker account side) = mf at hloop
  obtain ⟨hI, hcf⟩ := hloop
  have hA := absOf_stop hs hI hcf
  obtain ⟨T, hT, hR⟩ := hI.out
  rw [hA] at hR
  simp only [List.append_nil] at hR
  rw [hR]
  refine ⟨hI.shape, hI.count, ?_, rfl, rfl, hT⟩
  rw [toSpec_eq, toSpec_eq, hI.nextId, ofLevels_setOpposite hs _ hI.own, restOf]
  rw [flatMap_levelsOf hI.price hI.above]

/-! ## Submission -/

/-- The chains after a new next id are the same. -/
theorem levelSlots_nextId (b : Book) (n : UInt64) (l : Nat) :
    levelSlots { b with nextId := n } l = levelSlots b l := by
  apply levelSlots_congr <;> rfl

/-- A new next id keeps the structural invariant. -/
theorem shape_nextId {b : Book} (h : Shape b) (n : UInt64) : Shape { b with nextId := n } where
  oidSize := h.oidSize
  acctSize := h.acctSize
  qtySize := h.qtySize
  lvlSize := h.lvlSize
  nxtSize := h.nxtSize
  headSize := h.headSize
  tailSize := h.tailSize
  chainNodup l hl := by rw [levelSlots_nextId]; exact h.chainNodup l hl
  chainSlots l hl t ht := by rw [levelSlots_nextId] at ht; exact h.chainSlots l hl t ht
  chainTail l hl := by rw [levelSlots_nextId]; exact h.chainTail l hl
  used t h1 h2 hne := by rw [levelSlots_nextId]; exact h.used t h1 h2 hne
  oidPos l hl t ht := by rw [levelSlots_nextId] at ht; exact h.oidPos l hl t ht

/-- A new next id changes only the next id of `toSpec`. -/
theorem toSpec_nextId (b : Book) (n : UInt64) :
    toSpec { b with nextId := n } = { toSpec b with nextId := n } := by
  have : ordersAt { b with nextId := n } = ordersAt b := by
    funext l
    unfold ordersAt
    rw [levelSlots_nextId]
    rfl
  rw [toSpec_eq, toSpec_eq, this]
  simp only [ofLevels]

/-- The next id of `toSpec` is the book's. -/
theorem toSpec_nextId_eq (b : Book) : (toSpec b).nextId = b.nextId := rfl

/-- `submit` keeps the invariant and gives the book and the event words of `Spec.submit`. -/
theorem submit_refines {b : Book} (h : Inv b) (hn : b.nextId.toNat < 2 ^ 64 - 1)
    (out : Array UInt64) {side limit : UInt64} (q account tag tif : UInt64) (tf : Spec.Tif)
    (hs : side ≤ 1) (hl : 1 ≤ limit.toNat ∧ limit.toNat ≤ 1023)
    (hq : q.toNat ≤ Spec.maxQty) (htf : tf = .ioc ↔ tif = 1) :
    Inv (Program.submit b out side limit q account tag tif).1 ∧
      toSpec (Program.submit b out side limit q account tag tif).1 =
        (Spec.submit (toSpec b) (toSide side) limit.toNat q.toNat account tag tf).1 ∧
      (Program.submit b out side limit q account tag tif).2 =
        out ++ Spec.encodeAll
          (Spec.submit (toSpec b) (toSide side) limit.toNat q.toNat account tag tf).2 := by
  suffices H : Shape (Program.submit b out side limit q account tag tif).1 ∧
      (Program.submit b out side limit q account tag tif).1.count.toNat =
        Spec.size (toSpec (Program.submit b out side limit q account tag tif).1) ∧
      toSpec (Program.submit b out side limit q account tag tif).1 =
        (Spec.submit (toSpec b) (toSide side) limit.toNat q.toNat account tag tf).1 ∧
      (Program.submit b out side limit q account tag tif).2 =
        out ++ Spec.encodeAll
          (Spec.submit (toSpec b) (toSide side) limit.toNat q.toNat account tag tf).2 by
    refine ⟨Inv.of_shape H.1 H.2.1 ?_, H.2.2⟩
    rw [H.2.2.1]
    exact Spec.valid_submit h.valid hn _ _ _ _ hl hq
  have hsh := h.shape
  have hsh0 := shape_nextId hsh (b.nextId + 1)
  have hts0 := toSpec_nextId b (b.nextId + 1)
  have hsize0 : Spec.size (toSpec { b with nextId := b.nextId + 1 }) = Spec.size (toSpec b) := by
    rw [hts0]
    simp only [Spec.size]
  have hF := fill_refines hsh0 (by rw [hsize0]; exact h.count)
    (by rw [hsize0]; exact h.valid.bounded)
    (Program.emit out 1 b.nextId tag 0 0 0 0) b.nextId account q hs hl
  have hP : ∀ m : Matching, m = Program.fill { b with nextId := b.nextId + 1 }
      (Program.emit out 1 b.nextId tag 0 0 0 0) b.nextId account side limit q →
      Program.submit b out side limit q account tag tif =
        if m.rem == 0 then (m.book, m.out)
        else if m.selfTrade then (m.book, Program.emit m.out 4 b.nextId m.rem 3 0 0 0)
        else if tif == 1 then (m.book, Program.emit m.out 4 b.nextId m.rem 2 0 0 0)
        else if m.book.count < Program.capacity then
          (Program.place m.book side limit b.nextId account m.rem, m.out)
        else (m.book, Program.emit m.out 4 b.nextId m.rem 4 0 0 0) := by
    rintro m rfl
    rfl
  have hQ : ∀ f : Spec.Fill, f = fillOutcome { b with nextId := b.nextId + 1 } b.nextId account
      side limit q →
      Spec.submit (toSpec b) (toSide side) limit.toNat q.toNat account tag tf =
        if f.remaining = 0 then
          (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 }) (toSide side) f.others,
            .accepted b.nextId tag :: f.trades)
        else if f.selfTrade then
          (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 }) (toSide side) f.others,
            .accepted b.nextId tag :: f.trades ++ [.cancelled b.nextId f.remaining .selfTrade])
        else if tf = .ioc then
          (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 }) (toSide side) f.others,
            .accepted b.nextId tag :: f.trades ++ [.cancelled b.nextId f.remaining .ioc])
        else if Spec.size (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 })
            (toSide side) f.others) < Spec.capacity then
          (Spec.rest (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 }) (toSide side)
            f.others) ⟨b.nextId, account, toSide side, limit.toNat, f.remaining⟩,
            .accepted b.nextId tag :: f.trades)
        else
          (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 }) (toSide side) f.others,
            .accepted b.nextId tag :: f.trades ++ [.cancelled b.nextId f.remaining .bookFull]) := by
    rintro f rfl
    simp only [Spec.submit, fillOutcome, toSpec_nextId_eq, hts0]
    rfl
  generalize hm : Program.fill { b with nextId := b.nextId + 1 }
    (Program.emit out 1 b.nextId tag 0 0 0 0) b.nextId account side limit q = m at hF hP
  generalize hf : fillOutcome { b with nextId := b.nextId + 1 } b.nextId account side limit q = f
    at hF hQ
  rw [hP m rfl, hQ f rfl]
  obtain ⟨hshm, hcm, htsm, hrem, hst, hout⟩ := hF
  have hout' : m.out = out ++ Spec.encodeAll (.accepted b.nextId tag :: f.trades) := by
    rw [hout, encodeAll_cons, emit_eq]
    simp [Spec.encode]
  have hcancel : ∀ (w : UInt64) (r : Spec.CancelReason), Spec.cancelCode r = w →
      Program.emit m.out 4 b.nextId m.rem w 0 0 0 =
        out ++ Spec.encodeAll (.accepted b.nextId tag :: f.trades ++
          [.cancelled b.nextId f.remaining r]) := by
    intro w r hw
    subst hw
    rw [emit_eq, encodeAll_append, ← Array.append_assoc, ← hout', ← hrem]
    simp [Spec.encodeAll, Spec.encode]
  by_cases h1 : f.remaining = 0
  · have : (m.rem == 0) = true := by
      rw [beq_iff_eq]
      exact UInt64.toNat_inj.1 (by rw [hrem, h1]; rfl)
    simp only [this, h1, ↓reduceIte]
    exact ⟨hshm, hcm, htsm, hout'⟩
  have h1' : (m.rem == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    rw [he] at hrem
    exact h1 hrem.symm
  simp only [h1, h1', Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : f.selfTrade = true
  · have h2m : m.selfTrade = true := by rw [hst]; exact h2
    simp only [h2m, h2, ↓reduceIte]
    exact ⟨hshm, hcm, htsm, hcancel 3 .selfTrade rfl⟩
  have h2' : m.selfTrade = false := by rw [hst]; simpa using h2
  simp only [h2', Bool.false_eq_true, ↓reduceIte, show f.selfTrade = false by simpa using h2]
  by_cases h3 : tf = .ioc
  · have : (tif == 1) = true := by rw [beq_iff_eq]; exact htf.1 h3
    simp only [this, h3, ↓reduceIte]
    exact ⟨hshm, hcm, htsm, hcancel 2 .ioc rfl⟩
  have h3' : (tif == 1) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun he => h3 (htf.2 he)
  simp only [h3', h3, Bool.false_eq_true, ↓reduceIte]
  have hcount : m.book.count < Program.capacity ↔
      Spec.size (Spec.setOpposite (toSpec { b with nextId := b.nextId + 1 }) (toSide side)
        f.others) < Spec.capacity := by
    rw [← htsm, ← hcm, UInt64.lt_iff_toNat_lt]
    simp [Program.capacity, Spec.capacity]
  by_cases h4 : m.book.count < Program.capacity
  · simp only [h4, hcount.1 h4, ↓reduceIte]
    rw [place_eq]
    have hsz : Spec.size (toSpec m.book) < 4096 := by
      rw [← hcm]
      have := UInt64.lt_iff_toNat_lt.1 h4
      simpa [Program.capacity] using this
    obtain ⟨hs1, hs2, hs3⟩ := freeSlot_spec (hshm.exists_free hsz)
    have hlvN := toNat_level hs (p := limit) (by omega)
    have hside := levelSide_level hs (p := limit.toNat) (by omega)
    have hband : BandLevel (Program.level side limit).toNat := by
      rw [hlvN]
      have := UInt64.le_iff_toNat_le.1 hs
      simp at this
      constructor <;> omega
    have hpa : PlaceAt m.book (Program.level side limit) (Program.freeSlot m.book.oid) :=
      ⟨hband, hs1, hs2, hs3⟩
    have hid : b.nextId ≠ 0 := fun he => by
      have := h.valid.nextPositive
      rw [toSpec_nextId_eq, he] at this
      simp at this
    refine ⟨placed_shape hshm hpa hid, ?_, ?_, hout'⟩
    · show (m.book.count + 1).toNat = _
      rw [placed_size hshm hpa, toNat_add_one (by omega), hcm]
    · have ho : (⟨b.nextId, account, toSide side, limit.toNat, f.remaining⟩ : Spec.Order) =
          ⟨b.nextId, account, levelSide (Program.level side limit).toNat,
            levelPrice (Program.level side limit).toNat, m.rem.toNat⟩ := by
        rw [hlvN, hside.1, hside.2, hrem]
      rw [toSpec_eq, ofLevels_congr (fun l hl => placed_ordersAt hshm hpa hl), ← htsm, toSpec_eq,
        ho, rest_ofLevels (levelsOK_ordersAt _) _ hband rfl rfl]
      have hn : (placed m.book (Program.level side limit) (Program.freeSlot m.book.oid) b.nextId
          account m.rem).nextId = m.book.nextId := rfl
      rw [hn]
      apply congrArg (fun F => ofLevels F m.book.nextId)
      funext l
      by_cases he : l = (Program.level side limit).toNat
      · rw [ite_eq_left he, ite_eq_left he, he]
      · rw [ite_eq_right he, ite_eq_right he]
  · simp only [h4, (not_congr hcount).1 h4, ↓reduceIte]
    exact ⟨hshm, hcm, htsm, hcancel 4 .bookFull rfl⟩

end Demos.OrderBook.Refinement
