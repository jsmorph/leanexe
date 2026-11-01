import Demos.OrderBook.RefineMatch

/-! The refinement of one step of [the specification](Spec.lean) by [the program](Program.lean),
and the program's top of the book and empty book.  `step_eq` follows the branches of
`Program.step` and `Spec.step` on the record at the offset: a rejection leaves the book and gives
one `rejected` event, a limit or market order goes to `submit_refines`, and a cancel or reduce
finds the order's slot with `findSlot` and changes that slot alone. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

/-! ## The empty book -/

/-- Every element of an array built of zeros is 0. -/
theorem build_zero_get (n : UInt64) (i : Nat) :
    (LeanExe.build n (fun _ => (0 : UInt64)))[i]! = 0 := by
  unfold LeanExe.build
  by_cases h : i < n.toNat
  · simp [h]
  · simp [h]
    rfl

/-- An array built of `n` zeros has `n` elements. -/
theorem build_zero_size (n : UInt64) :
    (LeanExe.build n (fun _ => (0 : UInt64))).size = n.toNat := by
  simp [LeanExe.build]

/-- Every level of the empty book is empty. -/
theorem levelSlots_init (l : Nat) : levelSlots (Program.init ()) l = [] :=
  levelSlots_eq_nil.2 (by simp only [Program.init]; exact build_zero_get _ _)

/-- The empty book holds no orders. -/
theorem ordersAt_init : ordersAt (Program.init ()) = fun _ => [] := by
  funext l
  unfold ordersAt
  rw [levelSlots_init]
  rfl

/-! ## Results -/

/-- A program result keeps the invariant and gives the book and the event words of a
specification result, after the words `out`. -/
def Rel (out : Array UInt64) (r : Book × Array UInt64) (R : Spec.Book × List Spec.Event) : Prop :=
  Inv r.1 ∧ toSpec r.1 = R.1 ∧ r.2 = out ++ Spec.encodeAll R.2

/-- A rejection of the program refines the specification's rejection with its reason's code. -/
theorem reject_rel {b : Book} (h : Inv b) (out : Array UInt64) (kind ref : UInt64)
    (reason : Spec.RejectReason) :
    Rel out (Program.reject b out kind ref (Spec.rejectCode reason))
      (Spec.reject (toSpec b) kind ref reason) := by
  refine ⟨h, rfl, ?_⟩
  simp only [Program.reject, Spec.reject, emit_eq]
  simp [Spec.encodeAll, Spec.encode]

/-! ## Finding an order -/

/-- Every order of the specification's book is the order of a slot of a chain of the band. -/
theorem mem_toSpec_iff {b : Book} {x : Spec.Order} :
    x ∈ (toSpec b).bids ++ (toSpec b).asks ↔
      ∃ l, BandLevel l ∧ ∃ t ∈ levelSlots b l, x = orderAt b l t := by
  rw [toSpec_eq]
  simp only [ofLevels, ← List.flatMap_append, List.mem_flatMap, ordersAt, List.mem_map,
    List.mem_append]
  constructor
  · rintro ⟨l, hl, t, ht, rfl⟩
    exact ⟨l, bandLevel_iff.2 hl, t, ht, rfl⟩
  · rintro ⟨l, hl, t, ht, rfl⟩
    exact ⟨l, bandLevel_iff.1 hl, t, ht, rfl⟩

/-- When `findSlot` gives 0, no order of the specification's book has the id. -/
theorem find_none {b : Book} (h : Inv b) {id : UInt64} (hs : Program.findSlot b.oid id = 0) :
    Spec.find (toSpec b) id = none := by
  rw [Spec.find_eq_none]
  intro x hx hid
  obtain ⟨l, hl, t, ht, rfl⟩ := mem_toSpec_iff.1 hx
  have hpos := h.shape.oidPos l hl t ht
  have hb := h.shape.chainSlots l hl t ht
  rcases (findSlot_spec b.oid id).1 hs with h0 | hno
  · exact hpos (hid.trans h0)
  · exact hno t.toNat hb.1 hb.2.1 hid

/-- When `findSlot` gives a slot, it lies in the chain of its level, and the specification's
`find` gives its order. -/
theorem find_some {b : Book} (h : Inv b) {id : UInt64} (hs : Program.findSlot b.oid id ≠ 0) :
    BandLevel (b.lvl[(Program.findSlot b.oid id).toNat]!).toNat ∧
      Program.findSlot b.oid id ∈
        levelSlots b (b.lvl[(Program.findSlot b.oid id).toNat]!).toNat ∧
      b.oid[(Program.findSlot b.oid id).toNat]! = id ∧
      Spec.find (toSpec b) id = some (orderAt b (b.lvl[(Program.findSlot b.oid id).toNat]!).toNat
        (Program.findSlot b.oid id)) := by
  obtain ⟨h1, h2, h3⟩ := (findSlot_spec b.oid id).2 hs
  generalize Program.findSlot b.oid id = s at h1 h2 h3 ⊢
  have hid0 : id ≠ 0 := by
    intro he
    subst he
    have := (findSlot_spec b.oid 0).1
    simp [Program.findSlot] at hs
  have hne : b.oid[s.toNat]! ≠ 0 := by rw [h3]; exact hid0
  obtain ⟨hb, hm⟩ := h.used s.toNat h1 h2 hne
  have hs' : s.toNat.toUInt64 = s := by simp
  rw [hs'] at hm
  refine ⟨hb, hm, h3, ?_⟩
  have := Spec.find_of_mem h.valid (mem_toSpec hb hm)
  rw [show (orderAt b (b.lvl[s.toNat]!).toNat s).id = id from h3] at this
  exact this

/-! ## Cancel and reduce -/

/-- A cancel of the order in a slot of a chain refines the specification's removal of its id. -/
theorem cancel_rel {b : Book} (h : Inv b) (out : Array UInt64) {id s : UInt64}
    (hb : BandLevel (b.lvl[s.toNat]!).toNat) (hm : s ∈ levelSlots b (b.lvl[s.toNat]!).toNat)
    (hid : b.oid[s.toNat]! = id) :
    Rel out (Program.cancel b out id s)
      (Spec.remove (toSpec b) id,
        [.cancelled id (orderAt b (b.lvl[s.toNat]!).toNat s).qty .requested]) := by
  have hsh := h.shape
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hm
  have hpr := predecessor_spec hsh hb hAB
  have hcancel : Program.cancel b out id s =
      (Program.unlink b b.lvl[s.toNat]! (Program.predecessor b.head b.nxt b.lvl[s.toNat]! s) s,
        Program.emit out 4 id b.qty[s.toNat]! 1 0 0 0) := rfl
  rw [hcancel]
  generalize b.lvl[s.toNat]! = lv at hb hm hAB hpr ⊢
  generalize Program.predecessor b.head b.nxt lv s = pr at hpr ⊢
  have hu : UnlinkAt b lv pr s A B := ⟨hb, hAB, hpr⟩
  have hn := hsh.chainNodup _ hb
  rw [hAB] at hn
  have hsA : s ∉ A := fun hs => (List.nodup_append.1 hn).2.2 s hs s (by simp) rfl
  have hsB : s ∉ B := ((List.nodup_append.1 hn).2.1 |> List.nodup_cons.1).1
  have hne : ∀ l, BandLevel l → ∀ t ∈ levelSlots b l, t ≠ s → b.oid[t.toNat]! ≠ id :=
    fun l hl t ht hts he => hts (h.oid_inj hl hb ht hm (he.trans hid.symm))
  have hts : toSpec (Program.unlink b lv pr s) = Spec.remove (toSpec b) id := by
    rw [toSpec_eq, toSpec_eq, remove_ofLevels,
      show (Program.unlink b lv pr s).nextId = b.nextId from rfl]
    apply ofLevels_congr
    intro l hl
    rw [unlink_ordersAt hsh hu hl]
    unfold ordersAt
    rw [List.filter_map]
    by_cases he : l = lv.toNat
    · subst he
      rw [ite_eq_left rfl, hAB, List.filter_append, List.filter_cons]
      have hs' : ((fun o : Spec.Order => o.id != id) ∘ orderAt b lv.toNat) s = false := by
        simp [orderAt, hid]
      simp only [hs', Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_eq_self.2, List.filter_eq_self.2]
      · intro t ht
        have := hne _ hb t (by rw [hAB]; simp [ht]) (fun he => hsB (he ▸ ht))
        simp [orderAt, this]
      · intro t ht
        have := hne _ hb t (by rw [hAB]; simp [ht]) (fun he => hsA (he ▸ ht))
        simp [orderAt, this]
    · rw [ite_eq_right he, List.filter_eq_self.2]
      intro t ht
      have := hne l hl t ht (fun he' => he (hsh.disjoint hl hb ht (he' ▸ hm)))
      simp [orderAt, this]
  refine ⟨Inv.of_shape (unlink_shape hsh hu) (unlink_count hsh hu h.count)
    (hts ▸ Spec.valid_remove h.valid id), hts, ?_⟩
  simp only [emit_eq]
  simp [Spec.encodeAll, Spec.encode, Spec.cancelCode, orderAt]

/-- A reduction of the order in a slot of a chain refines the specification's quantity update of
its id. -/
theorem reduce_rel {b : Book} (h : Inv b) (out : Array UInt64) {id s q : UInt64}
    (hb : BandLevel (b.lvl[s.toNat]!).toNat) (hm : s ∈ levelSlots b (b.lvl[s.toNat]!).toNat)
    (hid : b.oid[s.toNat]! = id) (hq : 1 ≤ q.toNat ∧ q.toNat ≤ Spec.maxQty) :
    Rel out (Program.reduce b out id s q)
      (Spec.setQty (toSpec b) id q.toNat, [.reduced id q.toNat]) := by
  have hsh := h.shape
  have hsz : s.toNat < 4097 := hsh.lt_size hb hm
  have hred : Program.reduce b out id s q =
      ({ b with qty := b.qty.set! s.toNat q }, Program.emit out 5 id q 0 0 0 0) := rfl
  rw [hred]
  have hts : toSpec { b with qty := b.qty.set! s.toNat q } = Spec.setQty (toSpec b) id q.toNat := by
    rw [toSpec_eq, toSpec_eq, setQty_ofLevels,
      show ({ b with qty := b.qty.set! s.toNat q } : Book).nextId = b.nextId from rfl]
    apply ofLevels_congr
    intro l hl
    rw [setQ_ordersAt hsh hsz]
    unfold ordersAt
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    by_cases hts : t = s
    · subst hts
      simp [orderAt, hid]
    · have : b.oid[t.toNat]! ≠ id := fun he => hts (h.oid_inj hl hb ht hm (he.trans hid.symm))
      simp [hts, orderAt, this]
  refine ⟨Inv.of_shape (setQ_shape hsh) (by rw [setQ_size]; exact h.count)
    (hts ▸ Spec.valid_setQty h.valid id hq), hts, ?_⟩
  simp only [emit_eq]
  simp [Spec.encodeAll, Spec.encode]

/-! ## Records -/

/-- A word of the record at an offset with seven words to spare is the stream's word. -/
theorem recordAt_get {ws : Array UInt64} {o k : Nat} (hk : k < 7) (h7 : o + 7 ≤ ws.size) :
    (recordAt ws o)[k]! = ws[o + k]! := by
  unfold recordAt
  have hsz : k < (ws.extract o (o + 7)).size := by rw [Array.size_extract]; omega
  rw [getElem!_pos (ws.extract o (o + 7)) k hsz, Array.getElem_extract,
    getElem!_pos ws (o + k) (by omega)]

/-- `word` reads the record at the offset. -/
theorem word_eq {ws : Array UInt64} {o : UInt64} (h7 : o.toNat + 7 ≤ ws.size)
    (hs : ws.size < 2 ^ 64) (k : UInt64) (hk : k.toNat < 7) :
    Program.word ws o k = (recordAt ws o.toNat)[k.toNat]! := by
  unfold Program.word
  rw [recordAt_get hk h7, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- The program's test for a short record is the specification's test of the record's size. -/
theorem short_iff {ws : Array UInt64} {o : UInt64} (ho : o.toNat < ws.size)
    (hs : ws.size < 2 ^ 64) :
    ws.size.toUInt64 - o < 7 ↔ (recordAt ws o.toNat).size ≠ 7 := by
  have hsz : ws.size.toUInt64.toNat = ws.size := by
    simp only [Nat.toUInt64_eq]
    exact toNat_ofNat hs
  have hle : o ≤ ws.size.toUInt64 := UInt64.le_iff_toNat_le.2 (by omega)
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ hle, hsz, recordAt, Array.size_extract]
  simp only [UInt64.reduceToNat]
  omega

/-! ## Fields -/

/-- The specification's time in force of a word from 0 to 2. -/
def toTif (w : UInt64) : Spec.Tif := if w = 0 then .gtc else if w = 1 then .ioc else .postOnly

/-- `sideOf` of a side word of at most 1. -/
theorem sideOf_le {w : UInt64} (hw : w ≤ 1) : Spec.sideOf w = some (toSide w) := by
  rcases side_cases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

/-- `tifOf` of a word of at most 2. -/
theorem tifOf_le {w : UInt64} (hw : w ≤ 2) : Spec.tifOf w = some (toTif w) := by
  have : w.toNat ≤ 2 := by simpa using UInt64.le_iff_toNat_le.1 hw
  have h3 : w = 0 ∨ w = 1 ∨ w = 2 := by
    rcases (by omega : w.toNat = 0 ∨ w.toNat = 1 ∨ w.toNat = 2) with h | h | h
    · exact Or.inl (UInt64.toNat_inj.1 (by rw [h]; rfl))
    · exact Or.inr (Or.inl (UInt64.toNat_inj.1 (by rw [h]; rfl)))
    · exact Or.inr (Or.inr (UInt64.toNat_inj.1 (by rw [h]; rfl)))
  rcases h3 with rfl | rfl | rfl <;> rfl

/-- The time in force of a word is IOC exactly for the word 1. -/
theorem toTif_ioc (w : UInt64) : toTif w = .ioc ↔ w = 1 := by
  unfold toTif
  by_cases h0 : w = 0
  · simp [h0]
  · by_cases h1 : w = 1
    · simp [h1]
    · simp [h0, h1]

/-- The time in force of a word is post-only exactly for the word 2, when the word is at most 2. -/
theorem toTif_post {w : UInt64} (hw : w ≤ 2) : (toTif w == .postOnly) = (w == 2) := by
  have : w.toNat ≤ 2 := by simpa using UInt64.le_iff_toNat_le.1 hw
  unfold toTif
  by_cases h0 : w = 0
  · subst h0
    rfl
  · by_cases h1 : w = 1
    · subst h1
      rfl
    · have h2 : w = 2 := UInt64.toNat_inj.1 (by
        have : w.toNat ≠ 0 := fun he => h0 (UInt64.toNat_inj.1 (by rw [he]; rfl))
        have : w.toNat ≠ 1 := fun he => h1 (UInt64.toNat_inj.1 (by rw [he]; rfl))
        simp only [UInt64.reduceToNat]
        omega)
      subst h2
      rfl

/-- The program's range test of a price is the specification's. -/
theorem inRange_price (w : UInt64) :
    Program.inRange 1 Program.maxPrice w = Spec.inRange 1 Spec.maxPrice w := by
  unfold Program.inRange Spec.inRange
  have h1 : (1 ≤ w) ↔ (1 ≤ w.toNat) := by rw [UInt64.le_iff_toNat_le]; rfl
  have h2 : (w ≤ Program.maxPrice) ↔ (w.toNat ≤ Spec.maxPrice) := by
    rw [UInt64.le_iff_toNat_le]; rfl
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [h1, h2]

/-- The program's range test of a quantity is the specification's. -/
theorem inRange_qty (w : UInt64) :
    Program.inRange 1 Program.maxQty w = Spec.inRange 1 Spec.maxQty w := by
  unfold Program.inRange Spec.inRange
  have h1 : (1 ≤ w) ↔ (1 ≤ w.toNat) := by rw [UInt64.le_iff_toNat_le]; rfl
  have h2 : (w ≤ Program.maxQty) ↔ (w.toNat ≤ Spec.maxQty) := by
    rw [UInt64.le_iff_toNat_le]; rfl
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [h1, h2]

/-- A word that passes a range test lies in the range. -/
theorem inRange_true {lo hi : Nat} {w : UInt64} (h : Spec.inRange lo hi w = true) :
    lo ≤ w.toNat ∧ w.toNat ≤ hi := by
  unfold Spec.inRange at h
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-! ## One step -/

/-- The program's `submitArrays` on a book's arrays is `submit` on the book. -/
theorem submitArrays_eq (b : Book) :
    Program.submitArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count =
      Program.submit b := rfl

/-- A limit record refines the specification's limit command. -/
theorem step_limit {b : Book} (h : Inv b) (hn : b.nextId.toNat < 2 ^ 64 - 1)
    (out : Array UInt64) (r : Array UInt64) :
    Rel out
      (if r[1]! > 1 then Program.reject b out 1 r[5]! 3
        else if r[6]! > 2 then Program.reject b out 1 r[5]! 4
        else if !Program.inRange 1 Program.maxPrice r[2]! then Program.reject b out 1 r[5]! 5
        else if !Program.inRange 1 Program.maxQty r[3]! then Program.reject b out 1 r[5]! 6
        else if (r[6]! == 2 && Program.crosses b.head r[1]! r[2]!) = true then
          Program.reject b out 1 r[5]! 9
        else Program.submitArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count
          out r[1]! r[2]! r[3]! r[4]! r[5]! r[6]!)
      (match Spec.sideOf r[1]!, Spec.tifOf r[6]! with
        | none, _ => Spec.reject (toSpec b) 1 r[5]! .badSide
        | some _, none => Spec.reject (toSpec b) 1 r[5]! .badTif
        | some side, some tif =>
          if !Spec.inRange 1 Spec.maxPrice r[2]! then Spec.reject (toSpec b) 1 r[5]! .badPrice
          else if !Spec.inRange 1 Spec.maxQty r[3]! then Spec.reject (toSpec b) 1 r[5]! .badQty
          else if (tif == .postOnly && Spec.crosses (toSpec b) side r[2]!.toNat) = true then
            Spec.reject (toSpec b) 1 r[5]! .wouldCross
          else Spec.submit (toSpec b) side r[2]!.toNat r[3]!.toNat r[4]! r[5]! tif) := by
  by_cases hside : r[1]! ≤ 1
  · have hgt : ¬ (r[1]! > 1) := UInt64.not_lt.2 hside
    rw [sideOf_le hside]
    simp only [hgt, ↓reduceIte]
    by_cases htif : r[6]! ≤ 2
    · have hgt6 : ¬ (r[6]! > 2) := UInt64.not_lt.2 htif
      rw [tifOf_le htif]
      simp only [hgt6, ↓reduceIte, inRange_price, inRange_qty, crosses_spec b hside,
        toTif_post htif]
      cases hp : Spec.inRange 1 Spec.maxPrice r[2]!
      · exact reject_rel h out 1 r[5]! .badPrice
      cases hq : Spec.inRange 1 Spec.maxQty r[3]!
      · exact reject_rel h out 1 r[5]! .badQty
      cases hc : (r[6]! == 2 && Spec.crosses (toSpec b) (toSide r[1]!) r[2]!.toNat)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [submitArrays_eq]
        exact submit_refines h hn out r[3]! r[4]! r[5]! r[6]! (toTif r[6]!) hside
          (inRange_true hp) (inRange_true hq).2 (toTif_ioc r[6]!)
      · exact reject_rel h out 1 r[5]! .wouldCross
    · have hgt6 : r[6]! > 2 := UInt64.not_le.1 htif
      have hnone : Spec.tifOf r[6]! = none := (Spec.tifOf_eq_none _).2 hgt6
      rw [hnone]
      simp only [hgt6, ↓reduceIte]
      exact reject_rel h out 1 r[5]! .badTif
  · have hgt : r[1]! > 1 := UInt64.not_le.1 hside
    have hnone : Spec.sideOf r[1]! = none := (Spec.sideOf_eq_none _).2 hgt
    rw [hnone]
    simp only [hgt, ↓reduceIte]
    exact reject_rel h out 1 r[5]! .badSide

/-- A market record refines the specification's market command. -/
theorem step_market {b : Book} (h : Inv b) (hn : b.nextId.toNat < 2 ^ 64 - 1)
    (out : Array UInt64) (r : Array UInt64) :
    Rel out
      (if r[1]! > 1 then Program.reject b out 2 r[4]! 3
        else if !Program.inRange 1 Program.maxQty r[2]! then Program.reject b out 2 r[4]! 6
        else Program.submitArrays b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count
          out r[1]! (if (r[1]! == 0) = true then Program.maxPrice else 1) r[2]! r[3]! r[4]! 1)
      (match Spec.sideOf r[1]! with
        | none => Spec.reject (toSpec b) 2 r[4]! .badSide
        | some side =>
          if !Spec.inRange 1 Spec.maxQty r[2]! then Spec.reject (toSpec b) 2 r[4]! .badQty
          else Spec.submit (toSpec b) side
            (match side with
              | .buy => Spec.maxPrice
              | .sell => 1)
            r[2]!.toNat r[3]! r[4]! .ioc) := by
  by_cases hside : r[1]! ≤ 1
  · have hgt : ¬ (r[1]! > 1) := UInt64.not_lt.2 hside
    rw [sideOf_le hside]
    simp only [hgt, ↓reduceIte, inRange_qty]
    cases hq : Spec.inRange 1 Spec.maxQty r[2]!
    · simp only [Bool.not_false, ↓reduceIte]
      exact reject_rel h out 2 r[4]! .badQty
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [submitArrays_eq]
      rcases side_cases hside with ⟨h0, -⟩ | ⟨h1, -⟩
      · simp only [h0, beq_self_eq_true, ↓reduceIte]
        have ht : toSide 0 = .buy := rfl
        rw [ht]
        exact submit_refines h hn out r[2]! r[3]! r[4]! 1 .ioc (by decide) (by decide)
          (inRange_true hq).2 (by simp)
      · simp only [h1, show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true,
          ↓reduceIte]
        have ht : toSide 1 = .sell := rfl
        rw [ht]
        exact submit_refines h hn out r[2]! r[3]! r[4]! 1 .ioc (by decide) (by decide)
          (inRange_true hq).2 (by simp)
  · have hgt : r[1]! > 1 := UInt64.not_le.1 hside
    have hnone : Spec.sideOf r[1]! = none := (Spec.sideOf_eq_none _).2 hgt
    rw [hnone]
    simp only [hgt, ↓reduceIte]
    exact reject_rel h out 2 r[4]! .badSide

/-- A cancel record whose id `findSlot` finds refines the specification's cancel command. -/
theorem step_cancel {b : Book} (h : Inv b) (out : Array UInt64) (r : Array UInt64)
    (hs0 : Program.findSlot b.oid r[1]! ≠ 0) :
    Rel out
      (if (Program.findSlot b.oid r[1]! == 0) = true then Program.reject b out 3 r[1]! 7
        else if (b.acct[(Program.findSlot b.oid r[1]!).toNat]! != r[2]!) = true then
          Program.reject b out 3 r[1]! 8
        else Program.cancel b out r[1]! (Program.findSlot b.oid r[1]!))
      (if (orderAt b (b.lvl[(Program.findSlot b.oid r[1]!).toNat]!).toNat
            (Program.findSlot b.oid r[1]!)).account ≠ r[2]! then
          Spec.reject (toSpec b) 3 r[1]! .otherAccount
        else (Spec.remove (toSpec b) r[1]!, [.cancelled r[1]! (orderAt b
          (b.lvl[(Program.findSlot b.oid r[1]!).toNat]!).toNat (Program.findSlot b.oid r[1]!)).qty
          .requested])) := by
  obtain ⟨hb, hm, hid, -⟩ := find_some h hs0
  have hs0' : (Program.findSlot b.oid r[1]! == 0) = false := by simp [hs0]
  simp only [hs0', Bool.false_eq_true, ↓reduceIte]
  generalize Program.findSlot b.oid r[1]! = s at hb hm hid ⊢
  have hacc : (orderAt b (b.lvl[s.toNat]!).toNat s).account = b.acct[s.toNat]! := rfl
  rw [hacc]
  by_cases ha : b.acct[s.toNat]! = r[2]!
  · have ha' : (b.acct[s.toNat]! != r[2]!) = false := by simp [ha]
    have hs : (b.acct[s.toNat]! ≠ r[2]!) = False := by simp [ha]
    simp only [ha', hs, Bool.false_eq_true, ↓reduceIte]
    exact cancel_rel h out hb hm hid
  · have ha' : (b.acct[s.toNat]! != r[2]!) = true := by simp [ha]
    have hs : (b.acct[s.toNat]! ≠ r[2]!) = True := by simp [ha]
    simp only [ha', hs, ↓reduceIte]
    exact reject_rel h out 3 r[1]! .otherAccount

/-- A reduce record whose id `findSlot` finds refines the specification's reduce command. -/
theorem step_reduce {b : Book} (h : Inv b) (out : Array UInt64) (r : Array UInt64)
    (hs0 : Program.findSlot b.oid r[1]! ≠ 0) :
    Rel out
      (if (Program.findSlot b.oid r[1]! == 0) = true then Program.reject b out 4 r[1]! 7
        else if (b.acct[(Program.findSlot b.oid r[1]!).toNat]! != r[2]!) = true then
          Program.reject b out 4 r[1]! 8
        else if !Program.inRange 1 Program.maxQty r[3]! then Program.reject b out 4 r[1]! 6
        else if b.qty[(Program.findSlot b.oid r[1]!).toNat]! ≤ r[3]! then
          Program.reject b out 4 r[1]! 10
        else Program.reduce b out r[1]! (Program.findSlot b.oid r[1]!) r[3]!)
      (if (orderAt b (b.lvl[(Program.findSlot b.oid r[1]!).toNat]!).toNat
            (Program.findSlot b.oid r[1]!)).account ≠ r[2]! then
          Spec.reject (toSpec b) 4 r[1]! .otherAccount
        else if !Spec.inRange 1 Spec.maxQty r[3]! then Spec.reject (toSpec b) 4 r[1]! .badQty
        else if (orderAt b (b.lvl[(Program.findSlot b.oid r[1]!).toNat]!).toNat
            (Program.findSlot b.oid r[1]!)).qty ≤ r[3]!.toNat then
          Spec.reject (toSpec b) 4 r[1]! .notReduction
        else (Spec.setQty (toSpec b) r[1]! r[3]!.toNat, [.reduced r[1]! r[3]!.toNat])) := by
  obtain ⟨hb, hm, hid, -⟩ := find_some h hs0
  have hs0' : (Program.findSlot b.oid r[1]! == 0) = false := by simp [hs0]
  simp only [hs0', Bool.false_eq_true, ↓reduceIte]
  generalize Program.findSlot b.oid r[1]! = s at hb hm hid ⊢
  have hacc : (orderAt b (b.lvl[s.toNat]!).toNat s).account = b.acct[s.toNat]! := rfl
  have hqty : (orderAt b (b.lvl[s.toNat]!).toNat s).qty = b.qty[s.toNat]!.toNat := rfl
  rw [hacc, hqty]
  by_cases ha : b.acct[s.toNat]! = r[2]!
  · have ha' : (b.acct[s.toNat]! != r[2]!) = false := by simp [ha]
    have hs : (b.acct[s.toNat]! ≠ r[2]!) = False := by simp [ha]
    simp only [ha', hs, Bool.false_eq_true, ↓reduceIte, inRange_qty]
    cases hq : Spec.inRange 1 Spec.maxQty r[3]!
    · simp only [Bool.not_false, ↓reduceIte]
      exact reject_rel h out 4 r[1]! .badQty
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : b.qty[s.toNat]! ≤ r[3]!
      · have hle' : b.qty[s.toNat]!.toNat ≤ r[3]!.toNat := UInt64.le_iff_toNat_le.1 hle
        simp only [hle, hle', ↓reduceIte]
        exact reject_rel h out 4 r[1]! .notReduction
      · have hle' : ¬ b.qty[s.toNat]!.toNat ≤ r[3]!.toNat :=
          fun h' => hle (UInt64.le_iff_toNat_le.2 h')
        simp only [hle, hle', ↓reduceIte]
        exact reduce_rel h out hb hm hid (inRange_true hq)
  · have ha' : (b.acct[s.toNat]! != r[2]!) = true := by simp [ha]
    have hs : (b.acct[s.toNat]! ≠ r[2]!) = True := by simp [ha]
    simp only [ha', hs, ↓reduceIte]
    exact reject_rel h out 4 r[1]! .otherAccount

/-- One step refines the specification's step on the record at the offset. -/
theorem step_rel {b : Book} (h : Inv b) (hn : b.nextId.toNat < 2 ^ 64 - 1) (out ws : Array UInt64)
    (o : UInt64) (ho : o.toNat < ws.size) (hs : ws.size < 2 ^ 64) :
    Rel out (Program.step b out ws o) (Spec.step (toSpec b) (recordAt ws o.toNat)) := by
  by_cases hshort : ws.size.toUInt64 - o < 7
  · have hne := (short_iff ho hs).1 hshort
    have e1 : Program.step b out ws o = Program.reject b out 0 0 1 := by
      simp only [Program.step, hshort, ↓reduceIte]
    have e2 : Spec.step (toSpec b) (recordAt ws o.toNat) =
        Spec.reject (toSpec b) 0 0 .malformed := by
      simp only [Spec.step, hne, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e1, e2]
    exact reject_rel h out 0 0 .malformed
  · have hr7 : (recordAt ws o.toNat).size = 7 :=
      Decidable.byContradiction fun hne => hshort ((short_iff ho hs).2 hne)
    have h7 : o.toNat + 7 ≤ ws.size := by
      have := hr7
      rw [recordAt, Array.size_extract] at this
      omega
    have hw := fun k hk => word_eq h7 hs k hk
    generalize recordAt ws o.toNat = r at hr7 hw ⊢
    have hw0 : Program.word ws o 0 = r[0]! := hw 0 (by decide)
    have hw1 : Program.word ws o 1 = r[1]! := hw 1 (by decide)
    have hw2 : Program.word ws o 2 = r[2]! := hw 2 (by decide)
    have hw3 : Program.word ws o 3 = r[3]! := hw 3 (by decide)
    have hw4 : Program.word ws o 4 = r[4]! := hw 4 (by decide)
    have hw5 : Program.word ws o 5 = r[5]! := hw 5 (by decide)
    have hw6 : Program.word ws o 6 = r[6]! := hw 6 (by decide)
    have hr7' : (r.size ≠ 7) = False := by simp [hr7]
    simp only [Program.step, hshort, ↓reduceIte, hw0, hw1, hw2, hw3, hw4, hw5, hw6, Spec.step,
      hr7']
    by_cases hk1 : r[0]! = 1
    · simp only [hk1, beq_self_eq_true, ↓reduceIte]
      exact step_limit h hn out r
    have hk1' : (r[0]! == 1) = false := by simp [hk1]
    simp only [hk1, hk1', Bool.false_eq_true, ↓reduceIte]
    by_cases hk2 : r[0]! = 2
    · simp only [hk2, beq_self_eq_true, ↓reduceIte]
      exact step_market h hn out r
    have hk2' : (r[0]! == 2) = false := by simp [hk2]
    simp only [hk2, hk2', Bool.false_eq_true, ↓reduceIte]
    by_cases hk3 : r[0]! = 3
    · simp only [hk3, beq_self_eq_true, ↓reduceIte]
      by_cases hs0 : Program.findSlot b.oid r[1]! = 0
      · rw [find_none h hs0]
        simp only [hs0, beq_self_eq_true, ↓reduceIte]
        exact reject_rel h out 3 r[1]! .unknownOrder
      · rw [(find_some h hs0).2.2.2]
        exact step_cancel h out r hs0
    have hk3' : (r[0]! == 3) = false := by simp [hk3]
    simp only [hk3, hk3', Bool.false_eq_true, ↓reduceIte]
    by_cases hk4 : r[0]! = 4
    · simp only [hk4, beq_self_eq_true, ↓reduceIte]
      by_cases hs0 : Program.findSlot b.oid r[1]! = 0
      · rw [find_none h hs0]
        simp only [hs0, beq_self_eq_true, ↓reduceIte]
        exact reject_rel h out 4 r[1]! .unknownOrder
      · rw [(find_some h hs0).2.2.2]
        exact step_reduce h out r hs0
    have hk4' : (r[0]! == 4) = false := by simp [hk4]
    simp only [hk4, hk4', Bool.false_eq_true, ↓reduceIte]
    exact reject_rel h out r[0]! 0 .unknownKind

/-! ## The theorems -/

/-- The step at an offset inside the stream refines `Spec.step` on a book that satisfies the
invariant, while the next id lies below 2^64 - 1. -/
theorem step_eq {b : Book} (h : Inv b) (hn : b.nextId.toNat < 2 ^ 64 - 1) (out ws : Array UInt64)
    (o : UInt64) (ho : o.toNat < ws.size) (hs : ws.size < 2 ^ 64) : StepRefines b out ws o :=
  step_rel h hn out ws o ho hs

/-- The empty book reads as the specification's empty book. -/
theorem toSpec_init : toSpec (Program.init ()) = Spec.empty := by
  rw [toSpec_eq, ordersAt_init, show (Program.init ()).nextId = 1 from rfl]
  simp [ofLevels, Spec.empty, List.flatMap_eq_nil_iff]

/-- The empty book satisfies the invariant. -/
theorem init_inv : Inv (Program.init ()) := by
  have hts := toSpec_init
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · simp only [Program.init]; rw [build_zero_size]; rfl
  · intro l _
    rw [levelSlots_init]
    exact List.nodup_nil
  · intro l _ t ht
    rw [levelSlots_init] at ht
    simp at ht
  · intro l _
    rw [levelSlots_init]
    simp only [Program.init]
    rw [build_zero_get]
    rfl
  · intro t _ _ hne
    exact absurd (by simp only [Program.init]; exact build_zero_get _ _) hne
  · rw [hts]
    rfl
  · rw [hts]
    exact Spec.empty_valid

/-- `top` gives the specification's top of the book. -/
theorem top_eq {b : Book} (h : Inv b) :
    ((Program.top b).1.toNat, (Program.top b).2.1.toNat, (Program.top b).2.2.1.toNat,
      (Program.top b).2.2.2.toNat) = Spec.top (toSpec b) := top_spec h

end Demos.OrderBook.Refinement
