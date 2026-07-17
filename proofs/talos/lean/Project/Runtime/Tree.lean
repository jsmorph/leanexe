import Project.Runtime.Defs
import Project.Common

/-!
# Release trees

A model of the object graphs the runtime release function tears down: a
tree of slots-kind heap objects at refcount one, whose masked slots hold
null, an owned subtree, or a shared object that the walk only decrements.
`TreeAt` ties a tree to a memory; `releaseEvents` lists the walk's writes
in traversal order; `applyEvents` folds them over a memory and the
free-list head.  The generic release theorem consumes these.
-/

namespace Project.Runtime

open Wasm Project.Common

mutual
inductive RelSlot where
  | scalar (value : UInt64)
  | null
  | child (t : RelTree)

inductive RelTree where
  | node (p : UInt64) (slots : List RelSlot)
  | shared (p : UInt64) (rc : UInt64)
end

instance : Inhabited RelSlot := ⟨.null⟩

def RelTree.root : RelTree → UInt64
  | .node p _ => p
  | .shared p _ => p

/-- The mask the compiler stores for these slots: one bit per masked slot. -/
def slotsMask (slots : List RelSlot) : UInt64 :=
  (slots.foldr
    (fun slot acc =>
      2 * acc + match slot with
        | .scalar _ => 0
        | _ => 1)
    0)

def RelSlot.stored : RelSlot → UInt64
  | .scalar value => value
  | .null => 0
  | .child t => t.root

/-- One walk event: a shared decrement or an owned free. -/
inductive RelEvent where
  | decr (p : UInt64) (rc : UInt64)
  | free (p : UInt64)

mutual
/-- The walk's events in traversal order: children first, then the node. -/
def RelTree.events : RelTree → List RelEvent
  | .node p slots => slotsEvents slots ++ [.free p]
  | .shared p rc => [.decr p rc]

def slotsEvents : List RelSlot → List RelEvent
  | [] => []
  | .child t :: rest => t.events ++ slotsEvents rest
  | _ :: rest => slotsEvents rest
end

/-- Release calls that reach the counter: one per shared or owned node. -/
def RelEvent.releases : RelEvent → Nat
  | .decr _ _ => 1
  | .free _ => 1

def releaseCountOf (t : RelTree) : Nat :=
  (t.events.map RelEvent.releases).sum

def freeCountOf (t : RelTree) : Nat :=
  t.events.countP (fun e => match e with | .free _ => true | _ => false)

/-- Fold the walk's writes over a memory and the free-list head. -/
def applyEvents (start : Mem × UInt64) (events : List RelEvent) :
    Mem × UInt64 :=
  events.foldl
    (fun acc e =>
      match e with
      | .decr p rc => (acc.1.write64 ((p - 40).toUInt32) (rc - 1), acc.2)
      | .free p =>
          ((acc.1.write64 ((p - 40).toUInt32) 0).write64
            ((p - 8).toUInt32) acc.2, p))
    start

mutual
/-- The address region a tree owns: each node's header and payload. -/
def RelTree.footprint : RelTree → List (Nat × Nat)
  | .node p slots => (p.toNat - 48, 48 + 8 * slots.length) :: slotsFootprint slots
  | .shared p _ => [(p.toNat - 48, 48)]

def slotsFootprint : List RelSlot → List (Nat × Nat)
  | [] => []
  | .child t :: rest => t.footprint ++ slotsFootprint rest
  | _ :: rest => slotsFootprint rest
end

def regionsDisjoint (a b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

def footprintOk (regions : List (Nat × Nat)) : Prop :=
  regions.Pairwise regionsDisjoint ∧
  ∀ r ∈ regions, 48 ≤ r.1 ∧ r.1 + r.2 < 4294967296

mutual
/-- The tree's shape holds in the memory: headers, masks, and slot words. -/
inductive TreeAt : Mem → RelTree → Prop where
  | node {m : Mem} {p : UInt64} {slots : List RelSlot} :
      48 ≤ p.toNat →
      m.read64 ((p - 48).toUInt32) = 5501223100278326855 →
      m.read64 ((p - 40).toUInt32) = 1 →
      m.read64 ((p - 24).toUInt32) = 1 →
      m.read64 ((p - 16).toUInt32) = UInt64.ofNat slots.length →
      m.read64 ((p - 8).toUInt32) = slotsMask slots →
      slots.length ≤ 32 →
      SlotsAt m p 0 slots →
      TreeAt m (.node p slots)
  | shared {m : Mem} {p rc : UInt64} :
      48 ≤ p.toNat →
      m.read64 ((p - 48).toUInt32) = 5501223100278326855 →
      m.read64 ((p - 40).toUInt32) = rc →
      2 ≤ rc.toNat →
      TreeAt m (.shared p rc)

inductive SlotsAt : Mem → UInt64 → Nat → List RelSlot → Prop where
  | nil {m : Mem} {p : UInt64} {i : Nat} : SlotsAt m p i []
  | scalar {m : Mem} {p v : UInt64} {i : Nat} {rest : List RelSlot} :
      m.read64 ((p + UInt64.ofNat (8 * i)).toUInt32) = v →
      SlotsAt m p (i + 1) rest →
      SlotsAt m p i (.scalar v :: rest)
  | null {m : Mem} {p : UInt64} {i : Nat} {rest : List RelSlot} :
      m.read64 ((p + UInt64.ofNat (8 * i)).toUInt32) = 0 →
      SlotsAt m p (i + 1) rest →
      SlotsAt m p i (.null :: rest)
  | child {m : Mem} {p : UInt64} {i : Nat} {t : RelTree}
      {rest : List RelSlot} :
      m.read64 ((p + UInt64.ofNat (8 * i)).toUInt32) = t.root →
      TreeAt m t →
      SlotsAt m p (i + 1) rest →
      SlotsAt m p i (.child t :: rest)
end

def RelEvent.ptr : RelEvent → UInt64
  | .decr p _ => p
  | .free p => p

/-- Separation of an eight-byte read at `b` from an event's header region. -/
def eventSep (b : UInt32) (e : RelEvent) : Prop :=
  48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296 ∧
    (b.toNat + 8 ≤ e.ptr.toNat - 48 ∨ e.ptr.toNat ≤ b.toNat)

theorem applyEvents_pages (start : Mem × UInt64) (events : List RelEvent) :
    (applyEvents start events).1.pages = start.1.pages := by
  induction events generalizing start with
  | nil => rfl
  | cons e rest ih =>
      cases e with
      | decr p rc =>
          rw [show applyEvents start (.decr p rc :: rest) =
            applyEvents (start.1.write64 ((p - 40).toUInt32) (rc - 1), start.2)
              rest from rfl]
          rw [ih]
          exact Mem.write64_pages ..
      | free p =>
          rw [show applyEvents start (.free p :: rest) =
            applyEvents ((start.1.write64 ((p - 40).toUInt32) 0).write64
              ((p - 8).toUInt32) start.2, p) rest from rfl]
          rw [ih]
          rw [Mem.write64_pages, Mem.write64_pages]

theorem read64_applyEvents_ne (start : Mem × UInt64) (events : List RelEvent)
    (b : UInt32) (_hb : b.toNat + 8 ≤ 4294967296)
    (hsep : ∀ e ∈ events, eventSep b e) :
    (applyEvents start events).1.read64 b = start.1.read64 b := by
  induction events generalizing start with
  | nil => rfl
  | cons e rest ih =>
      have hse := hsep e (List.mem_cons_self ..)
      obtain ⟨h48, h32, hor⟩ := hse
      have hnext : ∀ e' ∈ rest, eventSep b e' := fun e' he' =>
        hsep e' (List.mem_cons_of_mem _ he')
      cases e with
      | decr p rc =>
          rw [show applyEvents start (.decr p rc :: rest) =
            applyEvents (start.1.write64 ((p - 40).toUInt32) (rc - 1), start.2)
              rest from rfl]
          rw [ih _ hnext]
          exact read64_write64_ne _ _ _ _ (by
            rw [toUInt32_toNat, toNat_sub_le _ _ (by
              rw [show (40 : UInt64).toNat = 40 from rfl]
              simp only [RelEvent.ptr] at h48 ⊢
              omega)]
            rw [show (40 : UInt64).toNat = 40 from rfl,
              Nat.mod_eq_of_lt (by simp only [RelEvent.ptr] at h32 ⊢; omega)]
            simp only [RelEvent.ptr] at h48 h32 hor ⊢
            omega)
      | free p =>
          rw [show applyEvents start (.free p :: rest) =
            applyEvents ((start.1.write64 ((p - 40).toUInt32) 0).write64
              ((p - 8).toUInt32) start.2, p) rest from rfl]
          rw [ih _ hnext]
          simp only [RelEvent.ptr] at h48 h32 hor
          rw [read64_write64_ne _ _ _ _ (by
            rw [toUInt32_toNat, toNat_sub_le _ _ (by
              rw [show (8 : UInt64).toNat = 8 from rfl]; omega)]
            rw [show (8 : UInt64).toNat = 8 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega)]
          exact read64_write64_ne _ _ _ _ (by
            rw [toUInt32_toNat, toNat_sub_le _ _ (by
              rw [show (40 : UInt64).toNat = 40 from rfl]; omega)]
            rw [show (40 : UInt64).toNat = 40 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega)

def eventRegion (e : RelEvent) : Nat × Nat :=
  (e.ptr.toNat - 48, 48)

theorem footprintOk_append_left {a b : List (Nat × Nat)}
    (h : footprintOk (a ++ b)) : footprintOk a :=
  ⟨(List.pairwise_append.mp h.1).1,
   fun r hr => h.2 r (List.mem_append_left _ hr)⟩

theorem footprintOk_append_right {a b : List (Nat × Nat)}
    (h : footprintOk (a ++ b)) : footprintOk b :=
  ⟨(List.pairwise_append.mp h.1).2.1,
   fun r hr => h.2 r (List.mem_append_right _ hr)⟩

theorem eventSep_of_region {b : UInt32} {e : RelEvent} {r : Nat × Nat}
    (hin : r.1 ≤ b.toNat ∧ b.toNat + 8 ≤ r.1 + r.2)
    (hdis : regionsDisjoint (eventRegion e) r)
    (hbnd : 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296) :
    eventSep b e := by
  unfold regionsDisjoint eventRegion at hdis
  exact ⟨hbnd.1, hbnd.2, by omega⟩

/-- A read inside a region every event region avoids is unchanged. -/
theorem read64_applyEvents_region (start : Mem × UInt64)
    (events : List RelEvent) (b : UInt32) (r : Nat × Nat)
    (hin : r.1 ≤ b.toNat ∧ b.toNat + 8 ≤ r.1 + r.2)
    (hr32 : r.1 + r.2 ≤ 4294967296)
    (hsep : ∀ e ∈ events, regionsDisjoint (eventRegion e) r)
    (hbnd : ∀ e ∈ events, 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296) :
    (applyEvents start events).1.read64 b = start.1.read64 b :=
  read64_applyEvents_ne _ _ _ (by omega)
    (fun e he => eventSep_of_region hin (hsep e he) (hbnd e he))

private theorem slotsFrameCommon (start : Mem × UInt64)
    (events : List RelEvent) (p : UInt64) (i : Nat)
    {n : Nat}
    (hword : ∀ j, i ≤ j → j < i + n →
      ((p + UInt64.ofNat (8 * j)).toUInt32).toNat = p.toNat + 8 * j ∧
      p.toNat + 8 * j + 8 ≤ 4294967296 ∧
      ∀ e ∈ events, eventSep ((p + UInt64.ofNat (8 * j)).toUInt32) e)
    (hi : i < i + n) :
    (applyEvents start events).1.read64
      ((p + UInt64.ofNat (8 * i)).toUInt32) =
    start.1.read64 ((p + UInt64.ofNat (8 * i)).toUInt32) := by
  have hwi := hword i (le_refl _) hi
  exact read64_applyEvents_ne _ _ _ (by rw [hwi.1]; omega) hwi.2.2

private theorem frame_fuel (n : Nat) :
    (∀ (start : Mem × UInt64) (events : List RelEvent) (t : RelTree),
      sizeOf t ≤ n → TreeAt start.1 t → footprintOk t.footprint →
      (∀ e ∈ events, ∀ r ∈ t.footprint, regionsDisjoint (eventRegion e) r) →
      (∀ e ∈ events, 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296) →
      TreeAt (applyEvents start events).1 t) ∧
    (∀ (start : Mem × UInt64) (events : List RelEvent) (p : UInt64)
      (i : Nat) (slots : List RelSlot),
      sizeOf slots ≤ n → SlotsAt start.1 p i slots →
      (∀ j, i ≤ j → j < i + slots.length →
        ((p + UInt64.ofNat (8 * j)).toUInt32).toNat = p.toNat + 8 * j ∧
        p.toNat + 8 * j + 8 ≤ 4294967296 ∧
        ∀ e ∈ events, eventSep ((p + UInt64.ofNat (8 * j)).toUInt32) e) →
      footprintOk (slotsFootprint slots) →
      (∀ e ∈ events, ∀ r ∈ slotsFootprint slots,
        regionsDisjoint (eventRegion e) r) →
      (∀ e ∈ events, 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296) →
      SlotsAt (applyEvents start events).1 p i slots) := by
  induction n with
  | zero =>
      constructor
      · intro start events t hn
        cases t <;> simp at hn
      · intro start events p i slots hn
        cases slots with
        | nil =>
            intro _ _ _ _ _
            trivial
        | cons slot rest => simp at hn
  | succ n ih =>
      constructor
      · intro start events t hn ht hok hsep hbnd
        cases ht with
        | shared hp hm hr hc2 =>
            rename_i p rc
            have hmem : ((p.toNat - 48, 48) : Nat × Nat) ∈
                RelTree.footprint (.shared p rc) := by
              simp [RelTree.footprint]
            have hpb := hok.2 _ hmem
            simp only at hpb
            have hsub : ∀ q : UInt64, q.toNat ≤ 48 →
                ((p - q).toUInt32).toNat = p.toNat - q.toNat := by
              intro q hq
              rw [toUInt32_toNat, toNat_sub_le _ _ (by omega),
                Nat.mod_eq_of_lt (by omega)]
            have hread : ∀ (K : UInt64), 8 ≤ K.toNat → K.toNat ≤ 48 →
                (applyEvents start events).1.read64 ((p - K).toUInt32) =
                start.1.read64 ((p - K).toUInt32) := by
              intro K h8 hK
              refine read64_applyEvents_region _ _ _ (p.toNat - 48, 48) ?_
                (by omega) (fun e he => hsep e he _ hmem) hbnd
              rw [hsub K hK]
              constructor <;> omega
            exact TreeAt.shared hp
              (by rw [hread 48 (by decide) (by decide)]; exact hm)
              (by rw [hread 40 (by decide) (by decide)]; exact hr)
              hc2
        | node hp hm hr hk hl hmk h32 hslots =>
            rename_i p slots
            have hmem : ((p.toNat - 48, 48 + 8 * slots.length) : Nat × Nat) ∈
                RelTree.footprint (.node p slots) := by
              simp [RelTree.footprint]
            have hpb := hok.2 _ hmem
            simp only at hpb
            have hsub : ∀ q : UInt64, q.toNat ≤ 48 →
                ((p - q).toUInt32).toNat = p.toNat - q.toNat := by
              intro q hq
              rw [toUInt32_toNat, toNat_sub_le _ _ (by omega),
                Nat.mod_eq_of_lt (by omega)]
            have hread : ∀ (K : UInt64), 8 ≤ K.toNat → K.toNat ≤ 48 →
                (applyEvents start events).1.read64 ((p - K).toUInt32) =
                start.1.read64 ((p - K).toUInt32) := by
              intro K h8 hK
              refine read64_applyEvents_region _ _ _
                (p.toNat - 48, 48 + 8 * slots.length) ?_
                (by omega) (fun e he => hsep e he _ hmem) hbnd
              rw [hsub K hK]
              constructor <;> omega
            refine TreeAt.node hp
              (by rw [hread 48 (by decide) (by decide)]; exact hm)
              (by rw [hread 40 (by decide) (by decide)]; exact hr)
              (by rw [hread 24 (by decide) (by decide)]; exact hk)
              (by rw [hread 16 (by decide) (by decide)]; exact hl)
              (by rw [hread 8 (by decide) (by decide)]; exact hmk)
              h32 ?_
            refine ih.2 start events p 0 slots
              (by simp at hn; omega) hslots ?_
              (footprintOk_append_right
                (a := [(p.toNat - 48, 48 + 8 * slots.length)])
                (by simpa [RelTree.footprint] using hok))
              (fun e he r hr => hsep e he r (by
                simp only [RelTree.footprint, List.mem_cons]
                exact Or.inr hr))
              hbnd
            intro j hj0 hjl
            have haddr : ((p + UInt64.ofNat (8 * j)).toUInt32).toNat =
                p.toNat + 8 * j := by
              rw [toUInt32_toNat, UInt64.toNat_add,
                toNat_ofNat_lt (by rw [size_eq]; omega)]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            refine ⟨haddr, by omega, ?_⟩
            intro e he
            refine eventSep_of_region
              (r := (p.toNat - 48, 48 + 8 * slots.length))
              ?_ (hsep e he _ hmem) (hbnd e he)
            rw [haddr]
            constructor <;> omega
      · intro start events p i slots hn hs hword hok hsep hbnd
        cases hs with
        | nil => exact SlotsAt.nil
        | scalar hword0 hrest =>
            rename_i v rest
            have hcommon := slotsFrameCommon start events p i hword
              (by simp only [List.length_cons]; omega)
            refine SlotsAt.scalar (by rw [hcommon]; exact hword0)
              (ih.2 start events p (i + 1) rest (by simp at hn; omega) hrest
                (fun j hj0 hjl => hword j (by omega)
                  (by simp only [List.length_cons] at hjl ⊢; omega))
                (by simpa [slotsFootprint] using hok)
                (fun e he r hr => hsep e he r
                  (by simpa [slotsFootprint] using hr))
                hbnd)
        | null hword0 hrest =>
            rename_i rest
            have hcommon := slotsFrameCommon start events p i hword
              (by simp only [List.length_cons]; omega)
            refine SlotsAt.null (by rw [hcommon]; exact hword0)
              (ih.2 start events p (i + 1) rest (by simp at hn; omega) hrest
                (fun j hj0 hjl => hword j (by omega)
                  (by simp only [List.length_cons] at hjl ⊢; omega))
                (by simpa [slotsFootprint] using hok)
                (fun e he r hr => hsep e he r
                  (by simpa [slotsFootprint] using hr))
                hbnd)
        | child hword0 hchild hrest =>
            rename_i t rest
            have hcommon := slotsFrameCommon start events p i hword
              (by simp only [List.length_cons]; omega)
            refine SlotsAt.child (by rw [hcommon]; exact hword0)
              (ih.1 start events t (by simp at hn; omega) hchild
                (footprintOk_append_left (b := slotsFootprint rest)
                  (by simpa [slotsFootprint] using hok))
                (fun e he r hr => hsep e he r (by
                  simp only [slotsFootprint]
                  exact List.mem_append_left _ hr))
                hbnd)
              (ih.2 start events p (i + 1) rest (by simp at hn; omega) hrest
                (fun j hj0 hjl => hword j (by omega)
                  (by simp only [List.length_cons] at hjl ⊢; omega))
                (footprintOk_append_right (a := t.footprint)
                  (by simpa [slotsFootprint] using hok))
                (fun e he r hr => hsep e he r (by
                  simp only [slotsFootprint]
                  exact List.mem_append_right _ hr))
                hbnd)

theorem TreeAt_applyEvents (start : Mem × UInt64) (events : List RelEvent)
    (t : RelTree) (ht : TreeAt start.1 t) (hok : footprintOk t.footprint)
    (hsep : ∀ e ∈ events, ∀ r ∈ t.footprint,
      regionsDisjoint (eventRegion e) r)
    (hbnd : ∀ e ∈ events, 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296) :
    TreeAt (applyEvents start events).1 t :=
  (frame_fuel (sizeOf t)).1 start events t (le_refl _) ht hok hsep hbnd

theorem SlotsAt_applyEvents (start : Mem × UInt64) (events : List RelEvent)
    (p : UInt64) (i : Nat) (slots : List RelSlot)
    (hs : SlotsAt start.1 p i slots)
    (hword : ∀ j, i ≤ j → j < i + slots.length →
      ((p + UInt64.ofNat (8 * j)).toUInt32).toNat = p.toNat + 8 * j ∧
      p.toNat + 8 * j + 8 ≤ 4294967296 ∧
      ∀ e ∈ events, eventSep ((p + UInt64.ofNat (8 * j)).toUInt32) e)
    (hok : footprintOk (slotsFootprint slots))
    (hsep : ∀ e ∈ events, ∀ r ∈ slotsFootprint slots,
      regionsDisjoint (eventRegion e) r)
    (hbnd : ∀ e ∈ events, 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296) :
    SlotsAt (applyEvents start events).1 p i slots :=
  (frame_fuel (sizeOf slots)).2 start events p i slots (le_refl _) hs hword
    hok hsep hbnd

theorem applyEvents_append (start : Mem × UInt64) (a b : List RelEvent) :
    applyEvents start (a ++ b) = applyEvents (applyEvents start a) b :=
  List.foldl_append ..

/-- Containment of one region in another. -/
def regionSub (a b : Nat × Nat) : Prop :=
  b.1 ≤ a.1 ∧ a.1 + a.2 ≤ b.1 + b.2

theorem regionsDisjoint_of_sub {a b c : Nat × Nat}
    (hsub : regionSub a b) (hdis : regionsDisjoint b c) :
    regionsDisjoint a c := by
  unfold regionSub at hsub
  unfold regionsDisjoint at hdis ⊢
  omega

theorem regionsDisjoint_symm {a b : Nat × Nat}
    (h : regionsDisjoint a b) : regionsDisjoint b a := by
  unfold regionsDisjoint at h ⊢
  omega

/-- Every event's header region sits inside a footprint region of its tree. -/
private theorem events_sub_fuel (n : Nat) :
    (∀ t : RelTree, sizeOf t ≤ n →
      ∀ e ∈ t.events, ∃ r ∈ t.footprint, regionSub (eventRegion e) r) ∧
    (∀ slots : List RelSlot, sizeOf slots ≤ n →
      ∀ e ∈ slotsEvents slots, ∃ r ∈ slotsFootprint slots,
        regionSub (eventRegion e) r) := by
  induction n with
  | zero =>
      constructor
      · intro t hn
        cases t <;> simp at hn
      · intro slots hn
        cases slots <;> simp at hn ⊢
  | succ n ih =>
      constructor
      · intro t hn e he
        cases t with
        | shared p rc =>
            simp only [RelTree.events, List.mem_singleton] at he
            subst he
            exact ⟨(p.toNat - 48, 48), by simp [RelTree.footprint],
              by unfold regionSub eventRegion; simp [RelEvent.ptr]⟩
        | node p slots =>
            simp only [RelTree.events, List.mem_append,
              List.mem_singleton] at he
            cases he with
            | inl hin =>
                obtain ⟨r, hr, hsub⟩ := ih.2 slots (by simp at hn; omega) e hin
                exact ⟨r, by
                  simp only [RelTree.footprint, List.mem_cons]
                  exact Or.inr hr, hsub⟩
            | inr heq =>
                subst heq
                refine ⟨(p.toNat - 48, 48 + 8 * slots.length),
                  by simp [RelTree.footprint], ?_⟩
                unfold regionSub eventRegion
                simp [RelEvent.ptr]
      · intro slots hn e he
        cases slots with
        | nil => simp [slotsEvents] at he
        | cons slot rest =>
            cases slot with
            | child t =>
                simp only [slotsEvents, List.mem_append] at he
                cases he with
                | inl hin =>
                    obtain ⟨r, hr, hsub⟩ :=
                      ih.1 t (by simp at hn; omega) e hin
                    exact ⟨r, by
                      simp only [slotsFootprint]
                      exact List.mem_append_left _ hr, hsub⟩
                | inr hin =>
                    obtain ⟨r, hr, hsub⟩ :=
                      ih.2 rest (by simp at hn; omega) e hin
                    exact ⟨r, by
                      simp only [slotsFootprint]
                      exact List.mem_append_right _ hr, hsub⟩
            | scalar v =>
                simp only [slotsEvents] at he
                obtain ⟨r, hr, hsub⟩ := ih.2 rest (by simp at hn; omega) e he
                exact ⟨r, by simpa [slotsFootprint] using hr, hsub⟩
            | null =>
                simp only [slotsEvents] at he
                obtain ⟨r, hr, hsub⟩ := ih.2 rest (by simp at hn; omega) e he
                exact ⟨r, by simpa [slotsFootprint] using hr, hsub⟩

theorem events_sub (t : RelTree) :
    ∀ e ∈ t.events, ∃ r ∈ t.footprint, regionSub (eventRegion e) r :=
  (events_sub_fuel (sizeOf t)).1 t (le_refl _)

theorem slotsEvents_sub (slots : List RelSlot) :
    ∀ e ∈ slotsEvents slots, ∃ r ∈ slotsFootprint slots,
      regionSub (eventRegion e) r :=
  (events_sub_fuel (sizeOf slots)).2 slots (le_refl _)

/-- Event pointer bounds follow from the footprint bounds. -/
theorem events_bounds {t : RelTree} (hok : footprintOk t.footprint) :
    ∀ e ∈ t.events, 48 ≤ e.ptr.toNat ∧ e.ptr.toNat < 4294967296 := by
  intro e he
  obtain ⟨r, hr, hsub⟩ := events_sub t e he
  have hb := hok.2 r hr
  unfold regionSub eventRegion at hsub
  simp only at hsub
  omega

def RelSlot.masked : RelSlot → Bool
  | .scalar _ => false
  | _ => true

def natMask (slots : List RelSlot) : Nat :=
  slots.foldr (fun slot acc => 2 * acc + if slot.masked then 1 else 0) 0

theorem natMask_cons (slot : RelSlot) (rest : List RelSlot) :
    natMask (slot :: rest) =
    2 * natMask rest + (if slot.masked then 1 else 0) := rfl

theorem natMask_lt (slots : List RelSlot) :
    natMask slots < 2 ^ slots.length := by
  induction slots with
  | nil => simp [natMask]
  | cons slot rest ih =>
      rw [natMask_cons, List.length_cons, Nat.pow_succ]
      cases slot <;> simp [RelSlot.masked] <;> omega

theorem natMask_testBit (slots : List RelSlot) (k : Nat)
    (hk : k < slots.length) :
    (natMask slots).testBit k = (slots[k]!).masked := by
  induction slots generalizing k with
  | nil => simp at hk
  | cons slot rest ih =>
      cases k with
      | zero =>
          rw [natMask_cons, Nat.testBit_zero]
          cases slot <;> simp [RelSlot.masked]
      | succ k =>
          rw [natMask_cons]
          have hdiv : (2 * natMask rest +
              (if slot.masked then 1 else 0)) / 2 = natMask rest := by
            cases slot <;> simp [RelSlot.masked] <;> omega
          rw [Nat.testBit_succ, hdiv,
            ih k (by simpa using hk)]
          simp

end Project.Runtime
