import Project.Runtime.Tree
import Project.Runtime.Spec

/-!
# The generic teardown theorem's walk preamble

Facts the walk proof consumes at each loop iteration: the stored mask
word's shift-and-test agrees with the slot's kind, a slot list indexes to
its read fact and child shape, and a child is smaller than its tree for
the fuel induction.
-/

namespace Project.Runtime

open Wasm Project.Common

theorem slotsMask_cons (slot : RelSlot) (rest : List RelSlot) :
    slotsMask (slot :: rest) =
    2 * slotsMask rest + (if slot.masked then 1 else 0) := by
  cases slot <;> rfl

theorem slotsMask_eq (slots : List RelSlot) :
    slotsMask slots = UInt64.ofNat (natMask slots) := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      rw [slotsMask_cons, natMask_cons, ih]
      cases slot <;> simp [RelSlot.masked]

theorem slotsMask_shift_and (slots : List RelSlot) (k : Nat)
    (hk : k < slots.length) (h32 : slots.length ≤ 32) :
    ((slotsMask slots >>> UInt64.ofNat k) &&& 1) =
    (if (slots[k]!).masked then 1 else 0) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, slotsMask_eq]
  have hm32 : natMask slots < 4294967296 := by
    have h := Nat.lt_of_lt_of_le (natMask_lt slots)
      (Nat.pow_le_pow_right (by omega) h32)
    rw [show (2 : Nat) ^ 32 = 4294967296 from by norm_num] at h
    exact h
  have hk64 : (UInt64.ofNat k).toNat % 64 = k := by
    rw [toNat_ofNat_lt (by rw [size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hk64, toNat_ofNat_lt (by rw [size_eq]; omega)]
  have htb := natMask_testBit slots k hk
  rw [Nat.testBit_eq_decide_div_mod_eq] at htb
  rw [show (1 : UInt64).toNat = 1 from rfl]
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  cases hmask : (slots[k]!).masked <;> rw [hmask] at htb
  · simp only [decide_eq_false_iff_not] at htb
    have : natMask slots / 2 ^ k % 2 = 0 := by omega
    rw [this]
    rfl
  · simp only [decide_eq_true_eq] at htb
    rw [htb]
    rfl

theorem SlotsAt_get {m : Mem} {p : UInt64} {i : Nat} {slots : List RelSlot}
    (h : SlotsAt m p i slots) (k : Nat) (hk : k < slots.length) :
    m.read64 ((p + UInt64.ofNat (8 * (i + k))).toUInt32) =
      (slots[k]!).stored ∧
    (∀ t : RelTree, slots[k]! = .child t → TreeAt m t) := by
  induction slots generalizing i k with
  | nil => simp at hk
  | cons slot rest ih =>
      cases k with
      | zero =>
          cases h with
          | scalar hword hrest =>
              exact ⟨by simpa [RelSlot.stored] using hword,
                fun t ht => by simp at ht⟩
          | null hword hrest =>
              exact ⟨by simpa [RelSlot.stored] using hword,
                fun t ht => by simp at ht⟩
          | child hword hchild hrest =>
              refine ⟨by simpa [RelSlot.stored] using hword, ?_⟩
              intro t ht
              simp at ht
              subst ht
              exact hchild
      | succ k =>
          have hrest : SlotsAt m p (i + 1) rest := by
            cases h with
            | scalar _ hrest => exact hrest
            | null _ hrest => exact hrest
            | child _ _ hrest => exact hrest
          have := ih hrest k (by simpa using hk)
          rw [show i + 1 + k = i + (k + 1) from by omega] at this
          simpa using this

theorem sizeOf_child_lt {t : RelTree} {slots : List RelSlot}
    (h : RelSlot.child t ∈ slots) : sizeOf t < sizeOf slots := by
  induction slots with
  | nil => simp at h
  | cons slot rest ih =>
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        simp
        omega
      · have := ih hin
        simp
        omega

/-- Release counters of a tree's events. -/
theorem releaseCountOf_shared (p rc : UInt64) :
    releaseCountOf (.shared p rc) = 1 := rfl

theorem freeCountOf_shared (p rc : UInt64) :
    freeCountOf (.shared p rc) = 0 := rfl

/-- The events one slot contributes to the walk. -/
def slotEvents : RelSlot → List RelEvent
  | .child t => t.events
  | _ => []

def slotFootprint : RelSlot → List (Nat × Nat)
  | .child t => t.footprint
  | _ => []

theorem slotsEvents_append (a b : List RelSlot) :
    slotsEvents (a ++ b) = slotsEvents a ++ slotsEvents b := by
  induction a with
  | nil => rfl
  | cons slot rest ih =>
      cases slot <;> simp [slotsEvents, ih]

theorem slotsFootprint_append (a b : List RelSlot) :
    slotsFootprint (a ++ b) = slotsFootprint a ++ slotsFootprint b := by
  induction a with
  | nil => rfl
  | cons slot rest ih =>
      cases slot <;> simp [slotsFootprint, ih]

theorem slotsEvents_cons (slot : RelSlot) (rest : List RelSlot) :
    slotsEvents (slot :: rest) = slotEvents slot ++ slotsEvents rest := by
  cases slot <;> rfl

theorem slotsFootprint_cons (slot : RelSlot) (rest : List RelSlot) :
    slotsFootprint (slot :: rest) =
    slotFootprint slot ++ slotsFootprint rest := by
  cases slot <;> rfl

theorem getElem_bang {α : Type} [Inhabited α] (l : List α) (k : Nat)
    (hk : k < l.length) : l[k]! = l[k] := by
  simp [List.getElem?_eq_getElem hk]

theorem slots_take_drop (slots : List RelSlot) (k : Nat)
    (hk : k < slots.length) :
    slots = slots.take k ++ slots[k]! :: slots.drop (k + 1) := by
  rw [getElem_bang _ _ hk]
  conv_lhs => rw [← List.take_append_drop k slots]
  rw [List.drop_eq_getElem_cons hk]

theorem slotsEvents_take_succ (slots : List RelSlot) (k : Nat)
    (hk : k < slots.length) :
    slotsEvents (slots.take (k + 1)) =
    slotsEvents (slots.take k) ++ slotEvents (slots[k]!) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, slotsEvents_append]
  rw [getElem_bang _ _ hk]
  cases slots[k] <;> simp [slotsEvents, slotEvents]

theorem slotsEvents_take_mem {slots : List RelSlot} {k : Nat}
    {e : RelEvent} (he : e ∈ slotsEvents (slots.take k)) :
    e ∈ slotsEvents slots := by
  have hdecomp : slotsEvents slots =
      slotsEvents (slots.take k) ++ slotsEvents (slots.drop k) := by
    rw [← slotsEvents_append, List.take_append_drop]
  rw [hdecomp]
  exact List.mem_append_left _ he

theorem slotsFootprint_take_mem {slots : List RelSlot} {k : Nat}
    {r : Nat × Nat} (hr : r ∈ slotsFootprint (slots.take k)) :
    r ∈ slotsFootprint slots := by
  have hdecomp : slotsFootprint slots =
      slotsFootprint (slots.take k) ++ slotsFootprint (slots.drop k) := by
    rw [← slotsFootprint_append, List.take_append_drop]
  rw [hdecomp]
  exact List.mem_append_left _ hr

private def wFrame (p len mask k l8 : UInt64) : Locals :=
  { params := [.i64 p],
    locals := [.i64 1, .i64 1, .i64 len, .i64 0, .i64 mask, .i64 k,
      .i64 0, .i64 l8],
    values := [] }

private def relPre (slots : List RelSlot) (k : Nat) : Nat :=
  ((slotsEvents (slots.take k)).map RelEvent.releases).sum

private def freePre (slots : List RelSlot) (k : Nat) : Nat :=
  (slotsEvents (slots.take k)).countP
    (fun e => match e with | .free _ => true | _ => false)

set_option maxHeartbeats 4000000 in
private theorem release_tree_fuel (env : HostEnv Unit) (m : Module)
    (id : Nat)
    (hf : m.funcs[id - m.imports.length]? = some (releaseFuncDef id))
    (hImp : m.imports[id]? = none) :
    ∀ n : Nat, ∀ (st : Store Unit) (t : RelTree) (g1 g4 g5 : UInt64),
      sizeOf t ≤ n →
      TreeAt st.mem t →
      footprintOk t.footprint →
      (∀ r ∈ t.footprint, r.1 + r.2 ≤ st.mem.pages * 65536) →
      st.globals.globals[1]? = some (.i64 g1) →
      st.globals.globals[4]? = some (.i64 g4) →
      st.globals.globals[5]? = some (.i64 g5) →
      TerminatesWith (m := m) (id := id) (initial := st) (env := env)
        [.i64 t.root]
        (fun st' vs =>
          vs = [] ∧
          st'.mem = (applyEvents (st.mem, g1) t.events).1 ∧
          st'.globals.globals.length = st.globals.globals.length ∧
          st'.globals.globals[1]? =
            some (.i64 (applyEvents (st.mem, g1) t.events).2) ∧
          st'.globals.globals[4]? =
            some (.i64 (g4 + UInt64.ofNat (releaseCountOf t))) ∧
          st'.globals.globals[5]? =
            some (.i64 (g5 + UInt64.ofNat (freeCountOf t))) ∧
          (∀ k, k ≠ 1 → k ≠ 4 → k ≠ 5 →
            st'.globals.globals[k]? = st.globals.globals[k]?)) := by
  intro n
  induction n with
  | zero =>
      intro st t g1 g4 g5 hn
      cases t <;> simp at hn
  | succ n ih =>
      intro st t g1 g4 g5 hn ht hok hfit hg1 hg4 hg5
      cases ht with
      | shared hp hm hr hc2 =>
          rename_i p rc
          have hmem : ((p.toNat - 48, 48) : Nat × Nat) ∈
              RelTree.footprint (.shared p rc) := by
            simp [RelTree.footprint]
          have hpb := hok.2 _ hmem
          simp only at hpb
          have hfitp := hfit _ hmem
          simp only at hfitp
          have hlen : st.globals.globals.length =
              st.globals.globals.length := rfl
          refine TerminatesWith.mono
            (release_decrements env m id st p rc g4 hf hImp hp
              (by omega) (by omega) hm hr (by omega) hg4) ?_
          rintro st' vs ⟨hvs, hmem', hgl'⟩
          have hlen4 : 4 < st.globals.globals.length :=
            (List.getElem?_eq_some_iff.mp hg4).choose
          refine ⟨hvs, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact hmem'
          · rw [hgl']
            simp
          · rw [hgl']
            rw [List.getElem?_set]
            simp only [if_neg (by omega : ¬ (4 = 1))]
            exact hg1
          · rw [hgl']
            rw [List.getElem?_set]
            simp [hlen4]
            rw [show releaseCountOf (.shared p rc) = 1 from rfl]
            simp
          · rw [hgl']
            rw [List.getElem?_set]
            simp only [if_neg (by omega : ¬ (4 = 5))]
            rw [show freeCountOf (.shared p rc) = 0 from rfl]
            simpa using hg5
          · intro k hk1 hk4 hk5
            rw [hgl']
            rw [List.getElem?_set]
            simp only [if_neg (by omega : ¬ (4 = k))]
      | node hp hm hr hk hl hmk h32 hslots =>
          rename_i p slots
          have hmem : ((p.toNat - 48, 48 + 8 * slots.length) : Nat × Nat) ∈
              RelTree.footprint (.node p slots) := by
            simp [RelTree.footprint]
          have hpb := hok.2 _ hmem
          simp only at hpb
          have hfitp := hfit _ hmem
          simp only at hfitp
          have hp0 : ¬ (p = 0) := by
            intro h
            have := congrArg UInt64.toNat h
            have h0 : (0 : UInt64).toNat = 0 := rfl
            rw [h0] at this
            omega
          have hsub : ∀ c : UInt64, c.toNat ≤ 48 →
              ((p - c).toUInt32).toNat = p.toNat - c.toNat := by
            intro c hc
            rw [toUInt32_toNat, toNat_sub_le _ _ (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have hbridge : ∀ c : UInt64, c.toNat ≤ 48 →
              UInt32.ofNat ((p - c).toNat % 4294967296) = (p - c).toUInt32 := by
            intro c hc
            rw [toUInt32_eq_ofNat]
          have hmagic' : st.mem.read64
              (UInt32.ofNat ((p - 48).toNat % 4294967296)) =
              5501223100278326855 := by
            rw [hbridge 48 (by decide)]
            exact hm
          have hrc' : st.mem.read64
              (UInt32.ofNat ((p - 40).toNat % 4294967296)) = 1 := by
            rw [hbridge 40 (by decide)]
            exact hr
          have hkind' : st.mem.read64
              (UInt32.ofNat ((p - 24).toNat % 4294967296)) = 1 := by
            rw [hbridge 24 (by decide)]
            exact hk
          have hlimit' : st.mem.read64
              (UInt32.ofNat ((p - 16).toNat % 4294967296)) =
              UInt64.ofNat slots.length := by
            rw [hbridge 16 (by decide)]
            exact hl
          have hmask' : st.mem.read64
              (UInt32.ofNat ((p - 8).toNat % 4294967296)) =
              slotsMask slots := by
            rw [hbridge 8 (by decide)]
            exact hmk
          have hsubN : ∀ c : UInt64, c.toNat ≤ 48 →
              (p - c).toNat = p.toNat - c.toNat :=
            fun c hc => toNat_sub_le _ _ (by omega)
          have h48N : (p - 48).toNat = p.toNat - 48 := by
            rw [hsubN 48 (by decide), show (48 : UInt64).toNat = 48 from rfl]
          have h40N : (p - 40).toNat = p.toNat - 40 := by
            rw [hsubN 40 (by decide), show (40 : UInt64).toNat = 40 from rfl]
          have h24N : (p - 24).toNat = p.toNat - 24 := by
            rw [hsubN 24 (by decide), show (24 : UInt64).toNat = 24 from rfl]
          have h16N : (p - 16).toNat = p.toNat - 16 := by
            rw [hsubN 16 (by decide), show (16 : UInt64).toNat = 16 from rfl]
          have h8N : (p - 8).toNat = p.toNat - 8 := by
            rw [hsubN 8 (by decide), show (8 : UInt64).toNat = 8 from rfl]
          refine TerminatesWith.of_wp_entry_for hf ?_ hImp
          change wp m (releaseBody id) _ st
            { params := [.i64 p],
              locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
                .i64 0, .i64 0],
              values := [] } env
          unfold releaseBody
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hp0])]
          wp_run
          try simp
          refine ⟨by omega, ?_⟩
          simp only [hmagic']
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          try simp
          refine ⟨by omega, ?_⟩
          simp only [hrc']
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          try simp only [hg4]
          try wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          try simp
          refine ⟨by omega, ?_⟩
          simp only [hkind']
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          try simp
          refine ⟨by omega, ?_⟩
          simp only [hlimit']
          try wp_run
          try simp
          refine ⟨by omega, ?_⟩
          simp only [hmask']
          try wp_run
          try simp
          apply wp_block_cons
          apply wp_loop_cons
            (Inv := fun stL sL =>
              ∃ k : Nat, ∃ l8v : UInt64, k ≤ slots.length ∧
                sL = wFrame p (UInt64.ofNat slots.length)
                  (slotsMask slots) (UInt64.ofNat k) l8v ∧
                stL.mem =
                  (applyEvents (st.mem, g1)
                    (slotsEvents (slots.take k))).1 ∧
                stL.globals.globals.length = st.globals.globals.length ∧
                stL.globals.globals[1]? = some (.i64
                  (applyEvents (st.mem, g1)
                    (slotsEvents (slots.take k))).2) ∧
                stL.globals.globals[4]? = some (.i64
                  (g4 + 1 + UInt64.ofNat (relPre slots k))) ∧
                stL.globals.globals[5]? = some (.i64
                  (g5 + UInt64.ofNat (freePre slots k))) ∧
                (∀ j, j ≠ 1 → j ≠ 4 → j ≠ 5 →
                  stL.globals.globals[j]? = st.globals.globals[j]?))
            (μ := fun _ sL =>
              match sL.locals with
              | _ :: _ :: _ :: _ :: _ :: .i64 l6 :: _ =>
                  slots.length + 1 - l6.toNat
              | _ => 0)
          · refine ⟨0, 0, Nat.zero_le _, by simp [wFrame], ?_, ?_, ?_, ?_,
              ?_, ?_⟩
            · simp [applyEvents, slotsEvents]
            · simp
            · rw [List.getElem?_set]
              simp only [if_neg (by omega : ¬ (4 = 1))]
              simpa [applyEvents, slotsEvents] using hg1
            · have hlen4 : 4 < st.globals.globals.length :=
                (List.getElem?_eq_some_iff.mp hg4).choose
              rw [List.getElem?_set]
              simp [hlen4, relPre, slotsEvents]
            · rw [List.getElem?_set]
              simp only [if_neg (by omega : ¬ (4 = 5))]
              simpa [freePre, slotsEvents] using hg5
            · intro j hj1 hj4 hj5
              rw [List.getElem?_set]
              simp only [if_neg (by omega : ¬ (4 = j))]
          · rintro stL sL ⟨k, l8v, hkle, rfl, hmemL, hlenL, h1L, h4L, h5L,
              hothL⟩
            have hkU : (UInt64.ofNat k).toNat = k :=
              toNat_ofNat_lt (by rw [size_eq]; omega)
            have hlenU : (UInt64.ofNat slots.length).toNat = slots.length :=
              toNat_ofNat_lt (by rw [size_eq]; omega)
            have hpgL : stL.mem.pages = st.mem.pages := by
              rw [hmemL]
              exact applyEvents_pages ..
            simp only [wFrame]
            wp_run
            try simp
            by_cases hkend : k = slots.length
            · have hge : UInt64.ofNat k ≥ UInt64.ofNat slots.length := by
                rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
                omega
              rw [if_pos hge]
              subst hkend
              try simp
              try wp_run
              try simp
              have hpgL : stL.mem.pages = st.mem.pages := by
                rw [hmemL]
                exact applyEvents_pages ..
              refine wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_run
              try simp only [h5L]
              try wp_run
              try simp
              refine ⟨by omega, ?_⟩
              have h1L' : (stL.globals.globals.set 5
                  (.i64 (g5 + UInt64.ofNat (freePre slots slots.length) + 1)))[1]? =
                  some (.i64 (applyEvents (st.mem, g1)
                    (slotsEvents (slots.take slots.length))).2) := by
                rw [List.getElem?_set]
                simp only [if_neg (by omega : ¬ (5 = 1))]
                exact h1L
              try simp only [h1L']
              try wp_run
              try simp
              simp only [List.take_length] at hmemL h1L
              rw [h1L]
              try simp
              have hlen1 : 1 < st.globals.globals.length :=
                (List.getElem?_eq_some_iff.mp hg1).choose
              have hlen5 : 5 < st.globals.globals.length :=
                (List.getElem?_eq_some_iff.mp hg5).choose
              have hevn : RelTree.events (.node p slots) =
                  slotsEvents slots ++ [.free p] := rfl
              have hrel : releaseCountOf (RelTree.node p slots) =
                  relPre slots slots.length + 1 := by
                unfold releaseCountOf relPre
                rw [List.take_length, hevn, List.map_append, List.sum_append]
                rfl
              have hfree : freeCountOf (RelTree.node p slots) =
                  freePre slots slots.length + 1 := by
                unfold freeCountOf freePre
                rw [List.take_length, hevn, List.countP_append]
                rfl
              refine ⟨?_, ?_, ?_, hlenL, ?_, ?_, ?_, ?_⟩
              · rw [hpgL, h8N]
                omega
              · simp [releaseFuncDef]
              · rw [hbridge 40 (by decide), hbridge 8 (by decide), hmemL,
                  hevn, applyEvents_append]
                rfl
              · rw [hevn, applyEvents_append]
                rw [List.getElem?_set]
                rw [List.length_set, hlenL]
                simp [hlen1]
                rfl
              · have harith : g4 + 1 + UInt64.ofNat (relPre slots slots.length) =
                    g4 + UInt64.ofNat (relPre slots slots.length + 1) := by
                  apply UInt64.toNat.inj
                  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
                  rw [show (1 : UInt64).toNat = 1 from rfl]
                  omega
                rw [h4L, hrel, ← harith]
              · have harith : g5 + UInt64.ofNat (freePre slots slots.length) + 1 =
                    g5 + UInt64.ofNat (freePre slots slots.length + 1) := by
                  apply UInt64.toNat.inj
                  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
                  rw [show (1 : UInt64).toNat = 1 from rfl]
                  omega
                rw [List.getElem?_set]
                rw [hlenL]
                simp [hlen5]
                rw [hfree, ← harith]
              · intro j hj1 hj4 hj5
                rw [List.getElem?_set]
                simp only [if_neg (by omega : ¬ (1 = j))]
                rw [List.getElem?_set]
                simp only [if_neg (by omega : ¬ (5 = j))]
                exact hothL j hj1 hj4 hj5
            · have hklt : k < slots.length :=
                Nat.lt_of_le_of_ne hkle hkend
              have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat slots.length) := by
                rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
                omega
              rw [if_neg hnge]
              try simp
              try wp_run
              try simp
              have hbit := slotsMask_shift_and slots k hklt h32
              have hslotk := SlotsAt_get hslots k hklt
              have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
                apply UInt64.toNat.inj
                rw [toNat_add_one, hkU,
                  toNat_ofNat_lt (by rw [size_eq]; omega)]
                try rw [hkU, size_eq]
                try omega
              have hk1U : (UInt64.ofNat (k + 1)).toNat = k + 1 :=
                toNat_ofNat_lt (by rw [size_eq]; omega)
              refine wp_iff_cons rfl ?_
              have hmod : (UInt64.ofNat k) % 64 = UInt64.ofNat k := by
                apply UInt64.toNat.inj
                rw [UInt64.toNat_mod, hkU,
                  show (64 : UInt64).toNat = 64 from rfl]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hmod]
              have hmul8 : UInt64.ofNat k * 8 = UInt64.ofNat (8 * k) := by
                apply UInt64.toNat.inj
                rw [UInt64.toNat_mul, hkU,
                  show (8 : UInt64).toNat = 8 from rfl,
                  toNat_ofNat_lt (by rw [size_eq]; omega)]
                rw [show (2 : Nat) ^ 64 = 18446744073709551616 from by
                  norm_num]
                omega
              have haddrk : (p + UInt64.ofNat (8 * k)).toUInt32.toNat =
                  p.toNat + 8 * k := by
                rw [toUInt32_toNat, UInt64.toNat_add,
                  toNat_ofNat_lt (by rw [size_eq]; omega)]
                have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
                rw [Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega)]
              have hpardis : ∀ r ∈ slotsFootprint slots,
                  regionsDisjoint (p.toNat - 48, 48 + 8 * slots.length) r := by
                have hcons : RelTree.footprint (.node p slots) =
                    (p.toNat - 48, 48 + 8 * slots.length) ::
                    slotsFootprint slots := rfl
                have := hok.1
                rw [hcons] at this
                exact (List.pairwise_cons.mp this).1
              have hsepk : ∀ e ∈ slotsEvents (slots.take k),
                  eventSep ((p + UInt64.ofNat (8 * k)).toUInt32) e := by
                intro e he
                have heIn := slotsEvents_take_mem he
                obtain ⟨r, hr, hsub⟩ := slotsEvents_sub slots e heIn
                have hrb := hok.2 r (by
                  rw [show RelTree.footprint (.node p slots) =
                    (p.toNat - 48, 48 + 8 * slots.length) ::
                    slotsFootprint slots from rfl]
                  exact List.mem_cons_of_mem _ hr)
                unfold regionSub eventRegion at hsub
                simp only at hsub
                refine eventSep_of_region
                  (r := (p.toNat - 48, 48 + 8 * slots.length))
                  ⟨by rw [haddrk]; omega, by rw [haddrk]; omega⟩
                  (regionsDisjoint_of_sub
                    (by unfold regionSub eventRegion; exact hsub)
                    (regionsDisjoint_symm (hpardis r hr)))
                  ⟨by omega, by omega⟩
              have hreadk : stL.mem.read64
                  ((p + UInt64.ofNat (8 * k)).toUInt32) =
                  (slots[k]!).stored := by
                rw [hmemL]
                rw [read64_applyEvents_ne _ _ _
                  (by rw [haddrk]; omega) hsepk]
                have := (SlotsAt_get hslots k hklt).1
                simpa using this
              rcases hshape : slots[k]! with v | _ | t'
              · rw [hshape] at hbit
                simp only [RelSlot.masked] at hbit
                rw [if_neg (by simp [hbit])]
                wp_run
                try simp
                have hpre : slotsEvents (slots.take (k + 1)) =
                    slotsEvents (slots.take k) := by
                  rw [slotsEvents_take_succ _ _ hklt, hshape]
                  simp [slotEvents]
                have hrelpre : relPre slots (k + 1) = relPre slots k := by
                  unfold relPre
                  rw [hpre]
                have hfreepre : freePre slots (k + 1) = freePre slots k := by
                  unfold freePre
                  rw [hpre]
                refine ⟨⟨k + 1, by omega, hkadd, ?_, hlenL, ?_, ?_, ?_,
                  hothL⟩, by omega⟩
                · rw [hpre]
                  exact hmemL
                · rw [hpre]
                  exact h1L
                · rw [hrelpre]
                  exact h4L
                · rw [hfreepre]
                  exact h5L
              · rw [hshape] at hbit hreadk
                simp only [RelSlot.masked] at hbit
                simp only [RelSlot.stored] at hreadk
                rw [if_pos (by simp [hbit])]
                wp_run
                try simp
                refine ⟨by rw [hpgL]; omega, ?_⟩
                have hreadk' : stL.mem.read64
                    (UInt32.ofNat ((p.toNat + k * 8) % 4294967296)) = 0 := by
                  rw [show UInt32.ofNat ((p.toNat + k * 8) % 4294967296) =
                      (p + UInt64.ofNat (8 * k)).toUInt32 from by
                    apply UInt32.toNat.inj
                    rw [toUInt32_ofNat_mod_toNat, haddrk]
                    rw [Nat.mod_eq_of_lt (by omega)]
                    omega]
                  exact hreadk
                simp only [hreadk']
                refine wp_call_tw (release_null env m id _ hf hImp) ?_
                rintro st6 vs6 ⟨rfl, rfl⟩
                wp_run
                try simp
                have hpre : slotsEvents (slots.take (k + 1)) =
                    slotsEvents (slots.take k) := by
                  rw [slotsEvents_take_succ _ _ hklt, hshape]
                  simp [slotEvents]
                have hrelpre : relPre slots (k + 1) = relPre slots k := by
                  unfold relPre
                  rw [hpre]
                have hfreepre : freePre slots (k + 1) = freePre slots k := by
                  unfold freePre
                  rw [hpre]
                refine ⟨⟨k + 1, by omega, hkadd, ?_, hlenL, ?_, ?_, ?_,
                  hothL⟩, by omega⟩
                · rw [hpre]
                  exact hmemL
                · rw [hpre]
                  exact h1L
                · rw [hrelpre]
                  exact h4L
                · rw [hfreepre]
                  exact h5L
              · rw [hshape] at hbit hreadk
                simp only [RelSlot.masked] at hbit
                simp only [RelSlot.stored] at hreadk
                rw [if_pos (by simp [hbit])]
                wp_run
                try simp
                refine ⟨by rw [hpgL]; omega, ?_⟩
                have hreadk' : stL.mem.read64
                    (UInt32.ofNat ((p.toNat + k * 8) % 4294967296)) =
                    t'.root := by
                  rw [show UInt32.ofNat ((p.toNat + k * 8) % 4294967296) =
                      (p + UInt64.ofNat (8 * k)).toUInt32 from by
                    apply UInt32.toNat.inj
                    rw [toUInt32_ofNat_mod_toNat, haddrk]
                    rw [Nat.mod_eq_of_lt (by omega)]
                    omega]
                  exact hreadk
                simp only [hreadk']
                have hmemSlot : RelSlot.child t' ∈ slots := by
                  rw [← hshape, getElem_bang _ _ hklt]
                  exact List.getElem_mem ..
                have hsize : sizeOf t' ≤ n := by
                  have h1 := sizeOf_child_lt hmemSlot
                  simp at hn
                  omega
                have hokTail : footprintOk (slotsFootprint slots) := by
                  have hcons : RelTree.footprint (.node p slots) =
                      (p.toNat - 48, 48 + 8 * slots.length) ::
                      slotsFootprint slots := rfl
                  refine ⟨?_, fun r hr => hok.2 r (by
                    rw [hcons]
                    exact List.mem_cons_of_mem _ hr)⟩
                  have := hok.1
                  rw [hcons] at this
                  exact (List.pairwise_cons.mp this).2
                have hdecomp : slotsFootprint slots =
                    slotsFootprint (slots.take k) ++
                    (t'.footprint ++ slotsFootprint (slots.drop (k + 1))) := by
                  have h := congrArg slotsFootprint (slots_take_drop slots k hklt)
                  rw [hshape] at h
                  rw [h, slotsFootprint_append, slotsFootprint_cons]
                  simp [slotFootprint]
                have hokDecomp : footprintOk
                    (slotsFootprint (slots.take k) ++
                    (t'.footprint ++ slotsFootprint (slots.drop (k + 1)))) := by
                  rw [← hdecomp]
                  exact hokTail
                have hokT' : footprintOk t'.footprint :=
                  footprintOk_append_left (footprintOk_append_right hokDecomp)
                have hTree : TreeAt stL.mem t' := by
                  rw [hmemL]
                  refine TreeAt_applyEvents (st.mem, g1) _ t'
                    ((SlotsAt_get hslots k hklt).2 t' hshape) hokT' ?_ ?_
                  · intro e he r hr
                    obtain ⟨re, hre, hsub⟩ :=
                      slotsEvents_sub (slots.take k) e he
                    have hpw := List.pairwise_append.mp hokDecomp.1
                    have hdis := hpw.2.2 re hre r (List.mem_append_left _ hr)
                    exact regionsDisjoint_of_sub hsub hdis
                  · intro e he
                    have heIn := slotsEvents_take_mem he
                    obtain ⟨re, hre, hsub⟩ := slotsEvents_sub _ e heIn
                    have hrb := hok.2 re (by
                      rw [show RelTree.footprint (.node p slots) =
                        (p.toNat - 48, 48 + 8 * slots.length) ::
                        slotsFootprint slots from rfl]
                      exact List.mem_cons_of_mem _ hre)
                    unfold regionSub eventRegion at hsub
                    simp only at hsub
                    exact ⟨by omega, by omega⟩
                have hfitT' : ∀ r ∈ t'.footprint,
                    r.1 + r.2 ≤ stL.mem.pages * 65536 := by
                  intro r hr
                  rw [hpgL]
                  refine hfit r ?_
                  rw [show RelTree.footprint (.node p slots) =
                    (p.toNat - 48, 48 + 8 * slots.length) ::
                    slotsFootprint slots from rfl]
                  refine List.mem_cons_of_mem _ ?_
                  rw [hdecomp]
                  exact List.mem_append_right _ (List.mem_append_left _ hr)
                refine wp_call_tw (ih _ t'
                  (applyEvents (st.mem, g1) (slotsEvents (slots.take k))).2
                  (g4 + 1 + UInt64.ofNat (relPre slots k))
                  (g5 + UInt64.ofNat (freePre slots k))
                  hsize hTree hokT' hfitT' h1L h4L h5L) ?_
                rintro st6 vs6 ⟨rfl, hmem6, hlen6, h1L6, h4L6, h5L6, hoth6⟩
                wp_run
                try simp
                have hpair : applyEvents (st.mem, g1)
                    (slotsEvents (slots.take k)) =
                    (stL.mem, (applyEvents (st.mem, g1)
                      (slotsEvents (slots.take k))).2) := by
                  rw [hmemL]
                have hpre : slotsEvents (slots.take (k + 1)) =
                    slotsEvents (slots.take k) ++ t'.events := by
                  rw [slotsEvents_take_succ _ _ hklt, hshape]
                  rfl
                have hrelpre : relPre slots (k + 1) =
                    relPre slots k + releaseCountOf t' := by
                  unfold relPre releaseCountOf
                  rw [hpre, List.map_append, List.sum_append]
                  try rfl
                have hfreepre : freePre slots (k + 1) =
                    freePre slots k + freeCountOf t' := by
                  unfold freePre freeCountOf
                  rw [hpre, List.countP_append]
                  try rfl
                have harith4 : g4 + 1 + UInt64.ofNat (relPre slots k) +
                    UInt64.ofNat (releaseCountOf t') =
                    g4 + 1 + UInt64.ofNat (relPre slots (k + 1)) := by
                  rw [hrelpre]
                  apply UInt64.toNat.inj
                  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
                  omega
                have harith5 : g5 + UInt64.ofNat (freePre slots k) +
                    UInt64.ofNat (freeCountOf t') =
                    g5 + UInt64.ofNat (freePre slots (k + 1)) := by
                  rw [hfreepre]
                  apply UInt64.toNat.inj
                  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
                  omega
                refine ⟨⟨k + 1, by omega, hkadd, ?_, hlen6.trans hlenL, ?_,
                  ?_, ?_, fun j h1 h4 h5 =>
                    (hoth6 j h1 h4 h5).trans (hothL j h1 h4 h5)⟩,
                  by omega⟩
                · rw [hpre, applyEvents_append, hpair]
                  exact hmem6
                · rw [hpre, applyEvents_append, hpair]
                  exact h1L6
                · rw [← harith4]
                  exact h4L6
                · rw [← harith5]
                  exact h5L6

/-- The generic teardown theorem: releasing the root of an ownership tree
frees every owned node in traversal order, decrements every shared leaf,
and leaves the free list at the root, with the counters exact. -/
theorem release_frees_tree (env : HostEnv Unit) (m : Module) (id : Nat)
    (st : Store Unit) (t : RelTree) (g1 g4 g5 : UInt64)
    (hf : m.funcs[id - m.imports.length]? = some (releaseFuncDef id))
    (hImp : m.imports[id]? = none)
    (ht : TreeAt st.mem t)
    (hok : footprintOk t.footprint)
    (hfit : ∀ r ∈ t.footprint, r.1 + r.2 ≤ st.mem.pages * 65536)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5)) :
    TerminatesWith (m := m) (id := id) (initial := st) (env := env)
      [.i64 t.root]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (applyEvents (st.mem, g1) t.events).1 ∧
        st'.globals.globals.length = st.globals.globals.length ∧
        st'.globals.globals[1]? =
          some (.i64 (applyEvents (st.mem, g1) t.events).2) ∧
        st'.globals.globals[4]? =
          some (.i64 (g4 + UInt64.ofNat (releaseCountOf t))) ∧
        st'.globals.globals[5]? =
          some (.i64 (g5 + UInt64.ofNat (freeCountOf t))) ∧
        (∀ k, k ≠ 1 → k ≠ 4 → k ≠ 5 →
          st'.globals.globals[k]? = st.globals.globals[k]?)) :=
  release_tree_fuel env m id hf hImp (sizeOf t) st t g1 g4 g5 (le_refl _)
    ht hok hfit hg1 hg4 hg5

end Project.Runtime
