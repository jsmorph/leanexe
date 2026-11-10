import Demos.Rcv.Maine.RefineTally
import Demos.Rcv.Maine.Rounds

/-!
The end of a round of the Maine program: `Demos.Rcv.Maine.Program.decideRound` gives the words of
`Demos.Rcv.Maine.decision`.  The counters hold the votes `v i` of candidate `i` at slot `i - 1`, as
`Demos.Rcv.Refine.Votes` states, and the continuing set is `members cont n`.  `lastPlaceOf_eq`
states rule 2 as the Oakland module's rule 4, `Demos.Rcv.Rounds.lowestDecision` of
`Demos.Rcv.Rounds.ruleTied`, from the Oakland refinement's lemmas on `fewestOf`, `tiedOf`, and
`latestOf`.  With two continuing candidates, rule 2 eliminates the one with fewer votes or, when
they tie, the one later in the order (`fewest_two`), and the program names the other one through
the exclusive or of the continuing set's mask with the eliminated candidate's (`mask_xor_left`,
`mask_xor_right`).
-/

namespace Demos.Rcv.Maine.Refine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Refine Demos.Rcv.Rounds

theorem memberCount_eq (cont n : UInt64) (hn : n.toNat ≤ 63) :
    (Program.memberCount cont n).toNat = (members cont n.toNat).length := by
  unfold Program.memberCount
  rw [loop_members_filter (m := cont) (P := fun _ => true) (step := fun s _ => s + 1)
    (fun i hi s => by
      try dsimp only
      rw [bit_test cont (show i < 64 by omega)]
      cases cont.toNat.testBit i <;> simp), List.filter_true]
  have hl := length_members cont n.toNat
  rw [foldl_count _ 0 (by simp only [UInt64.toNat_zero]; omega)]
  simp

/-- Rule 2 of the rounds as the Oakland module's rule 4. -/
theorem lastPlaceOf_eq (ws t : Array UInt64) {v : Nat → Nat} (ht : Votes t v) (cont n : UInt64)
    (hn : n.toNat ≤ 63) (tl : Tally)
    (hvotes : tl.votes = (members cont n.toNat).map fun i => (i, v i))
    (hne : members cont n.toNat ≠ []) (order : List Nat)
    (horder : order = (List.range n.toNat).map fun j => (ws[3 + n.toNat + j]!).toNat)
    (hperm : order.Perm (List.range' 1 n.toNat)) :
    Program.lastPlaceOf ws t cont n = endWords (lowestDecision order (ruleTied tl.votes)) := by
  unfold Program.lastPlaceOf
  dsimp only
  have hfw := fewestOf_eq ht cont n hn hne
  obtain ⟨hzm, hzl⟩ := tiedOf_eq ht cont n (Program.fewestOf t cont n) hn
  have hsnd : ((members cont n.toNat).map fun i => (i, v i)).map (fun x : Nat × Nat => x.2) =
      (members cont n.toNat).map v := by
    rw [List.map_map]
    rfl
  have hZ : ruleTied tl.votes =
      (members cont n.toNat).filter fun j => decide (v j = (Program.fewestOf t cont n).toNat) := by
    unfold ruleTied
    rw [hvotes, hsnd, ← hfw, List.filter_map, List.map_map]
    exact List.map_id _
  have hZsub : ((members cont n.toNat).filter fun j =>
      decide (v j = (Program.fewestOf t cont n).toNat)).Sublist (List.range' 1 n.toNat) :=
    List.filter_sublist.trans (members_sublist _ _)
  have hZne : ((members cont n.toNat).filter fun j =>
      decide (v j = (Program.fewestOf t cont n).toNat)) ≠ [] := by
    rw [← hZ, ruleTied_eq_fewest]
    apply fewest_ne_nil
    rw [hvotes]
    simpa using hne
  rw [hZ]
  generalize hZv : ((members cont n.toNat).filter fun j =>
      decide (v j = (Program.fewestOf t cont n).toNat)) = Z at hzm hzl hZsub hZne ⊢
  by_cases h1 : Z.length = 1
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
    have hz2 : (Program.tiedOf t cont n (Program.fewestOf t cont n)).2 = 1 :=
      UInt64.toNat_inj.mp (by rw [hzl, h1]; rfl)
    simp only [hz2, beq_self_eq_true, ↓reduceIte]
    subst hx
    show _ = endWords (.eliminate (.lowest x))
    simp only [endWords]
    rw [ofNat_eq hzm]
  · have hz2 : ¬ ((Program.tiedOf t cont n (Program.fewestOf t cont n)).2 == 1) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, hzl]
      exact h1
    rw [ite_eq_right hz2, lowestDecision_of_ne (fun z hz => h1 (by rw [hz]; rfl))]
    simp only [endWords]
    have h3n : (3 + n).toNat = 3 + n.toNat := by
      rw [UInt64.toNat_add, show (3 : UInt64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hordm : ∀ j, j < n.toNat → (ws[3 + n.toNat + j]!).toNat ∈ order := by
      intro j hj
      rw [horder]
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have hord : ∀ j, j < n.toNat →
        1 ≤ (ws[(3 + n).toNat + j]!).toNat ∧ (ws[(3 + n).toNat + j]!).toNat ≤ 63 := by
      intro j hj
      rw [h3n]
      have := List.mem_range'_1.mp (hperm.subset (hordm j hj))
      omega
    have hz : ∀ i, 1 ≤ i → i ≤ 63 →
        ((Program.tiedOf t cont n (Program.fewestOf t cont n)).1.toNat.testBit (i - 1) = true ↔
          i ∈ Z) := by
      intro i hi1 _
      rw [hzm, testBit_mask_sublist hZsub, Nat.sub_add_cancel hi1]
      simp
    have hlat := latestOf_eq ws (3 + n) n (Program.tiedOf t cont n (Program.fewestOf t cont n)).1
      Z (by rw [h3n]; omega) hz hord
    have hord_eq :
        ((List.range n.toNat).map fun j => (ws[(3 + n).toNat + j]!).toNat) = order := by
      rw [horder, h3n]
    rw [hord_eq] at hlat
    have hlatest : ((order.filter fun o => decide (o ∈ Z)).getLast?).getD 0 = latest order Z := by
      unfold latest
      rw [List.getLastD_eq_getLast?]
      obtain ⟨z, hz'⟩ := List.exists_mem_of_ne_nil Z hZne
      have hzo : z ∈ order := hperm.symm.subset (hZsub.subset hz')
      have hfne : (order.filter fun o => decide (o ∈ Z)) ≠ [] := by
        intro hnil
        have hm : z ∈ order.filter fun o => decide (o ∈ Z) :=
          List.mem_filter.mpr ⟨hzo, by simpa using hz'⟩
        rw [hnil] at hm
        simp at hm
      rw [List.getLast?_eq_some_getLast hfne]
      rfl
    rw [hlatest] at hlat
    have hlm := latest_mem (order := order) hZne
    have hxr := List.mem_range'_1.mp (hZsub.subset hlm)
    have hl : Demos.Rcv.Program.latestOf ws (3 + n) n
        (Program.tiedOf t cont n (Program.fewestOf t cont n)).1 =
        UInt64.ofNat (latest order Z) := (ofNat_eq hlat).symm
    have hsh : (1 : UInt64) <<< (UInt64.ofNat (latest order Z) - 1) =
        (1 : UInt64) <<< UInt64.ofNat (latest order Z - 1) := by
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, ofNat_toNat_lt (by omega)]
          simp
          omega),
        ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
      rfl
    rw [hl, hsh, ofNat_eq hzm,
      ofNat_eq (show ((1 : UInt64) <<< UInt64.ofNat (latest order Z - 1)).toNat =
        mask [latest order Z] by rw [toNat_shift' (by omega), mask_singleton])]

/-! ## Two candidates -/

/-- The candidates with the fewest votes of two candidates. -/
theorem fewest_two (x y a b : Nat) :
    fewest [(x, a), (y, b)] = if a = b then [x, y] else if a < b then [x] else [y] := by
  unfold fewest
  by_cases hab : a = b
  · subst hab
    simp
  · by_cases hlt : a < b
    · simp [hab, hlt, Nat.le_of_lt hlt, Nat.not_le.mpr hlt]
    · have hba : b < a := by omega
      simp [hab, hlt, Nat.le_of_lt hba, Nat.not_le.mpr hba]

theorem lt_of_pair {x y n : Nat} (h : [x, y].Sublist (List.range' 1 n)) : x < y := by
  have := sorted_of_sublist h
  simpa using this

/-- Of two candidates, the mask less the first is the second's. -/
theorem mask_xor_left {x y n : Nat} (h : [x, y].Sublist (List.range' 1 n)) :
    mask [x, y] ^^^ mask [x] = mask [y] := by
  have hxy := lt_of_pair h
  have hx : [x].Sublist (List.range' 1 n) :=
    (List.Sublist.cons_cons x (List.nil_sublist [y])).trans h
  have hy : [y].Sublist (List.range' 1 n) := (List.sublist_cons_self x [y]).trans h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_mask_sublist h, testBit_mask_sublist hx, testBit_mask_sublist hy]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  by_cases h1 : j + 1 = x
  · simp [h1, Nat.ne_of_lt hxy]
  · simp [h1]

/-- Of two candidates, the mask less the second is the first's. -/
theorem mask_xor_right {x y n : Nat} (h : [x, y].Sublist (List.range' 1 n)) :
    mask [x, y] ^^^ mask [y] = mask [x] := by
  have hxy := lt_of_pair h
  have hx : [x].Sublist (List.range' 1 n) :=
    (List.Sublist.cons_cons x (List.nil_sublist [y])).trans h
  have hy : [y].Sublist (List.range' 1 n) := (List.sublist_cons_self x [y]).trans h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_mask_sublist h, testBit_mask_sublist hx, testBit_mask_sublist hy]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  by_cases h1 : j + 1 = y
  · simp [h1, Nat.ne_of_gt hxy]
  · simp [h1]

/-- The candidate of a mask that holds one candidate `i`. -/
theorem bitIndex_single {w : UInt64} {i : Nat} (h1 : 1 ≤ i) (h2 : i ≤ 63)
    (hw : w.toNat = 2 ^ (i - 1)) : Demos.Rcv.Program.bitIndex w + 1 = UInt64.ofNat i := by
  have hw' : w = (1 : UInt64) <<< UInt64.ofNat (i - 1) :=
    UInt64.toNat_inj.mp (by rw [hw, toNat_shift' (by omega)])
  rw [hw', bitIndex_shift' (by omega), ofNat_succ, Nat.sub_add_cancel h1]

/-! ## The end of a round -/

/-- `decideRound` gives the words of `decision` for a round whose counters hold the votes `v` of the
continuing set `members cont n`. -/
theorem decideRound_eq (ws t : Array UInt64) {v : Nat → Nat} (ht : Votes t v) (cont n : UInt64)
    (hn : n.toNat ≤ 63) (hcont : cont.toNat < 2 ^ n.toNat) (tl : Tally)
    (hvotes : tl.votes = (members cont n.toNat).map fun i => (i, v i)) (order : List Nat)
    (horder : order = (List.range n.toNat).map fun j => (ws[3 + n.toNat + j]!).toNat)
    (hperm : order.Perm (List.range' 1 n.toNat)) :
    Program.decideRound ws t cont n = endWords (decision order tl) := by
  have hs := memberCount_eq cont n hn
  have hmask := mask_members hcont
  have hlp := fun hne => lastPlaceOf_eq ws t ht cont n hn tl hvotes hne order horder hperm
  have hsub := members_sublist cont n.toNat
  unfold Program.decideRound
  dsimp only
  generalize members cont n.toNat = M at hs hmask hlp hvotes hsub
  rcases M with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · have h0 : Program.memberCount cont n = 0 := UInt64.toNat_inj.mp (by rw [hs]; rfl)
    rw [h0, decision_nil (by rw [hvotes]; rfl)]
    rfl
  · have h1 : Program.memberCount cont n = 1 := UInt64.toNat_inj.mp (by rw [hs]; rfl)
    have hx := List.mem_range'_1.mp (hsub.subset (List.mem_singleton_self x))
    rw [h1, decision_one (by rw [hvotes]; rfl)]
    simp only [beq_self_eq_true, ↓reduceIte, show ((1 : UInt64) == 0) = false from rfl,
      Bool.false_eq_true]
    rw [bitIndex_single hx.1 (by omega) (by rw [← hmask, mask_singleton])]
    rfl
  · have h2 : Program.memberCount cont n = 2 := UInt64.toNat_inj.mp (by rw [hs]; rfl)
    have hxy := lt_of_pair hsub
    have hx := List.mem_range'_1.mp (hsub.subset (List.mem_cons_self))
    have hy := List.mem_range'_1.mp (hsub.subset (List.mem_cons_of_mem x
      (List.mem_singleton_self y)))
    have htv : tl.votes = [(x, v x), (y, v y)] := by rw [hvotes]; rfl
    rw [h2, hlp (by simp), decision_two htv, htv, ruleTied_eq_fewest, fewest_two]
    simp only [show ((2 : UInt64) == 0) = false from rfl,
      show ((2 : UInt64) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      beq_self_eq_true, Bool.true_and]
    by_cases hab : v x = v y
    · rw [ite_eq_left hab, ite_eq_left hab, lowestDecision_of_ne (by simp)]
      rfl
    · rw [ite_eq_right hab, ite_eq_right hab]
      by_cases hlt : v x < v y
      · rw [ite_eq_left hlt, ite_eq_right (show ¬ v y < v x by omega)]
        simp only [show (endWords (lowestDecision order [x])).1 = 1 from rfl, beq_self_eq_true,
          ↓reduceIte]
        rw [show (endWords (lowestDecision order [x])).2.1 = UInt64.ofNat (mask [x]) from rfl]
        have hm : mask [x] < 2 ^ 64 := by
          rw [mask_singleton]
          exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        have hw : (cont ^^^ UInt64.ofNat (mask [x])).toNat = 2 ^ (y - 1) := by
          rw [UInt64.toNat_xor, ofNat_toNat_lt hm, ← hmask, mask_xor_left hsub,
            mask_singleton]
        rw [bitIndex_single hy.1 (by omega) hw]
        rfl
      · have hba : v y < v x := by omega
        rw [ite_eq_right hlt, ite_eq_left hba]
        simp only [show (endWords (lowestDecision order [y])).1 = 1 from rfl, beq_self_eq_true,
          ↓reduceIte]
        rw [show (endWords (lowestDecision order [y])).2.1 = UInt64.ofNat (mask [y]) from rfl]
        have hm : mask [y] < 2 ^ 64 := by
          rw [mask_singleton]
          exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        have hw : (cont ^^^ UInt64.ofNat (mask [y])).toNat = 2 ^ (x - 1) := by
          rw [UInt64.toNat_xor, ofNat_toNat_lt hm, ← hmask, mask_xor_right hsub,
            mask_singleton]
        rw [bitIndex_single hx.1 (by omega) hw]
        rfl
  · have hlen : 3 ≤ tl.votes.length := by rw [hvotes]; simp
    have hne0 : (Program.memberCount cont n == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      rw [h] at hs
      simp at hs
    have hne1 : (Program.memberCount cont n == 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      rw [h] at hs
      simp at hs
    have hne2 : (Program.memberCount cont n == 2) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      rw [h] at hs
      simp at hs
    rw [hne0, hne1, hne2, hlp (by simp), decision_three hlen]
    rfl

end Demos.Rcv.Maine.Refine
