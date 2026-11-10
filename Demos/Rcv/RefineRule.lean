import Demos.Rcv.RefineTally
import Demos.Rcv.Rounds

/-!
The end of a round: the loops of `Demos.Rcv.Program.decideRound` over the counters of a round
compute `Demos.Rcv.Spec.rule`, and `Demos.Rcv.Program.pushRound` appends the round's words.  The
counters hold the votes `v i` of candidate `i` at slot `i - 1`, as `Votes` states, and the
continuing set is `members cont n`, the candidates of the mask `cont`.
-/

namespace Demos.Rcv.Refine

open Demos.Rcv Demos.Rcv.Spec

theorem ofNat_toNat_lt {x : Nat} (h : x < 2 ^ 64) : (UInt64.ofNat x).toNat = x :=
  UInt64.toNat_ofNat_of_lt' h

theorem ofNat_succ (i : Nat) : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one, Nat.reducePow]
  omega

/-- The counters `t` of a round hold the votes `v i` of each candidate `i` from 1 to 63 at slot
`i - 1`, and every vote count is below `2 ^ 32`. -/
structure Votes (t : Array UInt64) (v : Nat → Nat) : Prop where
  get : ∀ i, 1 ≤ i → i ≤ 63 → t[i - 1]!.toNat = v i
  bound : ∀ i, v i < 2 ^ 32

theorem members_range {m : UInt64} {n : Nat} (hn : n ≤ 63) {i : Nat} (hi : i ∈ members m n) :
    1 ≤ i ∧ i ≤ 63 := by
  have := mem_members.mp hi
  omega

theorem length_members (m : UInt64) (n : Nat) : (members m n).length ≤ n := by
  have := (members_sublist m n).length_le
  simpa using this

theorem sum_le {L : List Nat} {v : Nat → Nat} {b : Nat} (hv : ∀ i ∈ L, v i < b) :
    (L.map v).sum ≤ L.length * b := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := hv x List.mem_cons_self
    have h2 := ih (fun i hi => hv i (List.mem_cons_of_mem x hi))
    omega

/-- The sum of the votes of at most 63 candidates is below `2 ^ 38`. -/
theorem sum_votes_lt {L : List Nat} {v : Nat → Nat} (hL : L.length ≤ 63)
    (hv : ∀ i, v i < 2 ^ 32) :
    (L.map v).sum < 2 ^ 38 := by
  have h1 := sum_le (L := L) (b := 2 ^ 32) (fun i _ => hv i)
  have h2 : L.length * 2 ^ 32 ≤ 63 * 2 ^ 32 := Nat.mul_le_mul_right _ hL
  have h3 : (63 : Nat) * 2 ^ 32 < 2 ^ 38 := by norm_num
  omega

/-- A loop over the candidates `0` to `n - 1` whose step changes the state only at the members of
the mask `m` that satisfy `P` is a fold over those members. -/
theorem loop_members_filter {α : Type} {m n : UInt64} {init : α} {f : UInt64 → α → α}
    {P : Nat → Bool} {step : α → Nat → α}
    (hf : ∀ i, i < n.toNat → ∀ s, f (UInt64.ofNat i) s =
      if (m.toNat.testBit i && P (i + 1)) = true then step s (i + 1) else s) :
    LeanExe.loop n init f = ((members m n.toNat).filter P).foldl step init := by
  rw [List.foldl_filter]
  apply loop_members
  intro i hi s
  rw [hf i hi s]
  cases m.toNat.testBit i <;> simp

/-! ## Folds -/

theorem foldl_triple {α β γ δ : Type} (L : List δ) (f₁ : α → δ → α) (f₂ : β → δ → β)
    (f₃ : γ → δ → γ) (a : α) (b : β) (c : γ) :
    L.foldl (fun s j => (f₁ s.1 j, f₂ s.2.1 j, f₃ s.2.2 j)) (a, b, c) =
      (L.foldl f₁ a, L.foldl f₂ b, L.foldl f₃ c) := by
  induction L generalizing a b c with
  | nil => rfl
  | cons x L ih => exact ih _ _ _

theorem foldl_pair {α β δ : Type} (L : List δ) (f₁ : α → δ → α) (f₂ : β → δ → β) (a : α)
    (b : β) :
    L.foldl (fun s j => (f₁ s.1 j, f₂ s.2 j)) (a, b) = (L.foldl f₁ a, L.foldl f₂ b) := by
  induction L generalizing a b with
  | nil => rfl
  | cons x L ih => exact ih _ _

theorem foldl_or_testBit :
    ∀ (L : List Nat) (m : UInt64), (∀ i ∈ L, 1 ≤ i ∧ i ≤ 64) → ∀ b,
    (L.foldl (fun m j => m ||| (1 : UInt64) <<< UInt64.ofNat (j - 1)) m).toNat.testBit b =
      (m.toNat.testBit b || decide (b + 1 ∈ L))
  | [], m, _, b => by simp
  | x :: L, m, hL, b => by
    have hx := hL x List.mem_cons_self
    rw [List.foldl_cons, foldl_or_testBit L _ (fun i hi => hL i (List.mem_cons_of_mem x hi)) b,
      UInt64.toNat_or, Nat.testBit_or, toNat_shift' (by omega), Nat.testBit_two_pow]
    have hd : decide (x - 1 = b) = decide (b + 1 = x) := decide_eq_decide.mpr (by omega)
    rw [hd]
    simp only [List.mem_cons, Bool.decide_or, Bool.or_assoc]

/-- The union of the bits of an increasing list of candidates is its mask. -/
theorem foldl_or_mask {L : List Nat} {n : Nat} (hn : n ≤ 63) (hL : L.Sublist (List.range' 1 n)) :
    (L.foldl (fun m j => m ||| (1 : UInt64) <<< UInt64.ofNat (j - 1)) 0).toNat = mask L := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [foldl_or_testBit L 0 (fun i hi => by have := List.mem_range'_1.mp (hL.subset hi); omega),
    testBit_mask_sublist hL]
  simp

theorem foldl_add_votes {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) :
    ∀ (L : List Nat) (a : UInt64), (∀ i ∈ L, 1 ≤ i ∧ i ≤ 63) →
      a.toNat + (L.map v).sum < 2 ^ 64 →
      (L.foldl (fun acc i => acc + t[i - 1]!) a).toNat = a.toNat + (L.map v).sum
  | [], a, _, _ => by simp
  | x :: L, a, hL, hs => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hs ⊢
    have hx := hL x List.mem_cons_self
    have ha : (a + t[x - 1]!).toNat = a.toNat + v x := by
      rw [UInt64.toNat_add, ht.get x hx.1 hx.2, Nat.mod_eq_of_lt (by omega)]
    rw [foldl_add_votes ht L (a + t[x - 1]!) (fun i hi => hL i (List.mem_cons_of_mem x hi))
      (by omega), ha]
    omega

theorem foldl_count {δ : Type} : ∀ (L : List δ) (c : UInt64), c.toNat + L.length < 2 ^ 64 →
    (L.foldl (fun s _ => s + 1) c).toNat = c.toNat + L.length
  | [], c, _ => by simp
  | x :: L, c, h => by
    simp only [List.foldl_cons, List.length_cons] at h ⊢
    have hc : (c + 1).toNat = c.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    rw [foldl_count L (c + 1) (by omega), hc]
    omega

theorem foldl_last {α : Type} (P : α → Bool) (l0 : α) (L : List α) :
    L.foldl (fun l x => if P x = true then x else l) l0 = (L.filter P).getLast?.getD l0 := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.filter_append]
    cases hp : P x
    · simp [hp]
    · simp [hp]

/-! ## The loops of a round -/

theorem continuingOf_eq {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) (cont n : UInt64)
    (hn : n.toNat ≤ 63) :
    (Program.continuingOf t cont n).toNat = ((members cont n.toNat).map v).sum := by
  unfold Program.continuingOf
  rw [loop_members_filter (m := cont) (P := fun _ => true) (step := fun acc i => acc + t[i - 1]!)
    (fun i hi s => by
      try dsimp only
      rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega)]
      simp)]
  rw [List.filter_true]
  have hs := sum_votes_lt (L := members cont n.toNat) ((length_members _ _).trans hn) ht.bound
  rw [foldl_add_votes ht (members cont n.toNat) 0 (fun i hi => members_range hn hi)
    (by simp; omega)]
  simp

theorem foldl_keep (L : List Nat) {w : UInt64} (hw : w ≠ 0) (q : Nat → Bool) :
    L.foldl (fun w i => if (w == 0 && q i) = true then UInt64.ofNat i else w) w = w := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.foldl_cons, ite_eq_right (by simp [hw]), ih]

theorem foldl_first (q p : Nat → Bool) :
    ∀ (L : List Nat), (∀ i ∈ L, 1 ≤ i ∧ i ≤ 63 ∧ q i = p i) →
    L.foldl (fun w i => if (w == 0 && q i) = true then UInt64.ofNat i else w) 0 =
      match L.find? p with
      | some i => UInt64.ofNat i
      | none => 0
  | [], _ => rfl
  | x :: L, hL => by
    obtain ⟨h1, h2, hq⟩ := hL x List.mem_cons_self
    rw [List.foldl_cons, List.find?_cons]
    cases hp : p x
    · rw [hq, hp]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact foldl_first q p L (fun i hi => hL i (List.mem_cons_of_mem x hi))
    · rw [hq, hp]
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
      apply foldl_keep
      intro h
      have := congrArg UInt64.toNat h
      rw [ofNat_toNat_lt (by omega)] at this
      simp at this
      omega

theorem majorityOf_eq {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) (cont T n : UInt64)
    (hn : n.toNat ≤ 63) :
    Program.majorityOf t cont T n =
      match (members cont n.toNat).find? (fun i => decide (T.toNat < 2 * v i)) with
      | some i => UInt64.ofNat i
      | none => 0 := by
  unfold Program.majorityOf
  rw [loop_members_filter (m := cont) (P := fun _ => true)
    (step := fun w i => if (w == 0 && decide (T < 2 * t[i - 1]!)) = true then UInt64.ofNat i else w)
    (fun i hi s => by
      try dsimp only
      rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega),
        ofNat_succ]
      cases cont.toNat.testBit i <;> simp)]
  rw [List.filter_true]
  apply foldl_first
  intro i hi
  obtain ⟨h1, h2⟩ := members_range hn hi
  refine ⟨h1, h2, ?_⟩
  have hv := ht.get i h1 h2
  have hb := ht.bound i
  apply decide_eq_decide.mpr
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, hv, show (2 : UInt64).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem lowerOf_eq {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) (cont n vx : UInt64)
    (hn : n.toNat ≤ 63) :
    (Program.lowerOf t cont n vx).1.toNat =
        mask ((members cont n.toNat).filter fun j => decide (v j < vx.toNat)) ∧
      (Program.lowerOf t cont n vx).2.1.toNat =
        (((members cont n.toNat).filter fun j => decide (v j < vx.toNat)).map v).sum ∧
      (Program.lowerOf t cont n vx).2.2.toNat =
        ((members cont n.toNat).filter fun j => decide (v j < vx.toNat)).length := by
  have hP : ((members cont n.toNat).filter fun j => decide (t[j - 1]! < vx)) =
      ((members cont n.toNat).filter fun j => decide (v j < vx.toNat)) := by
    apply List.filter_congr
    intro j hj
    obtain ⟨h1, h2⟩ := members_range hn hj
    apply decide_eq_decide.mpr
    rw [UInt64.lt_iff_toNat_lt, ht.get j h1 h2]
  have hloop : Program.lowerOf t cont n vx =
      ((members cont n.toNat).filter fun j => decide (t[j - 1]! < vx)).foldl
        (fun s j => (s.1 ||| (1 : UInt64) <<< UInt64.ofNat (j - 1), s.2.1 + t[j - 1]!, s.2.2 + 1))
        ((0 : UInt64), (0 : UInt64), (0 : UInt64)) := by
    unfold Program.lowerOf
    apply loop_members_filter
    intro i hi s
    try dsimp only
    rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega)]
    simp
  rw [hloop, hP, foldl_triple (f₁ := fun m j => m ||| (1 : UInt64) <<< UInt64.ofNat (j - 1))
    (f₂ := fun acc j => acc + t[j - 1]!) (f₃ := fun c _ => c + 1)]
  have hsub : ((members cont n.toNat).filter fun j => decide (v j < vx.toNat)).Sublist
      (List.range' 1 n.toNat) := List.filter_sublist.trans (members_sublist cont n.toNat)
  have hrange : ∀ i ∈ (members cont n.toNat).filter fun j => decide (v j < vx.toNat),
      1 ≤ i ∧ i ≤ 63 := fun i hi => members_range hn (List.mem_of_mem_filter hi)
  have hlen : ((members cont n.toNat).filter fun j => decide (v j < vx.toNat)).length ≤ 63 :=
    (hsub.length_le.trans (by simp)).trans hn
  have hs := sum_votes_lt hlen ht.bound
  refine ⟨foldl_or_mask hn hsub, ?_, ?_⟩
  · rw [foldl_add_votes ht _ 0 hrange (by simp; omega)]
    simp
  · rw [foldl_count ((members cont n.toNat).filter fun j => decide (v j < vx.toNat)) 0
      (by simp; omega)]
    simp

theorem fewestOf_fold {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) :
    ∀ (L : List Nat) (m : UInt64), (∀ i ∈ L, 1 ≤ i ∧ i ≤ 63) →
      (L.foldl (fun m j => if t[j - 1]! < m then t[j - 1]! else m) m).toNat =
        (L.map v).foldl min m.toNat
  | [], m, _ => by simp
  | x :: L, m, hL => by
    obtain ⟨h1, h2⟩ := hL x List.mem_cons_self
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      fewestOf_fold ht L _ (fun i hi => hL i (List.mem_cons_of_mem x hi))]
    congr 1
    by_cases h : t[x - 1]! < m
    · rw [ite_eq_left h, ht.get x h1 h2]
      rw [UInt64.lt_iff_toNat_lt, ht.get x h1 h2] at h
      omega
    · rw [ite_eq_right h]
      rw [UInt64.lt_iff_toNat_lt, ht.get x h1 h2] at h
      omega

theorem fewestOf_eq {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) (cont n : UInt64)
    (hn : n.toNat ≤ 63) (hne : members cont n.toNat ≠ []) :
    (Program.fewestOf t cont n).toNat = (((members cont n.toNat).map v).min?).getD 0 := by
  have hloop : Program.fewestOf t cont n =
      (members cont n.toNat).foldl (fun m j => if t[j - 1]! < m then t[j - 1]! else m)
        0xFFFFFFFFFFFFFFFF := by
    unfold Program.fewestOf
    rw [loop_members_filter (m := cont) (P := fun _ => true)
      (step := fun m j => if t[j - 1]! < m then t[j - 1]! else m)
      (fun i hi s => by
        try dsimp only
        rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega)]
        cases cont.toNat.testBit i <;> simp), List.filter_true]
  rw [hloop]
  obtain ⟨x, L, hxL⟩ : ∃ x L, members cont n.toNat = x :: L := List.exists_cons_of_ne_nil hne
  have hrange : ∀ i ∈ x :: L, 1 ≤ i ∧ i ≤ 63 := fun i hi => members_range hn (hxL ▸ hi)
  rw [hxL, List.foldl_cons, fewestOf_fold ht L _ (fun i hi => hrange i (List.mem_cons_of_mem x hi))]
  obtain ⟨h1, h2⟩ := hrange x List.mem_cons_self
  have hx : t[x - 1]! < 0xFFFFFFFFFFFFFFFF := by
    rw [UInt64.lt_iff_toNat_lt, ht.get x h1 h2]
    have := ht.bound x
    simp only [UInt64.reduceToNat]
    omega
  rw [ite_eq_left hx, ht.get x h1 h2]
  rfl

theorem tiedOf_eq {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) (cont n f : UInt64)
    (hn : n.toNat ≤ 63) :
    (Program.tiedOf t cont n f).1.toNat =
        mask ((members cont n.toNat).filter fun j => decide (v j = f.toNat)) ∧
      (Program.tiedOf t cont n f).2.toNat =
        ((members cont n.toNat).filter fun j => decide (v j = f.toNat)).length := by
  have hP : ((members cont n.toNat).filter fun j => t[j - 1]! == f) =
      ((members cont n.toNat).filter fun j => decide (v j = f.toNat)) := by
    apply List.filter_congr
    intro j hj
    obtain ⟨h1, h2⟩ := members_range hn hj
    rw [← ht.get j h1 h2, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, UInt64.toNat_inj]
  have hloop : Program.tiedOf t cont n f =
      ((members cont n.toNat).filter fun j => t[j - 1]! == f).foldl
        (fun s j => (s.1 ||| (1 : UInt64) <<< UInt64.ofNat (j - 1), s.2 + 1))
        ((0 : UInt64), (0 : UInt64)) := by
    unfold Program.tiedOf
    apply loop_members_filter
    intro i hi s
    try dsimp only
    rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega)]
    simp
  rw [hloop, hP, foldl_pair (f₁ := fun m j => m ||| (1 : UInt64) <<< UInt64.ofNat (j - 1))
    (f₂ := fun c _ => c + 1)]
  have hsub : ((members cont n.toNat).filter fun j => decide (v j = f.toNat)).Sublist
      (List.range' 1 n.toNat) := List.filter_sublist.trans (members_sublist cont n.toNat)
  have hlen : ((members cont n.toNat).filter fun j => decide (v j = f.toNat)).length ≤ 63 :=
    (hsub.length_le.trans (by simp)).trans hn
  refine ⟨foldl_or_mask hn hsub, ?_⟩
  rw [foldl_count ((members cont n.toNat).filter fun j => decide (v j = f.toNat)) 0
    (by simp; omega)]
  simp

/-- `latestOf` gives the last candidate of the order, whose words start at `base`, that the mask
`z` holds. -/
theorem latestOf_eq (ws : Array UInt64) (base n z : UInt64) (Z : List Nat)
    (hbase : base.toNat + n.toNat < 2 ^ 64)
    (hz : ∀ i, 1 ≤ i → i ≤ 63 → (z.toNat.testBit (i - 1) = true ↔ i ∈ Z))
    (hord : ∀ j, j < n.toNat →
      1 ≤ (ws[base.toNat + j]!).toNat ∧ (ws[base.toNat + j]!).toNat ≤ 63) :
    (Program.latestOf ws base n z).toNat =
      ((((List.range n.toNat).map fun j => (ws[base.toNat + j]!).toNat).filter
        fun o => decide (o ∈ Z)).getLast?).getD 0 := by
  unfold Program.latestOf
  rw [loop_eq_foldl]
  have hstep : ∀ j, j < n.toNat → ∀ l : UInt64,
      (let o := ws[(base + UInt64.ofNat j).toNat]!
       if ((z >>> (o - 1)) &&& 1 != 0) = true then o else l) =
        (fun l o => if decide (o.toNat ∈ Z) = true then o else l) l (ws[base.toNat + j]!) := by
    intro j hj l
    have hidx : (base + UInt64.ofNat j).toNat = base.toNat + j := by
      rw [UInt64.toNat_add, ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    try dsimp only
    rw [hidx]
    obtain ⟨h1, h2⟩ := hord j hj
    have hsub : ws[base.toNat + j]! - 1 = UInt64.ofNat ((ws[base.toNat + j]!).toNat - 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h1),
        ofNat_toNat_lt (by omega)]
      rfl
    rw [hsub, bit_test z (by omega)]
    have := hz _ h1 h2
    by_cases hm : (ws[base.toNat + j]!).toNat ∈ Z
    · simp [this.mpr hm, hm]
    · have hb : z.toNat.testBit ((ws[base.toNat + j]!).toNat - 1) = false := by
        cases hh : z.toNat.testBit ((ws[base.toNat + j]!).toNat - 1)
        · rfl
        · exact absurd (this.mp hh) hm
      simp [hb, hm]
  rw [foldl_range_congr (fun j hj l => hstep j hj l),
    ← List.foldl_map (f := fun j => ws[base.toNat + j]!)
      (g := fun l o => if decide (o.toNat ∈ Z) = true then o else l), foldl_last]
  have hmap : ∀ L : List UInt64,
      ((L.filter fun o => decide (o.toNat ∈ Z)).getLast?.getD 0).toNat =
        (((L.map UInt64.toNat).filter fun o => decide (o ∈ Z)).getLast?).getD 0 := by
    intro L
    rw [List.filter_map, List.getLast?_map]
    simp only [Function.comp_def]
    cases (L.filter fun o => decide (o.toNat ∈ Z)).getLast? <;> rfl
  rw [hmap, List.map_map]
  rfl

/-! ## Rule 3 -/

theorem batchOf_eq (t : Array UInt64) (cont n : UInt64) (hn : n.toNat ≤ 63) :
    Program.batchOf t cont n = (members cont n.toNat).foldl (fun best x =>
      let vx := t[x - 1]!
      let l := Program.lowerOf t cont n vx
      if 2 ≤ l.2.2 && l.2.1 < vx && best.2 < l.2.2 then (l.1, l.2.2) else best)
      ((0 : UInt64), (0 : UInt64)) := by
  unfold Program.batchOf
  rw [loop_members_filter (P := fun _ => true), List.filter_true]
  intro i hi s
  try dsimp only
  rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega)]
  cases cont.toNat.testBit i <;> simp

/-- The step of rule 3's fold over the qualifying sets. -/
def batchStep (best : Option (List Nat)) (s : List Nat) : Option (List Nat) :=
  match best with
  | some b => if b.length < s.length then some s else some b
  | none => some s

/-- `L(X)` for the candidate `x` of the continuing set `C`. -/
def lowerSet (C : List Nat) (v : Nat → Nat) (x : Nat) : List Nat :=
  C.filter fun j => decide (v j < v x)

/-- Rule 3 over the votes of `C` is a fold over `C`. -/
theorem batch_map (C : List Nat) (v : Nat → Nat) :
    batch (C.map fun i => (i, v i)) =
      C.foldl (fun best x =>
        if (decide (2 ≤ (lowerSet C v x).length) &&
            decide (((lowerSet C v x).map v).sum < v x)) = true then
          batchStep best (lowerSet C v x)
        else best) none := by
  have hlower : ∀ w, lower (C.map fun i => (i, v i)) w =
      (C.filter fun j => decide (v j < w)).map fun i => (i, v i) := by
    intro w
    simp only [lower, List.filter_map]
    rfl
  unfold batch
  simp only [List.foldl_filter, List.foldl_map]
  congr 1
  funext best x
  simp only [qualifies, hlower, List.map_map]
  have h1 : (Prod.fst ∘ fun i => (i, v i)) = id := rfl
  have h2 : (Prod.snd ∘ fun i => (i, v i)) = v := rfl
  rw [h1, h2, List.map_id]
  simp only [lowerSet]
  by_cases hlen : 2 ≤ (C.filter fun j => decide (v j < v x)).length
  · have hne : (C.filter fun j => decide (v j < v x)).isEmpty = false := by
      cases h : C.filter fun j => decide (v j < v x)
      · rw [h] at hlen; simp at hlen
      · rfl
    simp only [List.isEmpty_map, hne, hlen, decide_true, Bool.not_false, Bool.true_and]
    by_cases hs : ((C.filter fun j => decide (v j < v x)).map v).sum < v x
    · simp only [hs, decide_true, ↓reduceIte, batchStep]
      cases best <;> rfl
    · simp [hs]
  · simp [hlen]

/-- The program's state of rule 3, the mask and the size of the best set so far, stands for the
specification's best set. -/
def BatchRel (b : UInt64 × UInt64) : Option (List Nat) → Prop
  | none => b = (0, 0)
  | some s => b.1.toNat = mask s ∧ b.2.toNat = s.length ∧ 2 ≤ s.length

theorem batchOf_spec {t : Array UInt64} {v : Nat → Nat} (ht : Votes t v) (cont n : UInt64)
    (hn : n.toNat ≤ 63) :
    BatchRel (Program.batchOf t cont n) (batch ((members cont n.toNat).map fun i => (i, v i))) := by
  rw [batchOf_eq t cont n hn, batch_map]
  have hrange : ∀ i ∈ members cont n.toNat, 1 ≤ i ∧ i ≤ 63 :=
    fun i hi => members_range hn hi
  have key : ∀ (L : List Nat), (∀ x ∈ L, x ∈ members cont n.toNat) →
      ∀ b o, BatchRel b o →
      BatchRel (L.foldl (fun best x =>
        let vx := t[x - 1]!
        let l := Program.lowerOf t cont n vx
        if 2 ≤ l.2.2 && l.2.1 < vx && best.2 < l.2.2 then (l.1, l.2.2) else best) b)
        (L.foldl (fun best x =>
          if (decide (2 ≤ (lowerSet (members cont n.toNat) v x).length) &&
              decide (((lowerSet (members cont n.toNat) v x).map v).sum < v x)) = true then
            batchStep best (lowerSet (members cont n.toNat) v x)
          else best) o) := by
    intro L
    induction L with
    | nil => intro _ b o h; exact h
    | cons x L ih =>
      intro hL b o hbo
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun y hy => hL y (List.mem_cons_of_mem x hy))
      have hx := hL x List.mem_cons_self
      obtain ⟨h1, h2⟩ := hrange x hx
      have hvx := ht.get x h1 h2
      obtain ⟨hm, hsum, hcnt⟩ := lowerOf_eq ht cont n t[x - 1]! hn
      rw [hvx] at hm hsum hcnt
      have hsub : (lowerSet (members cont n.toNat) v x).Sublist (List.range' 1 n.toNat) :=
        List.filter_sublist.trans (members_sublist cont n.toNat)
      have hlen : (lowerSet (members cont n.toNat) v x).length ≤ 63 :=
        (hsub.length_le.trans (by simp)).trans hn
      have hs := sum_votes_lt hlen ht.bound
      try dsimp only
      generalize hl : Program.lowerOf t cont n t[x - 1]! = l at hm hsum hcnt ⊢
      have hm' : l.1.toNat = mask (lowerSet (members cont n.toNat) v x) := hm
      have hsum' : l.2.1.toNat = ((lowerSet (members cont n.toNat) v x).map v).sum := hsum
      have hcnt' : l.2.2.toNat = (lowerSet (members cont n.toNat) v x).length := hcnt
      have e1 : (2 ≤ l.2.2) ↔ 2 ≤ (lowerSet (members cont n.toNat) v x).length := by
        rw [UInt64.le_iff_toNat_le, hcnt']
        rfl
      have e2 : (l.2.1 < t[x - 1]!) ↔
          ((lowerSet (members cont n.toNat) v x).map v).sum < v x := by
        rw [UInt64.lt_iff_toNat_lt, hsum', hvx]
      by_cases hc : 2 ≤ (lowerSet (members cont n.toNat) v x).length ∧
          ((lowerSet (members cont n.toNat) v x).map v).sum < v x
      · have hsc : (decide (2 ≤ (lowerSet (members cont n.toNat) v x).length) &&
            decide (((lowerSet (members cont n.toNat) v x).map v).sum < v x)) = true := by
          simp [hc.1, hc.2]
        simp only [hsc, ↓reduceIte]
        cases o with
        | none =>
          have hb0 : b = (0, 0) := hbo
          subst hb0
          have hpos : (0 : UInt64) < l.2.2 := by
            rw [UInt64.lt_iff_toNat_lt, hcnt']
            have := hc.1
            simp only [UInt64.toNat_zero]
            omega
          have hpc : (decide (2 ≤ l.2.2) && decide (l.2.1 < t[x - 1]!) &&
              decide (((0 : UInt64), (0 : UInt64)).2 < l.2.2)) = true := by
            simp [e1.mpr hc.1, e2.mpr hc.2, hpos]
          simp only [hpc, ↓reduceIte, batchStep]
          exact ⟨hm', hcnt', hc.1⟩
        | some s =>
          obtain ⟨hbm, hbl, hb2⟩ := hbo
          simp only [batchStep]
          by_cases hlt : s.length < (lowerSet (members cont n.toNat) v x).length
          · have hlt' : b.2 < l.2.2 := by
              rw [UInt64.lt_iff_toNat_lt, hcnt', hbl]
              exact hlt
            have hpc : (decide (2 ≤ l.2.2) && decide (l.2.1 < t[x - 1]!) &&
                decide (b.2 < l.2.2)) = true := by
              simp [e1.mpr hc.1, e2.mpr hc.2, hlt']
            simp only [hpc, hlt, ↓reduceIte]
            exact ⟨hm', hcnt', hc.1⟩
          · have hlt' : ¬ b.2 < l.2.2 := by
              rw [UInt64.lt_iff_toNat_lt, hcnt', hbl]
              exact hlt
            have hpc : (decide (2 ≤ l.2.2) && decide (l.2.1 < t[x - 1]!) &&
                decide (b.2 < l.2.2)) = false := by
              simp [hlt']
            simp only [hpc, hlt, Bool.false_eq_true, ↓reduceIte]
            exact ⟨hbm, hbl, hb2⟩
      · have hsc : (decide (2 ≤ (lowerSet (members cont n.toNat) v x).length) &&
            decide (((lowerSet (members cont n.toNat) v x).map v).sum < v x)) = false := by
          simpa using hc
        have hpc : (decide (2 ≤ l.2.2) && decide (l.2.1 < t[x - 1]!) &&
            decide (b.2 < l.2.2)) = false := by
          cases h : (decide (2 ≤ l.2.2) && decide (l.2.1 < t[x - 1]!) && decide (b.2 < l.2.2))
          · rfl
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact absurd ⟨e1.mp h.1.1, e2.mp h.1.2⟩ hc
        simp only [hsc, hpc, Bool.false_eq_true, ↓reduceIte]
        exact hbo
  exact key _ (fun x hx => hx) (0, 0) none rfl

/-! ## The end of a round -/

theorem ofNat_eq {w : UInt64} {x : Nat} (h : w.toNat = x) : UInt64.ofNat x = w := by
  subst h
  exact UInt64.ofNat_toNat

/-- The words of a round's end: the code of the elimination, the masks of the eliminated
candidates and of the tied set, and the winner, or 0. -/
def endWords : Decision → UInt64 × UInt64 × UInt64 × UInt64
  | .winner w => (0, 0, 0, UInt64.ofNat (w.getD 0))
  | .eliminate (.batch s) => (3, UInt64.ofNat (mask s), 0, 0)
  | .eliminate (.lowest z) => (1, UInt64.ofNat (mask [z]), 0, 0)
  | .eliminate (.order Z i) => (2, UInt64.ofNat (mask [i]), UInt64.ofNat (mask Z), 0)

/-- `decideRound` gives the words of `rule`'s decision for a round whose counters hold the votes
`v` of the continuing set `members cont n`. -/
theorem decideRound_eq (ws t : Array UInt64) {v : Nat → Nat} (ht : Votes t v) (cont T n : UInt64)
    (hn : n.toNat ≤ 63) (tl : Tally)
    (hvotes : tl.votes = (members cont n.toNat).map fun i => (i, v i))
    (hT : T.toNat = ((members cont n.toNat).map v).sum)
    (order : List Nat)
    (horder : order = (List.range n.toNat).map fun j => (ws[3 + n.toNat + j]!).toNat)
    (hperm : order.Perm (List.range' 1 n.toNat)) :
    Program.decideRound ws t cont T n = endWords (rule order tl) := by
  have hrange : ∀ i ∈ members cont n.toNat, 1 ≤ i ∧ i ≤ 63 :=
    fun i hi => members_range hn hi
  have hcont : tl.continuing = T.toNat := by
    rw [hT]
    simp only [Tally.continuing, hvotes, List.map_map]
    rfl
  have hfind : tl.votes.find? (fun x : Nat × Nat => tl.continuing < 2 * x.2) =
      ((members cont n.toNat).find? fun i => decide (T.toNat < 2 * v i)).map
        fun i => (i, v i) := by
    rw [hvotes, hcont, List.find?_map]
    rfl
  unfold Program.decideRound
  rw [majorityOf_eq ht cont T n hn]
  cases hf : (members cont n.toNat).find? (fun i => decide (T.toNat < 2 * v i)) with
  | some i =>
    rw [hf, Option.map_some] at hfind
    rw [Demos.Rcv.Rounds.rule_of_majority hfind]
    obtain ⟨h1, h2⟩ := hrange i (List.mem_of_find?_eq_some hf)
    have hi0 : UInt64.ofNat i ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      rw [ofNat_toNat_lt (by omega)] at this
      simp at this
      omega
    simp only [bne_iff_ne, ne_eq, hi0, not_false_eq_true, ↓reduceIte]
    rfl
  | none =>
    rw [hf] at hfind
    simp only [Option.map_none] at hfind
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hT0 : T.toNat = 0
    · have hT0' : T = 0 := UInt64.toNat_inj.mp (by simpa using hT0)
      rw [ite_eq_left (by simp [hT0']), Demos.Rcv.Rounds.rule_of_zero hfind (by rw [hcont, hT0])]
      rfl
    · have hTne : ¬ (T == 0) = true := by
        intro h
        apply hT0
        rw [beq_iff_eq] at h
        rw [h]
        rfl
      have hc0 : tl.continuing ≠ 0 := by rw [hcont]; exact hT0
      rw [ite_eq_right hTne]
      have hrel := batchOf_spec ht cont n hn
      cases hbatch : batch ((members cont n.toNat).map fun i => (i, v i)) with
      | some s =>
        rw [hbatch] at hrel
        obtain ⟨hbm, hbl, hb2⟩ := hrel
        have hb0 : (Program.batchOf t cont n).2 ≠ 0 := by
          intro h
          rw [h] at hbl
          simp at hbl
          omega
        rw [Demos.Rcv.Rounds.rule_of_batch hfind hc0 (by rw [hvotes]; exact hbatch)]
        simp only [bne_iff_ne, ne_eq, hb0, not_false_eq_true, ↓reduceIte, endWords]
        rw [ofNat_eq hbm]
      | none =>
        rw [hbatch] at hrel
        have hb0 : Program.batchOf t cont n = (0, 0) := hrel
        rw [Demos.Rcv.Rounds.rule_of_lowest hfind hc0 (by rw [hvotes]; exact hbatch)]
        simp only [hb0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hne : members cont n.toNat ≠ [] := by
          intro h
          apply hT0
          rw [hT, h]
          rfl
        have hfw := fewestOf_eq ht cont n hn hne
        obtain ⟨hzm, hzl⟩ := tiedOf_eq ht cont n (Program.fewestOf t cont n) hn
        have hsnd : ((members cont n.toNat).map fun i => (i, v i)).map (fun x : Nat × Nat => x.2) =
            (members cont n.toNat).map v := by
          rw [List.map_map]
          rfl
        have hZ : Demos.Rcv.Rounds.ruleTied tl.votes =
            (members cont n.toNat).filter fun j =>
              decide (v j = (Program.fewestOf t cont n).toNat) := by
          unfold Demos.Rcv.Rounds.ruleTied
          rw [hvotes, hsnd, ← hfw, List.filter_map, List.map_map]
          exact List.map_id _
        have hZsub : ((members cont n.toNat).filter fun j =>
            decide (v j = (Program.fewestOf t cont n).toNat)).Sublist (List.range' 1 n.toNat) :=
          List.filter_sublist.trans (members_sublist _ _)
        have hZne : ((members cont n.toNat).filter fun j =>
            decide (v j = (Program.fewestOf t cont n).toNat)) ≠ [] := by
          rw [← hZ, Demos.Rcv.Rounds.ruleTied_eq_fewest]
          apply Demos.Rcv.Rounds.fewest_ne_nil
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
          rw [ite_eq_right hz2,
            Demos.Rcv.Rounds.lowestDecision_of_ne (fun z hz => h1 (by rw [hz]; rfl))]
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
              ((Program.tiedOf t cont n (Program.fewestOf t cont n)).1.toNat.testBit (i - 1) =
                true ↔
                i ∈ Z) := by
            intro i hi1 _
            rw [hzm, testBit_mask_sublist hZsub, Nat.sub_add_cancel hi1]
            simp
          have hlat := latestOf_eq ws (3 + n) n
            (Program.tiedOf t cont n (Program.fewestOf t cont n)).1
            Z (by rw [h3n]; omega) hz hord
          have hord_eq :
              ((List.range n.toNat).map fun j => (ws[(3 + n).toNat + j]!).toNat) = order := by
            rw [horder, h3n]
          rw [hord_eq] at hlat
          have hlatest :
              ((order.filter fun o => decide (o ∈ Z)).getLast?).getD 0 = latest order Z := by
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
          have hlm := Demos.Rcv.Rounds.latest_mem (order := order) hZne
          have hxr := List.mem_range'_1.mp (hZsub.subset hlm)
          have hl : Program.latestOf ws (3 + n) n
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

end Demos.Rcv.Refine
