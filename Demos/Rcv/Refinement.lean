import Demos.Rcv.RefineRule

/-!
The refinement of the count over words: `count_eq` states that `Demos.Rcv.Program.count`, the
program that the module compiles, equals `Demos.Rcv.Spec.countArray` on every array of fewer than
`2 ^ 64` words.  `validArray_iff` shows that the program's test of an array is
`Demos.Rcv.Spec.Words.Valid`, and `countValid_eq` that the program's rounds on a valid array give
the result words of `Demos.Rcv.Spec.count`: `go_eq` follows the `repeatWhile` of the rounds
against `Demos.Rcv.Spec.run`, a round at a time, with the counters of `tallyRound_eq`, the decision
of `decideRound_eq`, and the words of `pushRound_toList`.
-/

namespace Demos.Rcv.Refine

open Demos.Rcv Demos.Rcv.Spec

/-! ## Arrays as lists -/

theorem getD_toList (ws : Array UInt64) (i : Nat) : ws.toList.getD i 0 = ws[i]! := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  by_cases h : i < ws.size
  · rw [getElem?_pos ws i h, getElem!_pos ws i h]
    rfl
  · rw [getElem?_neg ws i h, getElem!_neg ws i h]
    rfl

theorem take_drop_eq_wordsAt (ws : Array UInt64) (q m : Nat) (h : q + m ≤ ws.size) :
    (ws.toList.drop q).take m = wordsAt ws q m := by
  apply List.ext_getElem
  · simp [wordsAt]
    omega
  · intro j h1 h2
    simp only [wordsAt, List.length_map, List.length_range] at h2
    simp only [wordsAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
      Array.getElem_toList]
    rw [getElem!_pos ws (q + j) (by omega)]

theorem drop_eq_wordsAt (ws : Array UInt64) (q : Nat) (h : q ≤ ws.size) :
    ws.toList.drop q = wordsAt ws q (ws.size - q) := by
  rw [← take_drop_eq_wordsAt ws q (ws.size - q) (by omega), List.take_of_length_le]
  simp

theorem chunks_eq (ws : Array UInt64) (k : Nat) : ∀ (N q : Nat), q + N * k ≤ ws.size →
    chunks k N (ws.toList.drop q) = (List.range N).map fun b => ballotAt ws q k b
  | 0, _, _ => rfl
  | N + 1, q, h => by
    rw [Nat.add_mul, Nat.one_mul] at h
    have hd : (ws.toList.drop q).drop k = ws.toList.drop (q + k) := by
      rw [List.drop_drop, Nat.add_comm]
    rw [chunks, take_drop_eq_wordsAt ws q k (by omega), hd, chunks_eq ws k N (q + k) (by omega),
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [ballotAt, Nat.zero_mul, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro b _
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    congr 1
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem wordsAt_map_toNat (ws : Array UInt64) (q m : Nat) :
    (wordsAt ws q m).map UInt64.toNat = (List.range m).map fun j => (ws[q + j]!).toNat := by
  simp only [wordsAt, List.map_map]
  rfl

/-! ## The test of a valid array -/

theorem loop_all_eq (n : UInt64) (P : UInt64 → Bool) :
    LeanExe.loop n true (fun c ok => if !ok then false else P c) =
      (List.range n.toNat).all fun i => P (UInt64.ofNat i) := by
  rw [loop_eq_foldl]
  have key : ∀ (L : List Nat) (b : Bool),
      L.foldl (fun ok i => if !ok then false else P (UInt64.ofNat i)) b =
        (b && L.all fun i => P (UInt64.ofNat i)) := by
    intro L
    induction L with
    | nil => intro b; simp
    | cons x L ih =>
      intro b
      rw [List.foldl_cons, ih]
      cases b <;> simp
  rw [key]
  simp

theorem toNat_add_ofNat (a : UInt64) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    (a + UInt64.ofNat i).toNat = a.toNat + i := by
  rw [UInt64.toNat_add, ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h]

theorem kindsOk_iff (ws : Array UInt64) (n : UInt64) (hn : n.toNat ≤ 63) :
    Program.kindsOk ws n = true ↔ ∀ x ∈ (wordsAt ws 3 n.toNat).map UInt64.toNat, x < 4 := by
  unfold Program.kindsOk
  rw [loop_all_eq, wordsAt_map_toNat, List.all_eq_true]
  simp only [List.mem_range, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro h x i hi rfl
    have := h i hi
    rw [toNat_add_ofNat 3 i (by simp; omega)] at this
    simpa [UInt64.lt_iff_toNat_lt] using this
  · intro h i hi
    rw [toNat_add_ofNat 3 i (by simp; omega)]
    have := h _ i hi rfl
    simpa [UInt64.lt_iff_toNat_lt] using this

/-- The step of `orderOk` at the word `o`. -/
def orderStep (n : UInt64) (s : Bool × UInt64) (o : UInt64) : Bool × UInt64 :=
  if (s.1 && 1 ≤ o && o ≤ n && (s.2 >>> (o - 1)) &&& 1 == 0) = true then
    (true, s.2 ||| (1 : UInt64) <<< (o - 1))
  else (false, s.2)

theorem orderStep_false (n : UInt64) (L : List UInt64) (seen : UInt64) :
    (L.foldl (orderStep n) (false, seen)).1 = false := by
  induction L generalizing seen with
  | nil => rfl
  | cons o L ih =>
    rw [List.foldl_cons]
    have : orderStep n (false, seen) o = (false, seen) := by
      simp [orderStep]
    rw [this, ih]

theorem orderStep_spec (n : UInt64) (hn : n.toNat ≤ 63) :
    ∀ (L : List UInt64) (seen : UInt64) (S : List Nat),
      (∀ b, b < 64 → (seen.toNat.testBit b = true ↔ b + 1 ∈ S)) →
      ((L.foldl (orderStep n) (true, seen)).1 = true ↔
        (∀ o ∈ L, 1 ≤ o.toNat ∧ o.toNat ≤ n.toNat) ∧ (L.map UInt64.toNat).Nodup ∧
          ∀ o ∈ L, o.toNat ∉ S) := by
  intro L
  induction L with
  | nil => intro seen S _; simp
  | cons o L ih =>
    intro seen S hS
    rw [List.foldl_cons]
    by_cases hr : 1 ≤ o.toNat ∧ o.toNat ≤ n.toNat
    · have hsub : o - 1 = UInt64.ofNat (o.toNat - 1) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hr.1),
          ofNat_toNat_lt (by omega)]
        rfl
      have hbit : ((seen >>> (o - 1)) &&& 1 == 0) = !decide (o.toNat ∈ S) := by
        rw [hsub]
        have hb := bit_test seen (show o.toNat - 1 < 64 by omega)
        have hS' := hS (o.toNat - 1) (by omega)
        rw [Nat.sub_add_cancel hr.1] at hS'
        cases h : seen.toNat.testBit (o.toNat - 1)
        · have hnot : o.toNat ∉ S := fun hm => by rw [hS'.mpr hm] at h; cases h
          rw [h] at hb
          have : ((seen >>> UInt64.ofNat (o.toNat - 1)) &&& 1) = 0 := by
            by_contra hne
            rw [bne_iff_ne.mpr hne] at hb
            cases hb
          simp [this, hnot]
        · rw [h] at hb
          have : ((seen >>> UInt64.ofNat (o.toNat - 1)) &&& 1) ≠ 0 :=
            bne_iff_ne.mp hb
          simp [this, hS'.mp h]
      have hle1 : (1 ≤ o) = (1 ≤ o.toNat) := by rw [UInt64.le_iff_toNat_le]; rfl
      have hle2 : (o ≤ n) = (o.toNat ≤ n.toNat) := by rw [UInt64.le_iff_toNat_le]
      by_cases hin : o.toNat ∈ S
      · have hstep : orderStep n (true, seen) o = (false, seen) := by
          simp only [orderStep, hbit, hin]
          simp
        rw [hstep, orderStep_false]
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro _ _ hall
        exact hall o List.mem_cons_self hin
      · have hstep : orderStep n (true, seen) o =
            (true, seen ||| (1 : UInt64) <<< UInt64.ofNat (o.toNat - 1)) := by
          simp only [orderStep]
          rw [hbit]
          simp [hin, UInt64.le_iff_toNat_le, hr.1, hr.2, hsub]
        rw [hstep, ih _ (o.toNat :: S)]
        · simp only [List.mem_cons, List.map_cons, List.nodup_cons, List.mem_map]
          constructor
          · rintro ⟨hrange, hnd, hnot⟩
            refine ⟨?_, ⟨?_, hnd⟩, ?_⟩
            · rintro x (rfl | hx)
              · exact hr
              · exact hrange x hx
            · rintro ⟨y, hy, hyo⟩
              exact hnot y hy (Or.inl hyo)
            · rintro x (rfl | hx)
              · exact hin
              · exact fun h => hnot x hx (Or.inr h)
          · rintro ⟨hrange, ⟨hno, hnd⟩, hnot⟩
            refine ⟨fun x hx => hrange x (Or.inr hx), hnd, ?_⟩
            intro x hx h
            rcases h with h | h
            · exact hno ⟨x, hx, h⟩
            · exact hnot x (Or.inr hx) h
        · intro b hb
          rw [UInt64.toNat_or, Nat.testBit_or, toNat_shift' (by omega), Nat.testBit_two_pow,
            Bool.or_eq_true, decide_eq_true_eq, hS b hb, List.mem_cons]
          constructor
          · rintro (h | h)
            · exact Or.inr h
            · left; omega
          · rintro (h | h)
            · right; omega
            · exact Or.inl h
    · have hstep : orderStep n (true, seen) o = (false, seen) := by
        have : ¬ (1 ≤ o ∧ o ≤ n) := by
          rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le]
          simpa using hr
        unfold orderStep
        rw [ite_eq_right]
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact this ⟨h.1.1.2, h.1.2⟩
      rw [hstep, orderStep_false]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro hall
      exact absurd (hall o List.mem_cons_self) hr

theorem perm_range'_iff {l : List Nat} {n : Nat} (hl : l.length = n) :
    l.Perm (List.range' 1 n) ↔ (∀ x ∈ l, 1 ≤ x ∧ x ≤ n) ∧ l.Nodup := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, h.nodup_iff.mpr List.nodup_range'⟩
    have := List.mem_range'_1.mp (h.subset hx)
    omega
  · rintro ⟨hr, hnd⟩
    apply List.Subperm.perm_of_length_le (List.Nodup.subperm hnd fun x hx => by
      have := hr x hx
      exact List.mem_range'_1.mpr (by omega))
    simp [hl]

theorem orderOk_iff (ws : Array UInt64) (n : UInt64) (hn : n.toNat ≤ 63) :
    Program.orderOk ws n = true ↔
      ((wordsAt ws (3 + n.toNat) n.toNat).map UInt64.toNat).Perm (List.range' 1 n.toNat) := by
  unfold Program.orderOk
  rw [loop_eq_foldl]
  have hstep : ∀ j, j < n.toNat → ∀ s : Bool × UInt64,
      (let o := ws[(3 + n + UInt64.ofNat j).toNat]!
       if (s.1 && 1 ≤ o && o ≤ n && (s.2 >>> (o - 1)) &&& 1 == 0) = true then
         (true, s.2 ||| (1 : UInt64) <<< (o - 1))
       else (false, s.2)) = orderStep n s (ws[3 + n.toNat + j]!) := by
    intro j hj s
    have h3 : (3 + n + UInt64.ofNat j).toNat = 3 + n.toNat + j := by
      rw [toNat_add_ofNat _ j (by simp; omega), UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
      rfl
    dsimp only
    rw [h3]
    rfl
  rw [foldl_range_congr (fun j hj s => hstep j hj s),
    ← List.foldl_map (f := fun j => ws[3 + n.toNat + j]!) (g := orderStep n)]
  have hw : (List.range n.toNat).map (fun j => ws[3 + n.toNat + j]!) =
      wordsAt ws (3 + n.toNat) n.toNat :=
    rfl
  rw [hw, perm_range'_iff (by simp [wordsAt]),
    orderStep_spec n hn _ 0 [] (fun b _ => by simp)]
  simp only [List.mem_map, forall_exists_index, and_imp, List.not_mem_nil, not_false_eq_true,
    implies_true, and_true]
  constructor
  · rintro ⟨hr, hnd⟩
    exact ⟨fun x o ho hx => hx ▸ hr o ho, hnd⟩
  · rintro ⟨hr, hnd⟩
    exact ⟨fun o ho => hr o.toNat o ho rfl, hnd⟩

theorem validWord_iff (n : UInt64) (hn : n.toNat ≤ 63) (w : UInt64) :
    (w == 0x8000000000000000 || w < (1 : UInt64) <<< n) = true ↔ ValidWord n.toNat w := by
  have hsh : ((1 : UInt64) <<< n).toNat = 2 ^ n.toNat := by
    have := toNat_shift' (show n.toNat < 64 by omega)
    rwa [UInt64.ofNat_toNat] at this
  have hov : unnamedOvervote = 0x8000000000000000 := rfl
  simp only [ValidWord, hov, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    UInt64.lt_iff_toNat_lt, hsh]
  constructor
  · rintro (h | h)
    · exact Or.inr (Or.inl h)
    · by_cases h0 : w = 0
      · exact Or.inl h0
      · refine Or.inr (Or.inr ⟨?_, h⟩)
        have : w.toNat ≠ 0 := fun h' => h0 (UInt64.toNat_inj.mp (by simpa using h'))
        omega
  · rintro (h | h | h)
    · right; rw [h]; simp
    · exact Or.inl h
    · exact Or.inr h.2

theorem wordsOk_iff (ws : Array UInt64) (base m n : UInt64) (hn : n.toNat ≤ 63)
    (hfit : base.toNat + m.toNat < 2 ^ 64) :
    Program.wordsOk ws base m n = true ↔
      ∀ w ∈ wordsAt ws base.toNat m.toNat, ValidWord n.toNat w := by
  unfold Program.wordsOk
  rw [loop_all_eq, List.all_eq_true]
  simp only [List.mem_range, wordsAt, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro h w p hp rfl
    have := h p hp
    rw [toNat_add_ofNat base p (by omega)] at this
    exact (validWord_iff n hn _).mp this
  · intro h p hp
    rw [toNat_add_ofNat base p (by omega)]
    exact (validWord_iff n hn _).mpr (h _ p hp rfl)

/-- The header test of `validArray`. -/
theorem header_iff (ws : Array UInt64) (hs : ws.size < 2 ^ 64) (n k N : UInt64) :
    (1 ≤ n && n ≤ 63 && 1 ≤ k && k ≤ 63 && N ≤ 0xFFFFFFFF &&
        ws.size.toUInt64 == 3 + 2 * n + N * k) = true ↔
      1 ≤ n.toNat ∧ n.toNat ≤ 63 ∧ 1 ≤ k.toNat ∧ k.toNat ≤ 63 ∧
        N.toNat ≤ 2 ^ 32 - 1 ∧
        ws.size = 3 + 2 * n.toNat + N.toNat * k.toNat := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, UInt64.le_iff_toNat_le,
    UInt64.reduceToNat]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    have hNk : N.toNat * k.toNat ≤ 4294967295 * 63 := Nat.mul_le_mul h5 h4
    have := congrArg UInt64.toNat h6
    rw [LeanExe.Dialect.size_toUInt64 ws hs] at this
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, Nat.reducePow] at this
    refine ⟨h1, h2, h3, h4, by norm_num; omega, ?_⟩
    rw [this]
    omega
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hNk : N.toNat * k.toNat ≤ 4294967295 * 63 := Nat.mul_le_mul (by norm_num at h5; omega) h4
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, by norm_num at h5; omega⟩, ?_⟩
    apply UInt64.toNat_inj.mp
    rw [LeanExe.Dialect.size_toUInt64 ws hs]
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, Nat.reducePow]
    omega

theorem readWords_n (ws : Array UInt64) : (readWords ws.toList).n = ws[0]!.toNat := by
  simp only [readWords, getD_toList]

theorem readWords_k (ws : Array UInt64) : (readWords ws.toList).k = ws[1]!.toNat := by
  simp only [readWords, getD_toList]

theorem readWords_N (ws : Array UInt64) : (readWords ws.toList).N = ws[2]!.toNat := by
  simp only [readWords, getD_toList]

/-- The program's test of an array is `Words.Valid`. -/
theorem validArray_iff (ws : Array UInt64) (hs : ws.size < 2 ^ 64) :
    Program.validArray ws = true ↔ (readWords ws.toList).Valid ws.toList.length := by
  have hva : Program.validArray ws =
      if ((1 : UInt64) ≤ ws[0]! && ws[0]! ≤ (63 : UInt64) && (1 : UInt64) ≤ ws[1]! &&
          ws[1]! ≤ (63 : UInt64) && ws[2]! ≤ (0xFFFFFFFF : UInt64) &&
          ws.size.toUInt64 == (3 : UInt64) + (2 : UInt64) * (ws[0]! : UInt64) +
          (ws[2]! : UInt64) * (ws[1]! : UInt64)) = true then
        Program.kindsOk ws ws[0]! && Program.orderOk ws ws[0]! &&
          Program.wordsOk ws ((3 : UInt64) + (2 : UInt64) * (ws[0]! : UInt64))
            ((ws[2]! : UInt64) * (ws[1]! : UInt64)) ws[0]!
      else false := rfl
  rw [hva, Array.length_toList]
  simp only [Words.Valid, readWords_n, readWords_k, readWords_N, maxIndex, maxBallots]
  by_cases hh : ((1 : UInt64) ≤ ws[0]! && ws[0]! ≤ (63 : UInt64) && (1 : UInt64) ≤ ws[1]! &&
          ws[1]! ≤ (63 : UInt64) && ws[2]! ≤ (0xFFFFFFFF : UInt64) &&
      ws.size.toUInt64 == (3 : UInt64) + (2 : UInt64) * (ws[0]! : UInt64) +
          (ws[2]! : UInt64) * (ws[1]! : UInt64)) = true
  · rw [ite_eq_left hh]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (header_iff ws hs _ _ _).mp hh
    have hNk' : ws[2]!.toNat * ws[1]!.toNat ≤ 4294967295 * 63 :=
      Nat.mul_le_mul (by norm_num at h5; omega) h4
    have hbase :
        ((3 : UInt64) + (2 : UInt64) * (ws[0]! : UInt64)).toNat = 3 + 2 * ws[0]!.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, Nat.reducePow]
      omega
    have hNk : ((ws[2]! : UInt64) * ws[1]!).toNat = ws[2]!.toNat * ws[1]!.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega)]
    have hfit : ((3 : UInt64) + (2 : UInt64) * (ws[0]! : UInt64)).toNat +
        ((ws[2]! : UInt64) * ws[1]!).toNat < 2 ^ 64 := by
      rw [hbase, hNk]
      norm_num
      omega
    have hpos : (readWords ws.toList).positions =
        wordsAt ws (3 + 2 * ws[0]!.toNat) (ws[2]!.toNat * ws[1]!.toNat) := by
      simp only [readWords, getD_toList]
      rw [drop_eq_wordsAt ws _ (by omega)]
      congr 1
      omega
    have hkinds : (readWords ws.toList).kinds = (wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat := by
      simp only [readWords, getD_toList]
      rw [take_drop_eq_wordsAt ws 3 _ (by omega)]
    have horder : (readWords ws.toList).order =
        (wordsAt ws (3 + ws[0]!.toNat) ws[0]!.toNat).map UInt64.toNat := by
      simp only [readWords, getD_toList]
      rw [take_drop_eq_wordsAt ws _ _ (by omega)]
    rw [Bool.and_eq_true, Bool.and_eq_true, kindsOk_iff ws ws[0]! h2, orderOk_iff ws ws[0]! h2,
      wordsOk_iff ws ((3 : UInt64) + (2 : UInt64) * (ws[0]! : UInt64))
        ((ws[2]! : UInt64) * (ws[1]! : UInt64)) ws[0]! h2 hfit,
      hbase, hNk, hpos, hkinds, horder]
    constructor
    · rintro ⟨⟨hk', ho⟩, hw⟩
      exact ⟨h1, h2, h3, h4, h5, h6, hk', ho, hw⟩
    · rintro ⟨-, -, -, -, -, -, hk', ho, hw⟩
      exact ⟨⟨hk', ho⟩, hw⟩
  · rw [ite_eq_right hh]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, h3, h4, h5, h6, -⟩
    exact hh ((header_iff ws hs _ _ _).mpr ⟨h1, h2, h3, h4, h5, h6⟩)

/-! ## The counted set and the fuel -/

theorem allOnes_testBit' :
    ∀ i : Fin 64, (0xFFFFFFFFFFFFFFFF : UInt64).toNat.testBit i.val = true := by
  decide +kernel

theorem allOnes_testBit {i : Nat} (hi : i < 64) :
    (0xFFFFFFFFFFFFFFFF : UInt64).toNat.testBit i = true :=
  allOnes_testBit' ⟨i, hi⟩

theorem members_allOnes (n : Nat) (hn : n ≤ 64) :
    members 0xFFFFFFFFFFFFFFFF n = List.range' 1 n := by
  unfold members
  rw [List.filter_eq_self]
  intro i hi
  have := List.mem_range'_1.mp hi
  exact allOnes_testBit (by omega)

/-- The candidates of kind 0 or 1 among the `n` kinds from word 3. -/
def countedOfWords (ws : Array UInt64) (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun i => decide (ws[3 + (i - 1)]! < 2)

theorem countedOf_eq (ws : Array UInt64) (n : UInt64) (hn : n.toNat ≤ 63) :
    (Program.countedOf ws n).toNat = mask (countedOfWords ws n.toNat) := by
  unfold Program.countedOf
  rw [loop_members_filter (m := 0xFFFFFFFFFFFFFFFF) (P := fun i => decide (ws[3 + (i - 1)]! < 2))
    (step := fun m j => m ||| (1 : UInt64) <<< UInt64.ofNat (j - 1)) (fun i hi s => by
      try dsimp only
      rw [allOnes_testBit (by omega), toNat_add_ofNat 3 i (by simp; omega)]
      simp), members_allOnes _ (by omega)]
  exact foldl_or_mask hn List.filter_sublist

theorem countedSize_eq (ws : Array UInt64) (n : UInt64) (hn : n.toNat ≤ 63) :
    (Program.countedSize ws n).toNat = (countedOfWords ws n.toNat).length := by
  unfold Program.countedSize
  rw [loop_members_filter (m := 0xFFFFFFFFFFFFFFFF) (P := fun i => decide (ws[3 + (i - 1)]! < 2))
    (step := fun s _ => s + 1) (fun i hi s => by
      try dsimp only
      rw [allOnes_testBit (by omega), toNat_add_ofNat 3 i (by simp; omega)]
      simp), members_allOnes _ (by omega)]
  have hlen : (countedOfWords ws n.toNat).length ≤ 63 :=
    (List.filter_sublist.length_le.trans (by simp)).trans hn
  rw [foldl_count ((List.range' 1 n.toNat).filter fun i => decide (ws[3 + (i - 1)]! < 2)) 0
    (by
      simp only [UInt64.toNat_zero]
      exact lt_of_le_of_lt (Nat.add_le_add_left hlen 0) (by norm_num))]
  simp only [UInt64.toNat_zero, Nat.zero_add]
  rfl

theorem countedKind_code (x : Nat) : countedKind (kindOfCode x) = decide (x < 2) := by
  match x with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | x + 3 => simp [kindOfCode, countedKind]

theorem filterMap_zip (g : Nat → Kind) : ∀ (m s : Nat),
    ((List.range' s m).zip ((List.range m).map fun c => g (s + c))).filterMap
        (fun p : Nat × Kind => if countedKind p.2 then some p.1 else none) =
      (List.range' s m).filter fun i => countedKind (g i)
  | 0, _ => rfl
  | m + 1, s => by
    rw [List.range'_succ, List.range_succ_eq_map, List.map_cons, List.zip_cons_cons,
      List.filterMap_cons, List.filter_cons, List.map_map]
    have hm : ((List.range m).map ((fun c => g (s + c)) ∘ Nat.succ)) =
        (List.range m).map fun c => g (s + 1 + c) := by
      apply List.map_congr_left
      intro c _
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [hm, filterMap_zip g m (s + 1)]
    simp only [Nat.add_zero]
    cases countedKind (g s) <;> simp

theorem countedSet_eq (ws : Array UInt64) (n : Nat) :
    countedSet (((wordsAt ws 3 n).map UInt64.toNat).map kindOfCode) = countedOfWords ws n := by
  unfold countedSet countedOfWords
  have hlen : (((wordsAt ws 3 n).map UInt64.toNat).map kindOfCode).length = n := by
    simp [wordsAt]
  have hk : ((wordsAt ws 3 n).map UInt64.toNat).map kindOfCode =
      (List.range n).map fun c => (fun i => kindOfCode (ws[3 + (i - 1)]!.toNat)) (1 + c) := by
    rw [wordsAt_map_toNat, List.map_map]
    apply List.map_congr_left
    intro c _
    simp
  rw [hlen, hk]
  refine (filterMap_zip (fun i => kindOfCode (ws[3 + (i - 1)]!).toNat) n 1).trans ?_
  apply List.filter_congr
  intro i _
  rw [countedKind_code]
  apply decide_eq_decide.mpr
  rw [UInt64.lt_iff_toNat_lt]
  rfl

theorem members_counted (ws : Array UInt64) (n : UInt64) (hn : n.toNat ≤ 63) :
    members (Program.countedOf ws n) n.toNat = countedOfWords ws n.toNat := by
  have hsub : (countedOfWords ws n.toNat).Sublist (List.range' 1 n.toNat) := List.filter_sublist
  unfold members
  rw [show countedOfWords ws n.toNat =
    (List.range' 1 n.toNat).filter (fun i => decide (ws[3 + (i - 1)]! < 2)) from rfl]
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range'_1.mp hi
  rw [countedOf_eq ws n hn, testBit_mask_sublist hsub, Nat.sub_add_cancel (by omega)]
  unfold countedOfWords
  simp [List.mem_filter, hi]

/-! ## The words of a round -/

theorem foldl_push (h : Nat → UInt64) : ∀ (L : List Nat) (a : Array UInt64),
    (L.foldl (fun o i => o.push (h i)) a).toList = a.toList ++ L.map h
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, foldl_push h L, Array.toList_push]
    simp

theorem pushRound_toList (out t : Array UInt64) (cont T n code elim tie : UInt64)
    (hn : n.toNat ≤ 63) :
    (Program.pushRound out t cont T n code elim tie).toList =
      out.toList ++ [cont, T] ++
        (List.range n.toNat).map (fun i => if cont.toNat.testBit i = true then t[i]! else 0) ++
        [t[64]!, t[65]!, t[66]!, t[67]!, code, elim, tie] := by
  unfold Program.pushRound
  rw [loop_eq_foldl, foldl_range_congr
    (g := fun o i => o.push (if cont.toNat.testBit i = true then t[i]! else 0)) (fun i hi s => by
      try dsimp only
      rw [bit_test cont (show i < 64 by omega), ofNat_toNat_lt (show i < 2 ^ 64 by omega)])]
  simp only [Array.toList_push, foldl_push]
  simp

/-- The words of a round's elimination, as `roundWords` gives them. -/
def elimTail : Option Elimination → List Nat
  | none => [0, 0, 0]
  | some (.lowest i) => [1, mask [i], 0]
  | some (.order tied i) => [2, mask [i], mask tied]
  | some (.batch members) => [3, mask members, 0]

theorem roundWords_eq (n : Nat) (tl : Tally) (el : Option Elimination) :
    roundWords n ⟨tl, el⟩ = [mask (tl.votes.map fun x : Nat × Nat => x.1), tl.continuing] ++
      (List.range' 1 n).map (fun i : Nat => (tl.votes.lookup i).getD 0) ++
      [tl.blank, tl.uncounted, tl.overvote, tl.exhausted] ++ elimTail el := by
  cases el with
  | none => rfl
  | some e => cases e <;> rfl

theorem lookup_map (C : List Nat) (v : Nat → Nat) (i : Nat) :
    (C.map fun j => (j, v j)).lookup i = if i ∈ C then some (v i) else none := by
  induction C with
  | nil => simp
  | cons x C ih =>
    simp only [List.map_cons, List.lookup, List.mem_cons]
    by_cases h : i = x
    · subst h
      simp
    · have hb : (i == x) = false := by simp [h]
      simp only [hb, ih, h, false_or]

theorem count_slot {os : List Outcome} (hv : ∀ o ∈ os, validOutcome o) {o : Outcome}
    (ho : validOutcome o) : os.countP (fun o' => decide (slot o' = slot o)) = os.count o := by
  rw [List.count_eq_countP]
  apply List.countP_congr
  intro o' ho'
  simp only [decide_eq_true_eq, beq_iff_eq]
  exact ⟨slot_inj (hv o' ho') ho, fun h => h ▸ rfl⟩

/-- `pushRound` appends the words of the round with the counts `tl` and the elimination `el`. -/
theorem pushRound_eq (out t : Array UInt64) (cont T n : UInt64) (hn : n.toNat ≤ 63)
    (hcont : cont.toNat < 2 ^ n.toNat) (tl : Tally) {v : Nat → Nat} (ht : Votes t v)
    (hvotes : tl.votes = (members cont n.toNat).map fun i => (i, v i))
    (hT : T.toNat = tl.continuing)
    (hb : t[64]!.toNat = tl.blank) (hu : t[65]!.toNat = tl.uncounted)
    (ho : t[66]!.toNat = tl.overvote) (hx : t[67]!.toNat = tl.exhausted)
    (el : Option Elimination) (code elim tie : UInt64)
    (hel : [code, elim, tie] = (elimTail el).map Nat.toUInt64) :
    (Program.pushRound out t cont T n code elim tie).toList =
      out.toList ++ (roundWords n.toNat ⟨tl, el⟩).map Nat.toUInt64 := by
  have e1 : Nat.toUInt64 (mask (tl.votes.map fun x : Nat × Nat => x.1)) = cont := by
    apply toUInt64_eq
    rw [hvotes, List.map_map]
    show cont.toNat = mask ((members cont n.toNat).map id)
    rw [List.map_id, mask_members hcont]
  have e3 : ((List.range' 1 n.toNat).map fun i => (tl.votes.lookup i).getD 0).map Nat.toUInt64 =
      (List.range n.toNat).map fun i => if cont.toNat.testBit i = true then t[i]! else 0 := by
    rw [List.range'_eq_map_range, List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply, hvotes, lookup_map]
    have hmem : (1 + i ∈ members cont n.toNat) ↔ cont.toNat.testBit i = true := by
      rw [mem_members, Nat.add_sub_cancel_left]
      constructor
      · rintro ⟨_, _, h⟩
        exact h
      · intro h
        exact ⟨by omega, by omega, h⟩
    have hget : t[i]!.toNat = v (1 + i) := by
      have := ht.get (1 + i) (by omega) (by omega)
      rwa [Nat.add_sub_cancel_left] at this
    by_cases hbit : cont.toNat.testBit i = true
    · rw [ite_eq_left (hmem.mpr hbit), ite_eq_left hbit, Option.getD_some]
      exact toUInt64_eq hget
    · have hnot : 1 + i ∉ members cont n.toNat := fun h => hbit (hmem.mp h)
      rw [ite_eq_right hnot, ite_eq_right hbit, Option.getD_none]
      rfl
  rw [pushRound_toList out t cont T n code elim tie hn, roundWords_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, e1, e3, ← hel, toUInt64_eq hT,
    toUInt64_eq hb, toUInt64_eq hu, toUInt64_eq ho, toUInt64_eq hx]
  simp

theorem endWords_tail_winner (w : Option Nat) :
    [(endWords (.winner w)).1, (endWords (.winner w)).2.1, (endWords (.winner w)).2.2.1] =
      (elimTail none).map Nat.toUInt64 := rfl

theorem endWords_tail_eliminate (el : Elimination) :
    [(endWords (.eliminate el)).1, (endWords (.eliminate el)).2.1,
        (endWords (.eliminate el)).2.2.1] = (elimTail (some el)).map Nat.toUInt64 := by
  cases el <;> rfl

theorem endWords_eliminate (el : Elimination) :
    (endWords (.eliminate el)).2.1 = UInt64.ofNat (mask el.eliminated) ∧
      (endWords (.eliminate el)).1 ≠ 0 := by
  cases el <;> exact ⟨rfl, by simp [endWords]⟩

theorem lower_map (C : List Nat) (v : Nat → Nat) (w : Nat) :
    lower (C.map fun i => (i, v i)) w =
      (C.filter fun j => decide (v j < w)).map fun i => (i, v i) := by
  simp only [lower, List.filter_map]
  rfl

/-- The candidates that a round eliminates are an increasing list of continuing candidates. -/
theorem eliminated_sublist {order C : List Nat} {v : Nat → Nat} {tl : Tally}
    (hvotes : tl.votes = C.map fun i => (i, v i)) {el : Elimination}
    (h : rule order tl = .eliminate el) : el.eliminated.Sublist C := by
  have hmem := (Demos.Rcv.Rounds.rule_eliminated h).2
  have hfst : tl.votes.map (fun x : Nat × Nat => x.1) = C := by
    rw [hvotes, List.map_map]
    exact List.map_id C
  rw [hfst] at hmem
  obtain ⟨-, -, hcases⟩ := Demos.Rcv.Rounds.rule_eq_eliminate h
  rcases hcases with ⟨s, hs, rfl⟩ | ⟨-, ⟨z, -, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨-, ⟨x, -, -, rfl⟩, -⟩ := Demos.Rcv.Rounds.batch_some hs
    show ((lower tl.votes x.2).map fun y : Nat × Nat => y.1).Sublist C
    rw [hvotes, lower_map, List.map_map]
    show ((C.filter fun j => decide (v j < x.2)).map id).Sublist C
    rw [List.map_id]
    exact List.filter_sublist
  · exact List.singleton_sublist.mpr (hmem z (List.mem_singleton_self z))
  · exact List.singleton_sublist.mpr (hmem _ (List.mem_singleton_self _))

theorem members_remove (cont x : UInt64) (n : Nat) (L : List Nat)
    (hL : L.Sublist (List.range' 1 n)) (hn : n ≤ 63) (hx : x.toNat = mask L) :
    members (cont &&& (x ^^^ 0xFFFFFFFFFFFFFFFF)) n =
      (members cont n).filter fun i => decide (i ∉ L) := by
  unfold members
  rw [List.filter_filter]
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range'_1.mp hi
  rw [UInt64.toNat_and, UInt64.toNat_xor, Nat.testBit_and, Nat.testBit_xor,
    allOnes_testBit (by omega), hx, testBit_mask_sublist hL, Nat.sub_add_cancel (by omega)]
  cases cont.toNat.testBit (i - 1) <;> by_cases h : i ∈ L <;> simp [h]

/-! ## The rounds -/

/-- The ballots of a contest array with `n` candidates, `k` positions, and `N` ballots. -/
def ballotsOf (ws : Array UInt64) (n k N : Nat) : List (List UInt64) :=
  (List.range N).map fun b => ballotAt ws (3 + 2 * n) k b

/-- The loop of the rounds in `countValid`. -/
def roundsGo (ws : Array UInt64) (n k N counted : UInt64) (f : Nat)
    (s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 :=
  LeanExe.repeatWhile.go
    (fun s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => s.2.1 == 0)
    (fun s => Program.roundStep ws n k N counted s) f s

theorem roundsGo_stop (ws : Array UInt64) (n k N counted : UInt64)
    (s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) (h : (s.2.1 == 0) = false) :
    ∀ f, roundsGo ws n k N counted f s = s
  | 0 => rfl
  | f + 1 => by
    unfold roundsGo
    rw [LeanExe.repeatWhile.go, ite_eq_right (by simp [h])]

theorem go_eq (ws : Array UInt64) (n k N counted : UInt64) (kinds : List Kind) (order : List Nat)
    (hn : n.toNat ≤ 63) (hk : k.toNat ≤ 63) (hN : N.toNat < 2 ^ 32)
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    (horder : order = (List.range n.toNat).map fun j => (ws[3 + n.toNat + j]!).toNat)
    (hperm : order.Perm (List.range' 1 n.toNat)) :
    ∀ (f : Nat) (cont r : UInt64) (out : Array UInt64), cont.toNat < 2 ^ n.toNat →
      r.toNat + f < 2 ^ 64 →
      (roundsGo ws n k N counted f (cont, 0, 0, r, out)).2.2.1 =
          UInt64.ofNat ((run (interpret kinds) (rule order) (ballotsOf ws n.toNat k.toNat N.toNat) f
            (members cont n.toNat)).winner.getD 0) ∧
        (roundsGo ws n k N counted f (cont, 0, 0, r, out)).2.2.2.1.toNat =
          r.toNat + (run (interpret kinds) (rule order) (ballotsOf ws n.toNat k.toNat N.toNat) f
            (members cont n.toNat)).rounds.length ∧
        (roundsGo ws n k N counted f (cont, 0, 0, r, out)).2.2.2.2.toList =
          out.toList ++
            ((run (interpret kinds) (rule order) (ballotsOf ws n.toNat k.toNat N.toNat) f
            (members cont n.toNat)).rounds.flatMap (roundWords n.toNat)).map Nat.toUInt64 := by
  intro f
  induction f with
  | zero =>
    intro cont r out _ _
    simp [roundsGo, LeanExe.repeatWhile.go, run]
  | succ f ih =>
    intro cont r out hc hr
    have hgo : roundsGo ws n k N counted (f + 1) (cont, 0, 0, r, out) =
        roundsGo ws n k N counted f (Program.roundStep ws n k N counted (cont, 0, 0, r, out)) := by
      unfold roundsGo
      rw [LeanExe.repeatWhile.go, ite_eq_left (by simp)]
    rw [hgo]
    simp only [Program.roundStep]
    have hCbit : ∀ i, 1 ≤ i → i ≤ 63 →
        (i ∈ members cont n.toNat ↔ cont.toNat.testBit (i - 1) = true) := by
      intro i h1 h2
      rw [mem_members]
      constructor
      · rintro ⟨_, _, h⟩
        exact h
      · intro h
        refine ⟨h1, ?_, h⟩
        by_contra hgt
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
          (by omega)))] at h
        cases h
    have h3 : (3 + 2 * n).toNat = 3 + 2 * n.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, Nat.reducePow]
      omega
    have hfit : (3 + 2 * n).toNat + N.toNat * k.toNat < 2 ^ 64 := by
      have : N.toNat * k.toNat ≤ 4294967295 * 63 := Nat.mul_le_mul (by omega) hk
      rw [h3]
      norm_num
      omega
    obtain ⟨hsize, hcnt⟩ := tallyRound_eq ws cont counted k N (3 + 2 * n) kinds
      (members cont n.toNat) hCbit hK hfit
    rw [h3] at hcnt
    generalize htl : Program.tallyRound ws cont counted k N (3 + 2 * n) = t at hsize hcnt ⊢
    have hvalid : ∀ o ∈ (ballotsOf ws n.toNat k.toNat N.toNat).map
        (interpret kinds (members cont n.toNat)), validOutcome o := by
      intro o ho
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ho
      exact interpret_valid _ _ _
    have ht : Votes t fun i => ((ballotsOf ws n.toNat k.toNat N.toNat).map
        (interpret kinds (members cont n.toNat))).count (.counts i) := by
      constructor
      · intro i h1 h2
        rw [hcnt (i - 1) (by omega)]
        exact count_slot hvalid (o := .counts i) ⟨h1, h2⟩
      · intro i
        have := List.count_le_length (a := Outcome.counts i)
          (l := (ballotsOf ws n.toNat k.toNat N.toNat).map (interpret kinds (members cont n.toNat)))
        simp only [ballotsOf, List.length_map, List.length_range] at this ⊢
        omega
    set tl := tally (interpret kinds) (members cont n.toNat) (ballotsOf ws n.toNat k.toNat N.toNat)
      with htldef
    have hvotes : tl.votes = (members cont n.toNat).map fun i => (i,
        ((ballotsOf ws n.toNat k.toNat N.toNat).map
          (interpret kinds (members cont n.toNat))).count (.counts i)) := rfl
    have hT := continuingOf_eq ht cont n hn
    have hT' : (Program.continuingOf t cont n).toNat = tl.continuing := by
      rw [hT]
      simp only [Tally.continuing, hvotes, List.map_map]
      rfl
    rw [decideRound_eq ws t ht cont _ n hn tl hvotes hT order horder hperm]
    have hslot : ∀ (o : Outcome), validOutcome o → t[slot o]!.toNat =
        ((ballotsOf ws n.toNat k.toNat N.toNat).map
          (interpret kinds (members cont n.toNat))).count o := fun o ho => by
      rw [hcnt (slot o) (slot_lt ho)]
      exact count_slot hvalid ho
    have hpush := fun (el : Option Elimination) (code elim tie : UInt64)
        (hel : [code, elim, tie] = (elimTail el).map Nat.toUInt64) =>
      pushRound_eq out t cont (Program.continuingOf t cont n) n hn hc tl ht hvotes hT'
        (hslot (.inactive .blank) trivial) (hslot (.inactive .uncounted) trivial)
        (hslot (.inactive .overvote) trivial) (hslot (.inactive .exhausted) trivial) el code elim
        tie hel
    have hrun : run (interpret kinds) (rule order) (ballotsOf ws n.toNat k.toNat N.toNat) (f + 1)
        (members cont n.toNat) =
        match rule order tl with
        | .winner w => ⟨[⟨tl, none⟩], w⟩
        | .eliminate e =>
          let rest : Count := run (interpret kinds) (rule order)
            (ballotsOf ws n.toNat k.toNat N.toNat) f
            ((members cont n.toNat).filter fun i : Nat => decide (i ∉ e.eliminated))
          ⟨⟨tl, some e⟩ :: rest.rounds, rest.winner⟩ := rfl
    rw [hrun]
    cases hrule : rule order tl with
    | winner w =>
      rw [show endWords (.winner w) = (0, 0, 0, UInt64.ofNat (w.getD 0)) from rfl]
      simp only [beq_self_eq_true, ↓reduceIte]
      have hstop := roundsGo_stop ws n k N counted
        (cont, 1, UInt64.ofNat (w.getD 0), r + 1,
          Program.pushRound out t cont (Program.continuingOf t cont n) n 0 0 0) (by simp) f
      rw [hstop]
      refine ⟨rfl, ?_, ?_⟩
      · simp only [List.length_singleton]
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      · show (Program.pushRound out t cont (Program.continuingOf t cont n) n 0 0 0).toList = _
        rw [hpush none 0 0 0 rfl]
        simp
    | eliminate el =>
      obtain ⟨hel, hcode⟩ := endWords_eliminate el
      have hcode' : ((endWords (.eliminate el)).1 == 0) = false := by simpa using hcode
      simp only [hcode', Bool.false_eq_true, ↓reduceIte]
      have hsub := eliminated_sublist hvotes hrule
      have hsubr : el.eliminated.Sublist (List.range' 1 n.toNat) :=
        hsub.trans (members_sublist cont n.toNat)
      have hmr := members_remove cont (endWords (.eliminate el)).2.1 n.toNat el.eliminated hsubr hn
        (by rw [hel, ofNat_toNat_lt (lt_of_lt_of_le (mask_lt hsubr)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))])
      have hc' : (cont &&& ((endWords (.eliminate el)).2.1 ^^^ 0xFFFFFFFFFFFFFFFF)).toNat <
          2 ^ n.toNat := by
        rw [UInt64.toNat_and]
        exact lt_of_le_of_lt Nat.and_le_left hc
      have hr1 : (r + 1).toNat = r.toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨i1, i2, i3⟩ := ih _ (r + 1)
        (Program.pushRound out t cont (Program.continuingOf t cont n) n (endWords (.eliminate el)).1
          (endWords (.eliminate el)).2.1 (endWords (.eliminate el)).2.2.1) hc' (by omega)
      rw [hmr] at i1 i2 i3
      refine ⟨i1, ?_, ?_⟩
      · rw [i2, hr1]
        simp only [List.length_cons]
        omega
      · rw [i3, hpush (some el) _ _ _ (endWords_tail_eliminate el)]
        simp

/-! ## The count -/

/-- The result words of `countValid` on a valid contest array are those of the specification's
count. -/
theorem countValid_eq (ws : Array UInt64) (hs : ws.size < 2 ^ 64)
    (hv : (readWords ws.toList).Valid ws.toList.length) :
    Program.countValid ws =
      (resultWords (readWords ws.toList).n (count ((readWords ws.toList).kinds.map kindOfCode)
        (readWords ws.toList).order (readWords ws.toList).ballots)).toArray := by
  have hcv : Program.countValid ws =
      let s := roundsGo ws ws[0]! ws[1]! ws[2]! (Program.countedOf ws ws[0]!)
        (Program.countedSize ws ws[0]! + 1).toNat (Program.countedOf ws ws[0]!, 0, 0, 0, #[1, 0])
      (s.2.2.2.2.set! 1 s.2.2.2.1).push s.2.2.1 := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, -, hperm, -⟩ := hv
  rw [readWords_n, readWords_k, readWords_N] at *
  simp only [maxIndex, maxBallots, Array.length_toList] at h2 h4 h5 h6
  have hkinds : (readWords ws.toList).kinds = (wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat := by
    simp only [readWords, getD_toList]
    rw [take_drop_eq_wordsAt ws 3 _ (by omega)]
  have horder : (readWords ws.toList).order =
      (List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat := by
    simp only [readWords, getD_toList]
    rw [take_drop_eq_wordsAt ws _ _ (by omega), wordsAt_map_toNat]
  have hballots : (readWords ws.toList).ballots =
      ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat := by
    simp only [Words.ballots, readWords, getD_toList]
    exact chunks_eq ws _ _ _ (by omega)
  have hn : ws[0]!.toNat ≤ 63 := h2
  have hK := countedSet_eq ws ws[0]!.toNat
  have hcount := countedOf_eq ws ws[0]! hn
  have hsize := countedSize_eq ws ws[0]! hn
  have hmem := members_counted ws ws[0]! hn
  have hsub : (countedOfWords ws ws[0]!.toNat).Sublist (List.range' 1 ws[0]!.toNat) :=
    List.filter_sublist
  have hKlen : (countedOfWords ws ws[0]!.toNat).length ≤ 63 :=
    (hsub.length_le.trans (by simp)).trans hn
  have hfuel : (Program.countedSize ws ws[0]! + 1).toNat =
      (countedOfWords ws ws[0]!.toNat).length + 1 := by
    rw [UInt64.toNat_add, hsize, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  have hcK : (Program.countedOf ws ws[0]!).toNat < 2 ^ ws[0]!.toNat := by
    rw [hcount]
    exact mask_lt hsub
  have hKbit : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet (((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode) ↔
        (Program.countedOf ws ws[0]!).toNat.testBit (i - 1) = true) := by
    intro i hi1 _
    rw [hK, hcount, testBit_mask_sublist hsub, Nat.sub_add_cancel hi1]
    simp
  have hperm' : ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat).Perm
      (List.range' 1 ws[0]!.toNat) := by
    rw [← horder]
    exact hperm
  obtain ⟨g1, g2, g3⟩ := go_eq ws ws[0]! ws[1]! ws[2]! (Program.countedOf ws ws[0]!)
    (((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode)
    ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat) hn h4
    (by norm_num at h5; omega) hKbit rfl hperm' ((countedOfWords ws ws[0]!.toNat).length + 1)
    (Program.countedOf ws ws[0]!) 0 #[1, 0] hcK (by simp; omega)
  rw [hmem] at g1 g2 g3
  have hc : count (((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode)
      ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat)
      (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat) =
      run (interpret (((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode))
        (rule ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat))
        (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat)
        ((countedOfWords ws ws[0]!.toNat).length + 1) (countedOfWords ws ws[0]!.toNat) := by
    unfold count
    rw [hK]
  rw [hcv, hkinds, horder, hballots, hc, hfuel]
  apply Array.toList_inj.mp
  simp only [Array.toList_push, Array.toList_set!]
  rw [g3]
  generalize run (interpret (((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode))
    (rule ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat))
    (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat)
    ((countedOfWords ws ws[0]!.toNat).length + 1) (countedOfWords ws ws[0]!.toNat) = c at g1 g2 ⊢
  rw [UInt64.toNat_zero, Nat.zero_add] at g2
  rw [g1, ← toUInt64_eq g2]
  simp [resultWords]

/-- The program equals the specification's export over words on every array of fewer than
`2 ^ 64` words, which every array in memory is. -/
theorem count_eq (ws : Array UInt64) (hs : ws.size < 2 ^ 64) :
    Program.count ws = countArray ws := by
  unfold Program.count countArray countWords
  by_cases hv : Program.validArray ws = true
  · rw [ite_eq_left hv, ite_eq_left ((validArray_iff ws hs).mp hv)]
    exact countValid_eq ws hs ((validArray_iff ws hs).mp hv)
  · have hnv : ¬ (readWords ws.toList).Valid ws.toList.length := fun h =>
      hv ((validArray_iff ws hs).mpr h)
    rw [ite_eq_right hv, ite_eq_right hnv]

/-! ## The size of the result -/

theorem run_rounds_le (interp : List Nat → List UInt64 → Outcome)
    (decision : Tally → Decision)
    (ballots : List (List UInt64)) :
    ∀ (f : Nat) (C : List Nat), (run interp decision ballots f C).rounds.length ≤ f
  | 0, _ => Nat.le_refl 0
  | f + 1, C => by
    simp only [run]
    split
    · simp
    · next e _ =>
      simp only [List.length_cons]
      have := run_rounds_le interp decision ballots f
        (C.filter fun i : Nat => decide (i ∉ e.eliminated))
      omega

theorem roundWords_length (n : Nat) (rd : Round) : (roundWords n rd).length = n + 9 := by
  rcases rd with ⟨tl, el⟩
  rw [roundWords_eq]
  cases el with
  | none => simp [elimTail]
  | some e => cases e <;> simp [elimTail]

theorem flatMap_length_const {α β : Type} {f : α → List β} {c : Nat}
    (hf : ∀ x, (f x).length = c) :
    ∀ l : List α, (l.flatMap f).length = l.length * c
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, hf, flatMap_length_const hf l, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- On a valid contest array, the result words of the rounds before the winner number at most
4,610. -/
theorem rounds_size (ws : Array UInt64) (hs : ws.size < 2 ^ 64)
    (hv : Program.validArray ws = true) :
    (roundsGo ws ws[0]! ws[1]! ws[2]! (Program.countedOf ws ws[0]!)
      (Program.countedSize ws ws[0]! + 1).toNat
      (Program.countedOf ws ws[0]!, 0, 0, 0, #[1, 0])).2.2.2.2.size ≤ 4610 := by
  have hval := (validArray_iff ws hs).mp hv
  have heq := countValid_eq ws hs hval
  have hcv : Program.countValid ws =
      let s := roundsGo ws ws[0]! ws[1]! ws[2]! (Program.countedOf ws ws[0]!)
        (Program.countedSize ws ws[0]! + 1).toNat (Program.countedOf ws ws[0]!, 0, 0, 0, #[1, 0])
      (s.2.2.2.2.set! 1 s.2.2.2.1).push s.2.2.1 := rfl
  have hsz := congrArg Array.size heq
  rw [hcv] at hsz
  simp only [Array.size_push, Array.size_set!, List.size_toArray, resultWords, List.length_map,
    List.length_append, List.length_cons, List.length_nil] at hsz
  rw [flatMap_length_const (roundWords_length _)] at hsz
  obtain ⟨-, h2, -⟩ := hval
  rw [readWords_n] at h2 hsz
  simp only [maxIndex] at h2
  have hR : (count ((readWords ws.toList).kinds.map kindOfCode) (readWords ws.toList).order
      (readWords ws.toList).ballots).rounds.length ≤ 64 := by
    unfold count
    refine (run_rounds_le _ _ _ _ _).trans ?_
    have hK := (Demos.Rcv.Rounds.countedSet_sublist
      ((readWords ws.toList).kinds.map kindOfCode)).length_le
    have hlen : ((readWords ws.toList).kinds.map kindOfCode).length ≤ 63 := by
      simp only [List.length_map, readWords, List.length_take]
      rw [getD_toList]
      omega
    simp only [List.length_range'] at hK
    omega
  have hm := Nat.mul_le_mul hR (show ws[0]!.toNat + 9 ≤ 72 by omega)
  omega

end Demos.Rcv.Refine
