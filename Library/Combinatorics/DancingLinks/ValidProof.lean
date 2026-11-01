import Library.Combinatorics.DancingLinks.BuildLoop

/-! The proof that `valid` decides `Valid`.  After a prefix of the words, the loop's state holds
the number of the current option, which each zero increases, a flag, and the marks.  The invariant
relates them to the reader of `Read.lean`: every mark is at most the current number, an item's
mark equals the current number exactly when the item is in the current run, and the flag is 1
exactly when the finished options and the run hold no repeated item and no item above `N`.  A
nonzero word that is above `N` or already marked in its run clears the flag, and the reader's
options at the end are the specification's. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- The options read so far have no repeated item and no item above `N`. -/
def RunsOk (N : Nat) (st : List (List Nat) × List Nat) : Prop :=
  (∀ o ∈ st.1, o.Nodup ∧ ∀ j ∈ o, j ≤ N) ∧ st.2.Nodup ∧ ∀ j ∈ st.2, j ≤ N

instance (N : Nat) (st : List (List Nat) × List Nat) : Decidable (RunsOk N st) := by
  unfold RunsOk; infer_instance

/-- The loop of `valid`, as the program states it. -/
def validStep (x : Array UInt64) (n : UInt64) (k : UInt64) (s : UInt64 × UInt64 × Array UInt64) :
    UInt64 × UInt64 × Array UInt64 :=
  if k = 0 then s
  else if x[k.toNat]! = 0 then (s.1 + 1, s.2.1, s.2.2)
  else (s.1, if n < x[k.toNat]! ∨ s.2.2[(x[k.toNat]!).toNat]! = s.1 then 0 else s.2.1,
    s.2.2.set! (x[k.toNat]!).toNat s.1)

/-- The state of `valid`'s loop after the words before position `k`. -/
def ValidInv (x : Array UInt64) (N k : Nat) (s : UInt64 × UInt64 × Array UInt64) : Prop :=
  let st := ((words x).take (k - 1)).foldl readStep ([], [])
  1 ≤ s.1.toNat ∧ s.1.toNat ≤ k + 1 ∧ s.2.2.size = N + 1 ∧
    (∀ w ≤ N, (s.2.2[w]!).toNat ≤ s.1.toNat) ∧
    (∀ w ≤ N, (s.2.2[w]!).toNat = s.1.toNat ↔ w ∈ st.2) ∧
    s.2.1 = (if RunsOk N st then 1 else 0)

theorem runsOk_step_zero (N : Nat) (st : List (List Nat) × List Nat) :
    RunsOk N (readStep st 0) ↔ RunsOk N st := by
  unfold readStep RunsOk
  rw [ite_eq_left rfl]
  split
  · rfl
  · rename_i hc
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨h1, -, -⟩
      exact ⟨fun o ho => h1 o (Or.inl ho), (h1 _ (Or.inr rfl)).1, (h1 _ (Or.inr rfl)).2⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun o ho => ?_, List.nodup_nil, fun j hj => absurd hj (List.not_mem_nil)⟩
      rcases ho with ho | rfl
      · exact h1 o ho
      · exact ⟨h2, h3⟩

theorem nodup_concat_iff (l : List Nat) (w : Nat) : (l ++ [w]).Nodup ↔ l.Nodup ∧ w ∉ l := by
  rw [List.nodup_append]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, fun hm => h3 w hm w (List.mem_singleton_self w) rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, List.nodup_singleton w, fun a ha b hb e => ?_⟩
    rw [List.mem_singleton] at hb
    exact h2 (hb ▸ e ▸ ha)

theorem runsOk_step_word (N : Nat) (st : List (List Nat) × List Nat) {w : Nat} (hw : w ≠ 0) :
    RunsOk N (readStep st w) ↔ RunsOk N st ∧ w ∉ st.2 ∧ w ≤ N := by
  have hst : readStep st w = (st.1, st.2 ++ [w]) := by unfold readStep; rw [ite_eq_right hw]
  rw [hst]
  unfold RunsOk
  dsimp only
  rw [nodup_concat_iff]
  constructor
  · rintro ⟨h1, ⟨h2, h4⟩, h5⟩
    exact ⟨⟨h1, h2, fun j hj => h5 j (List.mem_append_left _ hj)⟩, h4,
      h5 w (List.mem_append_right _ (List.mem_singleton_self w))⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    refine ⟨h1, ⟨h2, h4⟩, fun j hj => ?_⟩
    rcases List.mem_append.mp hj with hj | hj
    · exact h3 j hj
    · rw [List.mem_singleton] at hj; rw [hj]; exact h5

theorem validStep_inv (x : Array UInt64) (hx : x.size < 2 ^ 50) {n : UInt64} {k : Nat}
    (hn : n.toNat = itemCount x) (hk : k < x.size) {s : UInt64 × UInt64 × Array UInt64}
    (h : ValidInv x (itemCount x) k s) :
    ValidInv x (itemCount x) (k + 1) (validStep x n (UInt64.ofNat k) s) := by
  obtain ⟨hs0, hs1, hsz, hle, hmark, hok⟩ := h
  have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hC : UInt64.ofNat 0 = 0 := rfl
    rw [validStep, ite_eq_left hC]
    exact ⟨hs0, by omega, hsz, hle, hmark, hok⟩
  have hk0' : UInt64.ofNat k ≠ 0 := fun e => by rw [e] at hk64; simp at hk64; omega
  have hwk := words_get x (k := k) (by omega) hk
  have htake : (words x).take (k + 1 - 1) =
      (words x).take (k - 1) ++ [(words x)[k - 1]'(by rw [words_length]; omega)] := by
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (by rw [words_length]; omega), Option.toList_some]
  generalize hst : ((words x).take (k - 1)).foldl readStep ([], []) = st at hmark hok
  have hst' : ((words x).take (k + 1 - 1)).foldl readStep ([], []) =
      readStep st (x[k]!).toNat := by
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hwk, hst]
  have hxk : x[(UInt64.ofNat k).toNat]! = x[k]! := by rw [hk64]
  unfold ValidInv
  rw [hst']
  rw [validStep, ite_eq_right hk0', hxk]
  by_cases hw0 : x[k]! = 0
  · have hwN : (x[k]!).toNat = 0 := by rw [hw0]; rfl
    rw [ite_eq_left hw0, hwN]
    dsimp only
    have hs1' : (s.1 + 1).toNat = s.1.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]; omega
    refine ⟨by rw [hs1']; omega, by rw [hs1']; omega, hsz, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · rw [hs1']; have := hle w hw; omega
    · rw [hs1']
      have hst0 : (readStep st 0).2 = [] := by
        unfold readStep; rw [ite_eq_left rfl]; split <;> simp_all
      rw [hst0]
      have := hle w hw
      simp only [List.not_mem_nil, iff_false]
      omega
    · rw [hok]
      by_cases hr : RunsOk (itemCount x) st
      · rw [ite_eq_left hr, ite_eq_left ((runsOk_step_zero _ st).mpr hr)]
      · rw [ite_eq_right hr, ite_eq_right (fun h' => hr ((runsOk_step_zero _ st).mp h'))]
  · have hwN : (x[k]!).toNat ≠ 0 := fun e => hw0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rw [ite_eq_right hw0]
    dsimp only
    set wN := (x[k]!).toNat with hwNd
    have hst2 : (readStep st wN).2 = st.2 ++ [wN] := by unfold readStep; rw [ite_eq_right hwN]
    have hsz' : (s.2.2.set! wN s.1).size = itemCount x + 1 := by simp [hsz]
    refine ⟨hs0, by omega, hsz', fun w hw => ?_, fun w hw => ?_, ?_⟩
    · by_cases hww : w = wN
      · subst hww
        rw [get_set _ _ _ _ (by omega), ite_eq_left rfl]
      · by_cases hin : wN < s.2.2.size
        · rw [get_set _ _ _ _ hin, ite_eq_right hww]; exact hle w hw
        · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dite_eq_right hin]
          exact hle w hw
    · rw [hst2, List.mem_append, List.mem_singleton]
      by_cases hww : w = wN
      · subst hww
        rw [get_set _ _ _ _ (by omega), ite_eq_left rfl]
        simp
      · have hset : (s.2.2.set! wN s.1)[w]! = s.2.2[w]! := by
          by_cases hin : wN < s.2.2.size
          · rw [get_set _ _ _ _ hin, ite_eq_right hww]
          · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dite_eq_right hin]
        rw [hset, hmark w hw]
        simp [hww]
    · have hiff := runsOk_step_word (itemCount x) st hwN
      by_cases hbig : itemCount x < wN
      · have hc : n < x[k]! ∨ s.2.2[wN]! = s.1 := Or.inl (by
          rw [UInt64.lt_iff_toNat_lt, hn]; exact hbig)
        rw [ite_eq_left hc, ite_eq_right (fun h' => by have := (hiff.mp h').2.2; omega)]
      · push Not at hbig
        have hseen : s.2.2[wN]! = s.1 ↔ wN ∈ st.2 := by
          rw [← hmark wN hbig, UInt64.toNat_inj]
        have hlt : ¬ n < x[k]! := by rw [UInt64.lt_iff_toNat_lt, hn]; omega
        by_cases hm : wN ∈ st.2
        · rw [ite_eq_left (Or.inr (hseen.mpr hm)), ite_eq_right (fun h' => (hiff.mp h').2.1 hm)]
        · have hc : ¬ (n < x[k]! ∨ s.2.2[wN]! = s.1) := by
            rintro (h' | h')
            · exact hlt h'
            · exact hm (hseen.mp h')
          rw [ite_eq_right hc, hok]
          by_cases hr : RunsOk (itemCount x) st
          · rw [ite_eq_left hr, ite_eq_left (hiff.mpr ⟨hr, hm, hbig⟩)]
          · rw [ite_eq_right hr, ite_eq_right (fun h' => hr (hiff.mp h').1)]

/-- `valid` decides `Valid`. -/
theorem valid_eq (x : Array UInt64) (hx : x.size < 2 ^ 50) : valid x = validSpec x := by
  have hn : (x[(0 : UInt64).toNat]!).toNat = itemCount x := first_word x
  have hsz : x.size.toUInt64.toNat = x.size := size_toUInt64 x (by omega)
  unfold valid validSpec
  dsimp only
  by_cases hbig : itemLimit < x[(0 : UInt64).toNat]!
  · rw [ite_eq_left hbig]
    have : ¬ Valid x := by
      intro hv
      have := hv.1
      rw [UInt64.lt_iff_toNat_lt, hn] at hbig
      simp [itemLimit] at hbig
      omega
    rw [ite_eq_right this]
  · rw [ite_eq_right hbig]
    have hN : itemCount x ≤ 998 := by
      rw [UInt64.lt_iff_toNat_lt, hn] at hbig
      simp [itemLimit] at hbig
      omega
    have hbs : (LeanExe.build (x[(0 : UInt64).toNat]! + 1) fun _ => (0 : UInt64)).size =
        itemCount x + 1 := by
      rw [build_size, UInt64.toNat_add, hn]; simp; omega
    have h0 : ValidInv x (itemCount x) 0 ((1 : UInt64), (1 : UInt64),
        LeanExe.build (x[(0 : UInt64).toNat]! + 1) fun _ => (0 : UInt64)) := by
      refine ⟨by simp, by simp, hbs, fun w hw => ?_, fun w hw => ?_, ?_⟩
      · rw [build_get (by rw [UInt64.toNat_add, hn]; simp; omega)]; simp
      · rw [build_get (by rw [UInt64.toNat_add, hn]; simp; omega)]
        simp [readStep]
      · simp [RunsOk]
    have hloop := loop_induction (n := x.size.toUInt64)
      (init := ((1 : UInt64), (1 : UInt64),
        LeanExe.build (x[(0 : UInt64).toNat]! + 1) fun _ => (0 : UInt64)))
      (f := validStep x x[(0 : UInt64).toNat]!) (fun k s => ValidInv x (itemCount x) k s) h0
      (fun k s hk h => validStep_inv x hx hn (by rw [hsz] at hk; exact hk) h)
    rw [hsz] at hloop
    show (LeanExe.loop x.size.toUInt64 _ (validStep x x[(0 : UInt64).toNat]!)).2.1 = _
    obtain ⟨-, -, -, -, -, hok⟩ := hloop
    rw [hok]
    have hall : (words x).take (x.size - 1) = words x := by
      rw [← words_length, List.take_length]
    rw [hall]
    have hfin : finish ((words x).foldl readStep ([], [])) = options x := by
      rw [finish_read (words x) [] [] (by simp), List.nil_append, List.nil_append]
      rfl
    have hiff : RunsOk (itemCount x) ((words x).foldl readStep ([], [])) ↔ Valid x := by
      unfold Valid
      rw [← hfin]
      generalize (words x).foldl readStep ([], []) = st
      unfold RunsOk finish
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨hN, fun o ho => ?_⟩
        rcases List.mem_append.mp ho with ho | ho
        · exact h1 o ho
        · split at ho
          · simp at ho
          · rw [List.mem_singleton] at ho; subst ho; exact ⟨h2, h3⟩
      · rintro ⟨-, h⟩
        refine ⟨fun o ho => h o (List.mem_append_left _ ho), ?_, ?_⟩
        · by_cases hc : st.2 = []
          · rw [hc]; exact List.nodup_nil
          · exact (h st.2 (List.mem_append_right _ (by rw [ite_eq_right hc]; simp))).1
        · by_cases hc : st.2 = []
          · rw [hc]; simp
          · exact (h st.2 (List.mem_append_right _ (by rw [ite_eq_right hc]; simp))).2
    by_cases hv : Valid x
    · rw [ite_eq_left (hiff.mpr hv), ite_eq_left hv]
    · rw [ite_eq_right (fun h => hv (hiff.mp h)), ite_eq_right hv]

end Library.Combinatorics.DancingLinks
