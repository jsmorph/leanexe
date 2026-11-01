import Library.Combinatorics.DancingLinks.Partial

/-! Step X1 as the program performs it.  `partial_init` shows that the array that `LeanExe.build`
makes holds `Partial` before any option: every header's list is empty, the items are linked in
order, and every node's words are 0.  The loop reads the words after the first one, and its state
holds the last spacer, the next node, the first node of the option being read, or 0, and the
array.  `build_loop` shows that after each prefix of the words the state matches the reader's
state of `Read.lean`: a nonzero word adds a node by `partial_append`, and a zero after a run
finishes the option by `partial_close`.  `build_inv` concludes that `build` leaves the invariant of
the search for all items. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

theorem nxt_Icc {N y : Nat} (hy : y ≤ N) : nxt 0 (Icc 1 N) y = if y < N then y + 1 else 0 := by
  unfold nxt
  split
  · rename_i h
    obtain ⟨z, hz⟩ := h
    obtain ⟨hzI, hyz⟩ := mem_filter.mp hz
    have hyN : y < N := by have := (mem_Icc.mp hzI).2; omega
    rw [ite_eq_left hyN]
    apply le_antisymm
    · exact min'_le _ (y + 1) (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩)
    · apply le_min'
      intro w hw
      exact (mem_filter.mp hw).2
  · rename_i h
    rw [ite_eq_right fun hyN => h ⟨y + 1, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩⟩]

theorem prv_Icc {N y : Nat} (hy : y ≤ N) : prv 0 (Icc 1 N) y = if y = 0 then N else y - 1 := by
  unfold prv
  by_cases hy0 : y = 0
  · rw [ite_eq_left hy0, ite_eq_left hy0]
    by_cases hN : (Icc 1 N).Nonempty
    · rw [dite_eq_left hN]
      apply le_antisymm
      · exact max'_le _ _ _ fun z hz => (mem_Icc.mp hz).2
      · exact le_max' _ N (mem_Icc.mpr ⟨by obtain ⟨z, hz⟩ := hN; have := mem_Icc.mp hz; omega,
          le_rfl⟩)
    · rw [dite_eq_right hN]
      by_contra hne
      exact hN ⟨N, mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
  · rw [ite_eq_right hy0, ite_eq_right hy0]
    by_cases h : ((Icc 1 N).filter (· < y)).Nonempty
    · rw [dite_eq_left h]
      apply le_antisymm
      · exact max'_le _ _ _ fun z hz => by have := (mem_filter.mp hz).2; omega
      · obtain ⟨z, hz⟩ := h
        have := mem_Icc.mp (mem_filter.mp hz).1
        have hzy := (mem_filter.mp hz).2
        exact le_max' _ (y - 1) (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩)
    · rw [dite_eq_right h]
      by_contra hne
      exact h ⟨y - 1, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩⟩

/-- A nonempty run without zeros begins the first run of any words that follow it. -/
theorem runs_head (a b : List Nat) (ha : a ≠ []) (h0 : 0 ∉ a) :
    ∃ c tl, runs (a ++ b) = (a ++ c) :: tl := by
  by_cases hb : 0 ∈ b
  · obtain ⟨c, d, rfl, hc⟩ : ∃ c d, b = c ++ 0 :: d ∧ 0 ∉ c := by
      induction b with
      | nil => simp at hb
      | cons z b ih =>
        by_cases hz : z = 0
        · exact ⟨[], b, by rw [hz]; rfl, by simp⟩
        · obtain ⟨c, d, hcd, hc⟩ := ih (by simpa [Ne.symm hz] using hb)
          exact ⟨z :: c, d, by rw [hcd]; rfl, by simp [Ne.symm hz, hc]⟩
    refine ⟨c, runs d, ?_⟩
    unfold runs
    rw [← List.append_assoc, runs_nozero_append (a ++ c) d (by simp [h0, hc])]
    simp [ha]
  · refine ⟨b, [], ?_⟩
    unfold runs
    rw [List.splitOn_eq_splitOnP, List.splitOnP_eq_singleton (fun z hz => by
      simp only [beq_eq_false_iff_ne]
      rintro rfl
      rcases List.mem_append.mp hz with h | h
      · exact h0 h
      · exact hb h)]
    simp [ha]

/-- The array that `build` starts from. -/
def initArray (b n : UInt64) : Array UInt64 :=
  LeanExe.build (b + 2 * (n + 1)) fun k =>
    if b ≤ k then
      (if (k - b) % 2 = 0 then (if k = b then n else (k - b) / 2 - 1)
       else (if (k - b) / 2 = n then 0 else (k - b) / 2 + 1))
    else if k % 3 = 0 ∨ n < k / 3 ∨ k / 3 = 0 then 0 else k / 3

theorem init_word {L : Layout} (hL : L.Good) {b n : UInt64} (hb : b.toNat = L.base)
    (hn : n.toNat = L.n) {m : Nat} (hm : m < L.base + 2 * (L.n + 1)) :
    W (initArray b n) m =
      if L.base ≤ m then
        (if (m - L.base) % 2 = 0 then (if m = L.base then L.n else (m - L.base) / 2 - 1)
         else (if (m - L.base) / 2 = L.n then 0 else (m - L.base) / 2 + 1))
      else if m % 3 = 0 ∨ L.n < m / 3 ∨ m / 3 = 0 then 0 else m / 3 := by
  have hsmall := hL.small
  have hsz : (b + 2 * (n + 1)).toNat = L.base + 2 * (L.n + 1) := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, hb, hn]; omega
  have hm64 : (UInt64.ofNat m).toNat = m := UInt64.toNat_ofNat_of_lt' (show m < 2 ^ 64 by omega)
  unfold W initArray
  rw [build_get (by rw [hsz]; exact hm)]
  have hle : b ≤ UInt64.ofNat m ↔ L.base ≤ m := by rw [UInt64.le_iff_toNat_le, hm64, hb]
  have hbeq : UInt64.ofNat m = b ↔ m = L.base := by rw [← UInt64.toNat_inj, hm64, hb]
  have hmod3 : (UInt64.ofNat m % 3).toNat = m % 3 := by rw [UInt64.toNat_mod, hm64]; rfl
  have hdiv3 : (UInt64.ofNat m / 3).toNat = m / 3 := by rw [UInt64.toNat_div, hm64]; rfl
  have hnode : (UInt64.ofNat m % 3 = 0 ∨ n < UInt64.ofNat m / 3 ∨ UInt64.ofNat m / 3 = 0) ↔
      (m % 3 = 0 ∨ L.n < m / 3 ∨ m / 3 = 0) := by
    rw [← UInt64.toNat_inj, ← UInt64.toNat_inj (a := UInt64.ofNat m / 3), UInt64.lt_iff_toNat_lt,
      hmod3, hdiv3, hn]
    simp
  by_cases h1 : L.base ≤ m
  · have hsub : (UInt64.ofNat m - b).toNat = m - L.base := by
      rw [UInt64.toNat_sub_of_le _ _ (hle.mpr h1), hm64, hb]
    have hmod : ((UInt64.ofNat m - b) % 2).toNat = (m - L.base) % 2 := by
      rw [UInt64.toNat_mod, hsub]; rfl
    have hdiv : ((UInt64.ofNat m - b) / 2).toNat = (m - L.base) / 2 := by
      rw [UInt64.toNat_div, hsub]; rfl
    have hmod2 : (UInt64.ofNat m - b) % 2 = 0 ↔ (m - L.base) % 2 = 0 := by
      rw [← UInt64.toNat_inj, hmod]; simp
    have hdivn : (UInt64.ofNat m - b) / 2 = n ↔ (m - L.base) / 2 = L.n := by
      rw [← UInt64.toNat_inj, hdiv, hn]
    rw [ite_eq_left (hle.mpr h1), ite_eq_left h1]
    simp only [hmod2, hbeq, hdivn]
    split_ifs with h2 h3 h4
    · exact hn
    · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hdiv]; simp; omega), hdiv]
      simp
    · rfl
    · rw [UInt64.toNat_add, hdiv]; simp; omega
  · rw [ite_eq_right (fun h => h1 (hle.mp h)), ite_eq_right h1]
    simp only [hnode]
    split_ifs
    · rfl
    · exact hdiv3

theorem nxt_empty (c : Nat) : nxt c ∅ c = c := by unfold nxt; simp
theorem prv_empty (c : Nat) : prv c ∅ c = c := by unfold prv; simp

theorem made_first_zero (L : Layout) : made L (L.first 0 + 0) = ∅ := by
  ext q
  simp only [made, mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro _ hqn hq
  have := (L.node_lt hqn).1
  simp [Layout.first] at hq
  omega

/-- The array that `build` starts from holds `Partial` before any option. -/
theorem partial_init {L : Layout} (hL : L.Good) {b n : UInt64} (hb : b.toNat = L.base)
    (hn : n.toNat = L.n) : Partial (initArray b n) L 0 0 := by
  have hsmall := hL.small
  have hsz : (initArray b n).size = L.base + 2 * (L.n + 1) := by
    unfold initArray
    rw [build_size]
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, hb, hn]; omega
  have hbase : 3 * (L.n + 2) ≤ L.base := by
    have := L.first_le (Nat.zero_le L.os.length)
    unfold Layout.base; simp [Layout.first] at this; omega
  have hw := fun m hm => init_word hL hb hn (m := m) hm
  refine ⟨hsz, ⟨fun y hy => ?_, fun y hy => ?_⟩, ?_, ?_, fun k hk => absurd hk (Nat.not_lt_zero _),
    fun k hk => absurd hk (Nat.not_lt_zero _), ?_⟩
  · have hyn : y ≤ L.n := by
      rcases mem_insert.mp hy with rfl | hy
      · omega
      · exact (mem_Icc.mp hy).2
    rw [hw _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega), prv_Icc hyn]
    by_cases h0 : y = 0
    · rw [ite_eq_left (by omega), ite_eq_left h0]
    · rw [ite_eq_right (by omega), ite_eq_right h0]; omega
  · have hyn : y ≤ L.n := by
      rcases mem_insert.mp hy with rfl | hy
      · omega
      · exact (mem_Icc.mp hy).2
    rw [hw _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega), nxt_Icc hyn]
    by_cases h0 : y = L.n
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; omega
  · rw [made_first_zero]
    refine ⟨fun p hp => absurd hp (Finset.notMem_empty p), fun c hc => (mem_Icc.mp hc).2,
      fun c hc => ?_⟩
    have hcI := mem_Icc.mp hc
    have hcQ : L.colQ ∅ c = ∅ := by simp [Layout.colQ]
    rw [hcQ]
    refine ⟨fun q hq => absurd hq (Finset.notMem_empty q), fun y hy => ?_, ?_,
      fun q hq => absurd hq (Finset.notMem_empty q), fun y hy => ?_, fun y hy => ?_⟩
    · rw [insert_empty, mem_singleton] at hy; rw [hy, hsz]; omega
    · rw [hw _ (by omega), ite_eq_right (by omega), ite_eq_left (by omega), card_empty]
    · rw [insert_empty, mem_singleton] at hy
      subst hy
      rw [hw _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), nxt_empty]
      omega
    · rw [insert_empty, mem_singleton] at hy
      subst hy
      rw [hw _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), prv_empty]
      omega
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Layout.first]
    rw [hw _ (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  · intro q hq hqM r hr
    have hqb : 3 * q + r < L.base := by unfold Layout.base; omega
    have := hw (3 * q + r) (by omega)
    rw [ite_eq_right (by omega), ite_eq_left (by simp [Layout.first] at hq; omega)] at this
    exact UInt64.toNat_inj.mp (by rw [← W, this]; rfl)

theorem first_word (x : Array UInt64) : (x[(0 : UInt64).toNat]!).toNat = itemCount x := by
  unfold itemCount
  by_cases h : 0 < x.size
  · rw [getElem!_pos x _ h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl
  · rw [getElem!_neg x _ h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

/-- The options after the reader's state at any step of the words. -/
theorem options_at (x : Array UInt64) (k : Nat) :
    let st := ((words x).take k).foldl readStep ([], [])
    options x = st.1 ++ runs (st.2 ++ (words x).drop k) := by
  intro st
  rw [← runs_eq_options]
  have := read_prefix ((words x).take k) ((words x).drop k)
  rw [List.take_append_drop] at this
  exact this

/-- The state of `build`'s loop after the words before position `k` of the input. -/
def BuildInv (x : Array UInt64) (L : Layout) (k : Nat)
    (s : UInt64 × UInt64 × UInt64 × Array UInt64) : Prop :=
  let st := ((words x).take (k - 1)).foldl readStep ([], [])
  s.1.toNat = L.first st.1.length - 1 ∧ s.2.1.toNat = L.first st.1.length + st.2.length ∧
    s.2.2.1.toNat = (if st.2 = [] then 0 else L.first st.1.length) ∧
    Partial s.2.2.2 L st.1.length st.2.length

/-- The writes of `build`'s loop for a word, as the program states them. -/
def buildStep (x : Array UInt64) (k : UInt64) (s : UInt64 × UInt64 × UInt64 × Array UInt64) :
    UInt64 × UInt64 × UInt64 × Array UInt64 :=
  if k = 0 ∨ (x[k.toNat]! = 0 ∧ s.2.2.1 = 0) then s
  else if x[k.toNat]! = 0 then
    (s.2.1, s.2.1 + 1, 0, (s.2.2.2.set! (3 * s.2.1 + 1).toNat s.2.2.1).set! (3 * s.1 + 2).toNat
      (s.2.1 - 1))
  else
    (s.1, s.2.1 + 1, if s.2.2.1 = 0 then s.2.1 else s.2.2.1,
      ((((s.2.2.2.set! (3 * s.2.1).toNat x[k.toNat]!).set! (3 * s.2.1 + 1).toNat
        s.2.2.2[(3 * x[k.toNat]! + 1).toNat]!).set! (3 * s.2.1 + 2).toNat x[k.toNat]!).set!
        (3 * s.2.2.2[(3 * x[k.toNat]! + 1).toNat]! + 2).toNat s.2.1 |>.set!
        (3 * x[k.toNat]! + 1).toNat s.2.1).set! (3 * x[k.toNat]!).toNat
        (s.2.2.2[(3 * x[k.toNat]!).toNat]! + 1))

theorem getElem!_append_cons {α : Type} [Inhabited α] (l : List α) (a : α) (r : List α) :
    (l ++ a :: r)[l.length]! = a := by
  rw [getElem!_pos _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

/-- One step of `build`'s loop keeps the invariant. -/
theorem buildStep_inv (x : Array UInt64) (hv : Valid x) (hx : x.size < 2 ^ 50) {k : Nat}
    (hk : k < x.size) {s : UInt64 × UInt64 × UInt64 × Array UInt64}
    (h : BuildInv x (layout x) k s) :
    BuildInv x (layout x) (k + 1) (buildStep x (UInt64.ofNat k) s) := by
  have hL : (layout x).Good := layout_good x hv hx
  have hsmall : (layout x).base + 2 * ((layout x).n + 1) < 2 ^ 60 := hL.small
  have hbase : 3 * (layout x).first (layout x).os.length = (layout x).base := rfl
  obtain ⟨hs1, hs2, hs3, hP⟩ := h
  have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hC : UInt64.ofNat 0 = 0 ∨
        (x[(UInt64.ofNat 0).toNat]! = 0 ∧ s.2.2.1 = 0) := Or.inl rfl
    rw [buildStep, ite_eq_left hC]
    exact ⟨hs1, hs2, hs3, hP⟩
  generalize hst : ((words x).take (k - 1)).foldl readStep ([], []) = st at hs1 hs2 hs3 hP
  have hk0' : UInt64.ofNat k ≠ 0 := fun e => by rw [e] at hk64; simp at hk64; omega
  have hwk := words_get x (k := k) (by omega) hk
  generalize hwN : (x[k]!).toNat = wN at hwk
  have htake : (words x).take (k + 1 - 1) =
      (words x).take (k - 1) ++ [(words x)[k - 1]'(by rw [words_length]; omega)] := by
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (by rw [words_length]; omega), Option.toList_some]
  have hst' : ((words x).take (k + 1 - 1)).foldl readStep ([], []) = readStep st wN := by
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hwk, hst]
  have hdrop : (words x).drop (k - 1) = wN :: (words x).drop k := by
    rw [← hwk, List.drop_eq_getElem_cons (by rw [words_length]; omega)]
    congr 2; omega
  have hos := options_at x (k - 1)
  rw [hst, hdrop] at hos
  have hos' : (layout x).os = st.1 ++ runs (st.2 ++ wN :: (words x).drop k) := hos
  have hnz := read_noZero ((words x).take (k - 1)) ([], []) (by simp)
  rw [hst] at hnz
  have hxk : x[(UInt64.ofNat k).toNat]! = x[k]! := by rw [hk64]
  have hpos : 0 < (layout x).first st.1.length := by
    have := (layout x).n_lt_first st.1.length; omega
  unfold BuildInv
  rw [hst']
  by_cases hw0 : wN = 0
  · have hxw : x[k]! = 0 := UInt64.toNat_inj.mp (by rw [hwN, hw0]; rfl)
    by_cases hc : st.2 = []
    · -- A zero between options: nothing changes.
      have hf : s.2.2.1 = 0 := UInt64.toNat_inj.mp (by rw [hs3, ite_eq_left hc]; rfl)
      have hC : UInt64.ofNat k = 0 ∨ (x[(UInt64.ofNat k).toNat]! = 0 ∧ s.2.2.1 = 0) :=
        Or.inr ⟨by rw [hxk, hxw], hf⟩
      rw [buildStep, ite_eq_left hC]
      have : readStep st wN = st := by unfold readStep; rw [ite_eq_left hw0, ite_eq_left hc]
      rw [this]
      exact ⟨hs1, hs2, hs3, hP⟩
    · -- A zero after a run: the option is finished.
      have hf : s.2.2.1 ≠ 0 := fun e => by
        rw [e, ite_eq_right hc] at hs3; simp at hs3; omega
      have hC : ¬ (UInt64.ofNat k = 0 ∨ (x[(UInt64.ofNat k).toNat]! = 0 ∧ s.2.2.1 = 0)) := by
        rintro (e | ⟨_, e⟩)
        · exact hk0' e
        · exact hf e
      have hC2 : x[(UInt64.ofNat k).toNat]! = 0 := by rw [hxk, hxw]
      rw [buildStep, ite_eq_right hC, ite_eq_left hC2]
      have hruns : runs (st.2 ++ wN :: (words x).drop k) = st.2 :: runs ((words x).drop k) := by
        rw [hw0]; unfold runs; rw [runs_nozero_append st.2 _ hnz]; simp [hc]
      rw [hruns] at hos'
      have hMc : st.1.length < (layout x).os.length := by rw [hos']; simp
      have hlen : (layout x).len st.1.length = st.2.length := by
        unfold Layout.len; rw [hos', getElem!_append_cons]
      have hP' : Partial s.2.2.2 (layout x) st.1.length ((layout x).len st.1.length) := by
        rw [hlen]; exact hP
      have hcl := partial_close hL hP' hMc
      have hsucc := (layout x).first_succ st.1.length
      have hlast := (layout x).first_le_last hMc
      have hp_eq : s.2.1.toNat = (layout x).first (st.1.length + 1) - 1 := by
        rw [hs2, hsucc, hlen]; omega
      obtain ⟨-, e1, -⟩ := idx3 s.2.1 (by omega)
      obtain ⟨-, -, e2⟩ := idx3 s.1 (by omega)
      have hfv : s.2.2.1 = UInt64.ofNat ((layout x).first st.1.length) := by
        rw [← UInt64.ofNat_toNat (x := s.2.2.1), hs3, ite_eq_right hc]
      have hpv : s.2.1 - 1 = UInt64.ofNat ((layout x).first (st.1.length + 1) - 2) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
          UInt64.toNat_ofNat_of_lt' (show (layout x).first (st.1.length + 1) - 2 < 2 ^ 64 by
            omega)]
        simp; omega
      have hstep : readStep st wN = (st.1 ++ [st.2], []) := by
        unfold readStep; rw [ite_eq_left hw0, ite_eq_right hc]
      rw [hstep]
      dsimp only
      simp only [List.length_append, List.length_singleton, List.length_nil, Nat.add_zero,
        ite_true]
      refine ⟨hp_eq, ?_, rfl, ?_⟩
      · rw [UInt64.toNat_add, hp_eq]; simp; omega
      · rw [e1, e2, hp_eq, hs1, hfv, hpv]
        exact hcl
  · -- A nonzero word: a node of the option being read.
    have hxw : x[k]! ≠ 0 := fun e => hw0 (by rw [← hwN, e]; rfl)
    have hC : ¬ (UInt64.ofNat k = 0 ∨ (x[(UInt64.ofNat k).toNat]! = 0 ∧ s.2.2.1 = 0)) := by
      rintro (e | ⟨e, _⟩)
      · exact hk0' e
      · exact hxw (by rw [← hxk]; exact e)
    have hC2 : ¬ x[(UInt64.ofNat k).toNat]! = 0 := by rw [hxk]; exact hxw
    rw [buildStep, ite_eq_right hC, ite_eq_right hC2]
    obtain ⟨c, tl, hrh⟩ := runs_head (st.2 ++ [wN]) ((words x).drop k) (by simp)
      (by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hnz, fun e => hw0 e.symm⟩)
    rw [List.append_assoc, List.singleton_append] at hrh
    rw [hrh] at hos'
    have hMc : st.1.length < (layout x).os.length := by rw [hos']; simp
    have hopt : (layout x).os[st.1.length]! = st.2 ++ [wN] ++ c := by
      rw [hos', getElem!_append_cons]
    have hj : st.2.length < (layout x).len st.1.length := by
      unfold Layout.len; rw [hopt]; simp
    have hitem : (layout x).item st.1.length st.2.length = wN := by
      unfold Layout.item
      rw [hopt, getElem!_pos _ _ (by simp)]
      simp [List.getElem_append]
    have hap := partial_append hL hP hMc hj
    rw [hitem] at hap
    have hlast := (layout x).first_le_last hMc
    rw [Layout.first_succ] at hlast
    have hwn : wN ≤ (layout x).n := by rw [← hitem]; exact (hL.items _ hMc _ hj).2
    have hwI : wN ∈ Icc 1 (layout x).n := mem_Icc.mpr ⟨by omega, hwn⟩
    have hcol := hP.cols.col wN hwI
    have hup := hcol.size _ (prv_mem_insert wN
      ((layout x).colQ (made (layout x) ((layout x).first st.1.length + st.2.length)) wN) wN)
    have hupw := hcol.up _ (mem_insert_self _ _)
    rw [W] at hupw
    obtain ⟨e0, e1, e2⟩ := idx3 s.2.1 (by omega)
    have hwv : x[k]! = UInt64.ofNat wN := by rw [← hwN, UInt64.ofNat_toNat]
    obtain ⟨f0, f1, -⟩ := idx3 (x[k]!) (by rw [hwN]; omega)
    obtain ⟨-, -, g2⟩ := idx3 (s.2.2.2[3 * wN + 1]!) (by rw [hupw]; rw [hP.size] at hup; omega)
    have hstep : readStep st wN = (st.1, st.2 ++ [wN]) := by
      unfold readStep; rw [ite_eq_right hw0]
    have hpv : s.2.1 = UInt64.ofNat ((layout x).first st.1.length + st.2.length) := by
      rw [← UInt64.ofNat_toNat (x := s.2.1), hs2]
    rw [hstep]
    dsimp only
    simp only [List.length_append, List.length_singleton]
    have hne : ¬ (st.2 ++ [wN] = []) := by simp
    rw [ite_eq_right hne]
    refine ⟨hs1, ?_, ?_, ?_⟩
    · rw [UInt64.toNat_add, hs2]; simp; omega
    · by_cases hc : st.2 = []
      · have hf : s.2.2.1 = 0 := UInt64.toNat_inj.mp (by rw [hs3, ite_eq_left hc]; rfl)
        rw [ite_eq_left hf, hs2, hc]
        rfl
      · have hf : s.2.2.1 ≠ 0 := fun e => by
          rw [e, ite_eq_right hc] at hs3; simp at hs3; omega
        rw [ite_eq_right hf, hs3, ite_eq_right hc]
    · rw [hk64, e0, e1, e2, f0, f1, hwN, g2, hwv]
      convert hap using 1
      unfold append
      rw [W, hupw, hpv, UInt64.toNat_ofNat_of_lt'
        (show (layout x).first st.1.length + st.2.length < 2 ^ 64 by omega)]

/-- The end of `build`: an input that ends inside an option gets the spacer after it. -/
def buildEnd (s : UInt64 × UInt64 × UInt64 × Array UInt64) : Array UInt64 :=
  if s.2.2.1 = 0 then s.2.2.2
  else (s.2.2.2.set! (3 * s.2.1 + 1).toNat s.2.2.1).set! (3 * s.1 + 2).toNat (s.2.1 - 1)

theorem build_eq (b : UInt64) (x : Array UInt64) :
    build b x = buildEnd (LeanExe.loop x.size.toUInt64
      (x[(0 : UInt64).toNat]! + 1, x[(0 : UInt64).toNat]! + 2, (0 : UInt64),
        initArray b x[(0 : UInt64).toNat]!) (buildStep x)) := rfl

/-- `build` leaves the invariant of the search for all items. -/
theorem build_inv (x : Array UInt64) (hv : Valid x) (hx : x.size < 2 ^ 50) {b : UInt64}
    (hb : b.toNat = (layout x).base) : Inv (build b x) (layout x) (Icc 1 (layout x).n) := by
  have hL : (layout x).Good := layout_good x hv hx
  have hsmall : (layout x).base + 2 * ((layout x).n + 1) < 2 ^ 60 := hL.small
  have hbase : 3 * (layout x).first (layout x).os.length = (layout x).base := rfl
  have hn : (x[(0 : UInt64).toNat]!).toNat = (layout x).n := first_word x
  have hsz : x.size.toUInt64.toNat = x.size := size_toUInt64 x (by omega)
  have h0 : BuildInv x (layout x) 0 (x[(0 : UInt64).toNat]! + 1, x[(0 : UInt64).toNat]! + 2,
      (0 : UInt64), initArray b x[(0 : UInt64).toNat]!) := by
    have hf0 : (layout x).first 0 = (layout x).n + 2 := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (x[(0 : UInt64).toNat]! + 1).toNat = (layout x).first 0 - 1
      rw [UInt64.toNat_add, hn, hf0]; simp; omega
    · show (x[(0 : UInt64).toNat]! + 2).toNat = (layout x).first 0 + 0
      rw [UInt64.toNat_add, hn, hf0]; simp; omega
    · rfl
    · exact partial_init hL hb hn
  have hloop := loop_induction (n := x.size.toUInt64)
    (init := (x[(0 : UInt64).toNat]! + 1, x[(0 : UInt64).toNat]! + 2, (0 : UInt64),
      initArray b x[(0 : UInt64).toNat]!)) (f := buildStep x)
    (fun k s => BuildInv x (layout x) k s) h0
    (fun k s hk h => buildStep_inv x hv hx (by rw [hsz] at hk; exact hk) h)
  rw [hsz] at hloop
  rw [build_eq]
  generalize LeanExe.loop _ _ _ = s at hloop ⊢
  obtain ⟨hs1, hs2, hs3, hP⟩ := hloop
  have hall : (words x).take (x.size - 1) = words x := by
    rw [← words_length, List.take_length]
  rw [hall] at hs1 hs2 hs3 hP
  generalize hst : (words x).foldl readStep ([], []) = st at hs1 hs2 hs3 hP
  have hos : (layout x).os = finish st := by
    show options x = finish st
    rw [← runs_eq_options, ← hst, finish_read (words x) [] [] (by simp), List.nil_append,
      List.nil_append]
    rfl
  unfold buildEnd
  by_cases hc : st.2 = []
  · have hf : s.2.2.1 = 0 := UInt64.toNat_inj.mp (by rw [hs3, ite_eq_left hc]; rfl)
    rw [ite_eq_left hf]
    have hM : st.1.length = (layout x).os.length := by
      rw [hos, finish, ite_eq_left hc, List.append_nil]
    have hj : st.2.length = 0 := by rw [hc]; rfl
    rw [hM, hj] at hP
    exact partial_final hL hP
  · have hpos : 0 < (layout x).first st.1.length := by
      have := (layout x).n_lt_first st.1.length; omega
    have hf : s.2.2.1 ≠ 0 := fun e => by
      rw [e, ite_eq_right hc] at hs3; simp at hs3; omega
    rw [ite_eq_right hf]
    have hos' : (layout x).os = st.1 ++ [st.2] := by rw [hos, finish, ite_eq_right hc]
    have hMc : st.1.length < (layout x).os.length := by rw [hos']; simp
    have hM : st.1.length + 1 = (layout x).os.length := by rw [hos']; simp
    have hlen : (layout x).len st.1.length = st.2.length := by
      unfold Layout.len; rw [hos', getElem!_append_cons]
    have hP' : Partial s.2.2.2 (layout x) st.1.length ((layout x).len st.1.length) := by
      rw [hlen]; exact hP
    have hcl := partial_close hL hP' hMc
    have hsucc := (layout x).first_succ st.1.length
    have hlast := (layout x).first_le_last hMc
    have hp_eq : s.2.1.toNat = (layout x).first (st.1.length + 1) - 1 := by
      rw [hs2, hsucc, hlen]; omega
    obtain ⟨-, e1, -⟩ := idx3 s.2.1 (by omega)
    obtain ⟨-, -, e2⟩ := idx3 s.1 (by omega)
    have hfv : s.2.2.1 = UInt64.ofNat ((layout x).first st.1.length) := by
      rw [← UInt64.ofNat_toNat (x := s.2.2.1), hs3, ite_eq_right hc]
    have hpv : s.2.1 - 1 = UInt64.ofNat ((layout x).first (st.1.length + 1) - 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
        UInt64.toNat_ofNat_of_lt' (show (layout x).first (st.1.length + 1) - 2 < 2 ^ 64 by
          omega)]
      simp; omega
    rw [e1, e2, hp_eq, hs1, hfv, hpv]
    rw [hM] at hcl
    exact partial_final hL hcl

end Library.Combinatorics.DancingLinks
