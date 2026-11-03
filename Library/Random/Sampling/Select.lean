import Library.Random.Sampling.Proof

/-! The proof that `sample` satisfies `Samples`.  The loop of `sample` keeps `m`, the number of
records chosen, and an array of `k` words whose first `m` words are the records chosen so far,
followed by the records that Algorithm S chooses from record `t` on (`sample_eq`).  At the end no
record is left, and `k - m ≤ N - t` forces `m = k`.  `selectFrom` chooses `k - m` of the remaining
records (`selectFrom_length`), since a word `u` gives `⌊(N - t)·u / 2^64⌋ < N - t`, so that when
`k - m = N - t` every remaining record is chosen.

For the count, `selL` states Algorithm S on a list of words, one word for each record, with `M`
records left and `c` records still to choose.  The word arrays that choose a given list `ps` split
at the first record: the record is chosen by the words `u` with `⌊M·u / 2^64⌋ < c`, which number
between `c⌊2^64 / M⌋` and `c⌈2^64 / M⌉`, and passed over by the others, which number between
`(M - c)⌊2^64 / M⌋` and `(M - c)⌈2^64 / M⌉`.  By induction on the number of records, `ps` comes
from between `c!(M - c)! ∏ ⌊2^64 / M⌋` and `c!(M - c)! ∏ ⌈2^64 / M⌉` word arrays
(`selL_count`). -/

namespace Library.Random.Sampling

open LeanExe.Dialect

/-! ### The program -/

theorem take_set_succ' (l : List UInt64) (m : Nat) (x : UInt64) (h : m < l.length) :
    (l.set m x).take (m + 1) = l.take m ++ [x] := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left h]
  have hlen : (l.take m).length = m := by simp; omega
  rw [List.take_append, hlen, show m + 1 - m = 1 by omega,
    List.take_of_length_le (by rw [hlen]; omega)]
  simp

theorem take_set_self (l : List UInt64) (m : Nat) (x : UInt64) :
    (l.set m x).take m = l.take m := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_set]
  rw [ite_eq_right (by simp at h1; omega)]

/-- The program's loop computes Algorithm S. -/
theorem sample_eq (us xs : Array UInt64) (n : UInt64) (hs : xs.size < 2 ^ 32) :
    sample us xs n = algorithmS us xs n.toNat := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [sample, algorithmS]
  generalize hK : (if n ≤ xs.size.toUInt64 then n else xs.size.toUInt64) = kU
  have hkU : kU.toNat = min n.toNat xs.size := by
    rw [← hK]
    split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le, hN] at h <;> simp [hN] <;> omega
  generalize hk : min n.toNat xs.size = k at hkU ⊢
  have hkN : k ≤ xs.size := by rw [← hk]; exact Nat.min_le_right _ _
  have h := loop_induction (n := xs.size.toUInt64)
    (init := ((0 : UInt64), LeanExe.build kU fun _ => (0 : UInt64)))
    (f := fun t s => (s.1 + (if scale us[t.toNat]! (xs.size.toUInt64 - t) < kU - s.1 then 1 else 0),
      s.2.set! s.1.toNat xs[t.toNat]!))
    (P := fun t s => s.2.size = k ∧ s.1.toNat ≤ k ∧ k - s.1.toNat ≤ xs.size - t ∧
      s.2.toList.take s.1.toNat ++ selectFrom us xs.size k t s.1.toNat (xs.toList.drop t) =
        selectFrom us xs.size k 0 0 xs.toList)
    ⟨by rw [build_size, hkU], by simp, by simp; omega, by simp⟩
    (by
      intro t s ht ⟨hsz, hmk, hrem, heq⟩
      rw [hN] at ht
      have htt : (UInt64.ofNat t).toNat = t := word_toNat (by omega)
      have hNt : (xs.size.toUInt64 - UInt64.ofNat t).toNat = xs.size - t := by
        simp only [UInt64.toNat_sub, hN, htt]; omega
      have hkm : (kU - s.1).toNat = k - s.1.toNat := by
        simp only [UInt64.toNat_sub, hkU]
        have := s.1.toNat_lt
        omega
      have hsc : (scale us[t]! (xs.size.toUInt64 - UInt64.ofNat t)).toNat =
          us[t]!.toNat * (xs.size - t) / 2 ^ 64 := by
        rw [scale_toNat _ _ (by rw [hNt]; omega), hNt]
      have hv : us[t]!.toNat * (xs.size - t) < (xs.size - t) * 2 ^ 64 := by
        rw [Nat.mul_comm (xs.size - t)]
        exact Nat.mul_lt_mul_of_pos_right us[t]!.toNat_lt (by omega)
      have hdrop : xs.toList.drop t = xs.toList[t]'(by simp; omega) :: xs.toList.drop (t + 1) :=
        List.drop_eq_getElem_cons (by simp; omega)
      have hx : xs[t]! = xs.toList[t]'(by simp; omega) := by
        rw [getElem!_pos xs t (by omega), Array.getElem_toList]
      rw [hdrop, selectFrom] at heq
      rw [htt, hx]
      by_cases hc : us[t]!.toNat * (xs.size - t) < (k - s.1.toNat) * 2 ^ 64
      · have hcU : scale us[t]! (xs.size.toUInt64 - UInt64.ofNat t) < kU - s.1 := by
          rw [UInt64.lt_iff_toNat_lt, hsc, hkm, Nat.div_lt_iff_lt_mul (by norm_num)]; exact hc
        rw [ite_eq_left hc] at heq
        rw [ite_eq_left hcU]
        dsimp only
        have hm1 : (s.1 + 1).toNat = s.1.toNat + 1 := by
          simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
        refine ⟨by rw [Array.size_set!, hsz], by omega, by omega, ?_⟩
        rw [hm1, Array.toList_set!, take_set_succ' _ _ _ (by simp; omega), ← heq]
        simp
      · have hcU : ¬ scale us[t]! (xs.size.toUInt64 - UInt64.ofNat t) < kU - s.1 := by
          rw [UInt64.lt_iff_toNat_lt, hsc, hkm, Nat.div_lt_iff_lt_mul (by norm_num)]; exact hc
        rw [ite_eq_right hc] at heq
        rw [ite_eq_right hcU, UInt64.add_zero]
        dsimp only
        refine ⟨by rw [Array.size_set!, hsz], hmk, by omega, ?_⟩
        rw [Array.toList_set!, take_set_self, ← heq])
  rw [hN] at h
  obtain ⟨hsz, hmk, hrem, heq⟩ := h
  generalize LeanExe.loop _ _ _ = r at hsz hmk hrem heq ⊢
  have hm : r.1.toNat = k := by omega
  rw [hm, List.drop_of_length_le (by simp), show selectFrom us xs.size k xs.size k [] = [] from rfl,
    List.append_nil, List.take_of_length_le (by simp [hsz])] at heq
  rw [← heq, Array.toArray_toList]

/-! ### The words chosen -/

theorem selectFrom_sublist (us : Array UInt64) (N k : Nat) :
    ∀ (t m : Nat) (l : List UInt64), (selectFrom us N k t m l).Sublist l
  | _, _, [] => List.Sublist.slnil
  | t, m, x :: rest => by
    rw [selectFrom]
    split
    · exact (selectFrom_sublist us N k (t + 1) (m + 1) rest).cons_cons x
    · exact (selectFrom_sublist us N k (t + 1) m rest).cons x

theorem selectFrom_map (us : Array UInt64) (N k : Nat) (g : UInt64 → UInt64) :
    ∀ (t m : Nat) (l : List UInt64),
      selectFrom us N k t m (l.map g) = (selectFrom us N k t m l).map g
  | _, _, [] => rfl
  | t, m, x :: rest => by
    rw [List.map_cons, selectFrom, selectFrom]
    split
    · rw [selectFrom_map us N k g (t + 1) (m + 1) rest, List.map_cons]
    · exact selectFrom_map us N k g (t + 1) m rest

/-- Algorithm S chooses `k - m` of the records left when no more are needed than are left. -/
theorem selectFrom_length (us : Array UInt64) (N k : Nat) :
    ∀ (t m : Nat) (l : List UInt64), t + l.length = N → m ≤ k → k - m ≤ l.length →
      (selectFrom us N k t m l).length = k - m
  | t, m, [], _, hmk, hrem => by
    simp at hrem; rw [show selectFrom us N k t m [] = [] from rfl]; simp; omega
  | t, m, x :: rest, hN, hmk, hrem => by
    simp only [List.length_cons] at hN hrem
    have hv : us[t]!.toNat * (N - t) < (N - t) * 2 ^ 64 := by
      rw [Nat.mul_comm (N - t)]
      exact Nat.mul_lt_mul_of_pos_right us[t]!.toNat_lt (by omega)
    rw [selectFrom]
    split
    · rename_i hc
      rw [List.length_cons, selectFrom_length us N k (t + 1) (m + 1) rest (by omega) (by omega)
        (by omega)]
      omega
    · rename_i hc
      exact selectFrom_length us N k (t + 1) m rest (by omega) hmk (by omega)

/-! ### Counting the word arrays -/

/-- Algorithm S on a list of words, one for each record, with `M` records left and `c` still to
choose. -/
def selL : List UInt64 → Nat → Nat → List UInt64 → List UInt64
  | w :: ws, M, c, x :: rest =>
    if w.toNat * M / 2 ^ 64 < c then x :: selL ws (M - 1) (c - 1) rest else selL ws (M - 1) c rest
  | _, _, _, _ => []

theorem selL_sublist : ∀ (ws : List UInt64) (M c : Nat) (l : List UInt64), (selL ws M c l).Sublist l
  | [], _, _, l => by cases l <;> exact List.nil_sublist _
  | _ :: _, _, _, [] => List.Sublist.slnil
  | w :: ws, M, c, x :: rest => by
    rw [selL]
    split
    · exact (selL_sublist ws (M - 1) (c - 1) rest).cons_cons x
    · exact (selL_sublist ws (M - 1) c rest).cons x

theorem selectFrom_eq_selL (us : Array UInt64) (N k : Nat) :
    ∀ (t m : Nat) (l : List UInt64), t + l.length = N → N ≤ us.size →
      selectFrom us N k t m l = selL (us.toList.drop t) (N - t) (k - m) l
  | t, m, [], _, _ => by
    rw [show selectFrom us N k t m [] = [] from rfl]
    cases us.toList.drop t <;> rfl
  | t, m, x :: rest, hN, hu => by
    simp only [List.length_cons] at hN
    have hdrop : us.toList.drop t = us.toList[t]'(by simp; omega) :: us.toList.drop (t + 1) :=
      List.drop_eq_getElem_cons (by simp; omega)
    have hget : us[t]! = us.toList[t]'(by simp; omega) := by
      rw [getElem!_pos us t (by omega), Array.getElem_toList]
    have hiff : ∀ a c : Nat, a < c * 2 ^ 64 ↔ a / 2 ^ 64 < c := fun a c =>
      (Nat.div_lt_iff_lt_mul (by norm_num)).symm
    rw [selectFrom, hdrop, selL, ← hget]
    simp only [hiff]
    rw [selectFrom_eq_selL us N k (t + 1) (m + 1) rest (by omega) hu,
      selectFrom_eq_selL us N k (t + 1) m rest (by omega) hu,
      show N - t - 1 = N - (t + 1) by omega, show k - m - 1 = k - (m + 1) by omega]

/-- The words `u` with `⌊M·u / 2^64⌋ = i`. -/
def fiber (M i : Nat) : Finset UInt64 :=
  Finset.univ.filter fun u => u.toNat * M / 2 ^ 64 = i

theorem fiber_card (M i : Nat) (hM0 : 0 < M) (hM : M < 2 ^ 32) (hi : i < M) :
    2 ^ 64 / M ≤ (fiber M i).card ∧ (fiber M i).card ≤ (2 ^ 64 + M - 1) / M := by
  have heq : fiber M i =
      Finset.univ.filter fun u : UInt64 => (scale u (UInt64.ofNat M)).toNat = i := by
    ext u
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [scale_toNat _ _ (by rw [word_toNat (by omega)]; omega), word_toNat (by omega)]
  rw [heq]
  exact scale_card M i hM0 hM hi

/-- The words `u` with `⌊M·u / 2^64⌋` in a set `s` of values below `M` number between
`|s|⌊2^64 / M⌋` and `|s|⌈2^64 / M⌉`. -/
theorem values_card (M : Nat) (hM0 : 0 < M) (hM : M < 2 ^ 32) (s : Finset Nat)
    (hs : ∀ i ∈ s, i < M) (p : Nat → Prop) [DecidablePred p]
    (hp : ∀ i, i < M → (p i ↔ i ∈ s)) :
    s.card * (2 ^ 64 / M) ≤ (Finset.univ.filter fun u : UInt64 => p (u.toNat * M / 2 ^ 64)).card ∧
      (Finset.univ.filter fun u : UInt64 => p (u.toNat * M / 2 ^ 64)).card ≤
        s.card * ((2 ^ 64 + M - 1) / M) := by
  have hlt : ∀ u : UInt64, u.toNat * M / 2 ^ 64 < M := fun u => by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), Nat.mul_comm M]
    exact Nat.mul_lt_mul_of_pos_right u.toNat_lt hM0
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u : UInt64 => u.toNat * M / 2 ^ 64) (t := s)
    (fun u hu => (hp _ (hlt u)).mp (Finset.mem_filter.mp hu).2)]
  have hf : ∀ i ∈ s, ((Finset.univ.filter fun u : UInt64 => p (u.toNat * M / 2 ^ 64)).filter
      fun u => u.toNat * M / 2 ^ 64 = i) = fiber M i := fun i hi => by
    ext u
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; exact (hp i (hs i hi)).mpr hi, h⟩
  rw [Finset.sum_congr rfl fun i hi => congrArg Finset.card (hf i hi)]
  constructor
  · calc s.card * (2 ^ 64 / M) = ∑ _i ∈ s, 2 ^ 64 / M := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun i hi => (fiber_card M i hM0 hM (hs i hi)).1
  · calc _ ≤ ∑ _i ∈ s, (2 ^ 64 + M - 1) / M :=
          Finset.sum_le_sum fun i hi => (fiber_card M i hM0 hM (hs i hi)).2
      _ = s.card * ((2 ^ 64 + M - 1) / M) := by rw [Finset.sum_const, smul_eq_mul]

/-- The word arrays of `R + 1` words whose first word satisfies `P` and whose other words satisfy
`Q` number `|P| · |Q|`. -/
theorem card_cons_split {R : Nat} (P : UInt64 → Prop) (Q : (Fin R → UInt64) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter fun w : Fin (R + 1) → UInt64 => P (w 0) ∧ Q (Fin.tail w)).card =
      (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [← Finset.card_product]
  refine Finset.card_equiv (Fin.consEquiv fun _ => UInt64).symm fun w => ?_
  simp [Fin.consEquiv]

/-- Every list of `c` records, a sublist of `M` distinct records, comes from between
`c!(M - c)! ∏ ⌊2^64 / M'⌋` and `c!(M - c)! ∏ ⌈2^64 / M'⌉` word arrays, the products over `M'` from
1 to `M`. -/
theorem selL_count : ∀ (M c : Nat) (l ps : List UInt64), M < 2 ^ 32 → l.length = M → l.Nodup →
    ps.Sublist l → ps.length = c →
      c.factorial * (M - c).factorial * ∏ M' ∈ Finset.Ico 1 (M + 1), 2 ^ 64 / M' ≤
          (Finset.univ.filter fun w : Fin M → UInt64 => selL (List.ofFn w) M c l = ps).card ∧
        (Finset.univ.filter fun w : Fin M → UInt64 => selL (List.ofFn w) M c l = ps).card ≤
          c.factorial * (M - c).factorial * ∏ M' ∈ Finset.Ico 1 (M + 1), (2 ^ 64 + M' - 1) / M'
  | 0, c, l, ps, _, hl, _, hps, hc => by
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero hl
    subst hl0
    have hps0 : ps = [] := List.eq_nil_of_sublist_nil hps
    subst hps0
    have hc0 : c = 0 := by simp at hc; omega
    subst hc0
    have : (Finset.univ.filter fun w : Fin 0 → UInt64 => selL (List.ofFn w) 0 0 [] = []) =
        Finset.univ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases List.ofFn w <;> rfl
    rw [this, Finset.card_univ]
    simp
  | M + 1, c, l, ps, hM, hl, hnd, hps, hc => by
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, l = x :: rest := by
      cases l with
      | nil => simp at hl
      | cons x rest => exact ⟨x, rest, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hsplit : ∀ w : Fin (M + 1) → UInt64, selL (List.ofFn w) (M + 1) c (x :: rest) =
        if (w 0).toNat * (M + 1) / 2 ^ 64 < c then x :: selL (List.ofFn (Fin.tail w)) M (c - 1) rest
        else selL (List.ofFn (Fin.tail w)) M c rest := fun w => by
      rw [List.ofFn_succ, selL]
      rfl
    have hprod : ∀ g : Nat → Nat, ∏ M' ∈ Finset.Ico 1 (M + 1 + 1), g M' =
        (∏ M' ∈ Finset.Ico 1 (M + 1), g M') * g (M + 1) :=
      fun g => Finset.prod_Ico_succ_top (by omega) g
    rcases List.sublist_cons_iff.mp hps with hsub | ⟨r, rfl, hr⟩
    · -- the first record is passed over
      have hxps : x ∉ ps := fun h => hx (hsub.subset h)
      have hcM : c ≤ M := by rw [← hc, ← hl]; exact hsub.length_le
      have hset : (Finset.univ.filter fun w : Fin (M + 1) → UInt64 =>
          selL (List.ofFn w) (M + 1) c (x :: rest) = ps) =
          Finset.univ.filter fun w : Fin (M + 1) → UInt64 =>
            ¬ (w 0).toNat * (M + 1) / 2 ^ 64 < c ∧
              selL (List.ofFn (Fin.tail w)) M c rest = ps := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsplit]
        split
        · exact ⟨fun h => absurd (h ▸ List.mem_cons_self) hxps, fun h => absurd ‹_› h.1⟩
        · exact ⟨fun h => ⟨‹_›, h⟩, fun h => h.2⟩
      rw [hset, card_cons_split (fun u => ¬ u.toNat * (M + 1) / 2 ^ 64 < c)
        (fun v => selL (List.ofFn v) M c rest = ps)]
      have hA := values_card (M + 1) (by omega) (by omega) (Finset.Ico c (M + 1))
        (fun i hi => (Finset.mem_Ico.mp hi).2) (fun i => ¬ i < c)
        (fun i hi => by simp only [Finset.mem_Ico]; omega)
      rw [Nat.card_Ico] at hA
      have hB := selL_count M c rest ps (by omega) hl hnd' hsub hc
      have hf : (M + 1 - c).factorial = (M + 1 - c) * (M - c).factorial := by
        rw [show M + 1 - c = M - c + 1 by omega, Nat.factorial_succ]
      rw [hprod, hprod, hf]
      constructor
      · calc c.factorial * ((M + 1 - c) * (M - c).factorial) *
              ((∏ M' ∈ Finset.Ico 1 (M + 1), 2 ^ 64 / M') * (2 ^ 64 / (M + 1)))
            = ((M + 1 - c) * (2 ^ 64 / (M + 1))) *
                (c.factorial * (M - c).factorial * ∏ M' ∈ Finset.Ico 1 (M + 1), 2 ^ 64 / M') := by
              ring
          _ ≤ _ := Nat.mul_le_mul hA.1 hB.1
      · calc _ ≤ ((M + 1 - c) * ((2 ^ 64 + (M + 1) - 1) / (M + 1))) *
                (c.factorial * (M - c).factorial *
                  ∏ M' ∈ Finset.Ico 1 (M + 1), (2 ^ 64 + M' - 1) / M') := Nat.mul_le_mul hA.2 hB.2
          _ = _ := by ring
    · -- the first record is chosen
      have hc1 : 1 ≤ c := by rw [← hc]; simp
      have hcM : c ≤ M + 1 := by rw [← hc, ← hl]; simpa using hr.length_le
      have hrlen : r.length = c - 1 := by rw [← hc]; simp
      have hset : (Finset.univ.filter fun w : Fin (M + 1) → UInt64 =>
          selL (List.ofFn w) (M + 1) c (x :: rest) = x :: r) =
          Finset.univ.filter fun w : Fin (M + 1) → UInt64 =>
            (w 0).toNat * (M + 1) / 2 ^ 64 < c ∧
              selL (List.ofFn (Fin.tail w)) M (c - 1) rest = r := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsplit]
        split
        · simp only [List.cons.injEq, true_and]
          exact ⟨fun h => ⟨‹_›, h⟩, fun h => h.2⟩
        · refine ⟨fun h => absurd ((selL_sublist _ _ _ rest).subset (h ▸ List.mem_cons_self)) hx,
            fun h => absurd h.1 ‹_›⟩
      rw [hset, card_cons_split (fun u => u.toNat * (M + 1) / 2 ^ 64 < c)
        (fun v => selL (List.ofFn v) M (c - 1) rest = r)]
      have hA := values_card (M + 1) (by omega) (by omega) (Finset.range c)
        (fun i hi => by have := Finset.mem_range.mp hi; omega) (fun i => i < c)
        (fun i hi => by simp only [Finset.mem_range])
      rw [Finset.card_range] at hA
      have hB := selL_count M (c - 1) rest r (by omega) hl hnd' hr hrlen
      have hf : c.factorial = c * (c - 1).factorial := by
        rw [← Nat.mul_factorial_pred (by omega)]
      rw [show M - (c - 1) = M + 1 - c by omega] at hB
      rw [hprod, hprod, hf]
      constructor
      · calc c * (c - 1).factorial * (M + 1 - c).factorial *
              ((∏ M' ∈ Finset.Ico 1 (M + 1), 2 ^ 64 / M') * (2 ^ 64 / (M + 1)))
            = (c * (2 ^ 64 / (M + 1))) *
                ((c - 1).factorial * (M + 1 - c).factorial *
                  ∏ M' ∈ Finset.Ico 1 (M + 1), 2 ^ 64 / M') := by ring
          _ ≤ _ := Nat.mul_le_mul hA.1 hB.1
      · calc _ ≤ (c * ((2 ^ 64 + (M + 1) - 1) / (M + 1))) *
                ((c - 1).factorial * (M + 1 - c).factorial *
                  ∏ M' ∈ Finset.Ico 1 (M + 1), (2 ^ 64 + M' - 1) / M') := Nat.mul_le_mul hA.2 hB.2
          _ = _ := by ring

/-! ### The specification -/

theorem iota_nodup (N : Nat) (hN : N < 2 ^ 64) : (iota N).toList.Nodup := by
  rw [iota, Array.toList_ofFn]
  apply List.nodup_ofFn.mpr
  intro i j h
  have := congrArg UInt64.toNat h
  rw [word_toNat (by omega), word_toNat (by omega)] at this
  exact Fin.ext this

theorem sample_spec : Samples sample where
  method us xs n hs := sample_eq us xs n hs
  sublist us xs n hs := by
    rw [sample_eq us xs n hs, algorithmS, List.toList_toArray]
    refine ⟨selectFrom_sublist _ _ _ _ _ _, ?_⟩
    rw [List.size_toArray, selectFrom_length us xs.size _ 0 0 xs.toList (by simp) (Nat.zero_le _)
      (by simp)]
    simp
  positions us xs n hs := by
    have hi : (iota xs.size).size = xs.size := Array.size_ofFn
    have hx : xs.toList = (iota xs.size).toList.map fun p => xs[p.toNat]! := by
      rw [← Array.toList_map, iota_map xs (by omega)]
    rw [sample_eq us xs n hs, sample_eq us (iota xs.size) n (by omega), algorithmS, algorithmS, hi,
      hx, selectFrom_map]
    apply Array.toList_inj.mp
    simp
  count N n ps hN hn hps hlen := by
    have hi : (iota N).size = N := Array.size_ofFn
    have hk : min n.toNat N = n.toNat := Nat.min_eq_left hn
    have hset : samplesTo sample (iota N) n ps.toArray =
        Finset.univ.filter fun w : Fin (iota N).size → UInt64 =>
          selL (List.ofFn w) (iota N).size n.toNat (iota N).toList = ps := by
      ext w
      simp only [samplesTo, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sample_eq _ _ n (by rw [hi]; omega), algorithmS,
        Nat.min_eq_left (show n.toNat ≤ (iota N).size by rw [hi]; exact hn),
        selectFrom_eq_selL (Array.ofFn w) (iota N).size n.toNat 0 0 (iota N).toList (by simp)
          (by simp),
        List.drop_zero, Array.toList_ofFn, Nat.sub_zero, Nat.sub_zero]
      exact ⟨fun h => by simpa using congrArg Array.toList h, fun h => by rw [h]⟩
    have e1 : fewestS N n.toNat = fewestS (iota N).size n.toNat := by rw [hi]
    have e2 : mostS N n.toNat = mostS (iota N).size n.toNat := by rw [hi]
    rw [hset, e1, e2]
    exact selL_count (iota N).size n.toNat (iota N).toList ps (by rw [hi]; omega) (by simp)
      (iota_nodup N (by omega)) hps hlen

end Library.Random.Sampling
