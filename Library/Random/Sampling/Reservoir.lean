import Library.Random.Sampling.Select

/-! The proof that `reservoir` satisfies `Reservoirs`.  The loop of `reservoir` keeps the candidates
of Algorithm R in an array, and step `t` replaces candidate `scale us[t] (k + t + 1)` with record
`k + t` when that index is below `k` (`reservoir_eq`).  A replacement removes one candidate and adds
the record, so the candidates are always a sub-multiset of the records (`reservoirFrom_subperm`),
and the indices do not depend on the records (`reservoirFrom_map`). -/

namespace Library.Random.Sampling

open LeanExe.Dialect

/-! ### The program -/

theorem build_toList (xs : Array UInt64) (kU : UInt64) (hk : kU.toNat ≤ xs.size) :
    (LeanExe.build kU fun i => xs[i.toNat]!).toList = xs.toList.take kU.toNat := by
  apply List.ext_getElem (by simp [build_size]; omega)
  intro i h1 h2
  simp only [List.length_take, Array.length_toList, build_size] at h1 h2
  rw [Array.getElem_toList, List.getElem_take, Array.getElem_toList,
    ← getElem!_pos _ i (by rw [build_size]; omega), build_get (by omega),
    word_toNat (by have := kU.toNat_lt; omega), getElem!_pos xs i (by omega)]

/-- The program's loop computes Algorithm R. -/
theorem reservoir_eq (us xs : Array UInt64) (n : UInt64) (hs : xs.size < 2 ^ 32) :
    reservoir us xs n = algorithmR us xs n.toNat := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [reservoir, algorithmR]
  generalize hK : (if n ≤ xs.size.toUInt64 then n else xs.size.toUInt64) = kU
  have hkU : kU.toNat = min n.toNat xs.size := by
    rw [← hK]
    split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le, hN] at h <;> simp [hN] <;> omega
  generalize hk : min n.toNat xs.size = k at hkU ⊢
  have hkN : k ≤ xs.size := by rw [← hk]; exact Nat.min_le_right _ _
  have hcount : (xs.size.toUInt64 - kU).toNat = xs.size - k := by
    simp only [UInt64.toNat_sub, hN, hkU]; omega
  have h := loop_induction (n := xs.size.toUInt64 - kU)
    (init := LeanExe.build kU fun i => xs[i.toNat]!)
    (f := fun t r => r.set! (scale us[t.toNat]! (kU + t + 1)).toNat xs[(kU + t).toNat]!)
    (P := fun s r => r.size = k ∧
      reservoirFrom us k (k + s) r.toList (xs.toList.drop (k + s)) =
        reservoirFrom us k k (xs.toList.take k) (xs.toList.drop k))
    ⟨by rw [build_size, hkU], by rw [build_toList xs kU (by omega), hkU, Nat.add_zero]⟩
    (by
      intro s r hs' ⟨hsz, heq⟩
      rw [hcount] at hs'
      have hss : (UInt64.ofNat s).toNat = s := word_toNat (by omega)
      have hks : (kU + UInt64.ofNat s).toNat = k + s := by
        simp only [UInt64.toNat_add, hkU, hss]; omega
      have hks1 : (kU + UInt64.ofNat s + 1).toNat = k + s + 1 := by
        simp only [UInt64.toNat_add, hkU, hss, UInt64.reduceToNat]; omega
      have hdrop : xs.toList.drop (k + s) =
          xs.toList[k + s]'(by simp; omega) :: xs.toList.drop (k + s + 1) :=
        List.drop_eq_getElem_cons (by simp; omega)
      have hx : xs[k + s]! = xs.toList[k + s]'(by simp; omega) := by
        rw [getElem!_pos xs (k + s) (by omega), Array.getElem_toList]
      have hM : (scale us[s]! (kU + UInt64.ofNat s + 1)).toNat =
          us[k + s - k]!.toNat * (k + s + 1) / 2 ^ 64 := by
        rw [scale_toNat _ _ (by rw [hks1]; omega), hks1, Nat.add_sub_cancel_left]
      refine ⟨by rw [Array.size_set!, hsz], ?_⟩
      rw [hss, hks, hx, hM, Array.toList_set!, ← heq, hdrop, reservoirFrom, Nat.add_assoc])
  rw [hcount] at h
  obtain ⟨-, heq⟩ := h
  generalize LeanExe.loop _ _ _ = r at heq ⊢
  rw [show k + (xs.size - k) = xs.size by omega, List.drop_of_length_le (by simp)] at heq
  rw [← heq, show reservoirFrom us k xs.size r.toList [] = r.toList from rfl, Array.toArray_toList]

/-! ### The candidates -/

theorem set_subperm (r : List UInt64) (i : Nat) (x : UInt64) : (r.set i x).Subperm (r ++ [x]) := by
  by_cases hi : i < r.length
  · rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
    have h1 : r.take i ++ r[i] :: r.drop (i + 1) = r := by
      rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    have hr : r ++ [x] = r.take i ++ r[i] :: (r.drop (i + 1) ++ [x]) :=
      calc r ++ [x] = (r.take i ++ r[i] :: r.drop (i + 1)) ++ [x] := by rw [h1]
        _ = r.take i ++ r[i] :: (r.drop (i + 1) ++ [x]) := by
          rw [List.append_assoc, List.cons_append]
    rw [hr]
    have hp : (r.take i ++ x :: r.drop (i + 1)).Perm (r.take i ++ (r.drop (i + 1) ++ [x])) :=
      List.Perm.append_left _ (List.perm_append_singleton _ _).symm
    exact hp.subperm.trans
      ((List.Sublist.append_left (List.sublist_cons_self _ _) _).subperm)
  · rw [List.set_eq_of_length_le (by omega)]
    exact (List.sublist_append_left _ _).subperm

theorem reservoirFrom_subperm (us : Array UInt64) (k : Nat) :
    ∀ (t : Nat) (r l : List UInt64), (reservoirFrom us k t r l).Subperm (r ++ l)
  | _, r, [] => by rw [List.append_nil]; exact List.Subperm.refl _
  | t, r, x :: rest => by
    rw [reservoirFrom]
    refine (reservoirFrom_subperm us k (t + 1) _ rest).trans ?_
    have := List.Subperm.append (set_subperm r (us[t - k]!.toNat * (t + 1) / 2 ^ 64) x)
      (List.Perm.refl rest).subperm
    rwa [List.append_assoc, List.singleton_append] at this

theorem reservoirFrom_length (us : Array UInt64) (k : Nat) :
    ∀ (t : Nat) (r l : List UInt64), (reservoirFrom us k t r l).length = r.length
  | _, _, [] => rfl
  | t, r, x :: rest => by rw [reservoirFrom, reservoirFrom_length us k (t + 1), List.length_set]

theorem reservoirFrom_map (us : Array UInt64) (k : Nat) (g : UInt64 → UInt64) :
    ∀ (t : Nat) (r l : List UInt64),
      reservoirFrom us k t (r.map g) (l.map g) = (reservoirFrom us k t r l).map g
  | _, _, [] => rfl
  | t, r, x :: rest => by
    rw [List.map_cons, reservoirFrom, reservoirFrom, ← List.map_set,
      reservoirFrom_map us k g (t + 1)]

/-! ### Counting the word arrays -/

/-- The word arrays of `L + 1` words split into their first `L` words and their last word. -/
theorem card_snoc_sum {L : Nat} (P : (Fin L → UInt64) → UInt64 → Prop)
    [∀ w u, Decidable (P w u)] :
    (Finset.univ.filter fun w : Fin (L + 1) → UInt64 => P (Fin.init w) (w (Fin.last L))).card =
      ∑ w' : Fin L → UInt64, (Finset.univ.filter fun u => P w' u).card := by
  have h1 : (Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
      P (Fin.init w) (w (Fin.last L))).card =
      (Finset.univ.filter fun p : (Fin L → UInt64) × UInt64 => P p.1 p.2).card := by
    refine Finset.card_equiv
      ((Fin.snocEquiv fun _ => UInt64).symm.trans (Equiv.prodComm _ _)) fun w => ?_
    simp [Fin.snocEquiv]
  rw [h1, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  exact Finset.sum_congr rfl fun w' _ => (Finset.card_filter _ _).symm

/-- The word arrays of `L + 1` words whose last word satisfies `P` and whose first `L` words
satisfy `Q` number `|P| · |Q|`. -/
theorem card_snoc_split {L : Nat} (P : UInt64 → Prop) (Q : (Fin L → UInt64) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter fun w : Fin (L + 1) → UInt64 => P (w (Fin.last L)) ∧ Q (Fin.init w)).card =
      (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [card_snoc_sum (fun w' u => P u ∧ Q w')]
  have h : ∀ w' : Fin L → UInt64, (Finset.univ.filter fun u => P u ∧ Q w').card =
      if Q w' then (Finset.univ.filter P).card else 0 := fun w' => by
    split <;> rename_i hq <;> simp [hq]
  rw [Finset.sum_congr rfl fun w' _ => h w', Finset.sum_ite, Finset.sum_const_zero, Nat.add_zero,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem reservoirFrom_snoc (us : Array UInt64) (k : Nat) :
    ∀ (t : Nat) (r l : List UInt64) (x : UInt64),
      reservoirFrom us k t r (l ++ [x]) =
        (reservoirFrom us k t r l).set
          (us[t + l.length - k]!.toNat * (t + l.length + 1) / 2 ^ 64) x
  | t, r, [], x => by simp [reservoirFrom]
  | t, r, y :: rest, x => by
    rw [List.cons_append, reservoirFrom, reservoirFrom, reservoirFrom_snoc us k (t + 1)]
    simp only [List.length_cons]
    rw [show t + 1 + rest.length = t + (rest.length + 1) by omega]

theorem reservoirFrom_congr (us us' : Array UInt64) (k : Nat) :
    ∀ (t : Nat) (r l : List UInt64), (∀ i, t ≤ i → i < t + l.length → us[i - k]! = us'[i - k]!) →
      reservoirFrom us k t r l = reservoirFrom us' k t r l
  | _, _, [], _ => rfl
  | t, r, x :: rest, h => by
    rw [reservoirFrom, reservoirFrom, h t le_rfl (by simp)]
    exact reservoirFrom_congr us us' k (t + 1) _ rest fun i h1 h2 => h i (by omega) (by simp; omega)

/-- The records `k, …, k + L - 1` of the positions. -/
def later (k L : Nat) : List UInt64 :=
  (List.range L).map fun i => UInt64.ofNat (k + i)

/-- The candidates after the `L` records that follow the first `k` positions, with the words `w`. -/
def cands (k L : Nat) (w : Fin L → UInt64) : List UInt64 :=
  reservoirFrom (Array.ofFn w) k k ((List.range k).map UInt64.ofNat) (later k L)

theorem cands_succ (k L : Nat) (w : Fin (L + 1) → UInt64) :
    cands k (L + 1) w =
      (cands k L (Fin.init w)).set ((w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64)
        (UInt64.ofNat (k + L)) := by
  have hlen : (later k L).length = L := by simp [later]
  have hl : later k (L + 1) = later k L ++ [UInt64.ofNat (k + L)] := by
    simp [later, List.range_succ]
  unfold cands
  rw [hl, reservoirFrom_snoc, hlen, show k + L - k = L by omega,
    getElem!_pos (Array.ofFn w) L (by simp), Array.getElem_ofFn]
  congr 1
  · refine reservoirFrom_congr _ _ k k _ _ fun i h1 h2 => ?_
    rw [hlen] at h2
    rw [getElem!_pos (Array.ofFn w) (i - k) (by simp; omega), Array.getElem_ofFn,
      getElem!_pos (Array.ofFn (Fin.init w)) (i - k) (by simp; omega), Array.getElem_ofFn]
    rfl

theorem mem_set_nodup {r : List UInt64} (hr : r.Nodup) {M : Nat} (hM : M < r.length)
    (p x : UInt64) :
    x ∈ r.set M p ↔ (x ∈ r ∧ x ≠ r[M]) ∨ x = p := by
  rw [List.mem_iff_getElem, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.length_set] at hi
    by_cases h : M = i
    · right; simp [h]
    · left
      rw [List.getElem_set_ne h]
      refine ⟨⟨i, hi, rfl⟩, fun he => h ?_⟩
      exact ((List.Nodup.getElem_inj_iff hr).mp he).symm
  · rintro (⟨⟨i, hi, rfl⟩, hne⟩ | rfl)
    · refine ⟨i, by simpa using hi, ?_⟩
      have : M ≠ i := fun h => hne (by simp [h])
      rw [List.getElem_set_ne this]
    · exact ⟨M, by simpa using hM, by simp⟩

/-- The candidates are `k` distinct positions below `k + L`. -/
theorem cands_inv (k : Nat) :
    ∀ (L : Nat) (w : Fin L → UInt64), k + L < 2 ^ 64 →
      (cands k L w).length = k ∧ (cands k L w).Nodup ∧ ∀ x ∈ cands k L w, x.toNat < k + L
  | 0, w, h => by
    have : cands k 0 w = (List.range k).map UInt64.ofNat := rfl
    rw [this]
    refine ⟨by simp, ?_, fun x hx => ?_⟩
    · apply List.Nodup.map_on _ List.nodup_range
      intro a ha b hb hab
      have := congrArg UInt64.toNat hab
      rw [word_toNat (by simp at ha; omega), word_toNat (by simp at hb; omega)] at this
      exact this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [word_toNat (by simp at hi; omega)]; simpa using hi
  | L + 1, w, h => by
    obtain ⟨hlen, hnd, hlt⟩ := cands_inv k L (Fin.init w) (by omega)
    rw [cands_succ]
    set M := (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64
    have hp : (UInt64.ofNat (k + L)).toNat = k + L := word_toNat (by omega)
    have hpn : UInt64.ofNat (k + L) ∉ cands k L (Fin.init w) := fun hm => by
      have := hlt _ hm; omega
    refine ⟨by rw [List.length_set, hlen], ?_, fun x hx => ?_⟩
    · exact List.Nodup.set hnd hpn
    · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · have := hlt x hx; omega
      · omega

/-- After `L` records, every set of `k` positions below `k + L` comes from between
`L! ∏ ⌊2^64 / (t + 1)⌋` and `L! ∏ ⌈2^64 / (t + 1)⌉` word arrays, the products over `t` from `k`
to `k + L - 1`. -/
theorem cands_count (k : Nat) :
    ∀ (L : Nat) (T : Finset UInt64), k + L < 2 ^ 32 → T.card = k → (∀ x ∈ T, x.toNat < k + L) →
      L.factorial * ∏ t ∈ Finset.Ico k (k + L), 2 ^ 64 / (t + 1) ≤
          (Finset.univ.filter fun w : Fin L → UInt64 => (cands k L w).toFinset = T).card ∧
        (Finset.univ.filter fun w : Fin L → UInt64 => (cands k L w).toFinset = T).card ≤
          L.factorial * ∏ t ∈ Finset.Ico k (k + L), (2 ^ 64 + t) / (t + 1)
  | 0, T, hk, hT, hlt => by
    have hnd : ((List.range k).map UInt64.ofNat).Nodup := (cands_inv k 0 Fin.elim0 (by omega)).2.1
    have hS : T = ((List.range k).map UInt64.ofNat).toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨x.toNat, List.mem_range.mpr (by have := hlt x hx; omega), UInt64.ofNat_toNat⟩
      · rw [hT, List.toFinset_card_of_nodup hnd]
        simp
    have hset : (Finset.univ.filter fun w : Fin 0 → UInt64 => (cands k 0 w).toFinset = T) =
        Finset.univ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [hS]
      rfl
    rw [hset, Finset.card_univ]
    simp
  | L + 1, T, hk, hT, hlt => by
    have hpt : (UInt64.ofNat (k + L)).toNat = k + L := word_toNat (by omega)
    have hprod : ∀ g : Nat → Nat, ∏ s ∈ Finset.Ico k (k + (L + 1)), g s =
        (∏ s ∈ Finset.Ico k (k + L), g s) * g (k + L) := fun g => by
      rw [show k + (L + 1) = k + L + 1 by omega]
      exact Finset.prod_Ico_succ_top (by omega) g
    have hfact : (L + 1).factorial = (L + 1) * L.factorial := Nat.factorial_succ L
    have hinv : ∀ w' : Fin L → UInt64, (cands k L w').length = k ∧ (cands k L w').Nodup ∧
        ∀ x ∈ cands k L w', x.toNat < k + L := fun w' => cands_inv k L w' (by omega)
    have hpn : ∀ w' : Fin L → UInt64, UInt64.ofNat (k + L) ∉ cands k L w' := fun w' h => by
      have := (hinv w').2.2 _ h; omega
    by_cases hpT : UInt64.ofNat (k + L) ∈ T
    · -- the last record is among the candidates: it replaced one word `e` outside `T`
      set p := UInt64.ofNat (k + L) with hp
      set E := (Finset.range (k + L)).image UInt64.ofNat \ T with hE
      have hk1 : 1 ≤ k := by
        rw [← hT]; exact Finset.card_pos.mpr ⟨p, hpT⟩
      have hEcard : E.card = L + 1 := by
        have hinj : Set.InjOn UInt64.ofNat (Finset.range (k + L) : Set Nat) :=
          fun a ha b hb hab => by
          have := congrArg UInt64.toNat hab
          rw [word_toNat (by simp at ha; omega), word_toNat (by simp at hb; omega)] at this
          exact this
        have himg : ((Finset.range (k + L)).image UInt64.ofNat).card = k + L := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
        have hinter : (Finset.range (k + L)).image UInt64.ofNat ∩ T = T.erase p := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_range, Finset.mem_erase]
          constructor
          · rintro ⟨⟨j, hj, rfl⟩, hx⟩
            refine ⟨fun h => ?_, hx⟩
            have := congrArg UInt64.toNat h
            rw [word_toNat (by omega), hpt] at this
            omega
          · rintro ⟨hne, hx⟩
            refine ⟨⟨x.toNat, ?_, UInt64.ofNat_toNat⟩, hx⟩
            have h1 := hlt x hx
            have h2 : x.toNat ≠ k + L := fun h => hne (UInt64.toNat_inj.mp (by rw [h, hpt]))
            omega
        have := Finset.card_sdiff_add_card_inter ((Finset.range (k + L)).image UInt64.ofNat) T
        rw [hinter, Finset.card_erase_of_mem hpT, hT, himg] at this
        rw [hE]
        omega
      have hmem : ∀ w : Fin (L + 1) → UInt64, (cands k (L + 1) w).toFinset = T →
          (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64 < k := fun w h => by
        by_contra hM
        rw [cands_succ, List.set_eq_of_length_le (by rw [(hinv _).1]; omega)] at h
        have : p ∈ (cands k L (Fin.init w)).toFinset := h ▸ hpT
        exact hpn _ (List.mem_toFinset.mp this)
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun w : Fin (L + 1) → UInt64 =>
          (cands k L (Fin.init w))[(w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64]!) (t := E)
        (fun w hw => by
          replace hw := (Finset.mem_filter.mp hw).2
          have hM := hmem w hw
          obtain ⟨hlen, hnd, hlt'⟩ := hinv (Fin.init w)
          simp only [Finset.mem_coe]
          have hMr : (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64 <
              (cands k L (Fin.init w)).length := by
            omega
          rw [getElem!_pos (cands k L (Fin.init w)) _ hMr]
          have he := hlt' _ (List.getElem_mem hMr)
          rw [hE, Finset.mem_sdiff, Finset.mem_image]
          refine ⟨⟨_, Finset.mem_range.mpr he, UInt64.ofNat_toNat⟩, fun hT' => ?_⟩
          rw [← hw, cands_succ, List.mem_toFinset, mem_set_nodup hnd (by omega)] at hT'
          rcases hT' with ⟨-, hne⟩ | h
          · exact hne rfl
          · have := congrArg UInt64.toNat h; rw [hpt] at this; omega)]
      have hfib : ∀ e ∈ E,
          ((Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
              (cands k (L + 1) w).toFinset = T).filter
            fun w => (cands k L (Fin.init w))[(w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64]! = e) =
          Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
            (cands k L (Fin.init w)).toFinset = insert e (T.erase p) ∧
              (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64 = (cands k L (Fin.init w)).idxOf e :=
          fun e he => by
        rw [hE, Finset.mem_sdiff] at he
        ext w
        simp only [Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨hlen, hnd, hlt'⟩ := hinv (Fin.init w)
        set r := cands k L (Fin.init w)
        set M := (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64
        constructor
        · rintro ⟨h, hfe⟩
          have hM := hmem w h
          rw [getElem!_pos r M (by omega)] at hfe
          rw [cands_succ] at h
          refine ⟨?_, by rw [← hfe, List.Nodup.idxOf_getElem hnd]⟩
          ext x
          rw [List.mem_toFinset, Finset.mem_insert, Finset.mem_erase, ← h, List.mem_toFinset,
            mem_set_nodup hnd (by omega)]
          constructor
          · intro hx
            by_cases hxe : x = e
            · exact Or.inl hxe
            · exact Or.inr ⟨fun hxp => hpn _ (hxp ▸ hx), Or.inl ⟨hx, by rw [hfe]; exact hxe⟩⟩
          · rintro (rfl | ⟨hxp, (⟨hx, -⟩ | rfl)⟩)
            · rw [← hfe]; exact List.getElem_mem _
            · exact hx
            · exact absurd rfl hxp
        · rintro ⟨h, hidx⟩
          have hem : e ∈ r := List.mem_toFinset.mp (h ▸ Finset.mem_insert_self e _)
          have hlt2 : r.idxOf e < r.length := List.idxOf_lt_length_of_mem hem
          have hre : r[M]'(by omega) = e := by
            simp only [hidx]; exact List.getElem_idxOf hlt2
          refine ⟨?_, by rw [getElem!_pos r M (by omega)]; exact hre⟩
          rw [cands_succ]
          ext x
          rw [List.mem_toFinset, mem_set_nodup hnd (by omega), hre]
          have hxr : x ∈ r ↔ x = e ∨ (x ≠ p ∧ x ∈ T) := by
            rw [← List.mem_toFinset, h, Finset.mem_insert, Finset.mem_erase]
          rw [hxr]
          constructor
          · rintro (⟨(rfl | ⟨-, hx⟩), hne⟩ | rfl)
            · exact absurd rfl hne
            · exact hx
            · exact hpT
          · intro hx
            by_cases hxp : x = p
            · exact Or.inr hxp
            · exact Or.inl ⟨Or.inr ⟨hxp, hx⟩, fun hxe => he.2 (hxe ▸ hx)⟩
      have hcount : ∀ e ∈ E,
          L.factorial * (∏ s ∈ Finset.Ico k (k + L), 2 ^ 64 / (s + 1)) * (2 ^ 64 / (k + L + 1)) ≤
            ((Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
              (cands k (L + 1) w).toFinset = T).filter fun w =>
                (cands k L (Fin.init w))[(w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64]! = e).card ∧
            ((Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
              (cands k (L + 1) w).toFinset = T).filter fun w =>
                (cands k L (Fin.init w))[(w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64]! = e).card ≤
              L.factorial * (∏ s ∈ Finset.Ico k (k + L), (2 ^ 64 + s) / (s + 1)) *
                ((2 ^ 64 + (k + L + 1) - 1) / (k + L + 1)) := fun e he => by
        rw [hfib e he, card_snoc_sum (fun w' u => (cands k L w').toFinset = insert e (T.erase p) ∧
          u.toNat * (k + L + 1) / 2 ^ 64 = (cands k L w').idxOf e)]
        have hsplit : ∀ w' : Fin L → UInt64, (Finset.univ.filter fun u : UInt64 =>
            (cands k L w').toFinset = insert e (T.erase p) ∧
              u.toNat * (k + L + 1) / 2 ^ 64 = (cands k L w').idxOf e).card =
            if (cands k L w').toFinset = insert e (T.erase p) then
              (fiber (k + L + 1) ((cands k L w').idxOf e)).card else 0 := fun w' => by
          split <;> rename_i hq <;> simp [fiber, hq]
        rw [Finset.sum_congr rfl fun w' _ => hsplit w', ← Finset.sum_filter]
        rw [hE, Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨j, hj, rfl⟩, heT⟩ := he
        rw [Finset.mem_range] at hj
        have hTe : (insert (UInt64.ofNat j) (T.erase p)).card = k := by
          rw [Finset.card_insert_of_notMem (fun h => heT (Finset.mem_of_mem_erase h)),
            Finset.card_erase_of_mem hpT, hT]
          omega
        have hTlt : ∀ x ∈ insert (UInt64.ofNat j) (T.erase p), x.toNat < k + L := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · rw [word_toNat (by omega)]; exact hj
          · have h1 := hlt x (Finset.mem_of_mem_erase hx)
            have h2 : x ≠ p := Finset.ne_of_mem_erase hx
            have h3 : x.toNat ≠ k + L := fun h => h2 (UInt64.toNat_inj.mp (by rw [h, hpt]))
            omega
        have hB := cands_count k L (insert (UInt64.ofNat j) (T.erase p)) (by omega) hTe hTlt
        have hfb : ∀ w' ∈ Finset.univ.filter fun w' : Fin L → UInt64 =>
            (cands k L w').toFinset = insert (UInt64.ofNat j) (T.erase p),
            2 ^ 64 / (k + L + 1) ≤
                (fiber (k + L + 1) ((cands k L w').idxOf (UInt64.ofNat j))).card ∧
              (fiber (k + L + 1) ((cands k L w').idxOf (UInt64.ofNat j))).card ≤
                (2 ^ 64 + (k + L + 1) - 1) / (k + L + 1) := fun w' hw' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw'
          have hem : UInt64.ofNat j ∈ cands k L w' :=
            List.mem_toFinset.mp (hw' ▸ Finset.mem_insert_self _ _)
          have := List.idxOf_lt_length_of_mem hem
          rw [(hinv w').1] at this
          exact fiber_card (k + L + 1) _ (by omega) (by omega) (by omega)
        constructor
        · calc L.factorial * (∏ s ∈ Finset.Ico k (k + L), 2 ^ 64 / (s + 1)) * (2 ^ 64 / (k + L + 1))
              ≤ (Finset.univ.filter fun w' : Fin L → UInt64 =>
                  (cands k L w').toFinset = insert (UInt64.ofNat j) (T.erase p)).card *
                (2 ^ 64 / (k + L + 1)) := Nat.mul_le_mul_right _ hB.1
            _ = ∑ _w' ∈ Finset.univ.filter fun w' : Fin L → UInt64 =>
                  (cands k L w').toFinset = insert (UInt64.ofNat j) (T.erase p),
                (2 ^ 64 / (k + L + 1)) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum fun w' hw' => (hfb w' hw').1
        · calc _ ≤ ∑ _w' ∈ Finset.univ.filter fun w' : Fin L → UInt64 =>
                  (cands k L w').toFinset = insert (UInt64.ofNat j) (T.erase p),
                ((2 ^ 64 + (k + L + 1) - 1) / (k + L + 1)) :=
              Finset.sum_le_sum fun w' hw' => (hfb w' hw').2
            _ = (Finset.univ.filter fun w' : Fin L → UInt64 =>
                  (cands k L w').toFinset = insert (UInt64.ofNat j) (T.erase p)).card *
                ((2 ^ 64 + (k + L + 1) - 1) / (k + L + 1)) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ _ := Nat.mul_le_mul_right _ hB.2
      rw [hprod, hprod, hfact]
      constructor
      · calc (L + 1) * L.factorial *
              ((∏ s ∈ Finset.Ico k (k + L), 2 ^ 64 / (s + 1)) * (2 ^ 64 / (k + L + 1)))
            = ∑ _e ∈ E, L.factorial * (∏ s ∈ Finset.Ico k (k + L), 2 ^ 64 / (s + 1)) *
                (2 ^ 64 / (k + L + 1)) := by rw [Finset.sum_const, smul_eq_mul, hEcard]; ring
          _ ≤ _ := Finset.sum_le_sum fun e he => (hcount e he).1
      · calc _ ≤ ∑ _e ∈ E, L.factorial * (∏ s ∈ Finset.Ico k (k + L), (2 ^ 64 + s) / (s + 1)) *
                ((2 ^ 64 + (k + L + 1) - 1) / (k + L + 1)) :=
              Finset.sum_le_sum fun e he => (hcount e he).2
          _ = _ := by
            rw [Finset.sum_const, smul_eq_mul, hEcard,
              show 2 ^ 64 + (k + L + 1) - 1 = 2 ^ 64 + (k + L) by omega]
            ring
    · -- the last record is not among the candidates: its index is `k` or more
      have hT' : ∀ x ∈ T, x.toNat < k + L := fun x hx => by
        have h1 := hlt x hx
        have h2 : x.toNat ≠ k + L := fun h => hpT (by
          rw [← UInt64.toNat_inj.mp (show x.toNat = (UInt64.ofNat (k + L)).toNat by rw [h, hpt])]
          exact hx)
        omega
      have hset : (Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
          (cands k (L + 1) w).toFinset = T) =
          Finset.univ.filter fun w : Fin (L + 1) → UInt64 =>
            ¬ (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64 < k ∧
              (cands k L (Fin.init w)).toFinset = T := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨hlen, hnd, -⟩ := hinv (Fin.init w)
        rw [cands_succ]
        by_cases hM : (w (Fin.last L)).toNat * (k + L + 1) / 2 ^ 64 < k
        · simp only [hM, not_true_eq_false, false_and, iff_false]
          intro h
          apply hpT
          rw [← h, List.mem_toFinset, mem_set_nodup hnd (by omega)]
          exact Or.inr rfl
        · rw [List.set_eq_of_length_le (by omega)]
          exact ⟨fun h => ⟨hM, h⟩, fun h => h.2⟩
      rw [hset, card_snoc_split (fun u => ¬ u.toNat * (k + L + 1) / 2 ^ 64 < k)
        (fun v => (cands k L v).toFinset = T)]
      have hA := values_card (k + L + 1) (by omega) (by omega) (Finset.Ico k (k + L + 1))
        (fun i hi => (Finset.mem_Ico.mp hi).2) (fun i => ¬ i < k)
        (fun i hi => by simp only [Finset.mem_Ico]; omega)
      rw [Nat.card_Ico, show k + L + 1 - k = L + 1 by omega] at hA
      have hB := cands_count k L T (by omega) hT hT'
      rw [hprod, hprod, hfact]
      constructor
      · calc (L + 1) * L.factorial *
              ((∏ s ∈ Finset.Ico k (k + L), 2 ^ 64 / (s + 1)) * (2 ^ 64 / (k + L + 1)))
            = ((L + 1) * (2 ^ 64 / (k + L + 1))) *
                (L.factorial * ∏ s ∈ Finset.Ico k (k + L), 2 ^ 64 / (s + 1)) := by ring
          _ ≤ _ := Nat.mul_le_mul hA.1 hB.1
      · calc _ ≤ ((L + 1) * ((2 ^ 64 + (k + L + 1) - 1) / (k + L + 1))) *
                (L.factorial * ∏ s ∈ Finset.Ico k (k + L), (2 ^ 64 + s) / (s + 1)) :=
              Nat.mul_le_mul hA.2 hB.2
          _ = _ := by rw [show 2 ^ 64 + (k + L + 1) - 1 = 2 ^ 64 + (k + L) by omega]; ring

/-! ### The specification -/

theorem iota_toList (N : Nat) : (iota N).toList = (List.range N).map UInt64.ofNat := by
  apply List.ext_getElem (by simp [iota])
  intro i h1 h2
  simp [iota]

theorem iota_take (N k : Nat) (hk : k ≤ N) :
    (iota N).toList.take k = (List.range k).map UInt64.ofNat := by
  rw [iota_toList, ← List.map_take, List.take_range, Nat.min_eq_left hk]

theorem iota_drop (N k : Nat) :
    (iota N).toList.drop k = later k ((iota N).size - k) := by
  apply List.ext_getElem (by simp [later, iota])
  intro i h1 h2
  simp [iota_toList, later]

theorem reservoir_spec : Reservoirs reservoir where
  method us xs n hs := reservoir_eq us xs n hs
  contents us xs n hs := by
    rw [reservoir_eq us xs n hs, algorithmR]
    refine ⟨?_, ?_⟩
    · rw [List.toList_toArray]
      have := reservoirFrom_subperm us (min n.toNat xs.size) (min n.toNat xs.size)
        (xs.toList.take (min n.toNat xs.size)) (xs.toList.drop (min n.toNat xs.size))
      rwa [List.take_append_drop] at this
    · rw [List.size_toArray, reservoirFrom_length, List.length_take]
      simp
  positions us xs n hs := by
    have hi : (iota xs.size).size = xs.size := Array.size_ofFn
    have hx : xs.toList = (iota xs.size).toList.map fun p => xs[p.toNat]! := by
      rw [← Array.toList_map, iota_map xs (by omega)]
    rw [reservoir_eq us xs n hs, reservoir_eq us (iota xs.size) n (by omega), algorithmR,
      algorithmR, hi, hx, ← List.map_take, ← List.map_drop, reservoirFrom_map]
    apply Array.toList_inj.mp
    simp
  count N n ps hN hn hps hlen := by
    have hi : (iota N).size = N := Array.size_ofFn
    have hk : min n.toNat (iota N).size = n.toNat := by rw [hi]; exact Nat.min_eq_left hn
    have hpsnd : ps.Nodup := (iota_nodup N (by omega)).sublist hps
    have hpslt : ∀ x ∈ ps.toFinset,
        x.toNat < min n.toNat (iota N).size + ((iota N).size - min n.toNat (iota N).size) :=
      fun x hx => by
        rw [List.mem_toFinset] at hx
        have := hps.subset hx
        rw [iota_toList, List.mem_map] at this
        obtain ⟨i, hi', rfl⟩ := this
        rw [word_toNat (by simp at hi'; omega), hk, hi]
        simp at hi'
        omega
    have hset : keepsTo reservoir (iota N) n ps =
        Finset.univ.filter fun w : Fin ((iota N).size - min n.toNat (iota N).size) → UInt64 =>
          (cands (min n.toNat (iota N).size) ((iota N).size - min n.toNat (iota N).size)
            w).toFinset =
            ps.toFinset := by
      ext w
      simp only [keepsTo, Finset.mem_filter, Finset.mem_univ, true_and]
      have hres : (reservoir (Array.ofFn w) (iota N) n).toList =
          cands (min n.toNat (iota N).size) ((iota N).size - min n.toNat (iota N).size) w := by
        rw [reservoir_eq _ _ n (by rw [hi]; omega), algorithmR, List.toList_toArray,
          iota_take N _ (by rw [hk]; exact hn), iota_drop]
        rfl
      rw [hres]
      have hcnd := (cands_inv (min n.toNat (iota N).size)
        ((iota N).size - min n.toNat (iota N).size) w (by rw [hk, hi]; omega)).2.1
      rw [List.perm_ext_iff_of_nodup hcnd hpsnd, Finset.ext_iff]
      simp only [List.mem_toFinset]
    have e1 : fewestR N n.toNat =
        ((iota N).size - min n.toNat (iota N).size).factorial *
          ∏ t ∈ Finset.Ico (min n.toNat (iota N).size)
            (min n.toNat (iota N).size + ((iota N).size - min n.toNat (iota N).size)),
            2 ^ 64 / (t + 1) := by
      rw [hk, hi, show n.toNat + (N - n.toNat) = N by omega]; rfl
    have e2 : mostR N n.toNat =
        ((iota N).size - min n.toNat (iota N).size).factorial *
          ∏ t ∈ Finset.Ico (min n.toNat (iota N).size)
            (min n.toNat (iota N).size + ((iota N).size - min n.toNat (iota N).size)),
            (2 ^ 64 + t) / (t + 1) := by
      rw [hk, hi, show n.toNat + (N - n.toNat) = N by omega]; rfl
    rw [hset, e1, e2]
    exact cands_count _ _ ps.toFinset (by rw [hk, hi]; omega)
      (by rw [List.toFinset_card_of_nodup hpsnd, hlen, hk]) hpslt

end Library.Random.Sampling
