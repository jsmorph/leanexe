import Demos.OrderBook.Invariant

/-! The stream theorems of [the program](Program.lean): a stream run in two parts gives the book and
the event words of one run, and the refinement of every step gives the refinement of `run`. -/

namespace Demos.OrderBook.Refinement

open Program (Book)
open Abstract

namespace StreamLemmas

/-! ## Words and offsets -/

/-- A stream's size as a word converts back to the size when the size lies below 2^64. -/
theorem toNat_size (ws : Array UInt64) (h : ws.size < 2 ^ 64) :
    ws.size.toUInt64.toNat = ws.size := by
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The loop count of `run` on a stream is the number of its records. -/
theorem count_toNat (ws : Array UInt64) (h : ws.size + 6 < 2 ^ 64) :
    ((ws.size.toUInt64 + 6) / 7).toNat = (ws.size + 6) / 7 := by
  rw [UInt64.toNat_div, UInt64.toNat_add, toNat_size ws (by omega)]
  simp [Nat.mod_eq_of_lt h]

/-- The position of word `k` of the record at offset `7 * i`, as a word, converts back to
`7 * i + k` when that lies below 2^64. -/
theorem toNat_offset (i : Nat) (k : UInt64) (h : 7 * i + k.toNat < 2 ^ 64) :
    (7 * UInt64.ofNat i + k).toNat = 7 * i + k.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega : 7 * i < 2 ^ 64), Nat.mod_eq_of_lt h]

/-- The offset `7 * i` as a word converts back to `7 * i` when that lies below 2^64. -/
theorem toNat_seven_mul (i : Nat) (h : 7 * i < 2 ^ 64) :
    (7 * UInt64.ofNat i).toNat = 7 * i := by
  simpa using toNat_offset i 0 (by simpa using h)

/-- The test of `step` for a short record at offset `o` compares the number of words from `o` to
the end with seven. -/
theorem short_iff (ws : Array UInt64) (o : UInt64) (h : o.toNat ≤ ws.size)
    (hs : ws.size < 2 ^ 64) : ws.size.toUInt64 - o < 7 ↔ ws.size - o.toNat < 7 := by
  have hle : o ≤ ws.size.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, toNat_size ws hs]
    exact h
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ hle, toNat_size ws hs]
  simp

/-- A word of the first part of two streams is the word of the first stream. -/
theorem getElem!_append_left {xs ys : Array UInt64} {i : Nat} (h : i < xs.size) :
    (xs ++ ys)[i]! = xs[i]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp; omega), getElem!_pos xs i h,
    Array.getElem_append_left h]

/-- A word of the second part of two streams is the word of the second stream. -/
theorem getElem!_append_right {xs ys : Array UInt64} {i : Nat} :
    (xs ++ ys)[xs.size + i]! = ys[i]! := by
  by_cases h : i < ys.size
  · rw [getElem!_pos (xs ++ ys) _ (by simp; omega), getElem!_pos ys i h,
      Array.getElem_append_right (by omega)]
    simp
  · rw [getElem!_neg (xs ++ ys) _ (by simp; omega), getElem!_neg ys i h]

/-! ## Steps -/

/-- `run` is the loop of `step` over the book and the event words, from no event words. -/
theorem run_eq_loop (b : Book) (ws : Array UInt64) :
    Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws =
      LeanExe.loop ((ws.size.toUInt64 + 6) / 7) (b, (#[] : Array UInt64))
        fun i s => Program.step s.1 s.2 ws (7 * i) := rfl

/-- Two steps on one book and event words agree when their short-record tests agree and the seven
words of their records agree. -/
theorem step_congr (b : Book) (out ws ws' : Array UInt64) (o o' : UInt64)
    (hlt : ws.size.toUInt64 - o < 7 ↔ ws'.size.toUInt64 - o' < 7)
    (hw : ∀ k : UInt64, k.toNat < 7 → Program.word ws o k = Program.word ws' o' k) :
    Program.step b out ws o = Program.step b out ws' o' := by
  unfold Program.step
  by_cases h : ws.size.toUInt64 - o < 7
  · rw [ite_eq_left h, ite_eq_left (hlt.1 h)]
  · rw [ite_eq_right h, ite_eq_right (mt hlt.2 h), hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw 6 (by decide)]

/-- `emit` appends the seven words of an event. -/
theorem emit_eq (out : Array UInt64) (w0 w1 w2 w3 w4 w5 w6 : UInt64) :
    Program.emit out w0 w1 w2 w3 w4 w5 w6 = out ++ #[w0, w1, w2, w3, w4, w5, w6] := by
  apply Array.toList_inj.1
  simp [Program.emit]

/-- A loop of `repeatWhile.go` commutes with a map that keeps the condition and commutes with the
step. -/
theorem go_map {α : Type} (cond : α → Bool) (step φ : α → α)
    (hc : ∀ s, cond (φ s) = cond s) (hs : ∀ s, step (φ s) = φ (step s)) (k : Nat) (s : α) :
    LeanExe.repeatWhile.go cond step k (φ s) = φ (LeanExe.repeatWhile.go cond step k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [LeanExe.repeatWhile.go, hc, hs, ih]
    split <;> rfl

/-- A step of matching on event words `out ++ m.out` gives the step on `m.out` with `out` in front
of its event words. -/
theorem matchStep_append (taker account side : UInt64) (out : Array UInt64)
    (m : Program.Matching) :
    Program.matchStep taker account side { m with out := out ++ m.out } =
      { Program.matchStep taker account side m with
        out := out ++ (Program.matchStep taker account side m).out } := by
  simp only [Program.matchStep]
  split
  · rfl
  · split
    · rfl
    · simp [emit_eq]

/-- Matching from event words `out ++ x` gives matching from `x` with `out` in front of its event
words. -/
theorem fill_append (b : Book) (out x : Array UInt64) (taker account side limit q : UInt64) :
    Program.fill b (out ++ x) taker account side limit q =
      { Program.fill b x taker account side limit q with
        out := out ++ (Program.fill b x taker account side limit q).out } := by
  unfold Program.fill LeanExe.repeatWhile
  exact go_map (fun m => m.rem != 0 && !m.selfTrade && Program.acceptable side limit m.price)
    (fun m => Program.matchStep taker account side m)
    (fun m : Program.Matching => { m with out := out ++ m.out }) (fun _ => rfl)
    (matchStep_append taker account side out) Program.matchFuel.toNat
    ⟨b, x, if side == 0 then 1 else Program.maxPrice, q, false⟩

/-- An accepted order's events follow the event words that it is given. -/
theorem submitArrays_append (oid acct qty lvl nxt head tail : Array UInt64)
    (nextId count : UInt64) (out : Array UInt64) (side limit q account tag tif : UInt64) :
    Program.submitArrays oid acct qty lvl nxt head tail nextId count out side limit q account tag
        tif =
      ((Program.submitArrays oid acct qty lvl nxt head tail nextId count #[] side limit q account
          tag tif).1,
        out ++ (Program.submitArrays oid acct qty lvl nxt head tail nextId count #[] side limit q
          account tag tif).2) := by
  simp only [Program.submitArrays, Program.submit, Program.fillArrays, emit_eq, fill_append,
    Array.empty_append]
  repeat' split
  all_goals simp [Array.append_assoc]

/-- A step's events follow the event words that it is given. -/
theorem step_append (b : Book) (out ws : Array UInt64) (o : UInt64) :
    Program.step b out ws o =
      ((Program.step b #[] ws o).1, out ++ (Program.step b #[] ws o).2) := by
  simp only [Program.step]
  repeat' split
  all_goals first
    | exact submitArrays_append ..
    | simp [Program.reject, Program.cancel, Program.reduce, emit_eq]

/-! ## Loops -/

/-- Two folds whose steps agree below the count give the same state. -/
theorem fold_congr {α : Type} (k : Nat) (f g : Nat → α → α) (init : α)
    (h : ∀ i, i < k → ∀ s, f i s = g i s) :
    Nat.fold k (fun i _ s => f i s) init = Nat.fold k (fun i _ s => g i s) init := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.fold_succ, Nat.fold_succ, h k (by omega), ih (fun i hi => h i (by omega))]

/-- The steps of the second part of two streams, whose first holds `n` whole records, give the
steps on the second stream from no event words, with the earlier event words in front. -/
theorem fold_second (ws₁ ws₂ : Array UInt64) (n : Nat) (hn : ws₁.size = 7 * n)
    (hs : ws₁.size + ws₂.size + 6 < 2 ^ 64) (k : Nat) (hk : k ≤ (ws₂.size + 6) / 7)
    (s : Book × Array UInt64) :
    Nat.fold k (fun i _ s => Program.step s.1 s.2 (ws₁ ++ ws₂) (7 * UInt64.ofNat (n + i))) s =
      ((Nat.fold k (fun i _ s => Program.step s.1 s.2 ws₂ (7 * UInt64.ofNat i)) (s.1, #[])).1,
        s.2 ++ (Nat.fold k (fun i _ s => Program.step s.1 s.2 ws₂ (7 * UInt64.ofNat i))
          (s.1, #[])).2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ih (by omega)]
    generalize Nat.fold k (fun i _ s => Program.step s.1 s.2 ws₂ (7 * UInt64.ofNat i))
      (s.1, #[]) = x
    have h₁ : (7 * UInt64.ofNat (n + k)).toNat = 7 * (n + k) := toNat_seven_mul _ (by omega)
    have h₂ : (7 * UInt64.ofNat k).toNat = 7 * k := toNat_seven_mul _ (by omega)
    have hlt : (ws₁ ++ ws₂).size.toUInt64 - 7 * UInt64.ofNat (n + k) < 7 ↔
        ws₂.size.toUInt64 - 7 * UInt64.ofNat k < 7 := by
      rw [short_iff _ _ (by simp; omega) (by simp; omega), short_iff _ _ (by omega) (by omega), h₁,
        h₂, Array.size_append]
      omega
    have hw : ∀ j : UInt64, j.toNat < 7 →
        Program.word (ws₁ ++ ws₂) (7 * UInt64.ofNat (n + k)) j =
          Program.word ws₂ (7 * UInt64.ofNat k) j := by
      intro j hj
      simp only [Program.word]
      rw [toNat_offset _ _ (by omega), toNat_offset _ _ (by omega),
        show 7 * (n + k) + j.toNat = ws₁.size + (7 * k + j.toNat) by omega,
        getElem!_append_right]
    dsimp only
    rw [step_congr _ _ _ _ _ _ hlt hw, step_append x.1 (s.2 ++ x.2), step_append x.1 x.2]
    simp [Array.append_assoc]

/-! ## Records -/

/-- `records.go` gives the single record of the accumulator followed by the words when together
they hold from one to seven words and the accumulator holds at most six. -/
theorem go_short (l : List UInt64) (acc : Array UInt64) (h : acc.size ≤ 6)
    (h0 : 0 < acc.size + l.length) (h7 : acc.size + l.length ≤ 7) :
    Spec.records.go l acc = [acc ++ l.toArray] := by
  induction l generalizing acc with
  | nil =>
    have he : acc.isEmpty = false := by
      cases he : acc.isEmpty
      · rfl
      · have := Array.isEmpty_iff_size_eq_zero.1 he
        simp at h0
        omega
    simp [Spec.records.go, he]
  | cons w t ih =>
    simp only [Spec.records.go]
    split
    · have ht : t = [] := List.eq_nil_of_length_eq_zero (by simp at h7; omega)
      subst ht
      simp only [Spec.records.go, Array.isEmpty_empty, ite_true]
      rw [Array.push_eq_append]
    · rw [ih (acc.push w) (by simp; omega) (by simp only [Array.size_push]; omega)
        (by simp at h7 ⊢; omega)]
      congr 1
      apply Array.toList_inj.1
      simp

/-- The records of a list of words are its pieces of seven words from offsets 0, 7, 14, and so
on. -/
theorem records_eq_take (l : List UInt64) :
    Spec.records l =
      (List.range ((l.length + 6) / 7)).map fun i => ((l.drop (7 * i)).take 7).toArray := by
  by_cases h : l.length ≤ 7
  · by_cases h0 : l.length = 0
    · rw [List.eq_nil_of_length_eq_zero h0]
      rfl
    · rw [show (l.length + 6) / 7 = 1 by omega, Spec.records,
        go_short l #[] (by simp) (by simp; omega) (by simp; omega)]
      simp [List.take_of_length_le h]
  · conv => lhs; rw [← List.take_append_drop 7 l]
    rw [Spec.records_append _ _ (by simp; omega), records_eq_take (l.drop 7), Spec.records,
      go_short (l.take 7) #[] (by simp) (by simp; omega) (by simp; omega)]
    rw [show (l.length + 6) / 7 = ((l.drop 7).length + 6) / 7 + 1 by simp; omega,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.length_drop, List.cons_append, List.nil_append,
      Array.empty_append, Nat.mul_zero, List.drop_zero, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.drop_drop]
    congr 3
    omega
termination_by l.length
decreasing_by simp; omega

/-- The records of a stream are the records `recordAt ws (7 * i)` below the number of records. -/
theorem records_eq (ws : Array UInt64) :
    Spec.records ws.toList =
      (List.range ((ws.size + 6) / 7)).map fun i => recordAt ws (7 * i) := by
  rw [records_eq_take, Array.length_toList]
  apply List.map_congr_left
  intro i _
  rw [recordAt, ← Array.toArray_toList (xs := ws.extract _ _), Array.toList_extract,
    List.extract_eq_take_drop]
  simp

/-- Folding `encode` from some words gives those words followed by the fold from no words. -/
theorem foldl_encode (es : List Spec.Event) (acc : Array UInt64) :
    es.foldl (fun ws e => ws ++ Spec.encode e) acc =
      acc ++ es.foldl (fun ws e => ws ++ Spec.encode e) #[] := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (#[] ++ _)]
    simp [Array.append_assoc]

/-- The words of two lists of events are the words of the first followed by the words of the
second. -/
theorem encodeAll_append (es₁ es₂ : List Spec.Event) :
    Spec.encodeAll (es₁ ++ es₂) = Spec.encodeAll es₁ ++ Spec.encodeAll es₂ := by
  unfold Spec.encodeAll
  rw [List.foldl_append, foldl_encode]

/-- The next id of the specification's book of a book is the book's next id. -/
theorem toSpec_nextId (b : Book) : (toSpec b).nextId = b.nextId := rfl

/-- After `k` steps of the loop of `run`, for `k` at most the number of records, the book satisfies
the invariant, `toSpec` gives the book of the specification's run on the first `k` records, the
event words encode its events, and the next id lies at most `k` above the first. -/
theorem fold_refines
    (hstep : ∀ (b : Book) (out ws : Array UInt64) (o : UInt64), Inv b →
      b.nextId.toNat < 2 ^ 64 - 1 → o.toNat < ws.size → ws.size < 2 ^ 64 →
      StepRefines b out ws o)
    {b : Book} (h : Inv b) (ws : Array UInt64) (hs : ws.size + 6 < 2 ^ 64)
    (hn : b.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1) (k : Nat)
    (hk : k ≤ (ws.size + 6) / 7) :
    Inv (Nat.fold k (fun i _ s => Program.step s.1 s.2 ws (7 * UInt64.ofNat i)) (b, #[])).1 ∧
      toSpec (Nat.fold k (fun i _ s => Program.step s.1 s.2 ws (7 * UInt64.ofNat i)) (b, #[])).1 =
        (((List.range k).map fun i => recordAt ws (7 * i)).foldl Spec.runStep
          (toSpec b, [])).1 ∧
      (Nat.fold k (fun i _ s => Program.step s.1 s.2 ws (7 * UInt64.ofNat i)) (b, #[])).2 =
        Spec.encodeAll (((List.range k).map fun i => recordAt ws (7 * i)).foldl Spec.runStep
          (toSpec b, [])).2 ∧
      (Nat.fold k (fun i _ s => Program.step s.1 s.2 ws (7 * UInt64.ofNat i))
        (b, #[])).1.nextId.toNat ≤ b.nextId.toNat + k := by
  induction k with
  | zero => exact ⟨h, rfl, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    rw [Nat.fold_succ, List.range_succ, List.map_append, List.foldl_append]
    generalize Nat.fold k (fun i _ s => Program.step s.1 s.2 ws (7 * UInt64.ofNat i)) (b, #[]) = s
      at h1 h2 h3 h4 ⊢
    generalize ((List.range k).map fun i => recordAt ws (7 * i)).foldl Spec.runStep
      (toSpec b, []) = r at h2 h3 ⊢
    have ho : (7 * UInt64.ofNat k).toNat = 7 * k := toNat_seven_mul k (by omega)
    obtain ⟨i1, i2, i3⟩ :=
      hstep s.1 s.2 ws (7 * UInt64.ofNat k) h1 (by omega) (by rw [ho]; omega) (by omega)
    rw [ho] at i2 i3
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, Spec.runStep]
    rw [← h2]
    refine ⟨i1, i2, ?_, ?_⟩
    · rw [i3, h3, encodeAll_append]
    · have hid := Spec.step_nextId (toSpec s.1) (recordAt ws (7 * k))
      rw [← i2, toSpec_nextId, toSpec_nextId] at hid
      split at hid
      · rw [hid, UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
        simp
        omega
      · rw [hid]
        omega

end StreamLemmas

open StreamLemmas

/-- A stream run in two parts, the first a whole number of records, gives the book of one run and
its event words, on any book. -/
theorem run_append (b : Book) (ws₁ ws₂ : Array UInt64) (h : ws₁.size % 7 = 0)
    (hs : ws₁.size + ws₂.size + 6 < 2 ^ 64) :
    Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count (ws₁ ++ ws₂) =
      let r₁ := Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws₁
      let r₂ := Program.run r₁.1.oid r₁.1.acct r₁.1.qty r₁.1.lvl r₁.1.nxt r₁.1.head r₁.1.tail
        r₁.1.nextId r₁.1.count ws₂
      (r₂.1, r₁.2 ++ r₂.2) := by
  obtain ⟨n, hn⟩ : ∃ n, ws₁.size = 7 * n := ⟨ws₁.size / 7, by omega⟩
  have hA : Nat.fold n (fun i _ s => Program.step s.1 s.2 (ws₁ ++ ws₂) (7 * UInt64.ofNat i))
      (b, #[]) =
        Nat.fold n (fun i _ s => Program.step s.1 s.2 ws₁ (7 * UInt64.ofNat i)) (b, #[]) := by
    apply fold_congr n (fun i s => Program.step s.1 s.2 (ws₁ ++ ws₂) (7 * UInt64.ofNat i))
      (fun i s => Program.step s.1 s.2 ws₁ (7 * UInt64.ofNat i))
    intro i hi s
    have hi' : (7 * UInt64.ofNat i).toNat = 7 * i := toNat_seven_mul _ (by omega)
    apply step_congr
    · rw [short_iff _ _ (by simp; omega) (by simp; omega), short_iff _ _ (by omega) (by omega),
        hi', Array.size_append]
      omega
    · intro j hj
      simp only [Program.word]
      rw [toNat_offset _ _ (by omega)]
      exact getElem!_append_left (by omega)
  dsimp only
  rw [run_eq_loop, run_eq_loop, run_eq_loop]
  simp only [LeanExe.loop]
  rw [count_toNat _ (by simp; omega), count_toNat _ (by omega), count_toNat _ (by omega),
    show ((ws₁ ++ ws₂).size + 6) / 7 = n + (ws₂.size + 6) / 7 by simp; omega,
    show (ws₁.size + 6) / 7 = n by omega, Nat.fold_add, hA,
    fold_second ws₁ ws₂ n hn hs _ (Nat.le_refl _)]

/-- If every step at an offset inside a stream refines `Spec.step` on a book that satisfies the
invariant while the next id lies below 2^64 - 1, then under the invariant, and while the next id
stays below 2^64 - 1, `run` keeps the invariant and gives the book and the event words of
`Spec.run` on the book that `toSpec` reads. -/
theorem run_eq_of_step
    (hstep : ∀ (b : Book) (out ws : Array UInt64) (o : UInt64), Inv b →
      b.nextId.toNat < 2 ^ 64 - 1 → o.toNat < ws.size → ws.size < 2 ^ 64 →
      StepRefines b out ws o)
    {b : Book} (h : Inv b) (ws : Array UInt64) (hs : ws.size + 6 < 2 ^ 64)
    (hn : b.nextId.toNat + (ws.size + 6) / 7 ≤ 2 ^ 64 - 1) :
    Inv (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).1 ∧
      toSpec (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).1 =
        (Spec.run (toSpec b) ws.toList).1 ∧
      (Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws).2 =
        Spec.encodeAll (Spec.run (toSpec b) ws.toList).2 := by
  rw [Spec.run_eq, records_eq, run_eq_loop]
  simp only [LeanExe.loop]
  rw [count_toNat ws hs]
  obtain ⟨h1, h2, h3, -⟩ := fold_refines hstep h ws hs hn _ (Nat.le_refl _)
  exact ⟨h1, h2, h3⟩

end Demos.OrderBook.Refinement

#print axioms Demos.OrderBook.Refinement.run_append
#print axioms Demos.OrderBook.Refinement.run_eq_of_step
