import Demos.Rcv.ReadProgramProof

/-!
The reader program's main theorem, `readContest_eq`: `readContest b` holds the words of
`readResult` of the bytes of `b`, for every buffer of fewer than `2 ^ 64` bytes.  `readLines_split`
divides the specification's reader into the header through line 4, which `readHead` reads, and the
rest, and the proof follows the lines in order with the theorems of `ReadProgramProof.lean`.
-/

namespace Demos.Rcv.Spec

/-- Lines 1 to 4 of the specification's reader: the contest identifier, `k`, `n`, and the lines
after line 4. -/
def headSpec (ps : List (List UInt8)) :
    Except (Nat × Role) (List UInt8 × Nat × Nat × List (List UInt8)) := do
  let ((), ps) ← readLine 1 .format parseFormat ps
  let (contest, ps) ← readLine 2 .contest parseContest ps
  let (k, ps) ← readLine 3 .positions (parseBounded "positions " 1 maxIndex) ps
  let (n, ps) ← readLine 4 .candidates (parseBounded "candidates " 1 maxIndex) ps
  pure (contest, k, n, ps)

/-- The specification's reader after line 4. -/
def restSpec (contest : List UInt8) (k n : Nat) (ps : List (List UInt8)) :
    Except (Nat × Role) Contest := do
  let (candidates, ps) ← readCandidates 1 n ps
  let (order, ps) ← readLine (5 + n) .order (parseOrder n) ps
  let (N, ps) ← readLine (6 + n) .ballots (parseBounded "ballots " 0 maxBallots) ps
  let (ballots, ps) ← readBallots k n (7 + n) N [] ps
  if ps = [[]] then pure { contest, positions := k, candidates, order, ballots }
  else throw (7 + n + N, .end)

theorem readLines_split (ps : List (List UInt8)) :
    readLines ps = (headSpec ps).bind fun x => restSpec x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [readLines, headSpec, restSpec, bind, Except.bind, pure, Except.pure]
  cases readLine 1 .format parseFormat ps <;> simp only []
  rename_i v1
  cases readLine 2 .contest parseContest v1.2 <;> simp only []
  rename_i v2
  cases readLine 3 .positions (parseBounded "positions " 1 maxIndex) v2.2 <;> simp only []
  rename_i v3
  cases readLine 4 .candidates (parseBounded "candidates " 1 maxIndex) v3.2 <;> simp only []

end Demos.Rcv.Spec

namespace Demos.Rcv.ReadProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec

/-- A line from the position `p` either reads, when it has its LF and its form, or fails. -/
theorem readLine_case {α : Type} (b : Bytes) (hb : b.data.size < 2 ^ 64) (j : Nat) (r : Role)
    (parse : List UInt8 → Option α) (p : UInt64) (hp : p ≤ b.size) :
    (∃ a, findByte b 10 p b.size < b.size ∧
        parse (slice b p.toNat (findByte b 10 p b.size).toNat) = some a ∧
        readLine j r parse (piecesFrom b p) = .ok (a, piecesFrom b (findByte b 10 p b.size + 1))) ∨
      ((findByte b 10 p b.size < b.size →
          parse (slice b p.toNat (findByte b 10 p b.size).toNat) = none) ∧
        readLine j r parse (piecesFrom b p) = .error (j, r)) := by
  rw [readLine_pieces b hb j r parse p hp]
  by_cases he : findByte b 10 p b.size < b.size
  · rw [ite_eq_left he]
    cases hpa : parse (slice b p.toNat (findByte b 10 p b.size).toNat) with
    | none => exact Or.inr ⟨fun _ => rfl, rfl⟩
    | some a => exact Or.inl ⟨a, he, rfl, rfl⟩
  · rw [ite_eq_right he]
    exact Or.inr ⟨fun h => absurd h he, rfl⟩

theorem cond_false {c : Bool} {P : Prop} [Decidable P] (h : P → c = false) :
    (decide P && c) = false := by
  by_cases hp : P
  · rw [decide_eq_true hp, h hp]; rfl
  · rw [decide_eq_false hp]; rfl

theorem ofNat_add_toNat (a : Nat) (n : UInt64) (h : a + n.toNat < 2 ^ 64) :
    (UInt64.ofNat a + n) = UInt64.ofNat (a + n.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, ofNat_toNat_small (n := a) (by omega), ofNat_toNat_small h,
    Nat.mod_eq_of_lt h]

theorem readAfter_some {b : Bytes} {s e w1 l1 w2 l2 lo hi : UInt64} {P : String} {lo' hi' v : Nat}
    (h : readAfter b s e w1 l1 w2 l2 lo hi =
      match parseBounded P lo' hi' (slice b s.toNat e.toNat) with
      | some v => (true, UInt64.ofNat v)
      | none => (false, 0))
    (hv : parseBounded P lo' hi' (slice b s.toNat e.toNat) = some v) :
    readAfter b s e w1 l1 w2 l2 lo hi = (true, UInt64.ofNat v) := by
  rw [h, hv]

theorem readAfter_none {b : Bytes} {s e w1 l1 w2 l2 lo hi : UInt64} {P : String} {lo' hi' : Nat}
    (h : readAfter b s e w1 l1 w2 l2 lo hi =
      match parseBounded P lo' hi' (slice b s.toNat e.toNat) with
      | some v => (true, UInt64.ofNat v)
      | none => (false, 0))
    (hv : parseBounded P lo' hi' (slice b s.toNat e.toNat) = none) :
    readAfter b s e w1 l1 w2 l2 lo hi = (false, 0) := by
  rw [h, hv]

theorem bounded_le {P : String} {lo hi v : Nat} {l : List UInt8}
    (h : parseBounded P lo hi l = some v) : lo ≤ v ∧ v ≤ hi := by
  unfold parseBounded at h
  split at h
  · split at h
    · split at h
      · cases h; assumption
      · simp at h
    · simp at h
  · simp at h

/-- `readHead` reads lines 1 to 4 as the specification does. -/
theorem readHead_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) :
    match headSpec (piecesFrom b 0) with
    | .ok (_, k, n, ps) => ∃ p, p ≤ b.size ∧ ps = piecesFrom b p ∧ 1 ≤ k ∧ k ≤ 63 ∧ 1 ≤ n ∧
        n ≤ 63 ∧ readHead b = (0, UInt64.ofNat k, UInt64.ofNat n, p)
    | .error (j, r) => (readHead b).1 = UInt64.ofNat j ∧ 1 ≤ j ∧ j ≤ 4 ∧ r.code = j - 1 := by
  have hsz := size_toNat b hb
  have h0 : (0 : UInt64) ≤ b.size := UInt64.le_iff_toNat_le.mpr (by simp)
  unfold headSpec readHead
  simp only []
  -- Line 1
  obtain ⟨ea1, eb1⟩ := findByte_le_size b 0 h0
  have he1 : (findByte b 10 0 b.size).toNat ≤ b.data.size := by
    rw [← hsz]; exact UInt64.le_iff_toNat_le.mp eb1
  simp only [isFormat_eq b hb 0 _ ea1 he1]
  rcases readLine_case b hb 1 .format parseFormat 0 h0 with ⟨u, hl1, hp1, hr1⟩ | ⟨hn1, hr1⟩
  swap
  · rw [hr1]
    simp only [bind, Except.bind]
    rw [cond_false (fun h => by rw [hn1 h]; rfl)]
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨rfl, le_refl _, by decide, rfl⟩
  rw [hr1]
  simp only [bind, Except.bind, decide_eq_true hl1, hp1, Option.isSome_some, Bool.and_self,
    ite_true]
  -- Line 2
  have hp2le : findByte b 10 0 b.size + 1 ≤ b.size := next_le_size hl1
  obtain ⟨ea2, eb2⟩ := findByte_le_size b _ hp2le
  have he2 : (findByte b 10 (findByte b 10 0 b.size + 1) b.size).toNat ≤ b.data.size := by
    rw [← hsz]; exact UInt64.le_iff_toNat_le.mp eb2
  simp only [isContest_eq b hb _ _ ea2 he2]
  rcases readLine_case b hb 2 .contest parseContest _ hp2le with ⟨cid, hl2, hp2, hr2⟩ |
    ⟨hn2, hr2⟩
  swap
  · rw [hr2]
    simp only []
    rw [cond_false (fun h => by rw [hn2 h]; rfl)]
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨rfl, by decide, by decide, rfl⟩
  rw [hr2]
  simp only [decide_eq_true hl2, hp2, Option.isSome_some, Bool.and_self, ite_true]
  -- Line 3
  have hp3le := next_le_size hl2
  obtain ⟨ea3, eb3⟩ := findByte_le_size b _ hp3le
  have he3 : (findByte b 10 (findByte b 10 (findByte b 10 0 b.size + 1) b.size + 1)
      b.size).toNat ≤ b.data.size := by
    rw [← hsz]; exact UInt64.le_iff_toNat_le.mp eb3
  have hra3 := readAfter_eq b hb _ _ 0x6e6f697469736f70 8 0x2073 2 1 63 (by decide) (by decide)
    "positions " (by decide) ea3 he3
  simp only [show (1 : UInt64).toNat = 1 from rfl, show (63 : UInt64).toNat = maxIndex from rfl]
    at hra3
  rcases readLine_case b hb 3 .positions (parseBounded "positions " 1 maxIndex) _ hp3le with
    ⟨k, hl3, hp3, hr3⟩ | ⟨hn3, hr3⟩
  swap
  · rw [hr3]
    simp only []
    rw [cond_false (fun h => by rw [readAfter_none hra3 (hn3 h)])]
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨rfl, by decide, by decide, rfl⟩
  rw [hr3, readAfter_some hra3 hp3]
  simp only [decide_eq_true hl3, Bool.and_self, ite_true]
  have hk := bounded_le hp3
  -- Line 4
  have hp4le := next_le_size hl3
  obtain ⟨ea4, eb4⟩ := findByte_le_size b _ hp4le
  have he4 : (findByte b 10 (findByte b 10 (findByte b 10 (findByte b 10 0 b.size + 1) b.size + 1)
      b.size + 1) b.size).toNat ≤ b.data.size := by
    rw [← hsz]; exact UInt64.le_iff_toNat_le.mp eb4
  have hra4 := readAfter_eq b hb _ _ 0x74616469646e6163 8 0x207365 3 1 63 (by decide) (by decide)
    "candidates " (by decide) ea4 he4
  simp only [show (1 : UInt64).toNat = 1 from rfl, show (63 : UInt64).toNat = maxIndex from rfl]
    at hra4
  rcases readLine_case b hb 4 .candidates (parseBounded "candidates " 1 maxIndex) _ hp4le with
    ⟨n, hl4, hp4, hr4⟩ | ⟨hn4, hr4⟩
  swap
  · rw [hr4]
    simp only []
    rw [cond_false (fun h => by rw [readAfter_none hra4 (hn4 h)])]
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨rfl, by decide, by decide, rfl⟩
  rw [hr4, readAfter_some hra4 hp4]
  simp only [decide_eq_true hl4, Bool.and_self, ite_true, pure, Except.pure]
  have hn := bounded_le hp4
  exact ⟨_, next_le_size hl4, rfl, hk.1, hk.2, hn.1, hn.2, rfl⟩

theorem takeLine_error {j : Nat} {r : Role} {ps : List (List UInt8)} {e : Nat × Role}
    (h : takeLine j r ps = .error e) : e = (j, r) := by
  unfold takeLine at h
  split at h
  · simp at h
  · cases h; rfl

theorem readLine_error_role {α : Type} {j : Nat} {r : Role} {parse : List UInt8 → Option α}
    {ps : List (List UInt8)} {e : Nat × Role} (h : readLine j r parse ps = .error e) : e.2 = r := by
  unfold readLine at h
  split at h
  · split at h
    · simp at h
    · cases h; rfl
  · rename_i e' he'
    cases h
    rw [takeLine_error he']

theorem readCandidates_error_role {i count : Nat} {ps : List (List UInt8)} {e : Nat × Role}
    (h : readCandidates i count ps = .error e) : e.2 = .candidate := by
  induction count generalizing i ps with
  | zero => simp [readCandidates] at h
  | succ count ih =>
    unfold readCandidates at h
    split at h
    · split at h
      · simp at h
      · rename_i e' h2
        cases h
        exact ih h2
    · rename_i e' h1
      cases h
      exact readLine_error_role h1

theorem readBallots_error_role {k n j count : Nat} {acc : List Ballot} {ps : List (List UInt8)}
    {e : Nat × Role} (h : readBallots k n j count acc ps = .error e) : e.2 = .ballot := by
  induction count generalizing j acc ps with
  | zero => simp [readBallots] at h
  | succ count ih =>
    unfold readBallots at h
    split at h
    · exact ih h
    · rename_i e' h1
      cases h
      exact readLine_error_role h1

theorem lit_add (a : Nat) (ha : a < 2 ^ 64) (n : Nat) (h : a + n < 2 ^ 64) :
    (UInt64.ofNat a + UInt64.ofNat n) = UInt64.ofNat (a + n) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, ofNat_toNat_small ha, ofNat_toNat_small (by omega), ofNat_toNat_small h,
    Nat.mod_eq_of_lt h]

theorem word_add_ofNat (a : UInt64) (n : Nat) (h : a.toNat + n < 2 ^ 64) :
    a + UInt64.ofNat n = UInt64.ofNat (a.toNat + n) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, ofNat_toNat_small (by omega), ofNat_toNat_small h, Nat.mod_eq_of_lt h]

theorem array3_toList (a b c : UInt64) : (#[a, b, c] : Array UInt64).toList = [a, b, c] := rfl

/-- The reader program returns the words of the specification's result. -/
theorem readContest_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) :
    (readContest b).toList = readResult (bytesOf b) := by
  have hsz := size_toNat b hb
  have hbytes : (bytesOf b).splitOn lf = piecesFrom b 0 := by
    unfold piecesFrom
    rw [UInt64.toNat_zero, slice_end, List.drop_zero]
  unfold readResult Spec.read
  rw [hbytes, readLines_split]
  have hh := readHead_spec b hb
  unfold readContest
  generalize readHead b = h at hh ⊢
  cases hs : headSpec (piecesFrom b 0) with
  | error e =>
    obtain ⟨j, r⟩ := e
    rw [hs] at hh
    obtain ⟨h1, hj1, hj4, hcode⟩ := hh
    simp only [Except.bind]
    have hne : (h.1 == 0) = false := by
      rw [h1]; simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg UInt64.toNat he
      rw [ofNat_toNat_small (by omega)] at this
      simp at this
      omega
    have hsub : UInt64.ofNat j - 1 = UInt64.ofNat (j - 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        rw [ofNat_toNat_small (by omega)]; simp; omega)), ofNat_toNat_small (by omega),
        ofNat_toNat_small (by omega)]
      simp
    rw [ite_eq_right (by rw [hne]; simp), array3_toList, h1, hcode, hsub]
  | ok v =>
    obtain ⟨cid, k, n, ps⟩ := v
    rw [hs] at hh
    obtain ⟨p, hp, rfl, hk1, hk2, hn1, hn2, rfl⟩ := hh
    simp only [Except.bind, beq_self_eq_true, ite_true]
    have hkN : (UInt64.ofNat k).toNat = k := ofNat_toNat_small (by omega)
    have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
    unfold restSpec
    -- Candidate lines
    have hc := candidatesFrom_spec b hb n p 1 (UInt64.ofNat n)
      #[UInt64.ofNat n, UInt64.ofNat k, 0] hnN hp (by decide) (by simp; omega)
    simp only [show (1 : UInt64).toNat = 1 from rfl] at hc
    generalize candidatesFrom b p 1 (UInt64.ofNat n) #[UInt64.ofNat n, UInt64.ofNat k, 0] = c
      at hc ⊢
    cases hrc : readCandidates 1 n (piecesFrom b p) with
    | error e =>
      obtain ⟨j, r⟩ := e
      rw [hrc] at hc
      obtain ⟨h1, hj5, hj⟩ := hc
      have hr := readCandidates_error_role hrc
      simp only [bind, Except.bind] at hr ⊢
      subst hr
      have hne : (c.1 == 0) = false := by
        rw [h1]; simp only [beq_eq_false_iff_ne, ne_eq]
        intro he
        have := congrArg UInt64.toNat he
        rw [ofNat_toNat_small hj] at this
        simp at this
        omega
      rw [ite_eq_right (by rw [hne]; simp), array3_toList, h1]
      rfl
    | ok v =>
      obtain ⟨cs, rest⟩ := v
      rw [hrc] at hc
      obtain ⟨p1, hp1, rfl, hc1, hc2, hc3⟩ := hc
      obtain ⟨hclen, -, -⟩ := readCandidates_ok hrc
      simp only [bind, Except.bind, hc1, beq_self_eq_true, ite_true, hc2]
      -- Order line
      obtain ⟨eo1, eo2⟩ := findByte_le_size b p1 hp1
      have heo : (findByte b 10 p1 b.size).toNat ≤ b.data.size := by
        rw [← hsz]; exact UInt64.le_iff_toNat_le.mp eo2
      obtain ⟨ho1, ho2⟩ := readOrder_spec b hb (UInt64.ofNat n) (by omega) p1 _ eo1 heo c.2.2
      rw [hnN] at ho1 ho2
      generalize readOrder b (UInt64.ofNat n) p1 (findByte b 10 p1 b.size) c.2.2 = o at ho1 ho2 ⊢
      rcases readLine_case b hb (5 + n) .order (parseOrder n) p1 hp1 with
        ⟨order, hl5, hp5, hr5⟩ | ⟨hn5, hr5⟩
      swap
      · rw [hr5]
        simp only []
        have hcond : (decide (findByte b 10 p1 b.size < b.size) && o.1) = false :=
          cond_false (fun h => by rw [ho1, hn5 h]; rfl)
        rw [ite_eq_right (by rw [hcond]; simp), array3_toList,
          word_add_ofNat 5 n (by simp; omega)]
        rfl
      rw [hr5]
      simp only []
      rw [ite_eq_left (by rw [decide_eq_true hl5, ho1, hp5]; rfl)]
      have ho2' := ho2 order hp5
      obtain ⟨-, hperm⟩ := eq_of_parseOrder hp5
      -- Ballots line
      have hp6le := next_le_size hl5
      obtain ⟨eb1, eb2⟩ := findByte_le_size b _ hp6le
      have heb : (findByte b 10 (findByte b 10 p1 b.size + 1) b.size).toNat ≤ b.data.size := by
        rw [← hsz]; exact UInt64.le_iff_toNat_le.mp eb2
      have hra := readAfter_eq b hb _ _ 0x2073746f6c6c6162 8 0 0 0 4294967295 (by decide)
        (by decide) "ballots " (by decide) eb1 heb
      simp only [show (0 : UInt64).toNat = 0 from rfl,
        show (4294967295 : UInt64).toNat = maxBallots from rfl] at hra
      rcases readLine_case b hb (6 + n) .ballots (parseBounded "ballots " 0 maxBallots) _ hp6le with
        ⟨N, hl6, hp6, hr6⟩ | ⟨hn6, hr6⟩
      swap
      · rw [hr6]
        simp only []
        rw [ite_eq_right (by rw [cond_false (fun h => by rw [readAfter_none hra (hn6 h)])]; simp),
          array3_toList, word_add_ofNat 6 n (by simp; omega)]
        rfl
      rw [hr6, readAfter_some hra hp6]
      simp only []
      rw [ite_eq_left (by rw [decide_eq_true hl6]; rfl)]
      have hN := bounded_le hp6
      have hNN : (UInt64.ofNat N).toNat = N := ofNat_toNat_small (by
        have := hN.2; simp [maxBallots] at this; omega)
      -- Ballot lines
      have hNle : N ≤ 4294967295 := by have := hN.2; simp [maxBallots] at this; omega
      have h7 : (7 + UInt64.ofNat n) = UInt64.ofNat (7 + n) := by
        rw [word_add_ofNat 7 n (by simp; omega)]
        rfl
      have h7N : (7 + UInt64.ofNat n).toNat = 7 + n := by
        rw [h7, ofNat_toNat_small (by omega)]
      have hb7 := ballotsFrom_spec b hb (UInt64.ofNat k) (UInt64.ofNat n) ⟨by omega, by omega⟩
        (by omega) N (findByte b 10 (findByte b 10 p1 b.size + 1) b.size + 1) (7 + UInt64.ofNat n)
        (UInt64.ofNat N) (o.2.set! (2 : UInt64).toNat (UInt64.ofNat N)) [] hNN
        (next_le_size hl6) (by rw [h7N]; omega) (by rw [h7N]; omega)
      rw [hkN, hnN, h7N] at hb7
      generalize ballotsFrom b (UInt64.ofNat k) (UInt64.ofNat n)
        (findByte b 10 (findByte b 10 p1 b.size + 1) b.size + 1) (7 + UInt64.ofNat n)
        (UInt64.ofNat N) (o.2.set! (2 : UInt64).toNat (UInt64.ofNat N)) = r at hb7 ⊢
      cases hrb : readBallots k n (7 + n) N [] (piecesFrom b
          (findByte b 10 (findByte b 10 p1 b.size + 1) b.size + 1)) with
      | error e =>
        obtain ⟨j, rr⟩ := e
        rw [hrb] at hb7
        obtain ⟨h1, hj1, hj⟩ := hb7
        have hr := readBallots_error_role hrb
        simp only [] at hr ⊢
        subst hr
        have hne : (r.1 == 0) = false := by
          rw [h1]; simp only [beq_eq_false_iff_ne, ne_eq]
          intro he
          have := congrArg UInt64.toNat he
          rw [ofNat_toNat_small hj] at this
          simp at this
          omega
        rw [ite_eq_right (by rw [hne]; simp), array3_toList, h1]
        rfl
      | ok v =>
        obtain ⟨bs, rest⟩ := v
        rw [hrb] at hb7
        obtain ⟨p2, new, hp2, rfl, hbs, h1, h2, h3⟩ := hb7
        obtain ⟨new2, hbs2, hblen, -, -⟩ := readBallots_ok (by omega) hrb
        have hbN : bs.length = N := by rw [hbs2]; simp [hblen]
        simp only [List.reverse_nil, List.nil_append] at hbs
        rw [← hbs] at h3
        simp only [h1, beq_self_eq_true, ite_true, h2]
        by_cases hend : p2 = b.size
        · rw [ite_eq_left (by rw [hend]; simp), ite_eq_left ((piecesFrom_end b hb p2 hp2).mpr hend),
            h3]
          have hset : (o.2.set! (2 : UInt64).toNat (UInt64.ofNat N)).toList =
              [UInt64.ofNat n, UInt64.ofNat k, UInt64.ofNat N] ++
                cs.map (fun x => UInt64.ofNat (Spec.kindCode x.kind)) ++
                order.map UInt64.ofNat := by
            rw [Array.toList_set!, ho2', hc3]
            rfl
          rw [hset]
          simp only [pure, Except.pure, contestWords, List.map_append, List.map_cons, List.map_nil,
            List.map_map, hclen, hbN, List.append_assoc]
          rfl
        · rw [ite_eq_right (by simpa using hend),
            ite_eq_right (fun h => hend ((piecesFrom_end b hb p2 hp2).mp h)), array3_toList,
            h7, word_add_ofNat _ N (by rw [ofNat_toNat_small (by omega)]; omega),
            ofNat_toNat_small (n := 7 + n) (by omega)]
          rfl

end Demos.Rcv.ReadProgram
