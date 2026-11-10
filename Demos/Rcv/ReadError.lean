import Demos.Rcv.ReadProgramMain

/-!
T2(c): a file that is the file of no structure that meets the constraints reads as the error of
its first faulty line, by number, with the role that the header gives it, and its report is the
error report.  The reader takes the lines in order and the error rule names them by number, so the
proof reads the pieces that the reader passes to line `j` as the pieces of the file from piece
`j - 1` on (`readLine_drop`), and every line before the reported one as a line that meets its role.
-/

namespace Demos.Rcv.Spec

open Demos.Rcv
open Demos.Rcv.ReadProgram (bounded_le)

variable (b : List UInt8)

/-- The pieces of the file from line `j` on. -/
abbrev piecesAt (j : Nat) : List (List UInt8) := (b.splitOn lf).drop (j - 1)

theorem takeLine_drop (j : Nat) (hj : 1 ≤ j) (r : Role) :
    takeLine j r (piecesAt b j) = match lineOf b j with
      | some l => .ok (l, piecesAt b (j + 1))
      | none => .error (j, r) := by
  unfold piecesAt lineOf
  by_cases h : j < (b.splitOn lf).length
  · rw [ite_eq_left ⟨hj, h⟩, List.getElem?_eq_getElem (by omega)]
    rw [List.drop_eq_getElem_cons (show j - 1 < (b.splitOn lf).length by omega),
      show j - 1 + 1 = j by omega, List.drop_eq_getElem_cons h]
    simp only [takeLine, Nat.add_sub_cancel]
    rw [List.drop_eq_getElem_cons h]
  · rw [ite_eq_right (by omega)]
    have hlen : ((b.splitOn lf).drop (j - 1)).length ≤ 1 := by simp; omega
    unfold takeLine
    split
    · rename_i l p ps' heq
      rw [heq] at hlen
      simp at hlen
    · rfl

theorem readLine_drop {α : Type} (j : Nat) (hj : 1 ≤ j) (r : Role) (parse : List UInt8 → Option α) :
    readLine j r parse (piecesAt b j) = match lineOf b j with
      | some l => match parse l with
        | some a => .ok (a, piecesAt b (j + 1))
        | none => .error (j, r)
      | none => .error (j, r) := by
  unfold readLine
  rw [takeLine_drop b j hj r]
  cases lineOf b j <;> rfl

/-- The candidate lines from candidate `i` on read in order: each line before the first that fails
reads, and the error is that line's. -/
theorem readCandidates_drop : ∀ (count i : Nat),
    match readCandidates i count (piecesAt b (4 + i)) with
    | .ok (_, rest) => rest = piecesAt b (4 + i + count) ∧
        ∀ t < count, ∃ l, lineOf b (4 + i + t) = some l ∧ (parseCandidate (i + t) l).isSome
    | .error (j, r) => r = .candidate ∧ 4 + i ≤ j ∧ j < 4 + i + count ∧
        (∀ t, 4 + i + t < j →
          ∃ l, lineOf b (4 + i + t) = some l ∧ (parseCandidate (i + t) l).isSome) ∧
        ∀ l, lineOf b j = some l → (parseCandidate (j - 4) l).isSome = false := by
  intro count
  induction count with
  | zero =>
    intro i
    simp only [readCandidates, Nat.add_zero]
    exact ⟨trivial, fun t ht => absurd ht (by omega)⟩
  | succ count ih =>
    intro i
    simp only [readCandidates]
    rw [readLine_drop b (4 + i) (by omega)]
    cases hl : lineOf b (4 + i) with
    | none =>
      simp only []
      refine ⟨by simp, by simp, by omega, fun t ht => absurd ht (by omega), ?_⟩
      intro l h; rw [hl] at h; cases h
    | some l =>
      simp only []
      cases hp : parseCandidate i l with
      | none =>
        simp only []
        refine ⟨by simp, by simp, by omega, fun t ht => absurd ht (by omega), ?_⟩
        intro l' h
        rw [hl] at h
        cases h
        simp [show 4 + i - 4 = i by omega, hp]
      | some x =>
        simp only []
        have := ih (i + 1)
        rw [show 4 + (i + 1) = 4 + i + 1 by omega] at this
        revert this
        cases readCandidates (i + 1) count (piecesAt b (4 + i + 1)) with
        | ok v =>
          simp only []
          rintro ⟨hrest, hall⟩
          refine ⟨by rw [hrest]; congr 1; omega, ?_⟩
          intro t ht
          cases t with
          | zero => exact ⟨l, by simpa using hl, by simp [hp]⟩
          | succ t =>
            obtain ⟨l', h1, h2⟩ := hall t (by omega)
            exact ⟨l', by rw [← h1]; congr 1; omega, by rw [← h2]; congr 2; omega⟩
        | error e =>
          obtain ⟨j, r⟩ := e
          simp only []
          rintro ⟨hr, h1, h2, hall, hlast⟩
          refine ⟨hr, by omega, by omega, ?_, hlast⟩
          intro t ht
          cases t with
          | zero => exact ⟨l, by simpa using hl, by simp [hp]⟩
          | succ t =>
            obtain ⟨l', e1, e2⟩ := hall t (by omega)
            exact ⟨l', by rw [← e1]; congr 1; omega, by rw [← e2]; congr 2; omega⟩

/-- The ballot lines from line `j` on read in order. -/
theorem readBallots_drop (k n : Nat) : ∀ (count j : Nat) (acc : List Ballot), 1 ≤ j →
    match readBallots k n j count acc (piecesAt b j) with
    | .ok (_, rest) => rest = piecesAt b (j + count) ∧
        ∀ t < count, ∃ l, lineOf b (j + t) = some l ∧ (parseBallot k n l).isSome
    | .error (j', r) => r = .ballot ∧ j ≤ j' ∧ j' < j + count ∧
        (∀ t, j + t < j' → ∃ l, lineOf b (j + t) = some l ∧ (parseBallot k n l).isSome) ∧
        ∀ l, lineOf b j' = some l → (parseBallot k n l).isSome = false := by
  intro count
  induction count with
  | zero =>
    intro j acc hj
    simp only [readBallots, Nat.add_zero]
    exact ⟨trivial, fun t ht => absurd ht (by omega)⟩
  | succ count ih =>
    intro j acc hj
    simp only [readBallots]
    rw [readLine_drop b j hj]
    cases hl : lineOf b j with
    | none =>
      simp only []
      refine ⟨by simp, by simp, by omega, fun t ht => absurd ht (by omega), ?_⟩
      intro l h; rw [hl] at h; cases h
    | some l =>
      simp only []
      cases hp : parseBallot k n l with
      | none =>
        simp only []
        refine ⟨by simp, by simp, by omega, fun t ht => absurd ht (by omega), ?_⟩
        intro l' h
        rw [hl] at h
        cases h
        simp [hp]
      | some x =>
        simp only []
        have := ih (j + 1) (x :: acc) (by omega)
        revert this
        cases readBallots k n (j + 1) count (x :: acc) (piecesAt b (j + 1)) with
        | ok v =>
          simp only []
          rintro ⟨hrest, hall⟩
          refine ⟨by rw [hrest]; congr 1; omega, ?_⟩
          intro t ht
          cases t with
          | zero => exact ⟨l, by simpa using hl, by simp [hp]⟩
          | succ t =>
            obtain ⟨l', h1, h2⟩ := hall t (by omega)
            exact ⟨l', by rw [← h1]; congr 1; omega, h2⟩
        | error e =>
          obtain ⟨j', r⟩ := e
          simp only []
          rintro ⟨hr, h1, h2, hall, hlast⟩
          refine ⟨hr, by omega, by omega, ?_, hlast⟩
          intro t ht
          cases t with
          | zero => exact ⟨l, by simpa using hl, by simp [hp]⟩
          | succ t =>
            obtain ⟨l', e1, e2⟩ := hall t (by omega)
            exact ⟨l', by rw [← e1]; congr 1; omega, e2⟩

/-! ## The first faulty line -/

theorem faulty_false {j : Nat} {l : List UInt8} (hl : lineOf b j = some l)
    (hm : meets (headerK b) (headerN b) j (roleAt b j) l = true) : faulty b j = false := by
  simp [faulty, hl, hm]

theorem faulty_of_fails {j : Nat} {l : List UInt8} (hl : lineOf b j = some l)
    (hm : meets (headerK b) (headerN b) j (roleAt b j) l = false) : faulty b j = true := by
  simp [faulty, hl, hm]

theorem faulty_of_absent {j : Nat} (hl : lineOf b j = none)
    (hj : j ≤ 6 + headerN b + headerBallots b) : faulty b j = true := by
  simp [faulty, hl, hj]

theorem lineOf_of_parse {j : Nat} {α : Type} {parse : List UInt8 → Option α} {a : α}
    {l : List UInt8} (hl : lineOf b j = some l) (hp : parse l = some a) :
    ∃ l, lineOf b j = some l ∧ (parse l).isSome := ⟨l, hl, by simp [hp]⟩

theorem roleOf_candidate {n N j : Nat} (h1 : 5 ≤ j) (h2 : j ≤ 4 + n) : roleOf n N j = .candidate := by
  unfold roleOf; split_ifs <;> first | rfl | omega

theorem roleOf_order {n N : Nat} : roleOf n N (5 + n) = .order := by
  unfold roleOf; split_ifs <;> first | rfl | omega

theorem roleOf_ballots {n N : Nat} : roleOf n N (6 + n) = .ballots := by
  unfold roleOf; split_ifs <;> first | rfl | omega

theorem roleOf_ballot {n N j : Nat} (h1 : 7 + n ≤ j) (h2 : j ≤ 6 + n + N) :
    roleOf n N j = .ballot := by
  unfold roleOf; split_ifs <;> first | rfl | omega

theorem roleOf_end {n N : Nat} : roleOf n N (7 + n + N) = .end := by
  unfold roleOf; split_ifs <;> first | rfl | omega

/-- A line that the reader reads with the parse of its role meets its role. -/
theorem meets_of_role {j : Nat} {l : List UInt8} (hl : lineOf b j = some l) (r : Role)
    (hr : roleAt b j = r) (hm : meets (headerK b) (headerN b) j r l = true) :
    faulty b j = false :=
  faulty_false b hl (by rw [hr]; exact hm)

/-- T2(c): a file that is the file of no structure that meets the constraints reads as the error of
its first faulty line `j ≥ 1`, with the role that `roleAt` gives line `j`. -/
theorem read_error_first (h : ∀ f : Contest, f.WellFormed → write f ≠ b) :
    ∃ j r, read b = .error j r ∧ 1 ≤ j ∧ r = roleAt b j ∧ faulty b j = true ∧
      ∀ j', 1 ≤ j' → j' < j → faulty b j' = false := by
  have hps : b.splitOn lf = piecesAt b 1 := rfl
  -- reading succeeds only on the file of a structure that meets the constraints
  cases hread : read b with
  | ok c =>
    exact absurd (write_of_read hread).1 (h c (write_of_read hread).2)
  | error j r =>
    refine ⟨j, r, rfl, ?_⟩
    have hrl : readLines (piecesAt b 1) = .error (j, r) := by
      unfold Spec.read at hread
      rw [hps] at hread
      split at hread
      · simp at hread
      · rename_i e he
        simp only [Reading.error.injEq] at hread
        obtain ⟨rfl, rfl⟩ := hread
        exact he
    rw [readLines_split] at hrl
    unfold headSpec at hrl
    simp only [bind, Except.bind] at hrl
    -- Line 1
    rw [readLine_drop b 1 (le_refl _)] at hrl
    cases hl1 : lineOf b 1 with
    | none =>
      rw [hl1] at hrl; cases hrl
      exact ⟨le_refl _, rfl, faulty_of_absent b hl1 (by omega), fun j' h1 h2 => absurd h2 (by omega)⟩
    | some l1 =>
    simp only [hl1] at hrl
    cases hp1 : parseFormat l1 with
    | none =>
      rw [hp1] at hrl; cases hrl
      exact ⟨le_refl _, rfl, faulty_of_fails b hl1 (by simp [meets, roleAt, roleOf, hp1]),
        fun j' h1 h2 => absurd h2 (by omega)⟩
    | some u =>
    rw [hp1] at hrl
    simp only [] at hrl
    have g1 : faulty b 1 = false := faulty_false b hl1 (by simp [meets, roleAt, roleOf, hp1])
    -- Line 2
    rw [readLine_drop b 2 (by omega)] at hrl
    cases hl2 : lineOf b 2 with
    | none =>
      rw [hl2] at hrl; cases hrl
      refine ⟨by omega, rfl, faulty_of_absent b hl2 (by omega), ?_⟩
      intro j' h1 h2; obtain rfl : j' = 1 := by omega
      exact g1
    | some l2 =>
    simp only [hl2] at hrl
    cases hp2 : parseContest l2 with
    | none =>
      rw [hp2] at hrl; cases hrl
      refine ⟨by omega, rfl, faulty_of_fails b hl2 (by simp [meets, roleAt, roleOf, hp2]), ?_⟩
      intro j' h1 h2; obtain rfl : j' = 1 := by omega
      exact g1
    | some cid =>
    rw [hp2] at hrl
    simp only [] at hrl
    have g2 : faulty b 2 = false := faulty_false b hl2 (by simp [meets, roleAt, roleOf, hp2])
    -- Line 3
    rw [readLine_drop b 3 (by omega)] at hrl
    cases hl3 : lineOf b 3 with
    | none =>
      rw [hl3] at hrl; cases hrl
      refine ⟨by omega, rfl, faulty_of_absent b hl3 (by omega), ?_⟩
      intro j' h1 h2
      rcases (show j' = 1 ∨ j' = 2 by omega) with rfl | rfl
      · exact g1
      · exact g2
    | some l3 =>
    simp only [hl3] at hrl
    cases hp3 : parseBounded "positions " 1 maxIndex l3 with
    | none =>
      rw [hp3] at hrl; cases hrl
      refine ⟨by omega, rfl, faulty_of_fails b hl3 (by simp [meets, roleAt, roleOf, hp3]), ?_⟩
      intro j' h1 h2
      rcases (show j' = 1 ∨ j' = 2 by omega) with rfl | rfl
      · exact g1
      · exact g2
    | some k =>
    rw [hp3] at hrl
    simp only [] at hrl
    have g3 : faulty b 3 = false := faulty_false b hl3 (by simp [meets, roleAt, roleOf, hp3])
    have hK : headerK b = k := by simp [headerK, hl3, hp3]
    -- Line 4
    rw [readLine_drop b 4 (by omega)] at hrl
    cases hl4 : lineOf b 4 with
    | none =>
      rw [hl4] at hrl; cases hrl
      refine ⟨by omega, rfl, faulty_of_absent b hl4 (by omega), ?_⟩
      intro j' h1 h2
      rcases (show j' = 1 ∨ j' = 2 ∨ j' = 3 by omega) with rfl | rfl | rfl
      · exact g1
      · exact g2
      · exact g3
    | some l4 =>
    simp only [hl4] at hrl
    cases hp4 : parseBounded "candidates " 1 maxIndex l4 with
    | none =>
      rw [hp4] at hrl; cases hrl
      refine ⟨by omega, rfl, faulty_of_fails b hl4 (by simp [meets, roleAt, roleOf, hp4]), ?_⟩
      intro j' h1 h2
      rcases (show j' = 1 ∨ j' = 2 ∨ j' = 3 by omega) with rfl | rfl | rfl
      · exact g1
      · exact g2
      · exact g3
    | some n =>
    rw [hp4] at hrl
    simp only [pure, Except.pure] at hrl
    have g4 : faulty b 4 = false := faulty_false b hl4 (by simp [meets, roleAt, roleOf, hp4])
    have hN' : headerN b = n := by simp [headerN, hl4, hp4]
    have hn := (bounded_le hp4).2
    simp only [maxIndex] at hn
    have ghead : ∀ j', 1 ≤ j' → j' ≤ 4 → faulty b j' = false := by
      intro j' h1 h2
      rcases (show j' = 1 ∨ j' = 2 ∨ j' = 3 ∨ j' = 4 by omega) with rfl | rfl | rfl | rfl
      · exact g1
      · exact g2
      · exact g3
      · exact g4
    -- The candidate lines
    unfold restSpec at hrl
    simp only [bind, Except.bind] at hrl
    have hc := readCandidates_drop b n 1
    revert hc
    cases hrc : readCandidates 1 n (piecesAt b (4 + 1)) with
    | error e =>
      obtain ⟨j0, r0⟩ := e
      rw [hrc] at hrl
      cases hrl
      rintro ⟨rfl, hj1, hj2, hall, hlast⟩
      have hrole : roleAt b j = .candidate := by
        rw [roleAt, hN']; exact roleOf_candidate (by omega) (by omega)
      refine ⟨by omega, hrole.symm, ?_, ?_⟩
      · cases hlj : lineOf b j with
        | none => exact faulty_of_absent b hlj (by rw [hN']; omega)
        | some l =>
          exact faulty_of_fails b hlj (by rw [hrole]; simp [meets, hlast l hlj])
      · intro j' h1 h2
        by_cases hj' : j' ≤ 4
        · exact ghead j' h1 hj'
        · obtain ⟨l, hl, hp⟩ := hall (j' - 5) (by omega)
          rw [show 4 + 1 + (j' - 5) = j' by omega] at hl
          refine faulty_false b hl ?_
          rw [roleAt, hN', roleOf_candidate (by omega) (by omega)]
          simp only [meets]
          rw [show j' - 4 = 1 + (j' - 5) by omega]
          exact hp
    | ok v =>
    obtain ⟨cs, ps5⟩ := v
    rw [hrc] at hrl
    simp only [] at hrl
    rintro ⟨rfl, hcall⟩
    have gcand : ∀ j', 5 ≤ j' → j' ≤ 4 + n → faulty b j' = false := by
      intro j' h1 h2
      obtain ⟨l, hl, hp⟩ := hcall (j' - 5) (by omega)
      rw [show 4 + 1 + (j' - 5) = j' by omega] at hl
      refine faulty_false b hl ?_
      rw [roleAt, hN', roleOf_candidate (by omega) (by omega)]
      simp only [meets]
      rw [show j' - 4 = 1 + (j' - 5) by omega]
      exact hp
    rw [show 4 + 1 + n = 5 + n by omega] at hrl
    -- The order line
    rw [readLine_drop b (5 + n) (by omega)] at hrl
    have gbefore5 : ∀ j', 1 ≤ j' → j' < 5 + n → faulty b j' = false := by
      intro j' h1 h2
      by_cases hj' : j' ≤ 4
      · exact ghead j' h1 hj'
      · exact gcand j' (by omega) (by omega)
    have hro : roleAt b (5 + n) = .order := by rw [roleAt, hN']; exact roleOf_order
    cases hl5 : lineOf b (5 + n) with
    | none =>
      rw [hl5] at hrl; cases hrl
      exact ⟨by omega, hro.symm, faulty_of_absent b hl5 (by rw [hN']; omega), gbefore5⟩
    | some l5 =>
    simp only [hl5] at hrl
    cases hp5 : parseOrder n l5 with
    | none =>
      rw [hp5] at hrl; cases hrl
      exact ⟨by omega, hro.symm, faulty_of_fails b hl5 (by rw [hro]; simp [meets, hN', hp5]),
        gbefore5⟩
    | some order =>
    rw [hp5] at hrl
    simp only [] at hrl
    have g5 : faulty b (5 + n) = false := faulty_false b hl5 (by rw [hro]; simp [meets, hN', hp5])
    -- The ballots line
    rw [show 5 + n + 1 = 6 + n by omega, readLine_drop b (6 + n) (by omega)] at hrl
    have gbefore6 : ∀ j', 1 ≤ j' → j' < 6 + n → faulty b j' = false := by
      intro j' h1 h2
      by_cases hj' : j' < 5 + n
      · exact gbefore5 j' h1 hj'
      · rw [show j' = 5 + n by omega]; exact g5
    have hrb : roleAt b (6 + n) = .ballots := by rw [roleAt, hN']; exact roleOf_ballots
    cases hl6 : lineOf b (6 + n) with
    | none =>
      rw [hl6] at hrl; cases hrl
      exact ⟨by omega, hrb.symm, faulty_of_absent b hl6 (by rw [hN']; omega), gbefore6⟩
    | some l6 =>
    simp only [hl6] at hrl
    cases hp6 : parseBounded "ballots " 0 maxBallots l6 with
    | none =>
      rw [hp6] at hrl; cases hrl
      exact ⟨by omega, hrb.symm, faulty_of_fails b hl6 (by rw [hrb]; simp [meets, hp6]), gbefore6⟩
    | some N =>
    rw [hp6] at hrl
    simp only [] at hrl
    have g6 : faulty b (6 + n) = false := faulty_false b hl6 (by rw [hrb]; simp [meets, hp6])
    have hNN : headerBallots b = N := by simp [headerBallots, hN', hl6, hp6]
    -- The ballot lines
    rw [show 6 + n + 1 = 7 + n by omega] at hrl
    have hbl := readBallots_drop b k n N (7 + n) [] (by omega)
    revert hbl
    cases hrb' : readBallots k n (7 + n) N [] (piecesAt b (7 + n)) with
    | error e =>
      obtain ⟨j0, r0⟩ := e
      rw [hrb'] at hrl
      cases hrl
      rintro ⟨rfl, hj1, hj2, hall, hlast⟩
      have hrole : roleAt b j = .ballot := by
        rw [roleAt, hN', hNN]; exact roleOf_ballot (by omega) (by omega)
      refine ⟨by omega, hrole.symm, ?_, ?_⟩
      · cases hlj : lineOf b j with
        | none => exact faulty_of_absent b hlj (by rw [hN', hNN]; omega)
        | some l =>
          exact faulty_of_fails b hlj (by rw [hrole]; simp [meets, hK, hN', hlast l hlj])
      · intro j' h1 h2
        by_cases hj' : j' < 7 + n
        · by_cases hj6 : j' < 6 + n
          · exact gbefore6 j' h1 hj6
          · rw [show j' = 6 + n by omega]; exact g6
        · obtain ⟨l, hl, hp⟩ := hall (j' - (7 + n)) (by omega)
          rw [show 7 + n + (j' - (7 + n)) = j' by omega] at hl
          refine faulty_false b hl ?_
          rw [roleAt, hN', hNN, roleOf_ballot (by omega) (by omega)]
          simp only [meets, hK]
          exact hp
    | ok v =>
    obtain ⟨bs, ps8⟩ := v
    rw [hrb'] at hrl
    simp only [] at hrl
    rintro ⟨rfl, hball⟩
    split at hrl
    · simp [pure, Except.pure] at hrl
    · rename_i hend
      simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq, Prod.mk.injEq] at hrl
      obtain ⟨rfl, rfl⟩ := hrl
      have hre : roleAt b (7 + n + N) = .end := by rw [roleAt, hN', hNN]; exact roleOf_end
      refine ⟨by omega, hre.symm, ?_, ?_⟩
      · cases hlj : lineOf b (7 + n + N) with
        | some l => exact faulty_of_fails b hlj (by rw [hre]; rfl)
        | none =>
          -- the line before the end has its LF, so the end is a final run without LF
          have hprev : 6 + n + N < (b.splitOn lf).length := by
            by_cases hN0 : N = 0
            · subst hN0
              have := hl6
              unfold lineOf at this
              split at this
              · rename_i hc; omega
              · simp at this
            · obtain ⟨l, hl, -⟩ := hball (N - 1) (by omega)
              unfold lineOf at hl
              split at hl
              · rename_i hc; omega
              · simp at hl
          have hlen : (b.splitOn lf).length = 7 + n + N := by
            unfold lineOf at hlj
            split at hlj
            · simp at hlj
              omega
            · rename_i hc; omega
          simp only [faulty, hlj, Bool.or_eq_true, decide_eq_true_eq]
          right
          refine ⟨hlen.symm, ?_⟩
          have hd : piecesAt b (7 + n + N) = [(b.splitOn lf).getLast (List.splitOn_ne_nil _ _)] := by
            simp only [piecesAt]
            rw [show 7 + n + N - 1 = (b.splitOn lf).length - 1 by omega]
            exact List.drop_length_sub_one (List.splitOn_ne_nil _ _)
          rw [List.getLast?_eq_some_getLast (List.splitOn_ne_nil _ _)]
          intro he
          apply hend
          rw [hd]
          simp only [Option.some.injEq] at he
          rw [he]
      · intro j' h1 h2
        by_cases hj' : j' < 7 + n
        · by_cases hj6 : j' < 6 + n
          · exact gbefore6 j' h1 hj6
          · rw [show j' = 6 + n by omega]; exact g6
        · obtain ⟨l, hl, hp⟩ := hball (j' - (7 + n)) (by omega)
          rw [show 7 + n + (j' - (7 + n)) = j' by omega] at hl
          refine faulty_false b hl ?_
          rw [roleAt, hN', hNN, roleOf_ballot (by omega) (by omega)]
          simp only [meets, hK]
          exact hp

/-- T2(c) with the report: the report of such a file is the error report of its first faulty
line. -/
theorem reportFile_error_first (h : ∀ f : Contest, f.WellFormed → write f ≠ b) :
    ∃ j, 1 ≤ j ∧ faulty b j = true ∧ (∀ j', 1 ≤ j' → j' < j → faulty b j' = false) ∧
      read b = .error j (roleAt b j) ∧ reportFile b = errorReport j (roleAt b j) := by
  obtain ⟨j, r, hr, hj, rfl, hf, hfirst⟩ := read_error_first b h
  exact ⟨j, hj, hf, hfirst, hr, by simp [reportFile, hr]⟩

#print axioms read_error_first
#print axioms reportFile_error_first

end Demos.Rcv.Spec
