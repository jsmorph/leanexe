import Demos.Rcv.ReadLemmas

/-!
T2(a): `read (write f) = .ok f` for every structure `f` that meets the constraints.  The written
file splits at LF into its lines and the empty piece after the last LF (`splitOn_text`), and each
line reads back as the field that `write` printed in it: the decimal forms through
`number_decimal`, the position fields through `parsePosition_field`, and the lines of several parts
through the spaces and commas that `write` places between parts that hold none.
-/

namespace Demos.Rcv.Spec

open Demos.Rcv

/-! ## Spans and joins at a separator -/

theorem span_sep {s : UInt8} {a r : List UInt8} (ha : s ∉ a) :
    (a ++ s :: r).span (· != s) = (a, s :: r) := by
  have hp : ∀ x ∈ a, (x != s) = true := fun x hx => by
    have : x ≠ s := fun e => ha (e ▸ hx)
    simpa using this
  rw [List.span_eq_takeWhile_dropWhile, List.takeWhile_append_of_pos hp,
    List.dropWhile_append_of_pos hp]
  simp

/-- A member of a join is the separator or a member of a part. -/
theorem mem_intercalate {s x : UInt8} {ls : List (List UInt8)} (h : x ∈ [s].intercalate ls) :
    x = s ∨ ∃ l ∈ ls, x ∈ l := by
  induction ls with
  | nil => simp at h
  | cons l ls ih =>
    cases ls with
    | nil => exact Or.inr ⟨l, List.mem_cons_self, by simpa using h⟩
    | cons l' ls =>
      rw [List.intercalate_cons_cons] at h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr ⟨l, List.mem_cons_self, h⟩
        · exact Or.inl (by simpa using h)
      · rcases ih h with h | ⟨l'', hl'', hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨l'', List.mem_cons_of_mem _ hl'', hx⟩

theorem not_mem_intercalate {s x : UInt8} {ls : List (List UInt8)} (hs : x ≠ s)
    (hl : ∀ l ∈ ls, x ∉ l) : x ∉ [s].intercalate ls := fun h => by
  rcases mem_intercalate h with h | ⟨l, hl', hx⟩
  · exact hs h
  · exact hl l hl' hx

/-! ## Bytes that the forms exclude -/

theorem not_mem_ident {x : UInt8} {id : List UInt8} (hid : identOk id = true)
    (hx : identByte x = false) : x ∉ id := fun h => by
  simp only [identOk, Bool.and_eq_true, List.all_eq_true] at hid
  rw [hid.2 x h] at hx
  exact absurd hx (by decide)

theorem not_mem_name {x : UInt8} {name : List UInt8} (hn : nameOk name = true) (hx : x < 0x20) :
    x ∉ name := fun h => by
  simp only [nameOk, Bool.and_eq_true, List.all_eq_true] at hn
  have h1 := hn.2 x h
  have hx' : x.toNat < 32 := by simpa [UInt8.lt_iff_toNat_lt] using hx
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h1
  simp only [UInt8.reduceToNat] at h1
  omega

/-- Every byte of a field is a digit, `|`, or `*`. -/
theorem mem_field {w : UInt64} {x : UInt8} (h : x ∈ field w) :
    isDigit x = true ∨ x = bar ∨ x = 0x2A := by
  unfold field at h
  split at h
  · exact Or.inr (Or.inr (by simpa [ascii_star] using h))
  · rw [ascii_bar] at h
    rcases mem_intercalate h with h | ⟨l, hl, hx⟩
    · exact Or.inr (Or.inl h)
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
      exact Or.inl (decimal_digit hx)

theorem not_mem_field {w : UInt64} {x : UInt8} (hd : isDigit x = false) (hb : x ≠ bar)
    (hs : x ≠ 0x2A) : x ∉ field w := fun h => by
  rcases mem_field h with h | h | h
  · rw [h] at hd; exact absurd hd (by decide)
  · exact hb h
  · exact hs h

/-! ## Lines of the written file -/

theorem readLine_cons {α : Type} {j : Nat} {r : Role} {parse : List UInt8 → Option α}
    {l p : List UInt8} {ps : List (List UInt8)} {a : α} (h : parse l = some a) :
    readLine j r parse (l :: p :: ps) = .ok (a, p :: ps) := by
  simp [readLine, takeLine, h]

theorem ascii_contest_sp : ascii "contest " = ascii "contest" ++ [sp] := rfl
theorem ascii_positions_sp : ascii "positions " = ascii "positions" ++ [sp] := rfl
theorem ascii_candidates_sp : ascii "candidates " = ascii "candidates" ++ [sp] := rfl
theorem ascii_candidate_sp : ascii "candidate " = ascii "candidate" ++ [sp] := rfl
theorem ascii_order_sp : ascii "order " = ascii "order" ++ [sp] := rfl
theorem ascii_ballots_sp : ascii "ballots " = ascii "ballots" ++ [sp] := rfl
theorem ascii_comma : ascii "," = [comma] := rfl

theorem parseFormat_line : parseFormat (ascii "rcv-ballots 1") = some () := by
  simp [parseFormat]

theorem parseContest_line {id : List UInt8} (h : identOk id = true) :
    parseContest (spaced [ascii "contest", id]) = some id := by
  rw [spaced_two, show ascii "contest" ++ sp :: id = ascii "contest " ++ id by
    rw [ascii_contest_sp, List.append_assoc]; rfl]
  simp [parseContest, after_append, h]

theorem parseBounded_line {p q : String} (hq : ascii q = ascii p ++ [sp]) {lo hi v : Nat}
    (hlo : lo ≤ v) (hhi : v ≤ hi) : parseBounded q lo hi (spaced [ascii p, decimal v]) = some v := by
  rw [spaced_two, show ascii p ++ sp :: decimal v = ascii q ++ decimal v by
    rw [hq, List.append_assoc]; rfl]
  simp [parseBounded, after_append, number_decimal, hlo, hhi]

theorem parseKind_word (k : Kind) : parseKind (ascii (kindWord k)) = some k := by
  cases k <;> decide

theorem kindWord_no_sp (k : Kind) : sp ∉ ascii (kindWord k) := by
  cases k <;> decide

theorem parseCandidate_line {i : Nat} {x : Candidate} (h : nameOk x.name = true) :
    parseCandidate i (spaced [ascii "candidate", decimal i, ascii (kindWord x.kind), x.name]) =
      some x := by
  have e : spaced [ascii "candidate", decimal i, ascii (kindWord x.kind), x.name] =
      ascii "candidate " ++ (decimal i ++ sp :: (ascii (kindWord x.kind) ++ sp :: x.name)) := by
    rw [spaced_cons_cons, spaced_cons_cons, spaced_two, ascii_candidate_sp, List.append_assoc]
    rfl
  rw [e]
  simp only [parseCandidate, after_append, span_sep (decimal_no_sp i),
    span_sep (kindWord_no_sp x.kind), number_decimal, h, parseKind_word]
  simp

theorem parseOrder_line {n : Nat} {o : List Nat} (hp : o.Perm (List.range' 1 n)) (hne : o ≠ []) :
    parseOrder n (spaced (ascii "order" :: o.map decimal)) = some o := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hne
  have e : spaced (ascii "order" :: (d :: ds).map decimal) =
      ascii "order " ++ [sp].intercalate ((d :: ds).map decimal) := by
    rw [List.map_cons, spaced_cons_cons, ascii_order_sp, List.append_assoc]
    rfl
  have hsplit : ([sp].intercalate ((d :: ds).map decimal)).splitOn sp = (d :: ds).map decimal := by
    refine List.splitOn_intercalate sp ?_ (by simp)
    intro l hl
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact decimal_no_sp i
  rw [e]
  simp only [parseOrder, after_append, hsplit,
    mapM_map_some number decimal id (d :: ds) (fun i _ => number_decimal i)]
  simp [hp]

/-- A ballot line that meets the constraints reads back as its ballot. -/
theorem parseBallot_line {k n : Nat} (hn : n ≤ 63) {b : Ballot}
    (hid : b.ident.all identOk = true) (hk : b.positions.length = k) (hk1 : 1 ≤ k)
    (hw : ∀ w ∈ b.positions, ValidWord n w) : parseBallot k n (ballotLine b) = some b := by
  have hfields : ∀ l ∈ b.ident.toList ++ b.positions.map field, comma ∉ l := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · cases hb : b.ident with
      | none => rw [hb] at hl; simp at hl
      | some id =>
        rw [hb] at hl hid
        have hl' : l = id := by simpa using hl
        rw [hl']
        exact not_mem_ident (by simpa using hid) (by decide)
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hl
      exact not_mem_field (by decide) (by decide) (by decide)
  have hne : b.ident.toList ++ b.positions.map field ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [List.length_append, List.length_map, List.length_nil] at this
    omega
  have hsplit : (ballotLine b).splitOn comma = b.ident.toList ++ b.positions.map field := by
    rw [ballotLine, ascii_comma]
    exact List.splitOn_intercalate comma hfields hne
  have hpos : (b.positions.map field).mapM (parsePosition n) = some b.positions := by
    have := mapM_map_some (parsePosition n) field id b.positions
      (fun w hw' => parsePosition_field hn (hw w hw'))
    simpa using this
  obtain ⟨ident, positions⟩ := b
  simp only at hsplit hpos hk hid
  cases ident with
  | none =>
    obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil (by
      intro he; subst he; simp at hk; omega : positions ≠ [])
    simp only [Option.toList_none, List.nil_append] at hsplit
    rw [parseBallot, hsplit, List.map_cons]
    simp only []
    rw [if_pos (by simpa using hk), ← List.map_cons, hpos]
    rfl
  | some id =>
    simp only [Option.toList_some, List.singleton_append] at hsplit
    have hid' : identOk id = true := by simpa using hid
    rw [parseBallot, hsplit]
    simp only []
    rw [if_neg (by simp [hk]), if_pos ⟨by simp [hk], hid'⟩, hpos]
    rfl

/-- The line of a candidate with its index, as `headerLines` writes it. -/
def candidateText (p : Candidate × Nat) : List UInt8 :=
  spaced [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind), p.1.name]

theorem readCandidates_lines (cs : List Candidate) (i : Nat) (rest : List (List UInt8))
    (hrest : rest ≠ []) (hnames : ∀ x ∈ cs, nameOk x.name = true) :
    readCandidates i cs.length ((cs.zipIdx i).map candidateText ++ rest) = .ok (cs, rest) := by
  induction cs generalizing i with
  | nil => simp [readCandidates]
  | cons x xs ih =>
    have hne : (xs.zipIdx (i + 1)).map candidateText ++ rest ≠ [] := by simp [hrest]
    obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil hne
    have hx : parseCandidate i (candidateText (x, i)) = some x :=
      parseCandidate_line (hnames x List.mem_cons_self)
    simp only [List.zipIdx_cons, List.map_cons, List.cons_append, List.length_cons]
    rw [readCandidates, hps, readLine_cons hx, ← hps]
    simp only []
    rw [ih (i + 1) (fun y hy => hnames y (List.mem_cons_of_mem x hy))]

theorem readBallots_lines (k n : Nat) (hn : n ≤ 63) (hk1 : 1 ≤ k) (bs : List Ballot) (j : Nat)
    (acc : List Ballot) (rest : List (List UInt8)) (hrest : rest ≠ [])
    (hb : ∀ b ∈ bs, b.ident.all identOk = true ∧ b.positions.length = k ∧
      ∀ w ∈ b.positions, ValidWord n w) :
    readBallots k n j bs.length acc (bs.map ballotLine ++ rest) = .ok (acc.reverse ++ bs, rest) := by
  induction bs generalizing j acc with
  | nil => simp [readBallots]
  | cons b bs ih =>
    have hne : bs.map ballotLine ++ rest ≠ [] := by simp [hrest]
    obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨h1, h2, h3⟩ := hb b List.mem_cons_self
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [readBallots, hps, readLine_cons (parseBallot_line hn h1 h2 hk1 h3), ← hps]
    simp only []
    rw [ih (j + 1) (b :: acc) (fun b' hb' => hb b' (List.mem_cons_of_mem b hb'))]
    simp

theorem spaced_no_lf {parts : List (List UInt8)} (h : ∀ l ∈ parts, lf ∉ l) : lf ∉ spaced parts :=
  not_mem_intercalate (by decide) h

/-- No line of the file of a structure that meets the constraints holds LF. -/
theorem lines_no_lf {c : Contest} (hc : c.WellFormed) :
    ∀ l ∈ (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine, lf ∉ l := by
  obtain ⟨_, _, _, _, _, hid, hnames, _, hballots⟩ := hc
  have hdec : ∀ v, lf ∉ decimal v := decimal_no_lf
  intro l hl
  rw [List.cons_append, List.mem_cons] at hl
  rcases hl with rfl | hl
  · decide
  rcases List.mem_append.mp hl with hl | hl
  · simp only [headerLines, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
      or_false] at hl
    rcases hl with ((rfl | rfl | rfl) | ⟨p, hp, rfl⟩) | (rfl | rfl)
    · refine spaced_no_lf ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl)
      · decide
      · exact not_mem_ident hid (by decide)
    · refine spaced_no_lf ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl)
      · decide
      · exact hdec _
    · refine spaced_no_lf ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl)
      · decide
      · exact hdec _
    · have hname := hnames p.1 (List.fst_mem_of_mem_zipIdx hp)
      refine spaced_no_lf ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl | rfl | rfl)
      · decide
      · exact hdec _
      · cases p.1.kind <;> decide
      · exact not_mem_name hname (by decide)
    · refine spaced_no_lf ?_
      simp only [List.mem_cons]
      rintro l (rfl | hl)
      · decide
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
        exact hdec _
    · refine spaced_no_lf ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro l (rfl | rfl)
      · decide
      · exact hdec _
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hl
    obtain ⟨hbid, _, _⟩ := hballots b hb
    rw [ballotLine, ascii_comma]
    refine not_mem_intercalate (by decide) ?_
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · cases hi : b.ident with
      | none => rw [hi] at hl; simp at hl
      | some id =>
        rw [hi] at hl hbid
        have hl' : l = id := by simpa using hl
        rw [hl']
        exact not_mem_ident (by simpa using hbid) (by decide)
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hl
      exact not_mem_field (by decide) (by decide) (by decide)

/-- The file of a structure that meets the constraints splits into its lines and the empty piece
after the final LF. -/
theorem write_splitOn {c : Contest} (hc : c.WellFormed) :
    (write c).splitOn lf =
      (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine ++ [[]] :=
  splitOn_text (lines_no_lf hc)

/-- T2(a) over the lines: the lines of the file of a structure that meets the constraints read as
the structure. -/
theorem readLines_write {c : Contest} (hc : c.WellFormed) :
    readLines ((write c).splitOn lf) = .ok c := by
  have hlines := write_splitOn hc
  obtain ⟨hk1, hk2, hn1, hn2, hN, hid, hnames, hperm, hballots⟩ := hc
  rw [hlines]
  have horder : c.order ≠ [] := by
    intro he
    rw [he] at hperm
    have := hperm.length_eq
    simp at this
    omega
  have hlist : (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine ++ [[]] =
      ascii "rcv-ballots 1" :: spaced [ascii "contest", c.contest] ::
        spaced [ascii "positions", decimal c.positions] ::
        spaced [ascii "candidates", decimal c.candidates.length] ::
        ((c.candidates.zipIdx 1).map candidateText ++
          (spaced (ascii "order" :: c.order.map decimal) ::
            spaced [ascii "ballots", decimal c.ballots.length] ::
            (c.ballots.map ballotLine ++ [[]]))) := by
    simp [headerLines, candidateText]
  rw [hlist]
  obtain ⟨p0, ps0, h0⟩ := List.exists_cons_of_ne_nil (show (c.candidates.zipIdx 1).map candidateText ++
    (spaced (ascii "order" :: c.order.map decimal) ::
      spaced [ascii "ballots", decimal c.ballots.length] :: (c.ballots.map ballotLine ++ [[]])) ≠ []
    by simp)
  rw [h0]
  have hrest : c.ballots.map ballotLine ++ [[]] ≠ [] := by simp
  obtain ⟨p, ps, hpps⟩ := List.exists_cons_of_ne_nil hrest
  have hcands := readCandidates_lines c.candidates 1
    (spaced (ascii "order" :: c.order.map decimal) ::
      spaced [ascii "ballots", decimal c.ballots.length] :: (c.ballots.map ballotLine ++ [[]]))
    (by simp) hnames
  have hbs := readBallots_lines c.positions c.candidates.length hn2 hk1 c.ballots
    (7 + c.candidates.length) [] [[]] (by simp) hballots
  simp only [List.reverse_nil, List.nil_append] at hbs
  have hpos := parseBounded_line (q := "positions ") (p := "positions") ascii_positions_sp hk1 hk2
  have hcan := parseBounded_line (q := "candidates ") (p := "candidates") ascii_candidates_sp hn1 hn2
  have hbal := parseBounded_line (q := "ballots ") (p := "ballots") ascii_ballots_sp
    (Nat.zero_le c.ballots.length) hN
  simp only [readLines, readLine_cons parseFormat_line, readLine_cons (parseContest_line hid),
    readLine_cons hpos, readLine_cons hcan, bind, Except.bind, pure, Except.pure]
  rw [← h0, hcands]
  simp only []
  rw [hpps, readLine_cons (parseOrder_line hperm horder)]
  simp only []
  rw [readLine_cons hbal, ← hpps]
  simp only []
  rw [hbs]
  simp

/-- T2(a): the file of a structure that meets the constraints reads as the structure. -/
theorem read_write {c : Contest} (hc : c.WellFormed) : read (write c) = .ok c := by
  simp [read, readLines_write hc]

/-! ## T2(b): a file that reads is the file of its structure -/

theorem span_some {s : UInt8} {l a r : List UInt8} {x : UInt8}
    (h : l.span (· != s) = (a, x :: r)) : l = a ++ s :: r ∧ s ∉ a := by
  rw [List.span_eq_takeWhile_dropWhile] at h
  injection h with h1 h2
  have hl := List.takeWhile_append_dropWhile (p := (· != s)) (l := l)
  have hx : x = s := by
    have := List.head_dropWhile_not (· != s) (l := l) (by rw [h2]; simp)
    simp only [h2, List.head_cons, bne_eq_false_iff_eq] at this
    exact this
  subst hx
  refine ⟨by rw [← hl, h1, h2], ?_⟩
  intro hm
  have := List.all_takeWhile (p := (· != x)) (l := l)
  rw [h1, List.all_eq_true] at this
  simpa using this x hm

theorem eq_of_parseFormat {l : List UInt8} {u : Unit} (h : parseFormat l = some u) :
    l = ascii "rcv-ballots 1" := by
  unfold parseFormat at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem eq_of_parseContest {l id : List UInt8} (h : parseContest l = some id) :
    l = spaced [ascii "contest", id] ∧ identOk id = true := by
  unfold parseContest at h
  split at h
  · rename_i r hr
    split at h
    · cases h
      refine ⟨?_, by assumption⟩
      rw [eq_of_after hr, spaced_two, ascii_contest_sp, List.append_assoc]
      rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem eq_of_parseBounded {p q : String} (hq : ascii q = ascii p ++ [sp]) {lo hi v : Nat}
    {l : List UInt8} (h : parseBounded q lo hi l = some v) :
    l = spaced [ascii p, decimal v] ∧ lo ≤ v ∧ v ≤ hi := by
  unfold parseBounded at h
  split at h
  · rename_i r hr
    split at h
    · rename_i v' hv
      split at h
      · rename_i hr'
        cases h
        refine ⟨?_, hr'⟩
        rw [eq_of_after hr, decimal_of_number hv, spaced_two, hq, List.append_assoc]
        rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem eq_of_parseKind {bs : List UInt8} {k : Kind} (h : parseKind bs = some k) :
    bs = ascii (kindWord k) := by
  unfold parseKind at h
  split at h
  · cases h; assumption
  · split at h
    · cases h; assumption
    · split at h
      · cases h; assumption
      · split at h
        · cases h; assumption
        · exact absurd h (by simp)

theorem eq_of_parseCandidate {i : Nat} {l : List UInt8} {x : Candidate}
    (h : parseCandidate i l = some x) :
    l = spaced [ascii "candidate", decimal i, ascii (kindWord x.kind), x.name] ∧
      nameOk x.name = true := by
  unfold parseCandidate at h
  split at h
  · rename_i rest hr
    split at h
    · rename_i index s1 rest1 hs1
      split at h
      · rename_i word s2 name hs2
        split at h
        · rename_i hc
          obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨e1, _⟩ := span_some hs1
          obtain ⟨e2, _⟩ := span_some hs2
          refine ⟨?_, hc.2⟩
          rw [eq_of_after hr, e1, e2, decimal_of_number hc.1, eq_of_parseKind hk,
            spaced_cons_cons, spaced_cons_cons, spaced_two, ascii_candidate_sp, List.append_assoc]
          rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem eq_of_parseOrder {n : Nat} {l : List UInt8} {o : List Nat} (h : parseOrder n l = some o) :
    l = spaced (ascii "order" :: o.map decimal) ∧ o.Perm (List.range' 1 n) := by
  unfold parseOrder at h
  split at h
  · rename_i rest hr
    split at h
    · rename_i is his
      split at h
      · rename_i hp
        cases h
        refine ⟨?_, hp⟩
        have hpieces := (mapM_some_iff number _ _).mp his
        have hmap := map_decimal_of_forall₂ hpieces
        have hne : rest.splitOn sp ≠ [] := List.splitOn_ne_nil _ _
        have his_ne : o ≠ [] := by
          intro he
          have hl := hpieces.length_eq
          rw [he, List.length_nil] at hl
          exact hne (List.eq_nil_of_length_eq_zero hl)
        obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil his_ne
        rw [eq_of_after hr, List.map_cons, spaced_cons_cons, ascii_order_sp, List.append_assoc,
          ← List.map_cons, spaced_eq, hmap, List.intercalate_splitOn]
        rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The ballot that a ballot line reads as meets the constraints and prints as the line. -/
theorem eq_of_parseBallot {k n : Nat} (hn : n ≤ 63) {l : List UInt8} {b : Ballot}
    (h : parseBallot k n l = some b) :
    ballotLine b = l ∧ b.ident.all identOk = true ∧ b.positions.length = k ∧
      ∀ w ∈ b.positions, ValidWord n w := by
  have fields : ∀ (fs : List (List UInt8)) (ws : List UInt64),
      fs.mapM (parsePosition n) = some ws →
        ws.map field = fs ∧ ws.length = fs.length ∧ ∀ w ∈ ws, ValidWord n w := by
    intro fs ws hws
    have hf := (mapM_some_iff _ _ _).mp hws
    refine ⟨?_, hf.length_eq.symm, ?_⟩
    · clear hws
      induction hf with
      | nil => rfl
      | cons hab _ ih => rw [List.map_cons, (field_of_parsePosition hn hab).1, ih]
    · clear hws
      induction hf with
      | nil => simp
      | cons hab _ ih =>
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact (field_of_parsePosition hn hab).2
        · exact ih w hw
  unfold parseBallot at h
  split at h
  · exact absurd h (by simp)
  · rename_i first rest hsplit
    have hl : l = [comma].intercalate (first :: rest) := by
      rw [← hsplit, List.intercalate_splitOn]
    split at h
    · rename_i hlen
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmap, hlen', hvalid⟩ := fields _ ws hws
      refine ⟨?_, rfl, by rw [hlen', hlen], hvalid⟩
      rw [ballotLine, ascii_comma, hl]
      simp [hmap]
    · split at h
      · rename_i _ hc
        obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hmap, hlen', hvalid⟩ := fields _ ws hws
        refine ⟨?_, by simpa using hc.2, by rw [hlen', hc.1], hvalid⟩
        rw [ballotLine, ascii_comma, hl]
        simp [hmap]
      · exact absurd h (by simp)

theorem readLine_ok {α : Type} {j : Nat} {r : Role} {parse : List UInt8 → Option α}
    {ps rest : List (List UInt8)} {a : α} (h : readLine j r parse ps = .ok (a, rest)) :
    ∃ l, ps = l :: rest ∧ rest ≠ [] ∧ parse l = some a := by
  unfold readLine takeLine at h
  match ps, h with
  | l :: p :: ps', h =>
    simp only [] at h
    split at h
    · rename_i a' ha
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨l, rfl, by simp, ha⟩
    · exact absurd h (by simp)
  | [], h => exact absurd h (by simp)
  | [_], h => exact absurd h (by simp)

theorem readCandidates_ok {i count : Nat} {ps rest : List (List UInt8)} {cs : List Candidate}
    (h : readCandidates i count ps = .ok (cs, rest)) :
    cs.length = count ∧ ps = (cs.zipIdx i).map candidateText ++ rest ∧
      ∀ x ∈ cs, nameOk x.name = true := by
  induction count generalizing i ps cs with
  | zero =>
    simp only [readCandidates, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ count ih =>
    unfold readCandidates at h
    split at h
    · rename_i x rest1 h1
      split at h
      · rename_i xs rest2 h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨l, rfl, _, hl⟩ := readLine_ok h1
        obtain ⟨hlen, hps, hnames⟩ := ih h2
        obtain ⟨hline, hname⟩ := eq_of_parseCandidate hl
        refine ⟨by simp [hlen], ?_, ?_⟩
        · rw [hps, hline]
          rfl
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hname
          · exact hnames y hy
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem readBallots_ok {k n : Nat} (hn : n ≤ 63) {j count : Nat} {acc bs : List Ballot}
    {ps rest : List (List UInt8)} (h : readBallots k n j count acc ps = .ok (bs, rest)) :
    ∃ new : List Ballot, bs = acc.reverse ++ new ∧ new.length = count ∧
      ps = new.map ballotLine ++ rest ∧
      ∀ b ∈ new, b.ident.all identOk = true ∧ b.positions.length = k ∧
        ∀ w ∈ b.positions, ValidWord n w := by
  induction count generalizing j acc ps with
  | zero =>
    simp only [readBallots, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, by simp, by simp⟩
  | succ count ih =>
    unfold readBallots at h
    split at h
    · rename_i x rest1 h1
      obtain ⟨l, rfl, _, hl⟩ := readLine_ok h1
      obtain ⟨new, hbs, hlen, hps, hprops⟩ := ih h
      obtain ⟨hline, hid, hk, hw⟩ := eq_of_parseBallot hn hl
      refine ⟨x :: new, by simp [hbs], by simp [hlen], by rw [hps, ← hline]; rfl, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hid, hk, hw⟩
      · exact hprops b hb
    · exact absurd h (by simp)

theorem bind_eq_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {b : β}
    (h : e.bind f = .ok b) : ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e with
  | error => simp [Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- The lines that read as a structure are the lines of its file, and the structure meets the
constraints. -/
theorem readLines_ok {ps : List (List UInt8)} {c : Contest} (h : readLines ps = .ok c) :
    ps = (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine ++ [[]] ∧
      c.WellFormed := by
  unfold readLines at h
  obtain ⟨⟨u, ps1⟩, h1, h⟩ := bind_eq_ok h
  obtain ⟨⟨contest, ps2⟩, h2, h⟩ := bind_eq_ok h
  obtain ⟨⟨k, ps3⟩, h3, h⟩ := bind_eq_ok h
  obtain ⟨⟨n, ps4⟩, h4, h⟩ := bind_eq_ok h
  obtain ⟨⟨candidates, ps5⟩, h5, h⟩ := bind_eq_ok h
  obtain ⟨⟨order, ps6⟩, h6, h⟩ := bind_eq_ok h
  obtain ⟨⟨N, ps7⟩, h7, h⟩ := bind_eq_ok h
  obtain ⟨⟨ballots, ps8⟩, h8, h⟩ := bind_eq_ok h
  simp only [] at h
  split at h
  · rename_i hend
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h hend
    obtain ⟨l1, rfl, _, hl1⟩ := readLine_ok h1
    obtain ⟨l2, rfl, _, hl2⟩ := readLine_ok h2
    obtain ⟨l3, rfl, _, hl3⟩ := readLine_ok h3
    obtain ⟨l4, rfl, _, hl4⟩ := readLine_ok h4
    obtain ⟨hclen, rfl, hnames⟩ := readCandidates_ok h5
    obtain ⟨l6, rfl, _, hl6⟩ := readLine_ok h6
    obtain ⟨l7, rfl, _, hl7⟩ := readLine_ok h7
    have e1 := eq_of_parseFormat hl1
    obtain ⟨e2, hid⟩ := eq_of_parseContest hl2
    obtain ⟨e3, hk1, hk2⟩ := eq_of_parseBounded ascii_positions_sp hl3
    obtain ⟨e4, hn1, hn2⟩ := eq_of_parseBounded ascii_candidates_sp hl4
    obtain ⟨e6, hperm⟩ := eq_of_parseOrder hl6
    obtain ⟨e7, -, hN⟩ := eq_of_parseBounded ascii_ballots_sp hl7
    obtain ⟨new, hbs, hblen, rfl, hprops⟩ := readBallots_ok hn2 h8
    simp only [List.reverse_nil, List.nil_append] at hbs
    subst hbs hclen hblen
    refine ⟨?_, hk1, hk2, hn1, hn2, hN, hid, hnames, hperm, hprops⟩
    subst e1 e2 e3 e4 e6 e7
    simp [headerLines, candidateText]
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- T2(b) and the constraints: a file that reads as a structure is the file of the structure, and
the structure meets the constraints. -/
theorem write_of_read {b : List UInt8} {c : Contest} (h : read b = .ok c) :
    write c = b ∧ c.WellFormed := by
  have h' : readLines (b.splitOn lf) = .ok c := by
    unfold read at h
    split at h
    · rename_i c' hc'
      cases h
      exact hc'
    · exact absurd h (by simp)
  obtain ⟨hlines, hc⟩ := readLines_ok h'
  refine ⟨?_, hc⟩
  rw [← intercalate_splitOn' lf b, hlines, write, text_eq]

end Demos.Rcv.Spec
