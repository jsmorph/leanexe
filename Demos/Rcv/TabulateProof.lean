import Demos.Rcv.TabulateProgram
import Demos.Rcv.PrintProof
import Demos.Rcv.Refinement

/-!
The export `tabulate` returns the report of every file: `tabulate_eq` states that the bytes of
`tabulate b` are `reportFile` of the bytes of `b`, for every buffer that memory holds.  The proof
composes the reader program's theorem `readContest_eq`, the count program's `count_eq`, and the
printer's `printReport_eq` and `printError_eq`, with `countWords_contestWords`, which states that
the count over the words of a structure is the count of the structure.
-/

namespace Demos.Rcv.TabulateProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram
open scoped List

/-! ## The error report -/

theorem pushRole_toList (o : Array UInt64) (r : Role) :
    (pushRole o (UInt64.ofNat r.code)).toList = o.toList ++ (ascii r.word).map UInt8.toUInt64 := by
  cases r <;>
    simp (config := { decide := true }) only [pushRole, Role.code, Role.word, ↓reduceIte,
      pushWord_toList, List.append_assoc] <;>
    exact congrArg (o.toList ++ ·) (by decide)

theorem spaced_one (a : List UInt8) : spaced [a] = a := by simp [spaced]

theorem errorReport_eq (j : Nat) (r : Role) :
    errorReport j r = text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++
      (ascii "error" ++ [sp] ++ decimal j ++ [sp] ++ ascii r.word ++ [lf]) := by
  have h3 : spaced [ascii "error", decimal j, ascii r.word] =
      ascii "error" ++ [sp] ++ decimal j ++ [sp] ++ ascii r.word := by
    rw [spaced_cons_cons, spaced_two]; simp
  rw [errorReport, show [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier],
    spaced [ascii "error", decimal j, ascii r.word]] = [ascii "rcv-report 1",
    spaced [ascii "rule", ascii ruleIdentifier]] ++ [spaced [ascii "error", decimal j,
    ascii r.word]] from rfl, text_append, h3]
  simp [text, lf]

set_option maxRecDepth 10000 in
theorem head_length :
    (text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]]).length = 213 := by
  decide

theorem printError_eq (j : Nat) (hj : j < 2 ^ 64) (r : Role) :
    bytesOf (printError (UInt64.ofNat j) (UInt64.ofNat r.code)) = errorReport j r := by
  have hd : (decimal j).length ≤ 20 := by
    have := Library.Numerics.Decimal.Int64Text.digitWords_length_le j hj
    rwa [digitWords_eq, List.length_map] at this
  have hw : (ascii r.word).length ≤ 10 := by cases r <;> decide
  have ho : ((pushRole ((pushNumber (pushWord (pushHead #[]) 0x20726f727265 6)
      (UInt64.ofNat j)).push 32) (UInt64.ofNat r.code)).push 10).toList =
      (errorReport j r).map UInt8.toUInt64 := by
    rw [Array.toList_push, pushRole_toList, Array.toList_push, pushNumber_toList, pushWord_toList,
      pushHead_toList, ofNat_toNat_small hj, errorReport_eq]
    have h6 : wordBytes 0x20726f727265 (6 : UInt64).toNat = (ascii "error" ++ [sp]).map
        UInt8.toUInt64 := by decide
    rw [h6]
    simp [lf, sp]
  have hlen : (errorReport j r).length < 2 ^ 64 := by
    rw [errorReport_eq, List.length_append, head_length]
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : (ascii "error").length = 5 := rfl
    omega
  unfold printError
  simp only []
  rw [toBytes_toList _ (by
    have := congrArg List.length ho
    rw [Array.length_toList] at this
    rw [this, List.length_map]
    exact hlen), ho, map_toUInt8_toUInt64]

/-! ## The count over the words of a structure -/

theorem chunks_flatMap (k : Nat) (bs : List Ballot) (h : ∀ b ∈ bs, b.positions.length = k) :
    chunks k bs.length (bs.flatMap fun b : Ballot => b.positions) = bs.map fun b : Ballot => b.positions := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    have hx := h x List.mem_cons_self
    simp only [List.length_cons, chunks, List.flatMap_cons, List.map_cons]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
      ih (fun b hb => h b (List.mem_cons_of_mem x hb))]

theorem flatMap_positions_length (k : Nat) (bs : List Ballot) (h : ∀ b ∈ bs, b.positions.length = k) :
    (bs.flatMap fun b : Ballot => b.positions).length = bs.length * k := by
  induction bs with
  | nil => simp
  | cons x bs ih =>
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem x hb)), List.length_cons, Nat.succ_mul]
    omega

theorem kindOfCode_kindCode (k : Kind) : kindOfCode (kindCode k) = k := by cases k <;> rfl

theorem kindCode_lt (k : Kind) : kindCode k < 4 := by cases k <;> decide

theorem contestWords_length (c : Contest) (hc : c.WellFormed) :
    (contestWords c).length = 3 + 2 * c.candidates.length + c.ballots.length * c.positions := by
  have hlenb : ∀ b ∈ c.ballots, b.positions.length = c.positions := fun b hb => (hc.2.2.2.2.2.2.2.2 b hb).2.1
  have hol : c.order.length = c.candidates.length := by simpa using hc.2.2.2.2.2.2.2.1.length_eq
  simp only [contestWords, List.length_append, List.length_map, List.length_cons, List.length_nil,
    hol, flatMap_positions_length _ _ hlenb]
  omega

/-- The count over the words of a structure that meets the constraints is the count of the
structure. -/
theorem countWords_contestWords (c : Contest) (hc : c.WellFormed) :
    countWords (contestWords c) = resultWords c.candidates.length (countContest c) := by
  obtain ⟨hk1, hk2, hn1, hn2, hN, hid, hnames, hperm, hballots⟩ := hc
  simp only [maxIndex] at hk2 hn2
  have hNb : c.ballots.length < 2 ^ 64 := by simp [maxBallots] at hN; omega
  have hlenb : ∀ b ∈ c.ballots, b.positions.length = c.positions := fun b hb => (hballots b hb).2.1
  have hon : ∀ i ∈ c.order, i < 2 ^ 64 := by
    intro i hi
    have := List.mem_range'_1.mp (hperm.subset hi)
    omega
  set n := c.candidates.length with hn
  set K := c.candidates.map fun x : Candidate => kindCode x.kind with hK
  set P := c.ballots.flatMap fun b : Ballot => b.positions with hP
  have hws : contestWords c = [UInt64.ofNat n, UInt64.ofNat c.positions,
      UInt64.ofNat c.ballots.length] ++ (K.map UInt64.ofNat ++ (c.order.map UInt64.ofNat ++ P)) := by
    simp only [contestWords, List.map_append, List.map_cons, List.map_nil, List.append_assoc, hK,
      hP, List.cons_append, List.nil_append]
    rfl
  have hKl : (K.map UInt64.ofNat).length = n := by simp [hK, hn]
  have hol : c.order.length = n := by simpa using hperm.length_eq
  have hOl : (c.order.map UInt64.ofNat).length = n := by simp [hol]
  have hd3 : (contestWords c).drop 3 = K.map UInt64.ofNat ++ (c.order.map UInt64.ofNat ++ P) := by
    rw [hws]; exact List.drop_left' rfl
  have hd3n : (contestWords c).drop (3 + n) = c.order.map UInt64.ofNat ++ P := by
    rw [← List.drop_drop, hd3]; exact List.drop_left' hKl
  have hd32n : (contestWords c).drop (3 + 2 * n) = P := by
    rw [show 3 + 2 * n = (3 + n) + n by omega, ← List.drop_drop, hd3n]; exact List.drop_left' hOl
  have h0 : ((contestWords c).getD 0 0).toNat = n := by
    rw [hws]; exact ofNat_toNat_small (by omega)
  have h1 : ((contestWords c).getD 1 0).toNat = c.positions := by
    rw [hws]; exact ofNat_toNat_small (by omega)
  have h2 : ((contestWords c).getD 2 0).toNat = c.ballots.length := by
    rw [hws]; exact ofNat_toNat_small hNb
  have hkinds : (K.map UInt64.ofNat).map UInt64.toNat = K := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id K]
    apply List.map_congr_left
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact ofNat_toNat_small (by have := kindCode_lt y.kind; omega)
  have horder : (c.order.map UInt64.ofNat).map UInt64.toNat = c.order := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id c.order]
    apply List.map_congr_left
    intro x hx
    exact ofNat_toNat_small (hon x hx)
  have hrd : readWords (contestWords c) =
      { n, k := c.positions, N := c.ballots.length, kinds := K, order := c.order,
        positions := P } := by
    simp only [readWords, h0, h1, h2, hd3, hd3n, hd32n, List.take_left' hKl, List.take_left' hOl,
      hkinds, horder]
  have hlen : (contestWords c).length = 3 + 2 * n + c.ballots.length * c.positions := by
    rw [hws]
    simp only [List.length_append, List.length_cons, List.length_nil, hKl, hOl, hP,
      flatMap_positions_length _ _ hlenb]
    omega
  have hvalid : (readWords (contestWords c)).Valid (contestWords c).length := by
    rw [hrd, hlen]
    refine ⟨hn1, hn2, hk1, hk2, hN, rfl, ?_, hperm, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact kindCode_lt y.kind
    · intro w hw
      obtain ⟨b, hb, hwb⟩ := List.mem_flatMap.mp hw
      exact (hballots b hb).2.2 w hwb
  unfold countWords
  simp only []
  rw [ite_eq_left hvalid, hrd]
  simp only [Words.ballots]
  rw [chunks_flatMap _ _ hlenb]
  congr 1
  simp only [countContest, kindsOf, hK, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id (c.candidates.map fun x : Candidate => x.kind)]
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  exact kindOfCode_kindCode x.kind

/-! ## The line of an error -/

theorem readLine_error_eq {α : Type} {j : Nat} {r : Role} {parse : List UInt8 → Option α}
    {ps : List (List UInt8)} {e : Nat × Role} (h : readLine j r parse ps = .error e) :
    e = (j, r) := by
  unfold readLine at h
  split at h
  · split at h
    · simp at h
    · cases h; rfl
  · rename_i e' he'
    cases h
    exact takeLine_error he'

theorem readCandidates_error_lt {i count : Nat} {ps : List (List UInt8)} {e : Nat × Role}
    (h : readCandidates i count ps = .error e) : e.1 < 4 + i + count := by
  induction count generalizing i ps with
  | zero => simp [readCandidates] at h
  | succ count ih =>
    unfold readCandidates at h
    split at h
    · split at h
      · simp at h
      · rename_i e' h2
        cases h
        have := ih h2
        omega
    · rename_i e' h1
      cases h
      rw [readLine_error_eq h1]
      simp

theorem readBallots_error_lt {k n j count : Nat} {acc : List Ballot} {ps : List (List UInt8)}
    {e : Nat × Role} (h : readBallots k n j count acc ps = .error e) : e.1 < j + count := by
  induction count generalizing j acc ps with
  | zero => simp [readBallots] at h
  | succ count ih =>
    unfold readBallots at h
    split at h
    · have := ih h
      omega
    · rename_i e' h1
      cases h
      rw [readLine_error_eq h1]
      simp

theorem bind_error {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε}
    (h : x.bind f = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error e' => left; simp [Except.bind] at h; rw [h]
  | ok a => right; exact ⟨a, rfl, h⟩

/-- The line of an error that the reader reports is below `2 ^ 64`. -/
theorem read_error_lt {b : List UInt8} {j : Nat} {r : Role} (h : Spec.read b = .error j r) :
    j < 2 ^ 64 := by
  have h' : readLines (b.splitOn lf) = .error (j, r) := by
    unfold Spec.read at h
    split at h
    · simp at h
    · rename_i e he
      cases h
      exact he
  rw [readLines_split] at h'
  rcases bind_error h' with hh | ⟨⟨cid, k, n, ps⟩, hh, hrest⟩
  · -- the header
    unfold headSpec at hh
    simp only [bind, Except.bind] at hh
    split at hh
    · rename_i e he; cases hh; have := readLine_error_eq he; simp only [Prod.mk.injEq] at this; omega
    · split at hh
      · rename_i e he; cases hh; have := readLine_error_eq he; simp only [Prod.mk.injEq] at this; omega
      · split at hh
        · rename_i e he; cases hh; have := readLine_error_eq he; simp only [Prod.mk.injEq] at this; omega
        · split at hh
          · rename_i e he; cases hh; have := readLine_error_eq he; simp only [Prod.mk.injEq] at this; omega
          · simp [pure, Except.pure] at hh
  · -- the lines after the header
    have hn : n ≤ 63 := by
      unfold headSpec at hh
      simp only [bind, Except.bind] at hh
      split at hh
      · simp at hh
      · split at hh
        · simp at hh
        · split at hh
          · simp at hh
          · split at hh
            · simp at hh
            · rename_i v4 h4
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hh
              obtain ⟨-, -, rfl, -⟩ := hh
              obtain ⟨l, -, -, hl⟩ := readLine_ok h4
              exact (Demos.Rcv.ReadProgram.bounded_le hl).2
    unfold restSpec at hrest
    simp only [bind, Except.bind] at hrest
    split at hrest
    · rename_i e he; cases hrest; have := readCandidates_error_lt he; omega
    · split at hrest
      · rename_i e he; cases hrest; have := readLine_error_eq he; simp only [Prod.mk.injEq] at this; omega
      · split at hrest
        · rename_i e he; cases hrest; have := readLine_error_eq he; simp only [Prod.mk.injEq] at this; omega
        · rename_i v6 h6
          obtain ⟨l, -, -, hl⟩ := readLine_ok h6
          have hN := (Demos.Rcv.ReadProgram.bounded_le hl).2
          simp only [maxBallots] at hN
          split at hrest
          · rename_i e he; cases hrest; have := readBallots_error_lt he; omega
          · split at hrest
            · simp [pure, Except.pure] at hrest
            · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq,
                Prod.mk.injEq] at hrest
              omega

/-! ## The length of a report -/

theorem decimal_length_le {v : Nat} (hv : v < 2 ^ 64) : (decimal v).length ≤ 20 := by
  have := Library.Numerics.Decimal.Int64Text.digitWords_length_le v hv
  rwa [digitWords_eq, List.length_map] at this

theorem text_length (ls : List (List UInt8)) :
    (text ls).length = (ls.map fun l => l.length + 1).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [text_cons, List.length_append, ih]; simp

theorem text_length_le {ls : List (List UInt8)} {m : Nat} (h : ∀ l ∈ ls, l.length ≤ m) :
    (text ls).length ≤ ls.length * (m + 1) := by
  induction ls with
  | nil => simp [text]
  | cons l ls ih =>
    rw [text_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h l List.mem_cons_self
    have := ih (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    simp
    omega

theorem spaced_length_le (parts : List (List UInt8)) :
    (spaced parts).length ≤ (parts.map fun p => p.length + 1).sum := by
  induction parts with
  | nil => simp [spaced]
  | cons p ps ih =>
    cases ps with
    | nil => simp [spaced]
    | cons q qs =>
      rw [spaced_cons_cons, List.length_append, List.length_cons]
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem line_le (X : String) (hX : (ascii X).length ≤ 20) {v : Nat} (hv : v < 2 ^ 64) :
    (spaced [ascii X, decimal v]).length ≤ 50 := by
  have := spaced_length_le [ascii X, decimal v]
  have := decimal_length_le hv
  simp at *
  omega

theorem members_line_le (X : String) (hX : (ascii X).length ≤ 20) {M : List Nat} {n : Nat}
    (hn : n ≤ 63) (hM : M <+ List.range' 1 n) :
    (spaced (ascii X :: M.map decimal)).length ≤ 2000 := by
  have h1 := spaced_length_le (ascii X :: M.map decimal)
  have hlen : M.length ≤ 63 := by have := hM.length_le; simp at this; omega
  have h2 : ((M.map decimal).map fun p => p.length + 1).sum ≤ M.length * 21 := by
    rw [List.map_map]
    have : ∀ x ∈ M.map ((fun p => p.length + 1) ∘ decimal), x ≤ 21 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := (sublist_range'_facts hM).2 i hi
      have := decimal_length_le (v := i) (by omega)
      simp
      omega
    have := List.sum_le_card_nsmul _ 21 this
    simpa using this
  simp only [List.map_cons, List.sum_cons] at h1
  omega

theorem roundLines_length (r : Nat) (rd : Round) {n : Nat} (hn : n ≤ 63) (S : List Nat)
    (f : Nat → Nat) (hvotes : rd.tally.votes = S.map fun i => (i, f i))
    (hS : S <+ List.range' 1 n) (hf : ∀ i ∈ S, f i < 2 ^ 64)
    (hcounts : rd.tally.continuing < 2 ^ 64 ∧ rd.tally.blank < 2 ^ 64 ∧
      rd.tally.uncounted < 2 ^ 64 ∧ rd.tally.overvote < 2 ^ 64 ∧ rd.tally.exhausted < 2 ^ 64)
    (he : ElimOk n rd.elimination) (hr : r < 2 ^ 64) :
    (text (roundLines r rd)).length ≤ 20000 := by
  obtain ⟨hT, hbl, hun, hov, hex⟩ := hcounts
  have hSl : S.length ≤ 63 := by have := hS.length_le; simp at this; omega
  have hrl : roundLines r rd = [spaced [ascii "round", decimal r],
      spaced [ascii "continuing", decimal rd.tally.continuing]] ++
      (rd.tally.votes.map fun x : Nat × Nat => spaced [ascii "votes", decimal x.1, decimal x.2]) ++
      [spaced [ascii "inactive blank", decimal rd.tally.blank],
        spaced [ascii "inactive uncounted", decimal rd.tally.uncounted],
        spaced [ascii "inactive overvote", decimal rd.tally.overvote],
        spaced [ascii "inactive exhausted", decimal rd.tally.exhausted]] ++
      elimLines rd.elimination := by
    unfold roundLines elimLines
    rcases rd.elimination with _ | e <;> rfl
  rw [hrl, text_append, text_append, text_append, List.length_append, List.length_append,
    List.length_append]
  have h1 : (text [spaced [ascii "round", decimal r],
      spaced [ascii "continuing", decimal rd.tally.continuing]]).length ≤ 2 * 51 :=
    text_length_le (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact line_le "round" (by decide) hr
      · exact line_le "continuing" (by decide) hT)
  have h2 : (text (rd.tally.votes.map fun x : Nat × Nat =>
      spaced [ascii "votes", decimal x.1, decimal x.2])).length ≤ 63 * 71 := by
    have := text_length_le (ls := rd.tally.votes.map fun x : Nat × Nat =>
      spaced [ascii "votes", decimal x.1, decimal x.2]) (m := 70) (by
      intro l hl
      rw [hvotes] at hl
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := spaced_length_le [ascii "votes", decimal i, decimal (f i)]
      have := decimal_length_le (v := i) (by have := (sublist_range'_facts hS).2 i hi; omega)
      have := decimal_length_le (hf i hi)
      have : (ascii "votes").length = 5 := rfl
      simp at *
      omega)
    rw [hvotes, List.length_map, List.length_map] at this
    rw [hvotes]
    have : S.length * (70 + 1) ≤ 63 * 71 := Nat.mul_le_mul_right _ hSl
    omega
  have h3 : (text [spaced [ascii "inactive blank", decimal rd.tally.blank],
      spaced [ascii "inactive uncounted", decimal rd.tally.uncounted],
      spaced [ascii "inactive overvote", decimal rd.tally.overvote],
      spaced [ascii "inactive exhausted", decimal rd.tally.exhausted]]).length ≤ 4 * 51 :=
    text_length_le (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact line_le _ (by decide) hbl
      · exact line_le _ (by decide) hun
      · exact line_le _ (by decide) hov
      · exact line_le _ (by decide) hex)
  have h4 : (text (elimLines rd.elimination)).length ≤ 2 * 2001 := by
    rcases hel : rd.elimination with _ | e
    · simp [text, elimLines]
    · rw [hel] at he
      cases e with
      | batch m =>
        have := text_length_le (ls := eliminationLines (.batch m)) (m := 2000) (by
          intro l hl
          simp only [eliminationLines, List.mem_cons, List.not_mem_nil, or_false] at hl
          rw [hl]
          exact members_line_le _ (by decide) hn he)
        simp [eliminationLines, elimLines] at this ⊢
        omega
      | lowest i =>
        have := text_length_le (ls := eliminationLines (.lowest i)) (m := 2000) (by
          intro l hl
          simp only [eliminationLines, List.mem_cons, List.not_mem_nil, or_false] at hl
          rw [hl]
          have := members_line_le "eliminate lowest" (by decide) hn he
          simpa [spaced] using this)
        simp [eliminationLines, elimLines] at this ⊢
        omega
      | order tied i =>
        have := text_length_le (ls := eliminationLines (.order tied i)) (m := 2000) (by
          intro l hl
          simp only [eliminationLines, List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact members_line_le _ (by decide) hn he.1
          · have := members_line_le "eliminate order" (by decide) hn he.2
            simpa [spaced] using this)
        simp [eliminationLines, elimLines] at this ⊢
        omega
  omega

/-- The report of a structure whose file has fewer than `2 ^ 32` bytes has fewer than `2 ^ 64`
bytes. -/
theorem report_length_lt (c : Contest) (hc : c.WellFormed) (hw : (write c).length < 2 ^ 32) :
    (report c).length < 2 ^ 64 := by
  have hn : c.candidates.length ≤ 63 := hc.2.2.2.1
  have hN : c.ballots.length ≤ maxBallots := hc.2.2.2.2.1
  have hNb : c.ballots.length < 2 ^ 32 := by simp [maxBallots] at hN; omega
  have hfacts := count_round_facts (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  have hwin := count_winner (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  have hRle := Demos.Rcv.Winner.rounds_le (kindsOf c) c.order
    (c.ballots.map fun b : Ballot => b.positions)
  have hkl : (kindsOf c).length = c.candidates.length := by simp [kindsOf]
  have hcs := Demos.Rcv.Rounds.countedSet_sublist (kindsOf c)
  have hcsl : (countedSet (kindsOf c)).length ≤ c.candidates.length := by
    have := hcs.length_le; rw [List.length_range', hkl] at this; exact this
  have hdef : count (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions) =
      countContest c := rfl
  rw [hdef, hkl] at hfacts hwin
  rw [hdef] at hRle
  have hR : (countContest c).rounds.length ≤ 64 := by omega
  have hrep : report c = text ([ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++
      headerLines c ++ (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat =>
        roundLines p.2 p.1) ++ [winnerLine (countContest c).winner]) := rfl
  rw [hrep, text_append, text_append, text_append, List.length_append, List.length_append,
    List.length_append, head_length]
  -- the header lines
  have hH : (text (headerLines c)).length ≤ (write c).length := by
    have : write c = text [ascii "rcv-ballots 1"] ++ text (headerLines c) ++
        text (c.ballots.map ballotLine) := by
      rw [write, show (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine =
        [ascii "rcv-ballots 1"] ++ headerLines c ++ c.ballots.map ballotLine from rfl,
        text_append, text_append]
    rw [this, List.length_append, List.length_append]
    omega
  -- the rounds
  have hrounds : (text (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat =>
      roundLines p.2 p.1)).length ≤ 64 * 20000 := by
    rw [text_flatMap, List.length_flatMap]
    have hb : ∀ x ∈ ((countContest c).rounds.zipIdx 1).map
        (fun p : Round × Nat => (text (roundLines p.2 p.1)).length), x ≤ 20000 := by
      intro x hx
      obtain ⟨⟨rd, r⟩, hp, rfl⟩ := List.mem_map.mp hx
      have hrd := List.fst_mem_of_mem_zipIdx hp
      have hr := List.snd_lt_add_of_mem_zipIdx hp
      obtain ⟨S, hvotes, hS, helim, hT, hbl, hun, hov, hex⟩ := hfacts rd hrd
      simp only [List.length_map] at hT hbl hun hov hex
      exact roundLines_length r rd hn S _ hvotes hS
        (fun j _ => Nat.lt_of_le_of_lt List.count_le_length (by simp; omega))
        ⟨by omega, by omega, by omega, by omega, by omega⟩ helim (by simp at hr; omega)
    have := List.sum_le_card_nsmul _ 20000 hb
    simp only [List.length_map, List.length_zipIdx, smul_eq_mul] at this
    exact le_trans this (Nat.mul_le_mul_right _ hR)
  -- the winner
  have hwl : (text [winnerLine (countContest c).winner]).length ≤ 40 := by
    rw [text_length]
    cases hwk : (countContest c).winner with
    | none => simp [winnerLine]; decide
    | some i =>
      have := hwin i hwk
      have hd := decimal_length_le (v := i) (by omega)
      have := spaced_length_le [ascii "winner", decimal i]
      have : (ascii "winner").length = 6 := rfl
      simp [winnerLine] at *
      omega
  omega

/-! ## T1 over bytes -/

theorem getElem!_eq_getD (ws : Array UInt64) (i : Nat) : ws[i]! = ws.toList.getD i 0 := by
  rw [getElem!_def, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  cases ws[i]? <;> rfl

/-- T1 over bytes: the export `tabulate`, on a buffer that memory holds, returns the bytes of the
report of the file, the error report when the reader fails and the printed count otherwise. -/
theorem tabulate_eq (b : Bytes) (hb : b.data.size < 2 ^ 32) :
    bytesOf (tabulate b) = reportFile (bytesOf b) := by
  have hb64 : b.data.size < 2 ^ 64 := by omega
  have hrc := readContest_eq b hb64
  unfold tabulate reportFile
  simp only []
  generalize readContest b = ws at hrc
  unfold readResult at hrc
  cases hr : Spec.read (bytesOf b) with
  | error j r =>
    rw [hr] at hrc
    simp only [] at hrc
    have hj := read_error_lt hr
    rw [getElem!_eq_getD, getElem!_eq_getD, getElem!_eq_getD, hrc]
    simp only [show ((0 : UInt64).toNat) = 0 from rfl, show ((1 : UInt64).toNat) = 1 from rfl,
      show ((2 : UInt64).toNat) = 2 from rfl, List.getD_cons_zero, List.getD_cons_succ]
    rw [ite_eq_left (by rfl), printError_eq j hj r]
  | ok c =>
    rw [hr] at hrc
    simp only [] at hrc
    obtain ⟨hwc, hc⟩ := write_of_read hr
    have hn1 : 1 ≤ c.candidates.length := hc.2.2.1
    have hn2 : c.candidates.length ≤ 63 := hc.2.2.2.1
    have h0 : ws[(0 : UInt64).toNat]! = UInt64.ofNat c.candidates.length := by
      rw [getElem!_eq_getD, hrc]
      rfl
    have hne : (ws[(0 : UInt64).toNat]! == 0) = false := by
      rw [h0]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg UInt64.toNat h
      rw [ofNat_toNat_small (by omega), UInt64.toNat_zero] at this
      omega
    have hsz : ws.size < 2 ^ 64 := by
      rw [← Array.length_toList, hrc, contestWords_length c hc]
      have h1 : c.ballots.length * c.positions ≤ (2 ^ 32) * 63 := by
        have := hc.2.2.2.2.1
        simp only [maxBallots] at this
        exact Nat.mul_le_mul (by omega) hc.2.1
      omega
    rw [ite_eq_right (by rw [hne]; simp), h0, Demos.Rcv.Refine.count_eq ws hsz, countArray, hrc,
      countWords_contestWords c hc]
    exact printReport_eq b hb64 c hc hwc.symm
      (report_length_lt c hc (by rw [hwc]; simpa using hb))

end Demos.Rcv.TabulateProgram
