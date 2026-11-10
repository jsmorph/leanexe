import Demos.Rcv.Maine.TabulateProgram
import Demos.Rcv.Maine.PrintProof
import Demos.Rcv.Maine.Refinement
import Demos.Rcv.TabulateProof

/-!
The Maine export `tabulate` returns the Maine report of every file: `tabulate_eq` states that the
bytes of `tabulate b` are `Demos.Rcv.Maine.reportFile` of the bytes of `b`, for every buffer that
memory holds.  The proof follows the Oakland tabulator's `Demos.Rcv.TabulateProgram.tabulate_eq`:
the shared reader program's theorem `Demos.Rcv.ReadProgram.readContest_eq`, the Maine count's
`Demos.Rcv.Maine.Refine.count_eq`, and the Maine printers' `printReport_eq` and `printError_eq`.
`readWords_contestWords` reads the parts of the words of a structure that meets the constraints,
from which `countWords_contestWords` equates the count over the words with the count of the
structure and `countedOf_contest` gives the mask of its counted set.
-/

namespace Demos.Rcv.Maine.TabulateProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram
open scoped List

/-! ## The error report -/

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
    (text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]]).length = 270 := by
  decide

theorem printError_eq (j : Nat) (hj : j < 2 ^ 64) (r : Role) :
    bytesOf (PrintProgram.printError (UInt64.ofNat j) (UInt64.ofNat r.code)) = errorReport j r := by
  have ho : ((Demos.Rcv.PrintProgram.pushRole ((pushNumber (pushWord (PrintProgram.pushHead #[])
      0x20726f727265 6) (UInt64.ofNat j)).push 32) (UInt64.ofNat r.code)).push 10).toList =
      (errorReport j r).map UInt8.toUInt64 := by
    rw [Array.toList_push, Demos.Rcv.TabulateProgram.pushRole_toList, Array.toList_push,
      pushNumber_toList, pushWord_toList, PrintProgram.pushHead_toList, ofNat_toNat_small hj,
      errorReport_eq]
    have h6 : wordBytes 0x20726f727265 (6 : UInt64).toNat = (ascii "error" ++ [sp]).map
        UInt8.toUInt64 := by decide
    rw [h6]
    simp [lf, sp]
  have hlen : (errorReport j r).length < 2 ^ 64 := by
    rw [errorReport_eq, List.length_append, head_length]
    have := Demos.Rcv.TabulateProgram.decimal_length_le hj
    have hw : (ascii r.word).length ≤ 10 := by cases r <;> decide
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : (ascii "error").length = 5 := rfl
    omega
  unfold PrintProgram.printError
  simp only []
  rw [toBytes_toList _ (by
    have := congrArg List.length ho
    rw [Array.length_toList] at this
    rw [this, List.length_map]
    exact hlen), ho, map_toUInt8_toUInt64]

/-! ## The words of a structure -/

/-- The parts of the words of a structure that meets the constraints are its parts, and the words
form a valid contest array. -/
theorem readWords_contestWords (c : Contest) (hc : c.WellFormed) :
    readWords (contestWords c) =
        { n := c.candidates.length, k := c.positions, N := c.ballots.length,
          kinds := c.candidates.map fun x : Candidate => kindCode x.kind, order := c.order,
          positions := c.ballots.flatMap fun b : Ballot => b.positions } ∧
      (readWords (contestWords c)).Valid (contestWords c).length := by
  obtain ⟨hk1, hk2, hn1, hn2, hN, hid, hnames, hperm, hballots⟩ := hc
  simp only [maxIndex] at hk2 hn2
  have hNb : c.ballots.length < 2 ^ 64 := by simp [maxBallots] at hN; omega
  have hlenb : ∀ b ∈ c.ballots, b.positions.length = c.positions :=
    fun b hb => (hballots b hb).2.1
  have hon : ∀ i ∈ c.order, i < 2 ^ 64 := by
    intro i hi
    have := List.mem_range'_1.mp (hperm.subset hi)
    omega
  set n := c.candidates.length with hn
  set K := c.candidates.map fun x : Candidate => kindCode x.kind with hK
  set P := c.ballots.flatMap fun b : Ballot => b.positions with hP
  have hws : contestWords c = [UInt64.ofNat n, UInt64.ofNat c.positions,
      UInt64.ofNat c.ballots.length] ++
        (K.map UInt64.ofNat ++ (c.order.map UInt64.ofNat ++ P)) := by
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
    exact ofNat_toNat_small (by have := Demos.Rcv.TabulateProgram.kindCode_lt y.kind; omega)
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
      Demos.Rcv.TabulateProgram.flatMap_positions_length _ _ hlenb]
    omega
  refine ⟨hrd, ?_⟩
  rw [hrd, hlen]
  refine ⟨hn1, hn2, hk1, hk2, hN, rfl, ?_, hperm, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact Demos.Rcv.TabulateProgram.kindCode_lt y.kind
  · intro w hw
    obtain ⟨b, hb, hwb⟩ := List.mem_flatMap.mp hw
    exact (hballots b hb).2.2 w hwb

theorem kinds_contestWords (c : Contest) :
    (c.candidates.map fun x : Candidate => kindCode x.kind).map kindOfCode = kindsOf c := by
  simp only [kindsOf, List.map_map]
  apply List.map_congr_left
  intro x _
  exact Demos.Rcv.TabulateProgram.kindOfCode_kindCode x.kind

/-- The count over the words of a structure that meets the constraints is the count of the
structure. -/
theorem countWords_contestWords (c : Contest) (hc : c.WellFormed) :
    countWords (contestWords c) =
      resultWords c.candidates.length (firstContest c) (countContest c) := by
  obtain ⟨hrd, hvalid⟩ := readWords_contestWords c hc
  have hlenb : ∀ b ∈ c.ballots, b.positions.length = c.positions :=
    fun b hb => (hc.2.2.2.2.2.2.2.2 b hb).2.1
  unfold countWords
  simp only []
  rw [ite_eq_left hvalid, hrd]
  simp only [Words.ballots]
  rw [Demos.Rcv.TabulateProgram.chunks_flatMap _ _ hlenb, kinds_contestWords]
  rfl

/-- The program's mask of the counted candidates of the words of a structure is the mask of its
counted set. -/
theorem countedOf_contest (c : Contest) (hc : c.WellFormed) (ws : Array UInt64)
    (hws : ws.toList = contestWords c) :
    Demos.Rcv.Program.countedOf ws (UInt64.ofNat c.candidates.length) =
      UInt64.ofNat (mask (countedSet (kindsOf c))) := by
  obtain ⟨hrd, hvalid⟩ := readWords_contestWords c hc
  have hn2 : c.candidates.length ≤ 63 := hc.2.2.2.1
  have hnN : (UInt64.ofNat c.candidates.length).toNat = c.candidates.length :=
    ofNat_toNat_small (by omega)
  have hsize : 3 + c.candidates.length ≤ ws.size := by
    have := congrArg List.length hws
    rw [Array.length_toList, (Demos.Rcv.TabulateProgram.contestWords_length c hc)] at this
    omega
  have hk : (Refine.wordsAt ws 3 c.candidates.length).map UInt64.toNat =
      c.candidates.map fun x : Candidate => kindCode x.kind := by
    have hkd := congrArg Words.kinds hrd
    have hn := congrArg Words.n hrd
    simp only [readWords] at hkd hn
    rw [hn] at hkd
    rw [← Refine.take_drop_eq_wordsAt ws 3 _ hsize, hws]
    exact hkd
  have hK := Refine.countedSet_eq ws c.candidates.length
  rw [hk, kinds_contestWords] at hK
  apply (Refine.ofNat_eq _).symm
  rw [Refine.countedOf_eq ws _ (by omega), hnN, ← hK]

/-! ## The length of a report -/

theorem first_line_le (i v : Nat) (hi : i < 2 ^ 64) (hv : v < 2 ^ 64) :
    (spaced [ascii "first", decimal i, decimal v]).length ≤ 48 := by
  have := Demos.Rcv.TabulateProgram.spaced_length_le [ascii "first", decimal i, decimal v]
  have := Demos.Rcv.TabulateProgram.decimal_length_le hi
  have := Demos.Rcv.TabulateProgram.decimal_length_le hv
  have : (ascii "first").length = 5 := rfl
  simp at *
  omega

/-- The Maine report of a structure that meets the constraints has at most 1,283,397 bytes beyond
its header lines: the first two lines, 270 bytes, at most 63 `first` lines of at most 49 bytes, at
most 64 rounds of at most 20,000 bytes each, and the winner's line of at most 40 bytes. -/
theorem report_length_le (c : Contest) (hc : c.WellFormed) :
    (report c).length ≤ (text (headerLines c)).length + 1283397 := by
  have hn : c.candidates.length ≤ 63 := hc.2.2.2.1
  have hN : c.ballots.length ≤ maxBallots := hc.2.2.2.2.1
  have hNb : c.ballots.length < 2 ^ 32 := by simp [maxBallots] at hN; omega
  have hfacts := round_facts (kindsOf c) c.order (positionsOf c)
  have hwin := count_winner (kindsOf c) c.order (positionsOf c)
  have hRle := (rounds_le (kindsOf c) c.order (positionsOf c)).2
  have hkl : (kindsOf c).length = c.candidates.length := by simp [kindsOf]
  have hcs := Demos.Rcv.Rounds.countedSet_sublist (kindsOf c)
  have hcsl : (countedSet (kindsOf c)).length ≤ c.candidates.length := by
    have := hcs.length_le; rw [List.length_range', hkl] at this; exact this
  have hdef : count (kindsOf c) c.order (positionsOf c) = countContest c := rfl
  have hpl : (positionsOf c).length = c.ballots.length := by simp [positionsOf]
  rw [hdef, hkl] at hfacts hwin
  rw [hdef] at hRle
  have hR : (countContest c).rounds.length ≤ 64 := by omega
  have hrep : report c = text ([ascii "rcv-report 1",
      spaced [ascii "rule", ascii ruleIdentifier]] ++ headerLines c ++
      firstLines (firstContest c) ++
      (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat => roundLines p.2 p.1) ++
      [winnerLine (countContest c).winner]) := rfl
  rw [hrep, text_append, text_append, text_append, text_append, List.length_append,
    List.length_append, List.length_append, List.length_append, head_length]
  -- the first lines
  have hfirst : (text (firstLines (firstContest c))).length ≤ 63 * 49 := by
    have := Demos.Rcv.TabulateProgram.text_length_le (m := 48)
      (ls := firstLines (firstContest c)) (by
      intro l hl
      simp only [firstLines, firstContest, firstCounts_eq, List.map_map, List.mem_map,
        Function.comp_apply] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      have hi' := Demos.Rcv.Rounds.mem_countedSet hi
      have hf := List.count_le_length (a := Position.single i)
        (l := (positionsOf c).map firstPosition)
      simp only [List.length_map, hpl] at hf
      exact first_line_le i _ (by omega) (by unfold firstCount; omega))
    simp only [firstLines, firstContest, firstCounts_eq, List.length_map] at this
    exact this.trans (Nat.mul_le_mul_right 49 (hcsl.trans hn))
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
      simp only [hpl] at hT hbl hun hov hex
      exact Demos.Rcv.TabulateProgram.roundLines_length r rd hn S _ hvotes hS
        (fun j _ => Nat.lt_of_le_of_lt List.count_le_length (by simp [hpl]; omega))
        ⟨by omega, by omega, by omega, by omega, by omega⟩ helim (by simp at hr; omega)
    have := List.sum_le_card_nsmul _ 20000 hb
    simp only [List.length_map, List.length_zipIdx, smul_eq_mul] at this
    exact le_trans this (Nat.mul_le_mul_right _ hR)
  -- the winner
  have hwl : (text [winnerLine (countContest c).winner]).length ≤ 40 := by
    rw [Demos.Rcv.TabulateProgram.text_length]
    cases hwk : (countContest c).winner with
    | none => simp [winnerLine]; decide
    | some i =>
      have := hwin i hwk
      have hd := Demos.Rcv.TabulateProgram.decimal_length_le (v := i) (by omega)
      have := Demos.Rcv.TabulateProgram.spaced_length_le [ascii "winner", decimal i]
      have : (ascii "winner").length = 6 := rfl
      simp [winnerLine] at *
      omega
  omega

/-- The report of a structure whose file has fewer than `2 ^ 32` bytes has fewer than `2 ^ 64`
bytes. -/
theorem report_length_lt (c : Contest) (hc : c.WellFormed) (hw : (write c).length < 2 ^ 32) :
    (report c).length < 2 ^ 64 := by
  have := report_length_le c hc
  have := Demos.Rcv.TabulateProgram.headerLines_length_le c
  omega

/-! ## T1 over bytes -/

/-- T1 over bytes: the export `tabulate`, on a buffer that memory holds, returns the bytes of the
Maine report of the file, the error report when the reader fails and the printed count
otherwise. -/
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
    have hj := Demos.Rcv.TabulateProgram.read_error_lt hr
    rw [Demos.Rcv.TabulateProgram.getElem!_eq_getD, Demos.Rcv.TabulateProgram.getElem!_eq_getD,
      Demos.Rcv.TabulateProgram.getElem!_eq_getD, hrc]
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
      rw [Demos.Rcv.TabulateProgram.getElem!_eq_getD, hrc]
      rfl
    have hne : (ws[(0 : UInt64).toNat]! == 0) = false := by
      rw [h0]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg UInt64.toNat h
      rw [ofNat_toNat_small (by omega), UInt64.toNat_zero] at this
      omega
    have hsz : ws.size < 2 ^ 64 := by
      rw [← Array.length_toList, hrc, Demos.Rcv.TabulateProgram.contestWords_length c hc]
      have h1 : c.ballots.length * c.positions ≤ (2 ^ 32) * 63 := by
        have := hc.2.2.2.2.1
        simp only [maxBallots] at this
        exact Nat.mul_le_mul (by omega) hc.2.1
      omega
    rw [ite_eq_right (by rw [hne]; simp), h0, Refine.count_eq ws hsz, countArray, hrc,
      countWords_contestWords c hc, countedOf_contest c hc ws hrc]
    exact PrintProgram.printReport_eq b hb64 c hc hwc.symm
      (report_length_lt c hc (by rw [hwc]; simpa using hb))

end Demos.Rcv.Maine.TabulateProgram
