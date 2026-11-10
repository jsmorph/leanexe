import Demos.Rcv.Maine.PrintProgram
import Demos.Rcv.Maine.Winner

/-!
The Maine report's printer equals the specification's report.  The proof is the Oakland printer's
proof of `Demos.Rcv.PrintProgram.printReport_eq` with two changes: `pushFirst_toList` prints the
`first` lines from the mask of `K` and the first counts of the result words, and the words of the
rounds start after the `n` first counts (`result_round`).  The facts about the rounds come from
`Demos.Rcv.Maine.round_facts` and `Demos.Rcv.Maine.count_winner`, and the bound on their number from
T3(d).
-/

namespace Demos.Rcv.Maine.PrintProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram
open scoped List

set_option maxRecDepth 100000 in
theorem pushHead_toList (o : Array UInt64) :
    (pushHead o).toList = o.toList ++
      (text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]]).map
        UInt8.toUInt64 := by
  simp only [pushHead, pushWord_toList, List.append_assoc]
  congr 1

/-- `pushFirst` prints the line `first i f(i)` of each member `i` of a set of candidates. -/
theorem pushFirst_toList (o res : Array UInt64) {K : List Nat} {n : Nat} (hn : n ≤ 63)
    (hK : K <+ List.range' 1 n) (f : Nat → Nat) (hf : ∀ i ∈ K, f i < 2 ^ 64)
    (hv : ∀ i < n, i + 1 ∈ K → res[2 + i]! = UInt64.ofNat (f (i + 1))) :
    (pushFirst o res (UInt64.ofNat n) (UInt64.ofNat (mask K))).toList =
      o.toList ++ (text (firstLines (K.map fun i => (i, f i)))).map UInt8.toUInt64 := by
  have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
  have hmN : (UInt64.ofNat (mask K)).toNat = mask K :=
    ofNat_toNat_small (Nat.lt_of_lt_of_le (mask_lt hK) (Nat.pow_le_pow_right (by decide)
      (by omega)))
  have hfm := flatMap_range_mem hK (fun i =>
    (spaced [ascii "first", decimal i, decimal (f i)] ++ [lf]).map UInt8.toUInt64)
  unfold pushFirst
  rw [loop_append' _ o _ (fun i => if i + 1 ∈ K then
      (spaced [ascii "first", decimal (i + 1), decimal (f (i + 1))] ++ [lf]).map UInt8.toUInt64
      else []), hnN, hfm]
  · simp only [firstLines, text, List.map_map, List.flatMap_map, List.map_flatMap]
    rfl
  · intro i hi o
    rw [hnN] at hi
    have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
    have hi1 : (UInt64.ofNat i + 1).toNat = i + 1 := by
      rw [UInt64.toNat_add, hiN]; simp; omega
    rw [shift_bit_one _ _ (by rw [hiN]; omega), hmN, hiN, mask_testBit hK]
    by_cases hm : i + 1 ∈ K
    · have hidx : (2 + UInt64.ofNat i).toNat = 2 + i := by
        rw [UInt64.toNat_add, hiN]; simp; omega
      rw [decide_eq_true hm, ite_eq_left rfl, ite_eq_left hm, Array.toList_push, pushNumber_toList,
        Array.toList_push, pushNumber_toList, pushWord_toList, hi1, hidx, hv i hi hm,
        ofNat_toNat_small (hf _ hm)]
      have hw : wordBytes 0x207473726966 6 = (ascii "first ").map UInt8.toUInt64 := by decide
      rw [show (6 : UInt64).toNat = 6 from rfl, hw, spaced_cons_cons, spaced_two]
      simp [sp]
      rfl
    · rw [decide_eq_false hm, ite_eq_right (by simp), ite_eq_right hm]
      simp

/-! ## The result words -/

theorem result_toList (n : Nat) (first : List (Nat × Nat)) (k : Count) :
    resultWords n first k = ([1, k.rounds.length] ++
      (List.range' 1 n).map (fun i => (first.lookup i).getD 0) ++
      k.rounds.flatMap (roundWords n) ++ [k.winner.getD 0]).map Nat.toUInt64 := rfl

theorem result_rounds (n : Nat) (first : List (Nat × Nat)) (k : Count) :
    (resultWords n first k).toArray[1]! = UInt64.ofNat k.rounds.length := by
  rw [getElem!_toArray_eq, result_toList]
  rfl

theorem result_first (n : Nat) (first : List (Nat × Nat)) (k : Count) (i : Nat) (hi : i < n) :
    (resultWords n first k).toArray[2 + i]! = UInt64.ofNat ((first.lookup (i + 1)).getD 0) := by
  rw [getElem!_toArray_eq, result_toList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp; omega)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_range', hi, ↓reduceIte, Option.map_some, Option.getD_some]
  rw [show 1 + 1 * i = i + 1 by omega]

theorem result_round (n : Nat) (first : List (Nat × Nat)) (k : Count) (r j : Nat)
    (hr : r < k.rounds.length) (hj : j < n + 9) :
    (resultWords n first k).toArray[2 + n + r * (n + 9) + j]! =
      UInt64.ofNat ((roundWords n k.rounds[r]).getD j 0) := by
  have hlen := flatMap_roundWords_length n k.rounds
  have hlt : r * (n + 9) + j < k.rounds.length * (n + 9) := by
    have : (r + 1) * (n + 9) ≤ k.rounds.length * (n + 9) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    omega
  have hpre : ([1, k.rounds.length] ++
      (List.range' 1 n).map (fun i => (first.lookup i).getD 0)).length = 2 + n := by
    simp
    omega
  rw [getElem!_toArray_eq, result_toList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.append_assoc, List.getElem?_append_right (by rw [hpre]; omega), hpre,
    show 2 + n + r * (n + 9) + j - (2 + n) = r * (n + 9) + j by omega,
    List.getElem?_append_left (by rw [hlen]; exact hlt)]
  have := getD_flatMap_block (roundWords n) (roundWords_length n) k.rounds r j hr hj
  rw [List.getD_eq_getElem?_getD] at this
  have hlt' : r * (n + 9) + j < (k.rounds.flatMap (roundWords n)).length := by
    rw [hlen]
    omega
  rw [List.getElem?_eq_getElem hlt'] at this ⊢
  simp only [Option.getD_some] at this
  simp only [Option.map_some, Option.getD_some, this]

theorem result_winner (n : Nat) (first : List (Nat × Nat)) (k : Count) :
    (resultWords n first k).toArray[2 + n + k.rounds.length * (n + 9)]! =
      UInt64.ofNat (k.winner.getD 0) := by
  have hlen := flatMap_roundWords_length n k.rounds
  have h2 : ([1, k.rounds.length] ++ (List.range' 1 n).map (fun i => (first.lookup i).getD 0) ++
      k.rounds.flatMap (roundWords n)).length = 2 + n + k.rounds.length * (n + 9) := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
      List.length_range', hlen]
  rw [getElem!_toArray_eq, result_toList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append_right (Nat.le_of_eq h2), h2, Nat.sub_self]
  rfl

/-! ## The report -/

/-- The printer prints the report of a structure that meets the constraints from its file, the
mask of its counted set, and the result words of its count, provided the report has fewer than
`2 ^ 64` bytes. -/
theorem printReport_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (c : Contest) (hc : c.WellFormed)
    (hw : bytesOf b = write c) (hlen : (report c).length < 2 ^ 64) :
    bytesOf (printReport b (UInt64.ofNat c.candidates.length)
      (UInt64.ofNat (mask (countedSet (kindsOf c))))
      (resultWords c.candidates.length (firstContest c) (countContest c)).toArray) = report c := by
  have hn : c.candidates.length ≤ 63 := hc.2.2.2.1
  have hN : c.ballots.length ≤ maxBallots := hc.2.2.2.2.1
  have hNb : c.ballots.length < 2 ^ 64 := by simp [maxBallots] at hN; omega
  have hrep : report c = text ([ascii "rcv-report 1",
      spaced [ascii "rule", ascii ruleIdentifier]] ++ headerLines c ++
      firstLines (firstContest c) ++
      (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat => roundLines p.2 p.1) ++
      [winnerLine (countContest c).winner]) := rfl
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
  rw [hkl] at hcs
  -- The header lines
  set L := (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine with hL
  have hwL : bytesOf b = text L := by rw [hw]; rfl
  have hLn : ∀ l ∈ L, lf ∉ l := lines_no_lf hc
  have hhl : (headerLines c).length = 5 + c.candidates.length := by
    simp only [headerLines, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_zipIdx]
    omega
  have hLlen : 6 + c.candidates.length ≤ L.length := by simp [hL, hhl]; omega
  have hfirst : firstContest c = (countedSet (kindsOf c)).map fun i =>
      (i, firstCount (positionsOf c) i) := firstCounts_eq _ _
  have hfb : ∀ i, firstCount (positionsOf c) i < 2 ^ 64 := by
    intro i
    have := List.count_le_length (a := Position.single i) (l := (positionsOf c).map firstPosition)
    simp only [List.length_map, hpl] at this
    unfold firstCount
    omega
  generalize hnn : c.candidates.length = n at *
  have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
  have h6 : (6 + UInt64.ofNat n).toNat = 6 + n := by
    rw [UInt64.toNat_add, hnN]; simp; omega
  have hh := header_loop b hb L hLn hwL (6 + UInt64.ofNat n) (by rw [h6]; exact hLlen)
  rw [h6] at hh
  have htake : L.take (6 + n) = ascii "rcv-ballots 1" :: headerLines c := by
    rw [hL, List.cons_append, show 6 + n = (5 + n) + 1 by omega, List.take_succ_cons,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [htake] at hh
  have hsize := size_toNat b hb
  have htextL : (text L).length = b.data.size := by rw [← hwL]; simp
  have hl1 : (ascii "rcv-ballots 1" ++ [lf]).length = 14 := rfl
  have hfile : text L = (ascii "rcv-ballots 1" ++ [lf]) ++
      (text (headerLines c) ++ text (c.ballots.map ballotLine)) := by
    rw [hL, List.cons_append, text_cons, text_append, List.append_assoc]
  have h14 : (text (ascii "rcv-ballots 1" :: headerLines c)).length =
      14 + (text (headerLines c)).length := by
    rw [text_cons, List.length_append, hl1]
  generalize hH : LeanExe.loop (6 + UInt64.ofNat n) (0 : UInt64)
      (fun _ p => findByte b 10 p b.size + 1) = H at hh
  have hl1' : (ascii "rcv-ballots 1").length + [lf].length = 14 := rfl
  have hHle : H.toNat ≤ b.data.size := by
    rw [hh, h14, ← htextL, hfile, List.length_append, List.length_append, List.length_append]
    omega
  have h14le : (14 : UInt64) ≤ H := by
    rw [UInt64.le_iff_toNat_le, hh, h14]; simp
  have hslice : slice b 14 H.toNat = text (headerLines c) := by
    rw [hh, h14, slice, hwL, hfile, List.drop_left' hl1, Nat.add_sub_cancel_left,
      List.take_left' rfl]
  -- The program
  unfold printReport
  simp only []
  rw [hH]
  rw [show ((1 : UInt64).toNat) = 1 from rfl, result_rounds]
  have ho1 := pushRange_toList (pushHead #[]) b hb 14 H h14le hHle
  rw [show (14 : UInt64).toNat = 14 from rfl, hslice, pushHead_toList] at ho1
  generalize pushRange (pushHead #[]) b 14 H = o1 at ho1
  -- The first lines
  have ho2 := pushFirst_toList o1 (resultWords n (firstContest c) (countContest c)).toArray hn hcs
    (firstCount (positionsOf c)) (fun i _ => hfb i) (fun i hi hm => by
      rw [result_first n _ _ i hi, hfirst,
        Demos.Rcv.PrintProgram.lookup_map (Demos.Rcv.Rounds.countedSet_nodup _) _ hm]
      rfl)
  rw [← hfirst] at ho2
  generalize pushFirst o1 (resultWords n (firstContest c) (countContest c)).toArray
    (UInt64.ofNat n) (UInt64.ofNat (mask (countedSet (kindsOf c)))) = o2 at ho2
  -- The rounds
  set R := (countContest c).rounds.length with hR
  have hR64 : R ≤ 64 := by have := hRle; omega
  have hRN : (UInt64.ofNat R).toNat = R := ofNat_toNat_small (by omega)
  have hloop := loop_append' (UInt64.ofNat R) o2
    (fun r o => pushRoundLines o (resultWords n (firstContest c) (countContest c)).toArray
      (UInt64.ofNat n) (2 + UInt64.ofNat n + r * (UInt64.ofNat n + 9)) (r + 1))
    (fun i => (text (roundLines (i + 1) ((countContest c).rounds.getD i noRound))).map
      UInt8.toUInt64) (by
      intro i hi o
      rw [hRN] at hi
      have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
      have hprod : i * (n + 9) ≤ 64 * 72 := Nat.mul_le_mul (by omega) (by omega)
      have hbase : (2 + UInt64.ofNat n + UInt64.ofNat i * (UInt64.ofNat n + 9) : UInt64) =
          UInt64.ofNat (2 + n + i * (n + 9)) := by
        apply UInt64.toNat_inj.mp
        rw [ofNat_toNat_small (by omega), UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul,
          UInt64.toNat_add, hiN, hnN]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (show n + 9 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show i * (n + 9) < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 2 + n < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 2 + n + i * (n + 9) < 2 ^ 64 by omega)]
      have hr1 : (UInt64.ofNat i + 1 : UInt64) = UInt64.ofNat (i + 1) := by
        apply UInt64.toNat_inj.mp
        rw [ofNat_toNat_small (by omega), UInt64.toNat_add, hiN]
        simp only [UInt64.reduceToNat]
        omega
      have hmem : (countContest c).rounds[i] ∈ (countContest c).rounds := List.getElem_mem hi
      obtain ⟨S, hvotes, hS, helim, hT, hbl, hun, hov, hex⟩ := hfacts _ hmem
      rw [hbase, hr1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      simp only [hpl] at hT hbl hun hov hex
      exact pushRoundLines_toList o _ hn _ S _ hvotes hS
        (fun j _ => Nat.lt_of_le_of_lt List.count_le_length (by simp [hpl]; omega))
        ⟨by omega, by omega, by omega, by omega, by omega⟩ helim (by omega) (by omega)
        (fun j hj => result_round n _ (countContest c) i j hi hj))
  rw [hRN, flatMap_range_zipIdx _ noRound (fun r rd => (text (roundLines r rd)).map
    UInt8.toUInt64)] at hloop
  generalize LeanExe.loop (UInt64.ofNat R) o2 _ = o3 at hloop
  -- The winner
  have hidx : (2 + UInt64.ofNat n + UInt64.ofNat R * (UInt64.ofNat n + 9) : UInt64).toNat =
      2 + n + R * (n + 9) := by
    have hprod : R * (n + 9) ≤ 64 * 72 := Nat.mul_le_mul (by omega) (by omega)
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_add, hRN, hnN]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (show n + 9 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show R * (n + 9) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 + n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 + n + R * (n + 9) < 2 ^ 64 by omega)]
  rw [hidx, result_winner]
  have hfinal : ∀ o : Array UInt64, o.toList = (report c).map UInt8.toUInt64 →
      bytesOf (toBytes o) = report c := by
    intro o ho
    have hs : o.size < 2 ^ 64 := by
      have := congrArg List.length ho
      simp at this
      omega
    rw [toBytes_toList o hs, ho, map_toUInt8_toUInt64]
  apply hfinal
  rw [hrep, text_append, text_append, text_append, text_append, text_flatMap]
  cases hwk : (countContest c).winner with
  | none =>
    simp only [Option.getD_none]
    rw [ite_eq_left (by rfl), pushWord_toList, pushWord_toList, hloop, ho2, ho1]
    have hw0 : wordBytes 0x6e2072656e6e6977 (8 : UInt64).toNat ++
        wordBytes 0xa656e6f (4 : UInt64).toNat = (text [winnerLine none]).map UInt8.toUInt64 := by
      decide
    simp only [List.map_append, List.append_assoc, ← hw0, List.map_flatMap]
    simp
  | some i =>
    simp only [Option.getD_some]
    obtain ⟨hi1, hin⟩ := hwin i hwk
    have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
    rw [ite_eq_right (by
      intro h
      have := congrArg UInt64.toNat (beq_iff_eq.mp h)
      rw [hiN] at this
      simp at this
      omega), Array.toList_push, pushNumber_toList, pushWord_toList, hloop, ho2, ho1, hiN]
    have hw7 : wordBytes 0x2072656e6e6977 (7 : UInt64).toNat =
        (ascii "winner" ++ [sp]).map UInt8.toUInt64 := by
      decide
    rw [hw7]
    simp only [List.map_append, List.append_assoc, winnerLine, text, spaced_two, List.map_flatMap]
    simp [sp]

end Demos.Rcv.Maine.PrintProgram
