import Demos.Rcv.Maine.TabulateCall
import Demos.Rcv.TabulateBound
import Verified.ChargeFacts

/-!
The closed forms of the generated bounds of the Maine module's exports `count` and `tabulate`.

The reader and the functions of the Oakland printer have the same generated costs in this module
as in the Oakland tabulator's compilation.  A proof by `rfl` of such an equation unfolds the
compiled programs and exceeds the heartbeat limit, so `readContest_bound_eq` and the lemmas before
it rewrite both sides with the generated `cost_eq` and `bound_eq` equations of the two compilations,
the callees' equations first.  For a tail-recursive function both sides are a
`Verified.Tail.costAt` of a step that the two compilations define alike, which `tail_cost_congr`
equates.  The Oakland tabulator's bounds of `Demos/Rcv/TabulateBound.lean` then apply.

`count_bound` closes the count's bound at 486,624 bytes for every array: 152 bytes for the result
`[0]` of an invalid array, and for a valid one 600 bytes for the counters of the first positions,
232 bytes for the literal `#[1, 0]`, 80 bytes for each of the at most 63 first counts, and either
80 bytes for the push of the test's winner or the rounds: at most 64 rounds of 600 bytes of counters
and `80 (n + 9)` bytes of words, and the move of the at most 4,601 result words before the winner's
to a block with room for it.  `tabulate_bound` closes the bound of `tabulate` at `80 L + 33,958,029`
bytes for a file of `L < 2 ^ 32` bytes: the reader's `80 L + 10,704`, the count's bound, and the
printer, which pushes the first two lines, at most 20,777 bytes of header lines, at most 63 `first`
lines, and at most 64 rounds, and copies the report, at most 1,304,174 bytes, into the buffer that
it returns.

`reportFile_length_le` bounds every Maine report at 1,304,174 bytes.  `tabulate_native_size` states
the C call theorem `tabulate_native` for a file of at most `L` bytes, with room for `top` and
`80 L + 33,958,029` bytes in the 11,520 pages of `lx_mem`, and `tabulate_native_8800000` for every
file of at most 8,800,000 bytes.
-/

namespace Demos.Rcv.Maine.TabulateProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram
open Library.Numerics.Decimal.Int64Text (digitCount)

/-! ## The costs shared with the Oakland tabulator -/

/-- Two tail costs of equal steps and equal charges are equal, whatever the proofs of
well-foundedness of their ranks. -/
theorem tail_cost_congr {α β : Type} {s1 s2 : α → α ⊕ β} (hs : s1 = s2) {c1 c2 : α → Nat}
    (hc : ∀ x, c1 x = c2 x) (wf1 : WellFounded fun next state => s1 state = .inl next)
    (wf2 : WellFounded fun next state => s2 state = .inl next) (x : α) :
    Verified.Tail.costAt s1 c1 (Verified.Tail.rank s1 wf1 x + 1) x =
      Verified.Tail.costAt s2 c2 (Verified.Tail.rank s2 wf2 x + 1) x := by
  subst hs
  have : c1 = c2 := funext hc
  subst this
  rfl

theorem fieldsFrom_cost_eq (b : Bytes) (n p e fuel : UInt64) (out : Array UInt64) :
    compiled.fieldsFrom.cost (b, n, p, e, fuel, ⟨out⟩) =
      Demos.Rcv.TabulateProgram.compiled.fieldsFrom.cost (b, n, p, e, fuel, ⟨out⟩) := by
  rw [compiled.fieldsFrom.cost_eq, Demos.Rcv.TabulateProgram.compiled.fieldsFrom.cost_eq]
  exact tail_cost_congr rfl (fun _ => rfl) _ _ _

theorem ballotWords_cost_eq (b : Bytes) (k n s e : UInt64) (out : Array UInt64) :
    compiled.ballotWords.cost (b, k, n, s, e, ⟨out⟩) =
      Demos.Rcv.TabulateProgram.compiled.ballotWords.cost (b, k, n, s, e, ⟨out⟩) := by
  rw [compiled.ballotWords.cost_eq, Demos.Rcv.TabulateProgram.compiled.ballotWords.cost_eq]
  simp only [fieldsFrom_cost_eq]

theorem ballotsFrom_cost_eq (b : Bytes) (k n p j count : UInt64) (out : Array UInt64) :
    compiled.ballotsFrom.cost (b, k, n, p, j, count, ⟨out⟩) =
      Demos.Rcv.TabulateProgram.compiled.ballotsFrom.cost (b, k, n, p, j, count, ⟨out⟩) := by
  rw [compiled.ballotsFrom.cost_eq, Demos.Rcv.TabulateProgram.compiled.ballotsFrom.cost_eq]
  exact tail_cost_congr rfl (fun _ => by simp only [ballotWords_cost_eq]) _ _ _

theorem candidatesFrom_cost_eq (b : Bytes) (p i count : UInt64) (out : Array UInt64) :
    compiled.candidatesFrom.cost (b, p, i, count, ⟨out⟩) =
      Demos.Rcv.TabulateProgram.compiled.candidatesFrom.cost (b, p, i, count, ⟨out⟩) := by
  rw [compiled.candidatesFrom.cost_eq, Demos.Rcv.TabulateProgram.compiled.candidatesFrom.cost_eq]
  exact tail_cost_congr rfl (fun _ => rfl) _ _ _

theorem orderFrom_cost_eq (b : Bytes) (n p e seen count fuel : UInt64) (out : Array UInt64) :
    compiled.orderFrom.cost (b, n, p, e, seen, count, fuel, ⟨out⟩) =
      Demos.Rcv.TabulateProgram.compiled.orderFrom.cost (b, n, p, e, seen, count, fuel, ⟨out⟩) := by
  rw [compiled.orderFrom.cost_eq, Demos.Rcv.TabulateProgram.compiled.orderFrom.cost_eq]
  exact tail_cost_congr rfl (fun _ => rfl) _ _ _

theorem readOrder_cost_eq (b : Bytes) (n s e : UInt64) (out : Array UInt64) :
    compiled.readOrder.cost (b, n, s, e, ⟨out⟩) =
      Demos.Rcv.TabulateProgram.compiled.readOrder.cost (b, n, s, e, ⟨out⟩) := by
  rw [compiled.readOrder.cost_eq, Demos.Rcv.TabulateProgram.compiled.readOrder.cost_eq]
  simp only [orderFrom_cost_eq]

theorem readContest_bound_eq (b : Bytes) :
    compiled.readContest.bound b = Demos.Rcv.TabulateProgram.compiled.readContest.bound b := by
  rw [compiled.readContest.bound_eq, Demos.Rcv.TabulateProgram.compiled.readContest.bound_eq]
  simp only [candidatesFrom_cost_eq, readOrder_cost_eq, ballotsFrom_cost_eq]

theorem pushWord_cost_eq (out : Array UInt64) (w len : UInt64) :
    compiled.pushWord.cost (⟨out⟩, w, len) =
      Demos.Rcv.TabulateProgram.compiled.pushWord.cost (⟨out⟩, w, len) := by
  rw [compiled.pushWord.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushWord.cost_eq]

theorem pushNumber_cost_eq (out : Array UInt64) (v : UInt64) :
    compiled.pushNumber.cost (⟨out⟩, v) =
      Demos.Rcv.TabulateProgram.compiled.pushNumber.cost (⟨out⟩, v) := by
  rw [compiled.pushNumber.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushNumber.cost_eq]

theorem pushRange_cost_eq (out : Array UInt64) (b : Bytes) (s e : UInt64) :
    compiled.pushRange.cost (⟨out⟩, b, s, e) =
      Demos.Rcv.TabulateProgram.compiled.pushRange.cost (⟨out⟩, b, s, e) := by
  rw [compiled.pushRange.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushRange.cost_eq]

theorem pushLine_cost_eq (out : Array UInt64) (w1 l1 w2 l2 v : UInt64) :
    compiled.pushLine.cost (⟨out⟩, w1, l1, w2, l2, v) =
      Demos.Rcv.TabulateProgram.compiled.pushLine.cost (⟨out⟩, w1, l1, w2, l2, v) := by
  rw [compiled.pushLine.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushLine.cost_eq]
  simp only [pushWord_cost_eq, pushNumber_cost_eq]

theorem pushMembers_cost_eq (out : Array UInt64) (mask n : UInt64) :
    compiled.pushMembers.cost (⟨out⟩, mask, n) =
      Demos.Rcv.TabulateProgram.compiled.pushMembers.cost (⟨out⟩, mask, n) := by
  rw [compiled.pushMembers.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushMembers.cost_eq]
  simp only [pushNumber_cost_eq]

theorem pushVotes_cost_eq (out res : Array UInt64) (n base : UInt64) :
    compiled.pushVotes.cost (⟨out⟩, res, n, base) =
      Demos.Rcv.TabulateProgram.compiled.pushVotes.cost (⟨out⟩, res, n, base) := by
  rw [compiled.pushVotes.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushVotes.cost_eq]
  simp only [pushWord_cost_eq, pushNumber_cost_eq]

theorem pushElimination_cost_eq (out : Array UInt64) (code elim tied n : UInt64) :
    compiled.pushElimination.cost (⟨out⟩, code, elim, tied, n) =
      Demos.Rcv.TabulateProgram.compiled.pushElimination.cost (⟨out⟩, code, elim, tied, n) := by
  rw [compiled.pushElimination.cost_eq,
    Demos.Rcv.TabulateProgram.compiled.pushElimination.cost_eq]
  simp only [pushWord_cost_eq, pushMembers_cost_eq]

theorem pushRoundLines_cost_eq (out res : Array UInt64) (n base r : UInt64) :
    compiled.pushRoundLines.cost (⟨out⟩, res, n, base, r) =
      Demos.Rcv.TabulateProgram.compiled.pushRoundLines.cost (⟨out⟩, res, n, base, r) := by
  rw [compiled.pushRoundLines.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushRoundLines.cost_eq]
  simp only [pushWord_cost_eq, pushLine_cost_eq, pushVotes_cost_eq, pushElimination_cost_eq]

theorem pushRole_cost_eq (out : Array UInt64) (code : UInt64) :
    compiled.pushRole.cost (⟨out⟩, code) =
      Demos.Rcv.TabulateProgram.compiled.pushRole.cost (⟨out⟩, code) := by
  rw [compiled.pushRole.cost_eq, Demos.Rcv.TabulateProgram.compiled.pushRole.cost_eq]
  simp only [pushWord_cost_eq]

/-! ## The printers -/

theorem pushWord_cost (out : Array UInt64) (w len : UInt64) :
    compiled.pushWord.cost (⟨out⟩, w, len) = 80 * len.toNat := by
  rw [pushWord_cost_eq]
  exact Demos.Rcv.TabulateProgram.pushWord_cost out w len

theorem pushNumber_cost (out : Array UInt64) (v : UInt64) :
    compiled.pushNumber.cost (⟨out⟩, v) ≤ 1600 := by
  rw [pushNumber_cost_eq]
  exact Demos.Rcv.TabulateProgram.pushNumber_cost out v

theorem pushRange_cost (out : Array UInt64) (b : Bytes) (s e : UInt64) :
    compiled.pushRange.cost (⟨out⟩, b, s, e) = 80 * (e - s).toNat := by
  rw [pushRange_cost_eq]
  exact Demos.Rcv.TabulateProgram.pushRange_cost out b s e

theorem pushRoundLines_cost (out res : Array UInt64) (n base r : UInt64) :
    compiled.pushRoundLines.cost (⟨out⟩, res, n, base, r) ≤ 7200 * n.toNat + 18720 := by
  rw [pushRoundLines_cost_eq]
  exact Demos.Rcv.TabulateProgram.pushRoundLines_cost out res n base r

theorem pushRole_cost (out : Array UInt64) (code : UInt64) :
    compiled.pushRole.cost (⟨out⟩, code) ≤ 800 := by
  rw [pushRole_cost_eq]
  exact Demos.Rcv.TabulateProgram.pushRole_cost out code

/-- The first two lines of every report, 270 bytes. -/
theorem pushHead_cost (out : Array UInt64) : compiled.pushHead.cost ⟨out⟩ = 21600 := by
  rw [compiled.pushHead.cost_eq]
  simp only [pushWord_cost]
  rfl

/-- The `first` lines: at most `n` lines of 48 bytes. -/
theorem pushFirst_cost (out res : Array UInt64) (n counted : UInt64) :
    compiled.pushFirst.cost (⟨out⟩, res, n, counted) ≤ 3840 * n.toNat := by
  rw [compiled.pushFirst.cost_eq]
  refine (Verified.loopCost_const_le 3840 (fun k s => ?_) _ _ _).trans
    (by omega)
  try dsimp only
  split
  · rw [pushWord_cost, Demos.Rcv.TabulateProgram.paidGrowCost_one]
    have h1 := pushNumber_cost (pushWord s 0x207473726966 6) (k + 1)
    have h2 := pushNumber_cost ((pushNumber (pushWord s 0x207473726966 6) (k + 1)).push 32)
      res[(2 + k).toNat]!
    simp only [UInt64.reduceToNat]
    omega
  · omega

/-- The bound of `printReport`: the first two lines, the header lines, which run from byte 14 to
the position after line `6 + n`, the `first` lines, the rounds, the winner's line, and the copy of
the report into the returned buffer. -/
theorem printReport_bound (b : Bytes) (n counted : UInt64) (res : Array UInt64)
    (hn : n.toNat ≤ 63) (hR : (res[(1 : UInt64).toNat]!).toNat ≤ 64) :
    compiled.printReport.bound (b, n, counted, res) ≤
      80 * ((LeanExe.loop (6 + n) 0 fun _ p => findByte b 10 p b.size + 1) - 14).toNat +
        Verified.Bytes.allocationCost (PrintProgram.printReport b n counted res).data.size +
          30494312 := by
  have key : ∀ o : Array UInt64, toBytes o = PrintProgram.printReport b n counted res →
      compiled.toBytes.bound o =
        Verified.Bytes.allocationCost (PrintProgram.printReport b n counted res).data.size := by
    intro o h
    rw [compiled.toBytes.bound_eq, ← h, toBytes, Bytes.data_size_build]
  rw [compiled.printReport.bound_eq, key _ rfl, pushHead_cost, pushRange_cost]
  grw [Verified.loopCost_const_le (7200 * n.toNat + 18720)
    (fun k s => pushRoundLines_cost s _ _ _ _), pushFirst_cost]
  have hblock : Verified.blockCost (UInt64.toNat 0) = 56 := rfl
  have hcredit : Verified.creditCost (#[] : Array UInt64).size = 16 := rfl
  rw [hblock, hcredit]
  have hloop : (res[(1 : UInt64).toNat]!).toNat * (7200 * n.toNat + 18720) ≤ 64 * 472320 :=
    Nat.mul_le_mul hR (by omega)
  simp only [UInt64.reduceToNat] at hloop
  split
  · simp only [pushWord_cost, UInt64.reduceToNat]
    omega
  · grw [pushNumber_cost]
    simp only [pushWord_cost, Demos.Rcv.TabulateProgram.paidGrowCost_one, UInt64.reduceToNat]
    omega

/-- The bound of `printError`: the first two lines, `error `, the line number, a space, the role,
the LF, and the copy of the report into the returned buffer. -/
theorem printError_bound (j code : UInt64) :
    compiled.printError.bound (j, code) ≤
      Verified.Bytes.allocationCost (PrintProgram.printError j code).data.size + 24712 := by
  have key : ∀ o : Array UInt64, toBytes o = PrintProgram.printError j code →
      compiled.toBytes.bound o =
        Verified.Bytes.allocationCost (PrintProgram.printError j code).data.size := by
    intro o h
    rw [compiled.toBytes.bound_eq, ← h, toBytes, Bytes.data_size_build]
  rw [compiled.printError.bound_eq, key _ rfl, pushHead_cost, pushWord_cost,
    Demos.Rcv.TabulateProgram.paidGrowCost_one]
  grw [pushNumber_cost, pushRole_cost]
  have hblock : Verified.blockCost (UInt64.toNat 0) = 56 := rfl
  have hcredit : Verified.creditCost (#[] : Array UInt64).size = 16 := rfl
  rw [hblock, hcredit]
  simp only [UInt64.reduceToNat]
  omega

/-- An error report holds at most 308 bytes. -/
theorem errorReport_length_le (j : Nat) (hj : j < 2 ^ 64) (r : Role) :
    (errorReport j r).length ≤ 308 := by
  rw [errorReport_eq]
  simp only [List.length_append, head_length, List.length_cons, List.length_nil]
  have := Demos.Rcv.TabulateProgram.decimal_length_le hj
  have hw : (ascii r.word).length ≤ 10 := by cases r <;> decide
  have : (ascii "error").length = 5 := rfl
  omega

/-! ## The count -/

/-- On a valid contest array whose initial test elects no one, the result words of the rounds
before the winner number at most 4,601. -/
theorem rounds_size (ws : Array UInt64) (hs : ws.size < 2 ^ 64)
    (hv : Demos.Rcv.Program.validArray ws = true)
    (h0 : Demos.Rcv.Program.majorityOf
      (Program.tallyRound ws (Demos.Rcv.Program.countedOf ws ws[0]!)
        (Demos.Rcv.Program.countedOf ws ws[0]!) ws[1]! (1 : UInt64) ws[2]!
        ((3 : UInt64) + (2 : UInt64) * ws[0]!))
      (Demos.Rcv.Program.countedOf ws ws[0]!) ws[2]! ws[0]! = 0) :
    (LeanExe.repeatWhile (Demos.Rcv.Program.countedSize ws ws[0]! + 1)
      (Demos.Rcv.Program.countedOf ws ws[0]!, (0 : UInt64), (0 : UInt64), (0 : UInt64),
        LeanExe.loop ws[0]! #[(1 : UInt64), 0] fun c o =>
          o.push (Program.tallyRound ws (Demos.Rcv.Program.countedOf ws ws[0]!)
            (Demos.Rcv.Program.countedOf ws ws[0]!) ws[1]! (1 : UInt64) ws[2]!
            ((3 : UInt64) + (2 : UInt64) * ws[0]!))[c.toNat]!)
      (fun s => s.2.1 == 0)
      (fun s => Program.roundStep ws ws[0]! ws[1]! ws[2]!
        (Demos.Rcv.Program.countedOf ws ws[0]!) s)).2.2.2.2.size ≤ 4601 := by
  have hval := (Demos.Rcv.Refine.validArray_iff ws hs).mp hv
  have heq := Demos.Rcv.Maine.Refine.countValid_eq ws hs hval
  have hcv : Program.countValid ws =
      let first := Program.tallyRound ws (Demos.Rcv.Program.countedOf ws ws[0]!)
        (Demos.Rcv.Program.countedOf ws ws[0]!) ws[1]! (1 : UInt64) ws[2]!
        ((3 : UInt64) + (2 : UInt64) * ws[0]!)
      let out := LeanExe.loop ws[0]! #[(1 : UInt64), 0] fun c o => o.push first[c.toNat]!
      let w := Demos.Rcv.Program.majorityOf first (Demos.Rcv.Program.countedOf ws ws[0]!) ws[2]!
        ws[0]!
      if w != 0 then out.push w
      else
        let s := LeanExe.repeatWhile (Demos.Rcv.Program.countedSize ws ws[0]! + 1)
          (Demos.Rcv.Program.countedOf ws ws[0]!, (0 : UInt64), (0 : UInt64), (0 : UInt64), out)
          (fun s => s.2.1 == 0)
          (fun s => Program.roundStep ws ws[0]! ws[1]! ws[2]!
            (Demos.Rcv.Program.countedOf ws ws[0]!) s)
        (s.2.2.2.2.set! 1 s.2.2.2.1).push s.2.2.1 := rfl
  rw [hcv] at heq
  dsimp only at heq
  rw [h0] at heq
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at heq
  have hsz := congrArg Array.size heq
  simp only [Array.size_push, Array.size_set!, List.size_toArray, resultWords, List.length_map,
    List.length_append, List.length_cons, List.length_nil, List.length_range'] at hsz
  rw [Demos.Rcv.Refine.flatMap_length_const (Demos.Rcv.Refine.roundWords_length _)] at hsz
  obtain ⟨-, h2, -⟩ := hval
  rw [Demos.Rcv.Refine.readWords_n] at h2 hsz
  simp only [Demos.Rcv.maxIndex] at h2
  have hR := (Demos.Rcv.Maine.rounds_le ((readWords ws.toList).kinds.map kindOfCode)
    (readWords ws.toList).order (readWords ws.toList).ballots).2
  have hK := (Demos.Rcv.Rounds.countedSet_sublist
    ((readWords ws.toList).kinds.map kindOfCode)).length_le
  have hlen : ((readWords ws.toList).kinds.map kindOfCode).length ≤ 63 := by
    simp only [List.length_map, readWords, List.length_take]
    rw [Demos.Rcv.Refine.getD_toList]
    omega
  simp only [List.length_range'] at hK
  have hR63 : (Demos.Rcv.Maine.count ((readWords ws.toList).kinds.map kindOfCode)
      (readWords ws.toList).order (readWords ws.toList).ballots).rounds.length ≤ 63 := by
    omega
  have hm := Nat.mul_le_mul hR63 (show ws[0]!.toNat + 9 ≤ 72 by omega)
  omega

theorem count_arith_initial {T B L P : Nat} (hT : T = 600) (hB : B ≤ 232) (hL : L ≤ 5040)
    (hP : P = 80) : T + (B + L + P) ≤ 486624 := by
  omega

theorem count_arith_rounds {T B L U K G : Nat} (hT : T = 600) (hB : B ≤ 232) (hL : L ≤ 5040)
    (hK : K ≤ 407040) (hG : G ≤ 73712) :
    T + (B + L + (min U (0 + 0 + 0 + 0 + K) + G)) ≤ 486624 := by
  have := min_le_right U (0 + 0 + 0 + 0 + K)
  omega

/-- The count's generated bound is at most 486,624 bytes for every array. -/
theorem count_bound (ws : Array UInt64) (hs : ws.size < 2 ^ 64) :
    compiled.count.bound ws ≤ 486624 := by
  rw [compiled.count.bound_eq]
  split
  · next hv =>
    rw [compiled.countValid.bound_eq]
    have hval := (Demos.Rcv.Refine.validArray_iff ws hs).mp hv
    obtain ⟨-, h2, -⟩ := hval
    rw [Demos.Rcv.Refine.readWords_n] at h2
    simp only [Demos.Rcv.maxIndex] at h2
    have hn : (ws[(0 : UInt64).toNat]!).toNat ≤ 63 := h2
    have hfuel : (Demos.Rcv.Program.countedSize ws ws[(0 : UInt64).toNat]! + 1).toNat ≤ 64 := by
      have hlen : (Demos.Rcv.Refine.countedOfWords ws (ws[(0 : UInt64).toNat]!).toNat).length ≤
          63 := (List.filter_sublist.length_le.trans (by simp)).trans hn
      rw [UInt64.toNat_add, Demos.Rcv.Refine.countedSize_eq ws ws[(0 : UInt64).toNat]! hn,
        UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      omega
    have htally : ∀ x, compiled.tallyRound.bound x = 600 := by
      intro x
      rcases x with ⟨a, b, c, d, e, f, g⟩
      rw [compiled.tallyRound.bound_eq, Verified.blockCost_eq]
      rfl
    have hB : Verified.blockCost (UInt64.toNat 0) +
        Verified.growCost ((#[] : Array UInt64).size + 1) 1 + Verified.paidGrowCost 1 ≤ 232 := by
      norm_num [Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq]
    have hL : ∀ (F : UInt64 → Array UInt64 → Array UInt64) (I : Array UInt64),
        Verified.loopCost (fun _ => 0) (fun _ => true) (fun _ _ => Verified.paidGrowCost 1) F
          (ws[(0 : UInt64).toNat]!).toNat 0 I ≤ 5040 := by
      intro F I
      rw [Verified.loopCost_const, Demos.Rcv.TabulateProgram.paidGrowCost_one]
      omega
    simp only [htally]
    split
    · exact count_arith_initial rfl hB (hL _ _) Demos.Rcv.TabulateProgram.paidGrowCost_one
    · next h0 =>
      have hsize := rounds_size ws hs hv (by simpa using h0)
      refine count_arith_rounds rfl hB (hL _ _) ?_ ?_
      · refine le_trans (Verified.loopCost_const_le 6360 (fun k s => ?_) _ _ _) ?_
        · simp only [compiled.pushRound.cost_eq, Verified.loopCost_const, Verified.paidGrowCost_eq,
            UInt64.reduceToNat]
          omega
        · have := Nat.mul_le_mul_right 6360 hfuel
          omega
      · rw [Array.size_set!]
        exact (fun m (hm : m ≤ 4601) => by rw [Verified.growCost_eq]; omega :
          ∀ m, m ≤ 4601 → Verified.growCost (m + 1) 1 ≤ 73712) _ hsize
  · norm_num [Verified.blockCost_eq, Verified.growCost_eq]

/-! ## The bound of `tabulate` -/

/-- The closed form of the generated bound of `tabulate`: a call on a file of fewer than `2 ^ 32`
bytes raises the allocator's `top` by at most 80 bytes for each byte of the file and 33,958,029
bytes more. -/
theorem tabulate_bound (b : Bytes) (hb : b.data.size < 2 ^ 32) :
    compiled.tabulate.bound b ≤ 80 * b.data.size + 33958029 := by
  have hb64 : b.data.size < 2 ^ 64 := by omega
  have hread : compiled.readContest.bound b ≤ 80 * b.data.size + 10704 := by
    rw [readContest_bound_eq]
    exact Demos.Rcv.TabulateProgram.readContest_bound b hb
  have hrc := readContest_eq b hb64
  rw [compiled.tabulate.bound_eq]
  generalize readContest b = ws at hrc ⊢
  unfold readResult at hrc
  cases hr : Spec.read (bytesOf b) with
  | error j r =>
    rw [hr] at hrc
    simp only [] at hrc
    have hj := Demos.Rcv.TabulateProgram.read_error_lt hr
    have h0 : ws[(0 : UInt64).toNat]! = 0 := by
      rw [Demos.Rcv.TabulateProgram.getElem!_eq_getD, hrc]; rfl
    have h1 : ws[(1 : UInt64).toNat]! = UInt64.ofNat j := by
      rw [Demos.Rcv.TabulateProgram.getElem!_eq_getD, hrc]; rfl
    have h2 : ws[(2 : UInt64).toNat]! = UInt64.ofNat r.code := by
      rw [Demos.Rcv.TabulateProgram.getElem!_eq_getD, hrc]; rfl
    rw [h0, h1, h2, ite_eq_left (by rfl)]
    have hpe := printError_bound (UInt64.ofNat j) (UInt64.ofNat r.code)
    have hsz : (PrintProgram.printError (UInt64.ofNat j) (UInt64.ofNat r.code)).data.size =
        (errorReport j r).length := by
      rw [← bytesOf_length, printError_eq j hj r]
    have hel := errorReport_length_le j hj r
    have hac := Verified.allocationCost_le
      (PrintProgram.printError (UInt64.ofNat j) (UInt64.ofNat r.code)).data.size
    omega
  | ok c =>
    rw [hr] at hrc
    simp only [] at hrc
    obtain ⟨hwc, hc⟩ := write_of_read hr
    have hn1 : 1 ≤ c.candidates.length := hc.2.2.1
    have hn2 : c.candidates.length ≤ 63 := hc.2.2.2.1
    have hnN : (UInt64.ofNat c.candidates.length).toNat = c.candidates.length :=
      ofNat_toNat_small (by omega)
    have h0 : ws[(0 : UInt64).toNat]! = UInt64.ofNat c.candidates.length := by
      rw [Demos.Rcv.TabulateProgram.getElem!_eq_getD, hrc]
      rfl
    have hne : (ws[(0 : UInt64).toNat]! == 0) = false := by
      rw [h0]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg UInt64.toNat h
      rw [hnN, UInt64.toNat_zero] at this
      omega
    have hsz : ws.size < 2 ^ 64 := by
      rw [← Array.length_toList, hrc, Demos.Rcv.TabulateProgram.contestWords_length c hc]
      have h1 : c.ballots.length * c.positions ≤ (2 ^ 32) * 63 := by
        have := hc.2.2.2.2.1
        simp only [maxBallots] at this
        exact Nat.mul_le_mul (by omega) hc.2.1
      omega
    have hcount := count_bound ws hsz
    have hres : Program.count ws =
        (resultWords c.candidates.length (firstContest c) (countContest c)).toArray := by
      rw [Refine.count_eq ws hsz, countArray, hrc, countWords_contestWords c hc]
    rw [ite_eq_right (by rw [hne]; simp), h0, hres, countedOf_contest c hc ws hrc]
    -- the rounds
    have hRle := (rounds_le (kindsOf c) c.order (positionsOf c)).2
    have hkl : (kindsOf c).length = c.candidates.length := by simp [kindsOf]
    have hcsl : (countedSet (kindsOf c)).length ≤ c.candidates.length := by
      have := (Demos.Rcv.Rounds.countedSet_sublist (kindsOf c)).length_le
      rw [List.length_range', hkl] at this
      exact this
    have hdef : count (kindsOf c) c.order (positionsOf c) = countContest c := rfl
    rw [hdef] at hRle
    have hR : ((resultWords c.candidates.length (firstContest c)
        (countContest c)).toArray[(1 : UInt64).toNat]!).toNat ≤ 64 := by
      rw [show ((1 : UInt64).toNat) = 1 from rfl, PrintProgram.result_rounds,
        ofNat_toNat_small (by omega)]
      omega
    have hpr := printReport_bound b (UInt64.ofNat c.candidates.length)
      (UInt64.ofNat (mask (countedSet (kindsOf c)))) _ (by omega) hR
    -- the header lines
    have hL : bytesOf b = text ((ascii "rcv-ballots 1" :: headerLines c) ++
        c.ballots.map ballotLine) := by
      rw [← hwc]
      rfl
    have hhl : (headerLines c).length = 5 + c.candidates.length := by
      simp only [headerLines, List.length_append, List.length_cons, List.length_nil,
        List.length_map, List.length_zipIdx]
      omega
    have h6 : (6 + UInt64.ofNat c.candidates.length).toNat = 6 + c.candidates.length := by
      rw [UInt64.toNat_add, hnN]
      simp only [UInt64.reduceToNat]
      omega
    have hh := header_loop b hb64 _ (lines_no_lf hc) hL (6 + UInt64.ofNat c.candidates.length)
      (by rw [h6]; simp only [List.length_append, List.length_cons, List.length_map, hhl]; omega)
    have htake : ((ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine).take
        (6 + c.candidates.length) = ascii "rcv-ballots 1" :: headerLines c := by
      rw [List.cons_append, show 6 + c.candidates.length = (5 + c.candidates.length) + 1 by omega,
        List.take_succ_cons, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [h6, htake, text_cons, List.length_append] at hh
    have h14 : (ascii "rcv-ballots 1" ++ [lf]).length = 14 := rfl
    have hH : ((LeanExe.loop (6 + UInt64.ofNat c.candidates.length) 0
        fun _ p => findByte b 10 p b.size + 1) - 14).toNat = (text (headerLines c)).length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hh, h14]; simp)), hh,
        h14]
      simp only [UInt64.reduceToNat]
      omega
    -- the report
    have hrep : (PrintProgram.printReport b (UInt64.ofNat c.candidates.length)
        (UInt64.ofNat (mask (countedSet (kindsOf c))))
        (resultWords c.candidates.length (firstContest c) (countContest c)).toArray).data.size =
        (report c).length := by
      rw [← bytesOf_length, PrintProgram.printReport_eq b hb64 c hc hwc.symm
        (report_length_lt c hc (by rw [hwc]; simpa using hb))]
    have hrl := report_length_le c hc
    have hht := Demos.Rcv.TabulateProgram.headerText_le c hc
    have hac := Verified.allocationCost_le (PrintProgram.printReport b
      (UInt64.ofNat c.candidates.length) (UInt64.ofNat (mask (countedSet (kindsOf c))))
      (resultWords c.candidates.length (firstContest c) (countContest c)).toArray).data.size
    omega

/-! ## The report's length and the C call in the size of the file -/

/-- Every Maine report holds at most 1,304,174 bytes: an error report at most 308, and the report
of a count its header lines, at most 20,777 bytes, and at most 1,283,397 more. -/
theorem reportFile_length_le (b : List UInt8) :
    (Demos.Rcv.Maine.reportFile b).length ≤ 1304174 := by
  unfold Demos.Rcv.Maine.reportFile
  split
  · next c hr =>
    have hc := (write_of_read hr).2
    have := report_length_le c hc
    have := Demos.Rcv.TabulateProgram.headerText_le c hc
    omega
  · next j r hr =>
    have := errorReport_length_le j (Demos.Rcv.TabulateProgram.read_error_lt hr) r
    omega

/-- `tabulate_native` in the size of the file: the C function of function 64 returns the Maine
report without a trap for a file of at most `L` bytes, when `top` and `80 L + 33,958,029` bytes
fit in the 720 MiB of `lx_mem`. -/
theorem tabulate_native_size (A : LClight.Archi) (X : LClight.ExtSem) (L : Nat) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 64, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[64]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X 11520 compiled.module compiled.translation ps rs fd false
        tabulateSpec
        (fun b heap _ => b.data.size ≤ L ∧ heap.top.toNat + 80 * L + 33958029 ≤ 65536 * 11520)
        (fun b heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.tabulate.bound b) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := tabulate_native A X
  refine ⟨fd, ps, rs, hfd, hsig, Demos.Rcv.TabulateProgram.nativeA_weaken h ?_⟩
  intro E store heap b m hcap hst hpre
  obtain ⟨hsize, hroom⟩ := hpre
  have hb := tabulate_bound b (by omega)
  show heap.top.toNat + compiled.tabulate.bound b ≤ 65536 * store.memoryCap compiled.module 0
  rw [LeanExe.Native.memoryCap_eq hst.2 compiled.module, hcap]
  omega

/-- `tabulate_native` for every file of at most 8,800,000 bytes, from a heap whose `top` is at
most 16,777,216 bytes, as it is after a host places a file of that size in a block of the module's
`alloc`. -/
theorem tabulate_native_8800000 (A : LClight.Archi) (X : LClight.ExtSem) :
    ∃ fd ps rs,
      (LeanExe.Native.funId 64, LClight.globdef.Gfun (LClight.fundef.Internal fd)) ∈
        compiled.translation.cprogram.prog_defs ∧
      (∀ g, compiled.module.funcs[64]? = some g → LeanExe.Native.signatureOf g = some (ps, rs)) ∧
      LeanExe.Native.NativeA A X 11520 compiled.module compiled.translation ps rs fd false
        tabulateSpec
        (fun b heap _ => b.data.size ≤ 8800000 ∧ heap.top.toNat ≤ 16777216)
        (fun b heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.tabulate.bound b) := by
  obtain ⟨fd, ps, rs, hfd, hsig, h⟩ := tabulate_native_size A X 8800000
  refine ⟨fd, ps, rs, hfd, hsig, Demos.Rcv.TabulateProgram.nativeA_weaken h ?_⟩
  intro E store heap b m _ _ hpre
  exact ⟨hpre.1, by omega⟩

#print axioms count_bound
#print axioms tabulate_bound
#print axioms reportFile_length_le
#print axioms tabulate_native_size
#print axioms tabulate_native_8800000

end Demos.Rcv.Maine.TabulateProgram
