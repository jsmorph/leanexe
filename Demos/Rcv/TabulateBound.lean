import Demos.Rcv.TabulateCall
import Demos.Rcv.VerifiedCall
import Verified.ChargeFacts

/-!
The closed form of the generated bound of `tabulate`.  `compiled.tabulate.bound b`, the number of
bytes by which a call of the export `tabulate` can raise the allocator's `top`, is the reader's
bound plus, for a malformed file, the bound of `printError`, and otherwise the count's bound and the
bound of `printReport`.  `tabulate_bound` closes it at `80 L + 33,702,909` bytes for a file of `L`
bytes, the bound that a host needs above `top` to call the export on every file of at most `L`
bytes.

Each push onto a paid array costs 80 bytes.  The reader pushes one word for each candidate line,
each index of the order line, and each position field of a ballot line, whose fields end at
distinct commas and LFs, so it costs at most `80 L + 10,080` bytes and two array literals of 312
bytes (`readContest_bound`).  The count's bound is that of `Demos.Rcv.Program.count_bound`, at
most 481,128 bytes: the two compilations generate the same bound, as `count_bound_eq` states.  The
report's printer pushes the first two lines, lines 2 to `6 + n` of the file, at most 20,777 bytes
for a structure that meets the constraints (`headerText_le`), and at most 64 rounds, each of which
costs at most `7,200 n + 18,720` bytes for `n` candidates when every number counts 20 digits, and
it copies the report, at most 1,301,030 bytes, into the buffer that it returns.
-/

namespace Demos.Rcv.TabulateProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram
open Library.Numerics.Decimal.Int64Text (digitCount)

theorem paidGrowCost_one : Verified.paidGrowCost 1 = 80 := rfl

/-- An `if` whose branches are bounded by `m` is bounded by `m`. -/
theorem ite_le {c : Prop} [Decidable c] {a b m : Nat} (ha : c → a ≤ m) (hb : ¬ c → b ≤ m) :
    (if c then a else b) ≤ m := by
  split
  next h => exact ha h
  next h => exact hb h

/-! ## The printers -/

theorem digitCount_le (v : UInt64) : (digitCount v).toNat ≤ 20 := by
  rw [Library.Numerics.Decimal.Int64Text.digitCount_toNat]
  exact Library.Numerics.Decimal.Int64Text.digitWords_length_le _ v.toNat_lt

theorem pushWord_cost (out : Array UInt64) (w len : UInt64) :
    compiled.pushWord.cost (⟨out⟩, w, len) = 80 * len.toNat := by
  rw [compiled.pushWord.cost_eq, Verified.loopCost_const, paidGrowCost_one, Nat.mul_comm]

theorem pushNumber_cost (out : Array UInt64) (v : UInt64) :
    compiled.pushNumber.cost (⟨out⟩, v) ≤ 1600 := by
  rw [compiled.pushNumber.cost_eq, Verified.loopCost_const, paidGrowCost_one]
  have := digitCount_le v
  omega

theorem pushRange_cost (out : Array UInt64) (b : Bytes) (s e : UInt64) :
    compiled.pushRange.cost (⟨out⟩, b, s, e) = 80 * (e - s).toNat := by
  rw [compiled.pushRange.cost_eq, Verified.loopCost_const, paidGrowCost_one, Nat.mul_comm]

theorem pushLine_cost (out : Array UInt64) (w1 l1 w2 l2 v : UInt64) :
    compiled.pushLine.cost (⟨out⟩, w1, l1, w2, l2, v) ≤ 80 * (l1.toNat + l2.toNat) + 1680 := by
  rw [compiled.pushLine.cost_eq, pushWord_cost, pushWord_cost, paidGrowCost_one]
  have := pushNumber_cost (pushWord (pushWord out w1 l1) w2 l2) v
  omega

/-- The first two lines of every report, 213 bytes. -/
theorem pushHead_cost (out : Array UInt64) : compiled.pushHead.cost ⟨out⟩ = 17040 := by
  rw [compiled.pushHead.cost_eq]
  simp only [pushWord_cost]
  rfl

theorem pushMembers_cost (out : Array UInt64) (mask n : UInt64) :
    compiled.pushMembers.cost (⟨out⟩, mask, n) ≤ 1680 * n.toNat := by
  rw [compiled.pushMembers.cost_eq]
  refine (Demos.Rcv.Program.loopCost_const_le (c := 1680) (fun k s => ?_) _ _).trans
    (by omega)
  try dsimp only
  split
  · have := pushNumber_cost (s.push 32) (k + 1)
    rw [paidGrowCost_one]
    omega
  · omega

theorem pushVotes_cost (out res : Array UInt64) (n base : UInt64) :
    compiled.pushVotes.cost (⟨out⟩, res, n, base) ≤ 3840 * n.toNat := by
  rw [compiled.pushVotes.cost_eq]
  refine (Demos.Rcv.Program.loopCost_const_le (c := 3840) (fun k s => ?_) _ _).trans
    (by omega)
  try dsimp only
  split
  · rw [pushWord_cost, paidGrowCost_one]
    have h1 := pushNumber_cost (pushWord s 35679995457398 6) (k + 1)
    have h2 := pushNumber_cost ((pushNumber (pushWord s 35679995457398 6) (k + 1)).push 32)
      res[(base + 2 + k).toNat]!
    simp only [UInt64.reduceToNat]
    omega
  · omega

theorem pushElimination_cost (out : Array UInt64) (code elim tied n : UInt64) :
    compiled.pushElimination.cost (⟨out⟩, code, elim, tied, n) ≤ 3360 * n.toNat + 1600 := by
  rw [compiled.pushElimination.cost_eq]
  split
  · simp only [pushWord_cost, paidGrowCost_one, UInt64.reduceToNat]
    grw [pushMembers_cost]
    omega
  · split
    · simp only [pushWord_cost, paidGrowCost_one, UInt64.reduceToNat]
      grw [pushMembers_cost, pushMembers_cost]
      omega
    · split
      · simp only [pushWord_cost, paidGrowCost_one, UInt64.reduceToNat]
        grw [pushMembers_cost]
        omega
      · omega

/-- The lines of a round: six lines of a text and a number, the votes, three words, and the
elimination. -/
theorem pushRoundLines_cost (out res : Array UInt64) (n base r : UInt64) :
    compiled.pushRoundLines.cost (⟨out⟩, res, n, base, r) ≤ 7200 * n.toNat + 18720 := by
  rw [compiled.pushRoundLines.cost_eq]
  simp only [pushWord_cost, UInt64.reduceToNat]
  grw [pushLine_cost, pushLine_cost, pushLine_cost, pushLine_cost, pushLine_cost, pushLine_cost,
    pushVotes_cost, pushElimination_cost]
  simp only [UInt64.reduceToNat]
  omega

theorem pushRole_cost (out : Array UInt64) (code : UInt64) :
    compiled.pushRole.cost (⟨out⟩, code) ≤ 800 := by
  rw [compiled.pushRole.cost_eq]
  simp only [pushWord_cost, UInt64.reduceToNat]
  split_ifs <;> omega

/-- The bound of `printReport`: the first two lines, the header lines, which run from byte 14 to
the position after line `6 + n`, the rounds, the winner's line, and the copy of the report into
the returned buffer. -/
theorem printReport_bound (b : Bytes) (n : UInt64) (res : Array UInt64) (hn : n.toNat ≤ 63)
    (hR : (res[(1 : UInt64).toNat]!).toNat ≤ 64) :
    compiled.printReport.bound (b, n, res) ≤
      80 * ((LeanExe.loop (6 + n) 0 fun _ p => findByte b 10 p b.size + 1) - 14).toNat +
        Verified.Bytes.allocationCost (printReport b n res).data.size + 30247832 := by
  have key : ∀ o : Array UInt64, toBytes o = printReport b n res →
      compiled.toBytes.bound o = Verified.Bytes.allocationCost (printReport b n res).data.size := by
    intro o h
    rw [compiled.toBytes.bound_eq, ← h, toBytes, Bytes.data_size_build]
  rw [compiled.printReport.bound_eq, key _ rfl, pushHead_cost, pushRange_cost]
  grw [Demos.Rcv.Program.loopCost_const_le (c := 7200 * n.toNat + 18720)
    (fun k s => pushRoundLines_cost s _ _ _ _)]
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
    simp only [pushWord_cost, paidGrowCost_one, UInt64.reduceToNat]
    omega

/-- The bound of `printError`: the first two lines, `error `, the line number, a space, the role,
the LF, and the copy of the report into the returned buffer. -/
theorem printError_bound (j code : UInt64) :
    compiled.printError.bound (j, code) ≤
      Verified.Bytes.allocationCost (printError j code).data.size + 20152 := by
  have key : ∀ o : Array UInt64, toBytes o = printError j code →
      compiled.toBytes.bound o = Verified.Bytes.allocationCost (printError j code).data.size := by
    intro o h
    rw [compiled.toBytes.bound_eq, ← h, toBytes, Bytes.data_size_build]
  rw [compiled.printError.bound_eq, key _ rfl, pushHead_cost, pushWord_cost, paidGrowCost_one]
  grw [pushNumber_cost, pushRole_cost]
  have hblock : Verified.blockCost (UInt64.toNat 0) = 56 := rfl
  have hcredit : Verified.creditCost (#[] : Array UInt64).size = 16 := rfl
  rw [hblock, hcredit]
  simp only [UInt64.reduceToNat]
  omega

/-! ## The reader -/

/-- `findByte` returns a position from `p` to `e` when `p ≤ e`, and `e` otherwise. -/
theorem findByte_range (b : Bytes) (c p e : UInt64) :
    (p ≤ e → p ≤ findByte b c p e ∧ findByte b c p e ≤ e) ∧
      (¬ p ≤ e → findByte b c p e = e) := by
  refine ⟨fun h => ⟨(findByte_spec b c p e h).1, (findByte_spec b c p e h).2.1⟩, fun h => ?_⟩
  rw [findByte, ite_eq_right (fun hlt => h (UInt64.le_of_lt hlt))]

/-- A position found below `e` lies at or after the start. -/
theorem findByte_lt_start {b : Bytes} {c p e : UInt64} (h : findByte b c p e < e) :
    p ≤ findByte b c p e := by
  by_cases hpe : p ≤ e
  · exact ((findByte_range b c p e).1 hpe).1
  · rw [(findByte_range b c p e).2 hpe] at h
    exact absurd h (UInt64.lt_irrefl _)

/-- The fields of a ballot line from `p` to `e` push at most one word for each byte from `p` to
`e` and one more. -/
theorem fieldsFrom_cost (b : Bytes) (n p e fuel : UInt64) (out : Array UInt64) :
    compiled.fieldsFrom.cost (b, n, p, e, fuel, ⟨out⟩) ≤ 80 * (e.toNat - p.toNat + 1) := by
  suffices h : ∀ (m : Nat) (p e fuel : UInt64) (out : Array UInt64), fuel.toNat = m →
      compiled.fieldsFrom.cost (b, n, p, e, fuel, ⟨out⟩) ≤ 80 * (e.toNat - p.toNat + 1) from
    h _ p e fuel out rfl
  intro m
  induction m with
  | zero =>
    intro p e fuel out hm
    have h0 : ¬ 0 < fuel := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.fieldsFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.fieldsFrom.wellFounded h)]
    simp [compiled.fieldsFrom.step, h0]
  | succ m ih =>
    intro p e fuel out hm
    have h0 : 0 < fuel := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.fieldsFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.fieldsFrom.wellFounded h)]
    by_cases hw : (fieldWord b n p (findByte b 44 p e)).1 = true
    · by_cases hq : findByte b 44 p e < e
      · have hs : compiled.fieldsFrom.step (b, n, p, e, fuel, out) =
            .inl (b, n, findByte b 44 p e + 1, e, fuel - 1,
              out.push (fieldWord b n p (findByte b 44 p e)).2) := by
          simp [compiled.fieldsFrom.step, h0, hw, hq]
        rw [hs, Sum.elim_inl, ← compiled.fieldsFrom.cost_eq]
        have hrest := ih (findByte b 44 p e + 1) e (fuel - 1)
          (out.push (fieldWord b n p (findByte b 44 p e)).2) (by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
            simp [hm])
        have hp := UInt64.le_iff_toNat_le.mp (findByte_lt_start hq)
        have hqe := UInt64.lt_iff_toNat_lt.mp hq
        rw [toNat_add_one hq] at hrest
        simp only [eq_true h0, eq_true hw, eq_true hq, ↓reduceIte, paidGrowCost_one]
        omega
      · have hs : compiled.fieldsFrom.step (b, n, p, e, fuel, out) =
            .inr (true, out.push (fieldWord b n p (findByte b 44 p e)).2) := by
          simp [compiled.fieldsFrom.step, h0, hw, hq]
        rw [hs]
        simp only [eq_true h0, eq_true hw, eq_false hq, ↓reduceIte, paidGrowCost_one,
          Sum.elim_inr]
        omega
    · have hs : compiled.fieldsFrom.step (b, n, p, e, fuel, out) = .inr (false, out) := by
        simp [compiled.fieldsFrom.step, h0, hw]
      rw [hs]
      simp only [eq_true h0, eq_false hw, ↓reduceIte, Sum.elim_inr]
      omega

/-- A ballot line from `s` to `e` pushes at most one word for each byte from `s` to `e` and one
more. -/
theorem ballotWords_cost (b : Bytes) (k n s e : UInt64) (out : Array UInt64)
    (he : e.toNat + 1 < 2 ^ 64) :
    compiled.ballotWords.cost (b, k, n, s, e, ⟨out⟩) ≤ 80 * (e.toNat - s.toNat + 1) := by
  rw [compiled.ballotWords.cost_eq]
  split
  · exact fieldsFrom_cost b n s e k out
  · split
    · split
      · have h := fieldsFrom_cost b n (findByte b 44 s e + 1) e k out
        have hle : (findByte b 44 s e).toNat ≤ e.toNat := by
          by_cases hse : s ≤ e
          · exact UInt64.le_iff_toNat_le.mp ((findByte_range b 44 s e).1 hse).2
          · rw [(findByte_range b 44 s e).2 hse]
        have hq : (findByte b 44 s e + 1).toNat = (findByte b 44 s e).toNat + 1 := by
          rw [UInt64.toNat_add]
          simp only [UInt64.reduceToNat]
          omega
        have hs : e.toNat - (findByte b 44 s e + 1).toNat ≤ e.toNat - s.toNat := by
          by_cases hse : s ≤ e
          · have := UInt64.le_iff_toNat_le.mp ((findByte_range b 44 s e).1 hse).1
            omega
          · rw [hq, (findByte_range b 44 s e).2 hse]
            omega
        omega
      · omega
    · omega

/-- The ballot lines from `p` on push at most one word for each byte from `p` to the end of the
file. -/
theorem ballotsFrom_cost (b : Bytes) (hb : b.data.size < 2 ^ 32) (k n p j count : UInt64)
    (out : Array UInt64) :
    compiled.ballotsFrom.cost (b, k, n, p, j, count, ⟨out⟩) ≤ 80 * (b.size.toNat - p.toNat) := by
  have hsize : b.size.toNat = b.data.size := Bytes.size_toNat b (by omega)
  suffices h : ∀ (m : Nat) (p j count : UInt64) (out : Array UInt64), count.toNat = m →
      compiled.ballotsFrom.cost (b, k, n, p, j, count, ⟨out⟩) ≤
        80 * (b.size.toNat - p.toNat) from h _ p j count out rfl
  intro m
  induction m with
  | zero =>
    intro p j count out hm
    have h0 : ¬ 0 < count := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.ballotsFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.ballotsFrom.wellFounded h)]
    simp [compiled.ballotsFrom.step, h0]
  | succ m ih =>
    intro p j count out hm
    have h0 : 0 < count := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.ballotsFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.ballotsFrom.wellFounded h)]
    by_cases he : findByte b 10 p b.size < b.size
    · have hp := UInt64.le_iff_toNat_le.mp (findByte_lt_start he)
      have hes := UInt64.lt_iff_toNat_lt.mp he
      have hline := ballotWords_cost b k n p (findByte b 10 p b.size) out (by omega)
      by_cases hr : (ballotWords b k n p (findByte b 10 p b.size) out).1 = true
      · have hs : compiled.ballotsFrom.step (b, k, n, p, j, count, out) =
            .inl (b, k, n, findByte b 10 p b.size + 1, j + 1, count - 1,
              (ballotWords b k n p (findByte b 10 p b.size) out).2) := by
          simp [compiled.ballotsFrom.step, h0, he, hr]
        rw [hs, Sum.elim_inl, ← compiled.ballotsFrom.cost_eq]
        have hrest := ih (findByte b 10 p b.size + 1) (j + 1) (count - 1)
          (ballotWords b k n p (findByte b 10 p b.size) out).2 (by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
            simp [hm])
        rw [toNat_add_one he] at hrest
        simp only [eq_true h0, eq_true he, ↓reduceIte]
        omega
      · have hs : compiled.ballotsFrom.step (b, k, n, p, j, count, out) =
            .inr (j, 0, (ballotWords b k n p (findByte b 10 p b.size) out).2) := by
          simp [compiled.ballotsFrom.step, h0, he, hr]
        rw [hs]
        simp only [eq_true h0, eq_true he, ↓reduceIte, Sum.elim_inr]
        omega
    · have hs : compiled.ballotsFrom.step (b, k, n, p, j, count, out) = .inr (j, 0, out) := by
        simp [compiled.ballotsFrom.step, h0, he]
      rw [hs]
      simp only [eq_true h0, eq_false he, ↓reduceIte, Sum.elim_inr]
      omega

/-- The candidate lines push at most one word each. -/
theorem candidatesFrom_cost (b : Bytes) (p i count : UInt64) (out : Array UInt64) :
    compiled.candidatesFrom.cost (b, p, i, count, ⟨out⟩) ≤ 80 * count.toNat := by
  suffices h : ∀ (m : Nat) (p i count : UInt64) (out : Array UInt64), count.toNat = m →
      compiled.candidatesFrom.cost (b, p, i, count, ⟨out⟩) ≤ 80 * count.toNat from
    h _ p i count out rfl
  intro m
  induction m with
  | zero =>
    intro p i count out hm
    have h0 : ¬ 0 < count := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.candidatesFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.candidatesFrom.wellFounded h)]
    simp [compiled.candidatesFrom.step, h0]
  | succ m ih =>
    intro p i count out hm
    have h0 : 0 < count := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.candidatesFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.candidatesFrom.wellFounded h)]
    by_cases he : findByte b 10 p b.size < b.size
    · by_cases hc : candidateCode b i p (findByte b 10 p b.size) < 4
      · have hs : compiled.candidatesFrom.step (b, p, i, count, out) =
            .inl (b, findByte b 10 p b.size + 1, i + 1, count - 1,
              out.push (candidateCode b i p (findByte b 10 p b.size))) := by
          simp [compiled.candidatesFrom.step, h0, he, hc]
        rw [hs, Sum.elim_inl, ← compiled.candidatesFrom.cost_eq]
        have hc1 : (count - 1).toNat = m := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
          simp [hm]
        have hrest := ih (findByte b 10 p b.size + 1) (i + 1) (count - 1)
          (out.push (candidateCode b i p (findByte b 10 p b.size))) hc1
        simp only [eq_true h0, eq_true he, eq_true hc, ↓reduceIte, paidGrowCost_one]
        omega
      · have hs : compiled.candidatesFrom.step (b, p, i, count, out) =
            .inr (4 + i, 0, out) := by
          simp [compiled.candidatesFrom.step, h0, he, hc]
        rw [hs]
        simp only [eq_true h0, eq_true he, eq_false hc, ↓reduceIte, Sum.elim_inr]
        omega
    · have hs : compiled.candidatesFrom.step (b, p, i, count, out) = .inr (4 + i, 0, out) := by
        simp [compiled.candidatesFrom.step, h0, he]
      rw [hs]
      simp only [eq_true h0, eq_false he, ↓reduceIte, Sum.elim_inr]
      omega

/-- The indices of an order line push at most one word each, and at most `fuel` of them. -/
theorem orderFrom_cost (b : Bytes) (n p e seen count fuel : UInt64) (out : Array UInt64) :
    compiled.orderFrom.cost (b, n, p, e, seen, count, fuel, ⟨out⟩) ≤ 80 * fuel.toNat := by
  suffices h : ∀ (m : Nat) (p e seen count fuel : UInt64) (out : Array UInt64), fuel.toNat = m →
      compiled.orderFrom.cost (b, n, p, e, seen, count, fuel, ⟨out⟩) ≤ 80 * fuel.toNat from
    h _ p e seen count fuel out rfl
  intro m
  induction m with
  | zero =>
    intro p e seen count fuel out hm
    have h0 : ¬ 0 < fuel := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.orderFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.orderFrom.wellFounded h)]
    simp [compiled.orderFrom.step, h0]
  | succ m ih =>
    intro p e seen count fuel out hm
    have h0 : 0 < fuel := by rw [UInt64.lt_iff_toNat_lt]; simp [hm]
    rw [compiled.orderFrom.cost_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.orderFrom.wellFounded h)]
    by_cases hok : ((readNumber b p (findByte b 32 p e)).1 &&
        decide (1 ≤ (readNumber b p (findByte b 32 p e)).2) &&
        decide ((readNumber b p (findByte b 32 p e)).2 ≤ n) &&
        seen >>> ((readNumber b p (findByte b 32 p e)).2 - 1) &&& 1 == 0) = true
    · by_cases hqe : findByte b 32 p e < e
      · have hs : compiled.orderFrom.step (b, n, p, e, seen, count, fuel, out) =
            .inl (b, n, findByte b 32 p e + 1, e,
              seen ||| 1 <<< ((readNumber b p (findByte b 32 p e)).2 - 1), count + 1, fuel - 1,
              out.push (readNumber b p (findByte b 32 p e)).2) := by
          simp only [compiled.orderFrom.step, eq_true h0, eq_true hok, eq_true hqe, ↓reduceIte]
        rw [hs, Sum.elim_inl, ← compiled.orderFrom.cost_eq]
        have hf1 : (fuel - 1).toNat = m := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
          simp [hm]
        have hrest := ih (findByte b 32 p e + 1) e
          (seen ||| 1 <<< ((readNumber b p (findByte b 32 p e)).2 - 1)) (count + 1) (fuel - 1)
          (out.push (readNumber b p (findByte b 32 p e)).2) hf1
        simp only [eq_true h0, eq_true hok, eq_true hqe, ↓reduceIte, paidGrowCost_one]
        omega
      · have hs : compiled.orderFrom.step (b, n, p, e, seen, count, fuel, out) =
            .inr (count + 1 == n, out.push (readNumber b p (findByte b 32 p e)).2) := by
          simp only [compiled.orderFrom.step, eq_true h0, eq_true hok, eq_false hqe, ↓reduceIte]
        rw [hs]
        simp only [eq_true h0, eq_true hok, eq_false hqe, ↓reduceIte, paidGrowCost_one,
          Sum.elim_inr]
        omega
    · have hs : compiled.orderFrom.step (b, n, p, e, seen, count, fuel, out) =
          .inr (false, out) := by
        simp only [compiled.orderFrom.step, eq_true h0, eq_false hok, ↓reduceIte]
      rw [hs]
      simp only [eq_true h0, eq_false hok, ↓reduceIte, Sum.elim_inr]
      omega

theorem readOrder_cost (b : Bytes) (n s e : UInt64) (out : Array UInt64) :
    compiled.readOrder.cost (b, n, s, e, ⟨out⟩) ≤ 80 * n.toNat := by
  rw [compiled.readOrder.cost_eq]
  split
  · exact orderFrom_cost b n (s + 6) e 0 0 n out
  · omega

theorem readAfter_le (b : Bytes) (s e w1 l1 w2 l2 lo hi : UInt64)
    (h : (readAfter b s e w1 l1 w2 l2 lo hi).1 = true) :
    (readAfter b s e w1 l1 w2 l2 lo hi).2 ≤ hi := by
  unfold readAfter at h ⊢
  split at h
  · rename_i hp
    rw [ite_eq_left hp]
    dsimp only at h ⊢
    split at h
    · rename_i hc
      rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.2
    · simp at h
  · simp at h

/-- A file whose first four lines meet their roles has at most 63 candidates. -/
theorem readHead_n (b : Bytes) : (readHead b).1 = 0 → (readHead b).2.2.1.toNat ≤ 63 := by
  unfold readHead
  dsimp only
  split
  · split
    · split
      · split
        · rename_i h4
          intro _
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
          exact UInt64.le_iff_toNat_le.mp (readAfter_le _ _ _ _ _ _ _ _ _ h4.2)
        · simp
      · simp
    · simp
  · simp

/-- The reader pushes at most one word for each candidate, each index of the order, and each
byte of the ballot lines, after an array literal of three words, and an error adds a second
literal of three words. -/
theorem readContest_bound (b : Bytes) (hb : b.data.size < 2 ^ 32) :
    compiled.readContest.bound b ≤ 80 * b.data.size + 10704 := by
  have hsize : b.size.toNat = b.data.size := Bytes.size_toNat b (by omega)
  rw [compiled.readContest.bound_eq]
  simp only [Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq,
    UInt64.reduceToNat, List.size_toArray, List.length_nil]
  split
  · rename_i hh
    have hn := readHead_n b (by simpa using hh)
    grw [candidatesFrom_cost]
    split
    · grw [readOrder_cost]
      split
      · split
        · grw [ballotsFrom_cost b hb]
          split <;> (try split) <;> omega
        · omega
      · omega
    · omega
  · omega

/-! ## The header lines and the reports -/

/-- The header lines of a structure that meets the constraints hold at most 20,777 bytes: the
contest line, at most 74, the lines of `k` and `n`, at most 32 and 33, at most 63 candidate lines
of at most 306 bytes, the order line, at most 1,330, and the ballot count's line, at most 30. -/
theorem headerText_le (c : Contest) (hc : c.WellFormed) :
    (text (headerLines c)).length ≤ 20777 := by
  obtain ⟨_, hk2, _, hn2, hN, hid, hnames, hperm, _⟩ := hc
  simp only [maxIndex, maxBallots] at hk2 hn2 hN
  have hidl : c.contest.length ≤ 64 := by
    simp only [identOk, Bool.and_eq_true, decide_eq_true_eq] at hid
    exact hid.1.2
  have hol : c.order.length = c.candidates.length := by
    rw [hperm.length_eq, List.length_range']
  have hom : ∀ i ∈ c.order, i < 2 ^ 64 := by
    intro i hi
    have := List.mem_range'_1.mp (hperm.mem_iff.mp hi)
    omega
  have hkw : ∀ k, (ascii (kindWord k)).length ≤ 17 := by
    intro k
    cases k <;> decide
  unfold headerLines
  rw [text_append, text_append, List.length_append, List.length_append]
  have h1 : (text [spaced [ascii "contest", c.contest], spaced [ascii "positions",
      decimal c.positions], spaced [ascii "candidates", decimal c.candidates.length]]).length ≤
      139 := by
    rw [text_length]
    have a1 := spaced_length_le [ascii "contest", c.contest]
    have a2 := spaced_length_le [ascii "positions", decimal c.positions]
    have a3 := spaced_length_le [ascii "candidates", decimal c.candidates.length]
    have d2 := decimal_length_le (v := c.positions) (by omega)
    have d3 := decimal_length_le (v := c.candidates.length) (by omega)
    have l1 : (ascii "contest").length = 7 := rfl
    have l2 : (ascii "positions").length = 9 := rfl
    have l3 : (ascii "candidates").length = 10 := rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at a1 a2 a3 ⊢
    omega
  have h2 : (text ((c.candidates.zipIdx 1).map fun p : Candidate × Nat =>
      spaced [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind), p.1.name])).length ≤
      63 * 306 := by
    have := text_length_le (m := 305) (ls := (c.candidates.zipIdx 1).map fun p : Candidate × Nat =>
      spaced [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind), p.1.name]) (by
      intro l hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      have hname := hnames p.1 (List.fst_mem_of_mem_zipIdx hp)
      simp only [nameOk, Bool.and_eq_true, decide_eq_true_eq] at hname
      have hi := List.snd_lt_add_of_mem_zipIdx hp
      have a := spaced_length_le [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind),
        p.1.name]
      have d := decimal_length_le (v := p.2) (by omega)
      have k := hkw p.1.kind
      have l : (ascii "candidate").length = 9 := rfl
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at a
      omega)
    rw [List.length_map, List.length_zipIdx] at this
    exact this.trans (Nat.mul_le_mul_right 306 hn2)
  have h3 : (text [spaced (ascii "order" :: c.order.map decimal),
      spaced [ascii "ballots", decimal c.ballots.length]]).length ≤ 1360 := by
    rw [text_length]
    have a1 := spaced_length_le (ascii "order" :: c.order.map decimal)
    have a2 := spaced_length_le [ascii "ballots", decimal c.ballots.length]
    have d2 := decimal_length_le (v := c.ballots.length) (by omega)
    have l1 : (ascii "order").length = 5 := rfl
    have l2 : (ascii "ballots").length = 7 := rfl
    have hsum : ((c.order.map decimal).map fun p => p.length + 1).sum ≤ c.order.length * 21 := by
      rw [List.map_map]
      have hb : ∀ x ∈ c.order.map ((fun p : List UInt8 => p.length + 1) ∘ decimal), x ≤ 21 := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have := decimal_length_le (hom i hi)
        simp only [Function.comp_apply]
        omega
      have := List.sum_le_card_nsmul _ 21 hb
      simpa using this
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at a1 a2 ⊢
    omega
  omega

/-- An error report holds at most 251 bytes. -/
theorem errorReport_length_le (j : Nat) (hj : j < 2 ^ 64) (r : Role) :
    (errorReport j r).length ≤ 251 := by
  rw [errorReport_eq]
  simp only [List.length_append, head_length, List.length_cons, List.length_nil]
  have := decimal_length_le hj
  have hw : (ascii r.word).length ≤ 10 := by cases r <;> decide
  have : (ascii "error").length = 5 := rfl
  omega

/-! ## The count -/

/-- The tabulator's compilation and the count's own compilation generate the same bound for the
count. -/
theorem count_bound_eq (ws : Array UInt64) :
    compiled.count.bound ws = Demos.Rcv.Program.compiled.count.bound ws := by
  rw [compiled.count.bound_eq, Demos.Rcv.Program.compiled.count.bound_eq,
    compiled.countValid.bound_eq, Demos.Rcv.Program.compiled.countValid.bound_eq]
  simp only [compiled.tallyRound.bound_eq, Demos.Rcv.Program.compiled.tallyRound.bound_eq,
    compiled.pushRound.cost_eq, Demos.Rcv.Program.compiled.pushRound.cost_eq]

theorem count_bound_tabulate (ws : Array UInt64) (hs : ws.size < 2 ^ 64) :
    compiled.count.bound ws ≤ 481128 := by
  rw [count_bound_eq]
  exact Demos.Rcv.Program.count_bound ws hs

/-! ## The bound of `tabulate` -/

/-- The closed form of the generated bound of `tabulate`: a call on a file of fewer than `2 ^ 32`
bytes raises the allocator's `top` by at most 80 bytes for each byte of the file and 33,702,909
bytes more. -/
theorem tabulate_bound (b : Bytes) (hb : b.data.size < 2 ^ 32) :
    compiled.tabulate.bound b ≤ 80 * b.data.size + 33702909 := by
  have hb64 : b.data.size < 2 ^ 64 := by omega
  have hread := readContest_bound b hb
  have hrc := readContest_eq b hb64
  rw [compiled.tabulate.bound_eq]
  generalize readContest b = ws at hrc ⊢
  unfold readResult at hrc
  cases hr : Spec.read (bytesOf b) with
  | error j r =>
    rw [hr] at hrc
    simp only [] at hrc
    have hj := read_error_lt hr
    have h0 : ws[(0 : UInt64).toNat]! = 0 := by rw [getElem!_eq_getD, hrc]; rfl
    have h1 : ws[(1 : UInt64).toNat]! = UInt64.ofNat j := by rw [getElem!_eq_getD, hrc]; rfl
    have h2 : ws[(2 : UInt64).toNat]! = UInt64.ofNat r.code := by rw [getElem!_eq_getD, hrc]; rfl
    rw [h0, h1, h2, ite_eq_left (by rfl)]
    have hpe := printError_bound (UInt64.ofNat j) (UInt64.ofNat r.code)
    have hsz : (printError (UInt64.ofNat j) (UInt64.ofNat r.code)).data.size =
        (errorReport j r).length := by
      rw [← bytesOf_length, printError_eq j hj r]
    have hel := errorReport_length_le j hj r
    have hac := Verified.allocationCost_le
      (printError (UInt64.ofNat j) (UInt64.ofNat r.code)).data.size
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
      rw [getElem!_eq_getD, hrc]
      rfl
    have hne : (ws[(0 : UInt64).toNat]! == 0) = false := by
      rw [h0]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg UInt64.toNat h
      rw [hnN, UInt64.toNat_zero] at this
      omega
    have hsz : ws.size < 2 ^ 64 := by
      rw [← Array.length_toList, hrc, contestWords_length c hc]
      have h1 : c.ballots.length * c.positions ≤ (2 ^ 32) * 63 := by
        have := hc.2.2.2.2.1
        simp only [maxBallots] at this
        exact Nat.mul_le_mul (by omega) hc.2.1
      omega
    have hcount := count_bound_tabulate ws hsz
    have hres : Demos.Rcv.Program.count ws =
        (resultWords c.candidates.length (countContest c)).toArray := by
      rw [Demos.Rcv.Refine.count_eq ws hsz, countArray, hrc, countWords_contestWords c hc]
    rw [ite_eq_right (by rw [hne]; simp), h0, hres]
    -- the rounds
    have hRle := Demos.Rcv.Winner.rounds_le (kindsOf c) c.order
      (c.ballots.map fun b : Ballot => b.positions)
    have hkl : (kindsOf c).length = c.candidates.length := by simp [kindsOf]
    have hcsl : (countedSet (kindsOf c)).length ≤ c.candidates.length := by
      have := (Demos.Rcv.Rounds.countedSet_sublist (kindsOf c)).length_le
      rw [List.length_range', hkl] at this
      exact this
    have hdef : count (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions) =
        countContest c := rfl
    rw [hdef] at hRle
    have hR : ((resultWords c.candidates.length
        (countContest c)).toArray[(1 : UInt64).toNat]!).toNat ≤ 64 := by
      rw [show ((1 : UInt64).toNat) = 1 from rfl, resultWords_rounds,
        ofNat_toNat_small (by omega)]
      omega
    have hpr := printReport_bound b (UInt64.ofNat c.candidates.length) _ (by omega) hR
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
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hh, h14]; simp)), hh, h14]
      simp only [UInt64.reduceToNat]
      omega
    -- the report
    have hrep : (printReport b (UInt64.ofNat c.candidates.length)
        (resultWords c.candidates.length (countContest c)).toArray).data.size =
        (report c).length := by
      rw [← bytesOf_length, printReport_eq b hb64 c hc hwc.symm
        (report_length_lt c hc (by rw [hwc]; simpa using hb))]
    have hrl := report_length_le c hc
    have hht := headerText_le c hc
    have hac := Verified.allocationCost_le (printReport b (UInt64.ofNat c.candidates.length)
      (resultWords c.candidates.length (countContest c)).toArray).data.size
    omega

/-- Every report holds at most 1,301,030 bytes: an error report at most 251, and the report of a
count its header lines, at most 20,777 bytes, and at most 1,280,253 more. -/
theorem reportFile_length_le (b : List UInt8) : (reportFile b).length ≤ 1301030 := by
  unfold reportFile
  split
  · next c hr =>
    have hc := (write_of_read hr).2
    have := report_length_le c hc
    have := headerText_le c hc
    omega
  · next j r hr =>
    have := errorReport_length_le j (read_error_lt hr) r
    omega

#print axioms tabulate_bound
#print axioms reportFile_length_le

end Demos.Rcv.TabulateProgram
