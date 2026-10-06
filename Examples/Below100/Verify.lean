import Examples.Below100.Module
import Examples.Below100.Spec
import LeanExe.IR.ArrayLiteral
import LeanExe.IR.Correct
import LeanExe.IR.OneArray
import LeanExe.IR.Append
import LeanExe.IR.Update
import LeanExe.IR.Words
import LeanExe.Encoding.RoundTrip

/-! The bytes of `below100.module` compute the specification `expected`. -/

namespace Examples.Below100

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.Below100

theorem keep_eq (xs : Array UInt64) (i : UInt64) (out : Array UInt64) :
    keep xs i out = (i + 1, if xs[i.toNat]! < 100 then out.push xs[i.toNat]! else out) := by
  by_cases h : xs[i.toNat]! < 100 <;> simp [keep, h]

/-- `keep` repeated from index `i` until `count` filters the first `count` elements. -/
theorem keep_go (xs : Array UInt64) (count : UInt64) (hc : count.toNat ≤ xs.size) :
    ∀ (k : Nat) (i : UInt64) (out : Array UInt64), i.toNat ≤ count.toNat →
      count.toNat - i.toNat ≤ k →
      out.toList = (xs.toList.take i.toNat).filter (fun e => decide (e < 100)) →
      (LeanExe.repeatWhile.go (fun (s : UInt64 × Array UInt64) => decide (s.1 < count))
        (fun s => keep xs s.1 s.2) k (i, out)).2.toList =
        (xs.toList.take count.toNat).filter (fun e => decide (e < 100)) := by
  have hcount := count.toNat_lt
  intro k
  induction k with
  | zero =>
    intro i out hi hk hout
    have : i.toNat = count.toNat := by omega
    simp only [LeanExe.repeatWhile.go]
    rw [hout, this]
  | succ k ih =>
    intro i out hi hk hout
    simp only [LeanExe.repeatWhile.go]
    by_cases hlt : i < count
    · have hlt' : i.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hix : i.toNat < xs.toList.length := by simp; omega
      have hx : xs[i.toNat]! = xs.toList[i.toNat] := by
        rw [getElem!_pos xs i.toNat (by omega)]; simp
      simp only [hlt, decide_true, ite_true]
      show (LeanExe.repeatWhile.go _ _ k (keep xs i out)).2.toList = _
      rw [keep_eq xs i out]
      refine ih (i + 1) _ (by omega) (by omega) ?_
      rw [hi1, List.take_add_one, List.filter_append, ← hout, List.getElem?_eq_getElem hix, hx]
      generalize xs.toList[i.toNat] = v
      by_cases h : v < 100 <;> simp [h]
    · have hge : count.toNat ≤ i.toNat :=
        Nat.le_of_not_lt fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      have : i.toNat = count.toNat := by omega
      simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      rw [hout, this]

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  by_cases hs : xs.size ≤ 8
  · have hle : xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_true, hs]
    apply Array.toList_inj.mp
    have := keep_go xs xs.size.toUInt64 (by rw [hn]) 8 0 #[] (by simp) (by rw [hn]; simp; omega)
      (by simp)
    rw [hn, List.take_of_length_le (by simp)] at this
    rw [Array.toList_filter, ← this]
    rfl
  · have hle : ¬ xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_false, hs]
    rfl

/-- `keep` with its three arguments as one tuple: the call consumes the output array. -/
def keepTuple (x : Array UInt64 × UInt64 × Moved (Array UInt64)) : UInt64 × Array UInt64 :=
  keep x.1 x.2.1 x.2.2.val

set_option maxHeartbeats 2000000 in
theorem keep_implements : Implements below100.module 2 keepTuple := by
  refine Func.implements_moves below100.funcs 0 below100.keep.ir "keep" rfl keepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨xs, i, ⟨out⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, rfl, po, rfl, hOut⟩ - hCap
  change heap.Owned initial po out at hOut
  have hLive := Live.start_moved hHeap (temps := [(po, out)]) (by simpa using hOut)
    (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial ([.i64 px] ++ (Scalar.values i ++ [.i64 po]))
      ((xs, i, ⟨out⟩) : Array UInt64 × UInt64 × Moved (Array UInt64)) = [po] := rfl
  rw [hMoves]
  have hW := hXs.values
  have hRead : ∀ (st : State) (k : UInt64), st.get 0 = some (.i64 px) →
      Expr.readValue initial.mem 0 k st = some (xs[k.toNat]!, st) :=
    fun _ _ h => Expr.readValue_at hW h
  have hImports : below100.module.imports = [] := rfl
  have hMemory32 : below100.module.memIs64 = false := rfl
  have hAlloc : below100.module.funcs[0]? = some (allocFunction 0) := rfl
  have hRelease : below100.module.funcs[1]? = some (releaseFunction 1) := rfl
  set start := below100.keep.ir.state ([.i64 px] ++ (Scalar.values i ++ [.i64 po])) with hStartDef
  have hStart : start.params.length + start.locals.length = 13 := rfl
  have hScratch : below100.keep.ir.scratch = 12 := rfl
  have hG0 : start.get 0 = some (.i64 px) := rfl
  have hG1 : start.get 1 = some (.i64 i) := rfl
  have hG2 : start.get 2 = some (.i64 po) := rfl
  let x := xs[i.toNat]!
  let s1 := (start.update 12 (.i64 i)).update 3 (.i64 x)
  have hS1 : s1.params.length + s1.locals.length = 13 := by simp [s1, hStart]
  refine Stmt.seq_run ⟨s1, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, hScratch, s1, hG0, hG1, hRead, x],
    ?_⟩
  refine Stmt.ite_test (b := decide (x < 100)) (by simp [Expr.eval, s1, hStart])
    (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    have hKeep : keepTuple (xs, i, ⟨out⟩) = (i + 1, out.push x) := by
      simp [keepTuple, keep, x, hlt]
    rw [hKeep]
    let s3 := (s1.update 4 (.i64 (i + 1))).update 6 (.i64 x)
    have hS3 : s3.params.length + s3.locals.length = 13 := by simp [s3, hS1]
    refine Stmt.seq_run ⟨s1.update 4 (.i64 (i + 1)), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, s1, hStart, hG1, U64Op.apply], ?_⟩
    refine Stmt.seq_run ⟨s3, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, s3, s1, hStart], ?_⟩
    refine Stmt.seq_spec ((Stmt.pushInPlace_spec (before := s3) (p := po) (vw := x) hMemory32
      hImports hAlloc hRelease (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by rw [hS3]; decide) (by simp [s3, s1, hG2]) (by simp [s3, hS1])
      hLive.at_ (hLive.cap hCap) (hLive.tempsOwned (po, out) (by simp))).mono (fun _ _ h => h)
        fun _ _ h => Live.appendPost (pre := []) (t := (po, out)) (post := []) hLive h) ?_
    apply Triple.of_forall
    rintro s st ⟨heap', q, hL, hF, gq⟩
    have hLen : st.params.length + st.locals.length = 13 := by rw [hF.params, hF.locals, hS3]
    have g4 : st.get 4 = some (.i64 (i + 1)) :=
      (hF.get 4 (by decide) (by decide)).trans (by simp [s3, hS1])
    refine Stmt.run_triple ⟨st.update 5 (.i64 q), by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hLen, gq], ?_⟩
    exact Live.finish_results_one (y := (i + 1, out.push x)) hL ⟨st.update 5 (.i64 q), by
      simp [below100.keep.ir, Func.scratch, Expr.evalResults, Expr.eval, hLen, g4,
        OneArray.scalars, Scalar.values]⟩
  · simp only [decide_eq_false_iff_not] at hge
    have hKeep : keepTuple (xs, i, ⟨out⟩) = (i + 1, out) := by
      simp [keepTuple, keep, x, hge]
    rw [hKeep]
    let s3 := (s1.update 4 (.i64 (i + 1))).update 5 (.i64 po)
    refine Stmt.run_triple ⟨s3, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, s3, s1, hStart, hG1, hG2, U64Op.apply],
      ?_⟩
    exact Live.finish_results_one (y := (i + 1, out)) hLive ⟨s3, by
      simp [below100.keep.ir, Func.scratch, Expr.evalResults, Expr.eval, s3, s1, hStart,
        OneArray.scalars, Scalar.values]⟩

theorem compute_loop (xs : Array UInt64) :
    ∃ (count : UInt64) (cond : UInt64 × Array UInt64 → Bool)
      (step : UInt64 × Array UInt64 → UInt64 × Array UInt64),
      count = (if xs.size.toUInt64 ≤ 8 then xs.size.toUInt64 else 0) ∧
      (∀ s, cond s = decide (s.1 < count)) ∧ (∀ s, step s = keep xs s.1 s.2) ∧
      compute xs = (LeanExe.repeatWhile 8 ((0 : UInt64), (#[] : Array UInt64)) cond step).2 :=
  ⟨_, _, _, rfl, fun _ => rfl, fun _ => rfl, rfl⟩

set_option maxHeartbeats 4000000 in
theorem compute_implements : Implements below100.module 3 compute := by
  refine Func.implements_heap below100.funcs 1 below100.compute.ir "compute" rfl compute
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨px, rfl, hXs⟩ hCap
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hImports : below100.module.imports = [] := rfl
  have hMemory32 : below100.module.memIs64 = false := rfl
  have hAlloc : below100.module.funcs[0]? = some (allocFunction 0) := rfl
  obtain ⟨count, cond, step, hCount, hCondEq, hStepEq, hDef⟩ := compute_loop xs
  set start := below100.compute.ir.state [.i64 px] with hStartDef
  have hStart : start.params.length + start.locals.length = 8 := rfl
  have hG0 : start.get 0 = some (.i64 px) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 2 (.i64 (UInt64.ofNat xs.size))
  let s3 := s2.update 3 (.i64 count)
  let s4 := s3.update 4 (.i64 0)
  have hS4 : s4.params.length + s4.locals.length = 8 := by simp [s4, s3, s2, s1, hStart]
  show Triple _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.get 1))
    (.seq (.assign 3 (.ite (.leU (.get 2) (.const 8)) (.get 2) (.const 0)))
    (.seq (.assign 4 (.const 0)) (.seq (.arrayLiteral 5 [])
      (.repeatWhile [4, 5] 6 7 (.const 8) (.ltU (.get 4) (.get 3)) 2
        [⟨.u64, .get 0⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 5⟩])))))) 8 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hG0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, hCount, Nat.toUInt64]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, s4]
  refine Stmt.seq_spec (Stmt.arrayLiteral_spec (values := []) (words := []) hMemory32 hImports
    hAlloc (by decide) (by rw [hS4]) hHeap hCap (by decide) .nil) ?_
  apply Triple.of_forall
  rintro s5 st5 ⟨p0, hF5, g5, hNew⟩
  have hL5 := Live.push (Live.start hHeap) hNew
  have hLen5 : st5.params.length + st5.locals.length = 8 := by rw [hF5.params, hF5.locals, hS4]
  have g50 : st5.get 0 = some (.i64 px) :=
    (hF5.get 0 (by decide) (by decide)).trans (by simp [s4, s3, s2, s1, hG0])
  have g53 : st5.get 3 = some (.i64 count) :=
    (hF5.get 3 (by decide) (by decide)).trans (by simp [s4, s3, s2, s1, hStart])
  have g54 : st5.get 4 = some (.i64 0) :=
    (hF5.get 4 (by decide) (by decide)).trans (by simp [s4, s3, s2, s1, hStart])
  let F : UInt64 × Array UInt64 → Array UInt64 × UInt64 × Moved (Array UInt64) :=
    fun s => (xs, s.1, ⟨s.2⟩)
  refine (Live.repeatWhileOne keep_implements rfl rfl rfl (by decide) (by decide)
    (by rw [hLen5]) (n := 8) ⟨st5, by simp [Expr.eval]⟩ cond step F (fun s => (hStepEq s).symm)
    (x0 := ((0 : UInt64), (#[] : Array UInt64))) (p0 := p0) hL5
    (by simp [State.Holds, OneArray.scalars, Scalar.values, g54, g5]) hCap (fun _ => rfl) ?_
    ?_).mono
      (fun _ _ h => h) ?_
  · rintro s st ⟨i, out⟩ p hHolds hFrame
    have h4 : st.get 4 = some (.i64 i) := by
      simp [State.Holds, Scalar.values, OneArray.scalars] at hHolds
      exact hHolds.1
    have h3 : st.get 3 = some (.i64 count) := (hFrame.get 3 (by decide) (by decide)).trans g53
    exact ⟨st, by simp [Expr.eval, h4, h3, hCondEq]⟩
  · rintro heap' s st ⟨i, out⟩ p hHolds hL hFrame
    have h0 : st.get 0 = some (.i64 px) := (hFrame.get 0 (by decide) (by decide)).trans g50
    have h45 : st.get 4 = some (.i64 i) ∧ st.get 5 = some (.i64 p) := by
      simpa [State.Holds, Scalar.values, OneArray.scalars] using hHolds
    have hOld : heap'.Owned s p out := hL.tempsOwned _ (List.mem_singleton_self _)
    have hX : heap'.Borrowed s px xs := hL.borrowed px xs hXs Apart.nil
    refine ⟨[.i64 px, .i64 i, .i64 p], st,
      by simp [Expr.evalResults, Expr.eval, h0, h45.1, h45.2],
      ⟨_, _, rfl, ⟨px, rfl, hX⟩, _, _, rfl, rfl, p, rfl, hOld⟩, rfl, fun q hq => ?_⟩
    simp [Represent.reads, Represent.width] at hq
    subst hq
    exact hL.apartB _ (List.mem_singleton_self _) px xs hXs Apart.nil
  · rintro s st ⟨heap4, p4, hL4, hHolds4, -⟩
    rw [hDef]
    generalize LeanExe.repeatWhile 8 ((0 : UInt64), (#[] : Array UInt64)) cond step = R
      at hL4 hHolds4 ⊢
    obtain ⟨i, out⟩ := R
    have h5 : st.get 5 = some (.i64 p4) := by
      simp [State.Holds, Scalar.values, OneArray.scalars] at hHolds4
      exact hHolds4.2
    exact Live.finish_results_one (y := out) hL4 ⟨st, by
      simp [below100.compute.ir, Func.scratch, Expr.evalResults, Expr.eval, h5, OneArray.scalars]⟩

/-- `encode` succeeds on `below100.module`, and its bytes decode to a module that computes the
specification `expected`. -/
theorem below100_bytes : ∃ bytes, Wasm.Encoding.encode below100.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 3 expected := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip below100.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, below100.module, decoded, compute_implements.congr
    fun _ _ _ xs ⟨_, _, hXs⟩ => compute_eq xs hXs.values.size_lt⟩

#print axioms below100_bytes

end Examples.Below100
