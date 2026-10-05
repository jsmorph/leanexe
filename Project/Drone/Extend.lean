import Project.Drone.Steps

/-! `extend` computes its Lean definition: below `count` it builds the table extended by the next
row and releases the old table, and otherwise it returns the table it consumed. -/

namespace Project.Drone

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Drone

def extendTuple : Array UInt64 × UInt64 × UInt64 × Moved (Array Choice) →
    UInt64 × UInt64 × Array Choice :=
  fun (terrain, count, i, table) => extend terrain count i table.val

/-- Entry `j` of the table that `extend` builds. -/
def extendChoice (terrain : Array UInt64) (count i : UInt64) (table : Array Choice) (j : UInt64) :
    Choice :=
  let size := table.size.toUInt64
  let target := j - size
  let c := best (floorAt terrain (i - 1)) (floorAt terrain i) table (size - stateCount) target
    (if (decide (j < size) || (i + 1 == count && target != 0)) = true then 0 else stateCount)
  ⟨if j < size then table[j.toNat]!.time else c.time,
    if j < size then table[j.toNat]!.excess else c.excess,
    if j < size then table[j.toNat]!.parent else c.parent⟩

/-- The compiler computes `x != y` as the negation of the equality test. -/
theorem word_and_neg (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& if q then 0 else 1) = if p ∧ ¬q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The floors as the compiled code computes them. -/
theorem floor_ir0 (terrain : Array UInt64) (i : UInt64) :
    (terrain[(i - 1).toNat]! + if (¬i - 1 = 0 → i = UInt64.ofNat terrain.size) then 0 else 100) =
      floorAt terrain (i - 1) := by
  simp only [floorAt, Nat.toUInt64_eq, UInt64.sub_add_cancel]
  by_cases h1 : i - 1 = 0 <;> by_cases h2 : i = UInt64.ofNat terrain.size <;> simp [h1, h2]

theorem floor_ir1 (terrain : Array UInt64) (i : UInt64) :
    (terrain[i.toNat]! + if (¬i = 0 → i + 1 = UInt64.ofNat terrain.size) then 0 else 100) =
      floorAt terrain i := by
  simp only [floorAt, Nat.toUInt64_eq]
  by_cases h1 : i = 0 <;> by_cases h2 : i + 1 = UInt64.ofNat terrain.size <;> simp [h1, h2]

theorem extend_lt (terrain : Array UInt64) (count i : UInt64) (table : Array Choice)
    (h : i < count) :
    extend terrain count i table = (0, i + 1,
      LeanExe.build (table.size.toUInt64 + stateCount) (extendChoice terrain count i table)) := by
  simp only [extend, h, ite_true]
  rfl

theorem extend_ge (terrain : Array UInt64) (count i : UInt64) (table : Array Choice)
    (h : ¬i < count) : extend terrain count i table = (1, i, table) := by
  simp only [extend, h, ite_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem extend_implements : Implements drone.module 13 extendTuple := by
  refine Func.implements_moves drone.funcs 11 drone.extend.ir "extend" rfl extendTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨terrain, count, i, ⟨table⟩⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pT, rfl, hTerrain⟩, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hTable⟩ - hCap
  change heap.Owned initial p (flatWords table) at hTable
  have hLive := Live.start_moved hHeap (temps := [(p, flatWords table)])
    (by simpa using hTable) (List.pairwise_singleton _ _)
  have hMoves : Represent.moves initial ([.i64 pT] ++ (Scalar.values count ++
      (Scalar.values i ++ [.i64 p])))
      ((terrain, count, i, ⟨table⟩) : Array UInt64 × UInt64 × UInt64 × Moved (Array Choice)) =
      [p] := rfl
  rw [hMoves]
  have hW := hTable.borrowed.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hSize : (flatWords table).size < 536870912 := by have := hW.1; omega
  have hCount := flatWords_count choice_length (by decide) (by decide) table hW.size_lt
  have hWords := flatWords_size choice_length table
  set start := drone.extend.ir.state
    ([.i64 pT] ++ (Scalar.values count ++ (Scalar.values i ++ [.i64 p]))) with hStartDef
  have hStart : start.params.length + start.locals.length = 50 := rfl
  have hG0 : start.get 0 = some (.i64 pT) := rfl
  have hG1 : start.get 1 = some (.i64 count) := rfl
  have hG2 : start.get 2 = some (.i64 i) := rfl
  have hG3 : start.get 3 = some (.i64 p) := rfl
  let s1 := start.update 4 (.i64 (UInt64.ofNat (flatWords table).size))
  let s2 := ((s1.update 48 (.i64 (UInt64.ofNat (flatWords table).size))).update 49 (.i64 3)).update 5
    (.i64 table.size.toUInt64)
  have hS2 : s2.params.length + s2.locals.length = 50 := by simp [s2, s1, hStart]
  have hS2g : s2.get 0 = some (.i64 pT) ∧ s2.get 1 = some (.i64 count) ∧
      s2.get 2 = some (.i64 i) ∧ s2.get 3 = some (.i64 p) ∧
      s2.get 5 = some (.i64 table.size.toUInt64) := by
    simp [s2, s1, hG0, hG1, hG2, hG3, hStart]
  refine Stmt.seq_run ⟨s1, by
    simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hG3], ?_⟩
  refine Stmt.seq_run ⟨s2, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, U64Op.apply, Func.scratch,
      Func.width, drone.extend.ir, ← hCount], ?_⟩
  refine Stmt.ite_test (b := decide (i < count))
    (by simp [Expr.eval, hS2g.2.1, hS2g.2.2.1]) (fun hlt => ?_) (fun hge => ?_)
  · -- The extending path.
    simp only [decide_eq_true_eq] at hlt
    rw [show extendTuple (terrain, count, i, ⟨table⟩) = _ from extend_lt terrain count i table hlt]
    let s3 := s2.update 6 (.i64 0)
    let s4 := s3.update 7 (.i64 (i + 1))
    refine Stmt.seq_run ⟨s3, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hS2, s3], ?_⟩
    refine Stmt.seq_run ⟨s4, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hS2, s3, s4, hS2g.2.2.1, U64Op.apply], ?_⟩
    have hS4 : s4.params.length + s4.locals.length = 50 := by simp [s4, s3, hS2]
    have hS4g : s4.get 0 = some (.i64 pT) ∧ s4.get 1 = some (.i64 count) ∧
        s4.get 2 = some (.i64 i) ∧ s4.get 3 = some (.i64 p) ∧
        s4.get 5 = some (.i64 table.size.toUInt64) ∧ s4.get 6 = some (.i64 0) ∧
        s4.get 7 = some (.i64 (i + 1)) := by
      simp [s4, s3, hS2g, hS2]
    have hP := predecessor_implements (a := true)
    have hC := choose_implements (a := true)
    have hTableSmall : table.size < 178956971 := by omega
    refine Stmt.seq_spec (Stmt.buildRecords_spec (writes := (List.range 37).map (· + 11))
      (n := table.size.toUInt64 + stateCount) (scratch := 48)
      (elements := [.get 41, .get 44, .get 47]) (before := s4)
      (extendChoice terrain count i table) choice_length (by decide) rfl rfl rfl (by decide)
      (by decide) (by decide) (by rw [hS4]; omega) hHeap hCap
      ⟨s4, by simp [Expr.eval, hS4g.2.2.2.2.1, U64Op.apply]⟩ ?_) (TripleA.of_forall ?_)
    · intro j store state hj hAt hFrame hIndex
      have hLength : state.params.length + state.locals.length = 50 := by
        rw [hFrame.params, hFrame.locals]; exact hS4
      have hT0 : state.get 0 = some (.i64 pT) :=
        (hFrame.get 0 (by decide) (by decide)).trans hS4g.1
      have hT1 : state.get 1 = some (.i64 count) :=
        (hFrame.get 1 (by decide) (by decide)).trans hS4g.2.1
      have hT2 : state.get 2 = some (.i64 i) :=
        (hFrame.get 2 (by decide) (by decide)).trans hS4g.2.2.1
      have hT3 : state.get 3 = some (.i64 p) :=
        (hFrame.get 3 (by decide) (by decide)).trans hS4g.2.2.2.1
      have hT5 : state.get 5 = some (.i64 table.size.toUInt64) :=
        (hFrame.get 5 (by decide) (by decide)).trans hS4g.2.2.2.2.1
      have hXT := hAt pT terrain hTerrain
      have hLenT := hXT.lengthBound
      simp only [UInt64.toNat_toUInt32] at hLenT
      have hX := hAt p _ hTable.borrowed
      have hRdT : ∀ (k : UInt64) (st : State), st.get 0 = some (.i64 pT) →
          Expr.readValue store.mem 0 k st = some (terrain[k.toNat]!, st) :=
        fun _ _ h => Expr.readValue_at hXT h
      have hRd : ∀ (j : Nat), j < 3 → ∀ (k : UInt64), k < 536870912 → ∀ st : State,
          st.get 3 = some (.i64 p) →
          Expr.readValue store.mem 3 (k * UInt64.ofNat 3 + UInt64.ofNat j) st =
            some (((Scalar.values table[k.toNat]!).map Value.word)[j]!, st) :=
        fun j hj k hk st h =>
          Expr.readValue_record choice_length hj (by decide) choice_default hX hk h
      have hR0 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 p) →
          Expr.readValue store.mem 3 (k * 3) st = some (table[k.toNat]!.time, st) :=
        fun k hk st h => by
          simpa [Scalar.values, Flat.flat, Value.word] using hRd 0 (by decide) k hk st h
      have hR1 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 p) →
          Expr.readValue store.mem 3 (k * 3 + 1) st = some (table[k.toNat]!.excess, st) :=
        fun k hk st h => by
          simpa [Scalar.values, Flat.flat, Value.word] using hRd 1 (by decide) k hk st h
      have hR2 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 p) →
          Expr.readValue store.mem 3 (k * 3 + 2) st = some (table[k.toNat]!.parent, st) :=
        fun k hk st h => by
          simpa [Scalar.values, Flat.flat, Value.word] using hRd 2 (by decide) k hk st h
      have hZ : ∀ (k : UInt64), ¬k < 536870912 → table[k.toNat]! = ⟨0, 0, 0⟩ := fun k hk => by
        have h0 := flatWords_read choice_length (j := 0) (by decide) (by decide) choice_default
          hSize k
        have h1 := flatWords_read choice_length (j := 1) (by decide) (by decide) choice_default
          hSize k
        have h2 := flatWords_read choice_length (j := 2) (by decide) (by decide) choice_default
          hSize k
        simp only [hk, ite_false] at h0 h1 h2
        cases hc : table[k.toNat]!
        simp_all [Scalar.values, Flat.flat, Value.word]
      have hJ : UInt64.ofNat j < 536870912 := by
        have hU : UInt64.size = 18446744073709551616 := rfl
        have hS : stateCount.toNat = 45 := rfl
        have hsz : table.size.toUInt64.toNat = table.size := by
          rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by omega)]
        have hn : (table.size.toUInt64 + stateCount).toNat = table.size + 45 := by
          rw [UInt64.toNat_add, hsz, hS]; exact Nat.mod_eq_of_lt (by omega)
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]
        simp only [UInt64.reduceToNat]
        omega
      set J := UInt64.ofNat j with hJdef
      iterate 10 (refine Stmt.seq_run ?_; eval_state [hLength, hIndex, hT0, hT2, hT5, hLenT,
        hXT.lengthRead, hRdT])
      simp only [floor_ir0, floor_ir1]
      let r0 := floorAt terrain (i - 1)
      let r1 := floorAt terrain i
      let target := J - UInt64.ofNat table.size
      let sources : UInt64 := if (decide (J < UInt64.ofNat table.size) ||
        (i + 1 == count && target != 0)) = true then 0 else 45
      refine Stmt.seq_spec (Stmt.loop_spec (vars := [18, 19, 20])
        (writes := [18, 19, 20, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35])
        (init := ((infinity : UInt64), (infinity : UInt64), (0 : UInt64)))
        (n := sources) (bestStep r0 r1 table (UInt64.ofNat table.size - 45) target)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [hLength])
        ⟨_, by
          simp [Expr.eval, U64Op.apply, hIndex, hT1, hT2, hT5, sources, target, hLength,
            word_and_neg, word_or, word_eq_one]
          refine ⟨?_, rfl⟩
          by_cases h1 : J < UInt64.ofNat table.size
          · simp [h1, UInt64.not_le.mpr h1]
          · simp [h1, UInt64.not_lt.mp h1]⟩
        (by simp [State.Holds, Scalar.values, hLength]) ?_)
        (TripleA.of_forall fun s0 st0 h0 => ?_)
      · rintro k ⟨a1, a2, a3⟩ st hk hFr hHolds hIdx hLim
        have hLen : st.params.length + st.locals.length = 50 := by
          rw [hFr.params, hFr.locals]; simp [hLength]
        have hU3 : st.get 3 = some (.i64 p) :=
          (hFr.get 3 (by decide) (by decide)).trans (by simp [hT3])
        have hU5 : st.get 5 = some (.i64 table.size.toUInt64) :=
          (hFr.get 5 (by decide) (by decide)).trans (by simp [hT5])
        have hU11 : st.get 11 = some (.i64 target) :=
          (hFr.get 11 (by decide) (by decide)).trans (by simp [hLength, target])
        have hU14 : st.get 14 = some (.i64 r0) :=
          (hFr.get 14 (by decide) (by decide)).trans (by simp [hLength, r0])
        have hU17 : st.get 17 = some (.i64 r1) :=
          (hFr.get 17 (by decide) (by decide)).trans (by simp [hLength, r1])
        have hA : st.get 18 = some (.i64 a1) ∧ st.get 19 = some (.i64 a2) ∧
            st.get 20 = some (.i64 a3) := by
          simpa [State.Holds, Scalar.values] using hHolds
        by_cases hG : UInt64.ofNat table.size - 45 + UInt64.ofNat k < 536870912
        · iterate 4 (refine Stmt.seq_run ?_; eval_state [hLen, hU3, hU5, hIdx, hG, hR0, hR1, hR2])
          refine Stmt.seq_callPure hP rfl rfl rfl
            (x := (r0, r1, table[(UInt64.ofNat table.size - 45 + UInt64.ofNat k).toNat]!, target,
              UInt64.ofNat k)) ?_
          eval_state [hLen, hU11, hU14, hU17, hIdx, predecessorTuple]
          refine Stmt.seq_callPure hC rfl rfl rfl
            (x := (⟨a1, a2, a3⟩, predecessor r0 r1
              table[(UInt64.ofNat table.size - 45 + UInt64.ofNat k).toNat]! target
              (UInt64.ofNat k))) ?_
          eval_state [hLen, hA.1, hA.2.1, hA.2.2, chooseTuple]
          refine Stmt.run_triple ?_
          eval_state [hLen]
          refine ⟨?_, ?_⟩
          · repeat refine State.Frame.update ?_ (by decide)
            exact State.Frame.refl _ _ _
          · simp [State.Holds, hLen, bestStep]
        · have hZk : table[((UInt64.ofNat table.size - 45).toNat + k) % 18446744073709551616]! =
              ⟨0, 0, 0⟩ := by
            simpa using hZ _ hG
          iterate 4 (refine Stmt.seq_run ?_; eval_state [hLen, hU3, hU5, hIdx, hG])
          refine Stmt.seq_callPure hP rfl rfl rfl
            (x := (r0, r1, table[(UInt64.ofNat table.size - 45 + UInt64.ofNat k).toNat]!, target,
              UInt64.ofNat k)) ?_
          eval_state [hLen, hU11, hU14, hU17, hIdx, predecessorTuple, hZk]
          refine Stmt.seq_callPure hC rfl rfl rfl
            (x := (⟨a1, a2, a3⟩, predecessor r0 r1
              table[(UInt64.ofNat table.size - 45 + UInt64.ofNat k).toNat]! target
              (UInt64.ofNat k))) ?_
          eval_state [hLen, hA.1, hA.2.1, hA.2.2, chooseTuple, hZk]
          refine Stmt.run_triple ?_
          eval_state [hLen]
          refine ⟨?_, ?_⟩
          · repeat refine State.Frame.update ?_ (by decide)
            exact State.Frame.refl _ _ _
          · simp [State.Holds, hLen, bestStep, hZk]
      · obtain ⟨rfl, hFr, hHolds⟩ := h0
        have hLen : st0.params.length + st0.locals.length = 50 := by
          rw [hFr.params, hFr.locals]; simp [hLength]
        have hc := best_loop r0 r1 table (UInt64.ofNat table.size - 45) target sources
        have hB : st0.get 18 = some (.i64 (best r0 r1 table (UInt64.ofNat table.size - 45) target
              sources).time) ∧
            st0.get 19 = some (.i64 (best r0 r1 table (UInt64.ofNat table.size - 45) target
              sources).excess) ∧
            st0.get 20 = some (.i64 (best r0 r1 table (UInt64.ofNat table.size - 45) target
              sources).parent) := by
          rw [hc]
          simpa [State.Holds, Scalar.values] using hHolds
        have hV3 : st0.get 3 = some (.i64 p) :=
          (hFr.get 3 (by decide) (by decide)).trans (by simp [hT3])
        have hV5 : st0.get 5 = some (.i64 table.size.toUInt64) :=
          (hFr.get 5 (by decide) (by decide)).trans (by simp [hT5])
        have hV10 : st0.get 10 = some (.i64 J) :=
          (hFr.get 10 (by decide) (by decide)).trans (by simp [hIndex])
        refine Stmt.run_triple ?_
        eval_state [hLen, hB.1, hB.2.1, hB.2.2, hV3, hV5, hV10, hJ, hR0, hR1, hR2]
        refine ⟨?_, fun jj hjj => ?_⟩
        · refine State.Frame.trans ?_ ((hFr.weaken (by decide)).trans ?_)
          · repeat refine State.Frame.update ?_ (by decide)
            exact State.Frame.refl _ _ _
          · repeat refine State.Frame.update ?_ (by decide)
            exact State.Frame.refl _ _ _
        · obtain rfl | rfl | rfl : jj = 0 ∨ jj = 1 ∨ jj = 2 := by omega
          all_goals
            simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some, Value.word]
            exact Expr.yields_get (by simp [hLen, Scalar.values, Flat.flat, extendChoice, r0, r1,
              target, sources, stateCount])
    · rintro s st ⟨ptr, hFr, hPtr, hNew⟩
      have hLive2 := Live.step (consumed := []) (news := [(ptr, flatWords (LeanExe.build
        (table.size.toUInt64 + stateCount) (extendChoice terrain count i table)))]) hLive
        hNew.at_ hNew.caps (by simpa using hNew.keeps)
        (fun t ht => by rw [List.mem_singleton.mp ht]; exact hNew.owned)
        (List.pairwise_singleton _ _)
      have hSt : st.get 3 = some (.i64 p) ∧ st.get 6 = some (.i64 0) ∧
          st.get 7 = some (.i64 (i + 1)) := by
        refine ⟨(hFr.get 3 (by decide) (by decide)).trans hS4g.2.2.2.1,
          (hFr.get 6 (by decide) (by decide)).trans hS4g.2.2.2.2.2.1,
          (hFr.get 7 (by decide) (by decide)).trans hS4g.2.2.2.2.2.2⟩
      have hLenF : st.params.length + st.locals.length = 50 := by
        rw [hFr.params, hFr.locals]; exact hS4
      refine Live.releaseSecond_last hLive2 rfl rfl hSt.1 fun s' hL => ?_
      refine Live.finish_results_one (y := ((0 : UInt64), i + 1, LeanExe.build
        (table.size.toUInt64 + stateCount) (extendChoice terrain count i table))) hL ⟨st, ?_⟩
      simp [drone.extend.ir, Expr.evalResults, Expr.eval, Func.scratch, OneArray.scalars,
        Scalar.values, hSt.2.1, hSt.2.2, hPtr]
  · -- The last call: the consumed table is the result.
    simp only [decide_eq_false_iff_not] at hge
    rw [show extendTuple (terrain, count, i, ⟨table⟩) = _ from extend_ge terrain count i table hge]
    let sF := ((s2.update 6 (.i64 1)).update 7 (.i64 i)).update 8 (.i64 p)
    refine Stmt.run_triple ⟨sF, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hS2, hS2g.2.2.1, hS2g.2.2.2.1, sF], ?_⟩
    refine Live.finish_results_one (y := ((1 : UInt64), i, table)) hLive ⟨sF, ?_⟩
    simp [drone.extend.ir, Expr.evalResults, Expr.eval, hS2, Func.scratch, OneArray.scalars,
      Scalar.values, sF]

def forwardTuple : Array UInt64 × UInt64 → UInt64 × UInt64 × Array Choice :=
  fun (terrain, count) => forward terrain count

theorem forward_loop (terrain : Array UInt64) (count : UInt64) :
    ∃ (cond : UInt64 × UInt64 × Array Choice → Bool)
      (step : UInt64 × UInt64 × Array Choice → UInt64 × UInt64 × Array Choice),
      (∀ x, cond x = (x.1 == 0)) ∧ (∀ x, step x = extend terrain count x.2.1 x.2.2) ∧
      forward terrain count =
        LeanExe.repeatWhile 64 ((0 : UInt64), (1 : UInt64), initial) cond step :=
  ⟨_, _, fun _ => rfl, fun _ => rfl, rfl⟩

set_option maxHeartbeats 4000000 in
theorem forward_implements : Implements drone.module 14 forwardTuple := by
  refine Func.implements_heap drone.funcs 12 drone.forward.ir "forward" rfl forwardTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨terrain, count⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨pT, rfl, hTerrain⟩, rfl⟩ hCap
  set start := drone.forward.ir.state ([.i64 pT] ++ Scalar.values count) with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hG0 : start.get 0 = some (.i64 pT) := rfl
  have hG1 : start.get 1 = some (.i64 count) := rfl
  let s2 := (start.update 2 (.i64 0)).update 3 (.i64 1)
  refine Stmt.seq_run ⟨start.update 2 (.i64 0), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
  refine Live.callOne_seq initial_implements rfl rfl rfl (consumed := []) (Live.start hHeap)
    hCap (x := ()) (vals := []) (before := s2) (afterArgs := s2)
    (by simp [Expr.evalResults]) rfl rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨s2.update 4 (.i64 q), by
      simp [State.setAll, State.set?_eq_update, s2, hStart, OneArray.scalars]⟩) ?_
  intro heap1 p1 s3 st3 hLive1 hst3
  have hst : st3 = s2.update 4 (.i64 p1) := by
    simp [State.setAll, State.set?_eq_update, s2, hStart, OneArray.scalars] at hst3
    exact hst3.symm
  subst hst
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := forward_loop terrain count
  let F : UInt64 × UInt64 × Array Choice →
      Array UInt64 × UInt64 × UInt64 × Moved (Array Choice) :=
    fun x => (terrain, count, x.2.1, ⟨x.2.2⟩)
  have hS3 : (s2.update 4 (.i64 p1)).params.length + (s2.update 4 (.i64 p1)).locals.length = 7 :=
    by simp [s2, hStart]
  refine (Live.repeatWhileOne extend_implements rfl rfl rfl (by decide) (by decide)
    (by rw [hS3]; decide)
    (n := 64) ⟨s2.update 4 (.i64 p1), by simp [Expr.eval]⟩ cond step F
    (fun x => (hStepEq x).symm)
    (x0 := ((0 : UInt64), (1 : UInt64), LeanExe.Examples.Drone.initial)) (p0 := p1)
    hLive1 (by simp [State.Holds, s2, hStart, OneArray.scalars, Scalar.values]) hCap
    (fun _ => rfl) ?_ ?_).mono (fun _ _ h => h) ?_
  · rintro s st ⟨a, b, c⟩ p hHolds -
    have hH : st.get 2 = some (.i64 a) := by
      simp [State.Holds, Scalar.values, OneArray.scalars] at hHolds
      exact hHolds.1
    exact ⟨st, by simp [Expr.eval, hH, hCondEq]⟩
  · rintro heap' s st ⟨a, b, c⟩ p hHolds hL hFrame
    have hT0 : st.get 0 = some (.i64 pT) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, hG0])
    have hT1 : st.get 1 = some (.i64 count) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s2, hG1])
    have hH : st.get 3 = some (.i64 b) ∧ st.get 4 = some (.i64 p) := by
      simp [State.Holds, Scalar.values, OneArray.scalars] at hHolds
      exact ⟨hHolds.2.1, hHolds.2.2⟩
    have hOld : heap'.Owned s p (flatWords c) := hL.tempsOwned _ (List.mem_singleton_self _)
    have hT : heap'.Borrowed s pT terrain := hL.borrowed pT terrain hTerrain Apart.nil
    refine ⟨[.i64 pT, .i64 count, .i64 b, .i64 p], st, ?_,
      ⟨_, _, rfl, ⟨pT, rfl, hT⟩, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOld⟩, rfl,
      fun q hq => ?_⟩
    · simp [Expr.evalResults, Expr.eval, hT0, hT1, hH.1, hH.2]
    · simp [Represent.reads, Represent.width] at hq
      subst hq
      exact hL.apartB _ (List.mem_singleton_self _) pT terrain hTerrain Apart.nil
  · rintro s st ⟨heap4, p4, hL4, hHolds4, hFrame4⟩
    rw [show forwardTuple (terrain, count) = _ from hDef]
    generalize LeanExe.repeatWhile 64 ((0 : UInt64), (1 : UInt64), LeanExe.Examples.Drone.initial)
      cond step = R
      at hL4 hHolds4 ⊢
    obtain ⟨a, b, c⟩ := R
    have hH : st.get 2 = some (.i64 a) ∧ st.get 3 = some (.i64 b) ∧ st.get 4 = some (.i64 p4) :=
      by simpa [State.Holds, Scalar.values, OneArray.scalars] using hHolds4
    exact Live.finish_results_one (y := (a, b, c)) hL4 ⟨st, by
      simp [drone.forward.ir, Expr.evalResults, Expr.eval, hH.1, hH.2.1, hH.2.2,
        OneArray.scalars, Scalar.values]⟩

end Project.Drone
