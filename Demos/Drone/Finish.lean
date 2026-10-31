import Demos.Drone.Steps
import Demos.Drone.Extend
import Demos.Drone.Correct

/-! `extend`, `forward`, `output`, and `compute` compute their Lean definitions.  Below `count`,
`extend` builds the table extended by the next row and releases the old table, and otherwise it
returns the table that it consumed. -/

namespace Demos.Drone

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime LeanExe.ProofKit Demos.Drone

def extendTuple : Array UInt64 × UInt64 × UInt64 × Moved (Array Choice) →
    UInt64 × UInt64 × Array Choice :=
  fun (terrain, count, i, table) => extend terrain count i table.val

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

/-- The spares an `extend` call uses: one when it builds a table. -/
def extendCost (count i : UInt64) : Nat := if i < count then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Under `a = false`, a call that builds a table has a table of at most 63 rows and room for
one more block of `tableBytes` bytes; the call uses `extendCost` spares of any budget. -/
theorem extend_implementsA {a : Bool} (pages : Nat) :
    ImplementsA a drone.module 13 extendTuple
      (fun x heap store => a = false → x.2.2.1 < x.2.1 →
        x.2.2.2.val.size ≤ 2835 ∧
        ∃ k, heap.Bounded store drone.module tableBytes (k + 1) pages)
      (fun x heap store heap' final => a = false → ∀ k,
        heap.Bounded store drone.module tableBytes (k + extendCost x.2.1 x.2.2.1) pages →
        heap'.Bounded final drone.module tableBytes k pages) := by
  refine Func.implements_movesA drone.funcs 11 drone.extend.ir "extend" rfl extendTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, rfl, _, _, rfl, rfl, _, rfl, -⟩; rfl) ?_
  rintro ⟨terrain, count, i, ⟨table⟩⟩ heap initial _ hHeap hPre
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
    have hP := predecessor_implements (a := a)
    have hC := choose_implements (a := a)
    have hTableSmall : table.size < 178956971 := by omega
    have hU : UInt64.size = 18446744073709551616 := rfl
    have hn : (table.size.toUInt64 + stateCount).toNat = table.size + 45 := by
      have hsz : table.size.toUInt64.toNat = table.size := by
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by omega)]
      have hS : stateCount.toNat = 45 := rfl
      rw [UInt64.toNat_add, hsz, hS]; exact Nat.mod_eq_of_lt (by omega)
    have hNeed : a = false → UInt64.ofNat (8 * ((table.size.toUInt64 + stateCount).toNat * 3 + 1))
        ≤ tableBytes := fun ha => by
      have := (hPre ha hlt).1
      change table.size ≤ 2835 at this
      rw [UInt64.le_iff_toNat_le, hn, UInt64.toNat_ofNat_of_lt' (by omega)]
      unfold tableBytes; simp; omega
    refine Stmt.seq_spec (Stmt.buildRecords_specA (writes := (List.range 37).map (· + 11))
      (n := table.size.toUInt64 + stateCount) (scratch := 48)
      (elements := [.get 41, .get 44, .get 47]) (before := s4)
      (extendChoice terrain count i table) choice_length (by decide) rfl rfl rfl (by decide)
      (by decide) (by decide) (by rw [hS4]; omega) hHeap hCap
      (fun ha => by
        have := (hPre ha hlt).1
        change table.size ≤ 2835 at this
        simp only [List.length_cons, List.length_nil]; omega)
      (fun ha => by
        obtain ⟨k, hk⟩ := (hPre ha hlt).2
        exact hk.room hHeap (by omega) (hNeed ha) tableBytes_eight hCap)
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
            word_and_not, word_or, word_eq_one]
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
    · rintro s st ⟨ptr, hFr, hPtr, hNew, hPages⟩
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
      refine Live.releaseSecond_last_pages hLive2 rfl rfl hSt.1 fun s' hL hPages' => ?_
      refine Live.finish_results_oneP (P := fun h s => a = false → ∀ k,
          heap.Bounded initial drone.module tableBytes (k + extendCost count i) pages →
          h.Bounded s drone.module tableBytes k pages) (y := ((0 : UInt64), i + 1, LeanExe.build
        (table.size.toUInt64 + stateCount) (extendChoice terrain count i table))) hL ⟨st, ?_⟩
        fun ha k hk => ?_
      · simp [drone.extend.ir, Expr.evalResults, Expr.eval, Func.scratch, OneArray.scalars,
          Scalar.values, hSt.2.1, hSt.2.2, hPtr]
      · have hk' : heap.Bounded initial drone.module tableBytes (k + 1) pages := by
          simpa [extendCost, hlt] using hk
        exact (hk'.allocate hHeap (hNeed ha) tableBytes_eight hCap hPages hNew.caps).release
          hLive2.at_ (hLive2.tempsOwned (p, flatWords table) (by simp)) hPages'
          (hL.caps.trans hLive2.caps.symm)
  · -- The last call: the consumed table is the result.
    simp only [decide_eq_false_iff_not] at hge
    rw [show extendTuple (terrain, count, i, ⟨table⟩) = _ from extend_ge terrain count i table hge]
    let sF := ((s2.update 6 (.i64 1)).update 7 (.i64 i)).update 8 (.i64 p)
    refine Stmt.run_triple ⟨sF, by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hS2, hS2g.2.2.1, hS2g.2.2.2.1, sF], ?_⟩
    refine Live.finish_results_oneP (P := fun h s => a = false → ∀ k,
        heap.Bounded initial drone.module tableBytes (k + extendCost count i) pages →
        h.Bounded s drone.module tableBytes k pages) (y := ((1 : UInt64), i, table)) hLive
      ⟨sF, ?_⟩ fun _ k hk => by simpa [extendCost, hge] using hk
    simp [drone.extend.ir, Expr.evalResults, Expr.eval, hS2, Func.scratch, OneArray.scalars,
      Scalar.values, sF]

theorem extend_implements : Implements drone.module 13 extendTuple :=
  (extend_implementsA (a := true) 0).implements_of fun _ _ _ h => nomatch h

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
/-- Under `a = false`, `count` is at most 64, and the heap has room for `count + 1` more blocks of
`tableBytes` bytes; the call uses all but `spare` of them. -/
theorem forward_implementsA {a : Bool} (spare pages : Nat) :
    ImplementsA a drone.module 14 forwardTuple
      (fun x heap store => a = false → x.2.toNat ≤ 64 ∧
        heap.Bounded store drone.module tableBytes (spare + x.2.toNat + 1) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final drone.module tableBytes spare pages) := by
  refine Func.implements_heapA drone.funcs 12 drone.forward.ir "forward" rfl forwardTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨terrain, count⟩ heap initial _ hHeap hPre ⟨_, _, rfl, ⟨pT, rfl, hTerrain⟩, rfl⟩ hCap
  set start := drone.forward.ir.state ([.i64 pT] ++ Scalar.values count) with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hG0 : start.get 0 = some (.i64 pT) := rfl
  have hG1 : start.get 1 = some (.i64 count) := rfl
  let s2 := (start.update 2 (.i64 0)).update 3 (.i64 1)
  refine Stmt.seq_run ⟨start.update 2 (.i64 0), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart], ?_⟩
  refine Stmt.seq_run ⟨s2, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s2], ?_⟩
  refine Live.callOne_seqA (initial_implementsA (spare + count.toNat) pages) rfl rfl rfl
    (consumed := []) (Live.start hHeap)
    hCap (x := ()) (vals := []) (before := s2) (afterArgs := s2)
    (by simp [Expr.evalResults]) rfl (fun ha => (hPre ha).2) rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨s2.update 4 (.i64 q), by
      simp [State.setAll, State.set?_eq_update, s2, hStart, OneArray.scalars]⟩) ?_
  intro heap1 p1 s3 st3 hLive1 hst3 hPost1
  have hst : st3 = s2.update 4 (.i64 p1) := by
    simp [State.setAll, State.set?_eq_update, s2, hStart, OneArray.scalars] at hst3
    exact hst3.symm
  subst hst
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := forward_loop terrain count
  let F : UInt64 × UInt64 × Array Choice →
      Array UInt64 × UInt64 × UInt64 × Moved (Array Choice) :=
    fun x => (terrain, count, x.2.1, ⟨x.2.2⟩)
  let Hold : UInt64 × UInt64 × Array Choice → Heap → Store Unit → Prop := fun x h s =>
    a = false → x.2.2.size = 45 * x.2.1.toNat ∧ 1 ≤ x.2.1.toNat ∧
      x.2.1.toNat ≤ max count.toNat 1 ∧
      h.Bounded s drone.module tableBytes (spare + (count.toNat - x.2.1.toNat)) pages
  have hS3 : (s2.update 4 (.i64 p1)).params.length + (s2.update 4 (.i64 p1)).locals.length = 7 :=
    by simp [s2, hStart]
  refine (Live.repeatWhileOneA (extend_implementsA pages) rfl rfl rfl (by decide) (by decide)
    (by rw [hS3]; decide)
    (n := 64) ⟨s2.update 4 (.i64 p1), by simp [Expr.eval]⟩ cond step F
    (fun x => (hStepEq x).symm) Hold ?_
    (x0 := ((0 : UInt64), (1 : UInt64), Demos.Drone.initial)) (p0 := p1)
    hLive1 (by simp [State.Holds, s2, hStart, OneArray.scalars, Scalar.values]) ?_ hCap
    (fun _ => rfl) ?_ ?_).mono (fun _ _ h => h) ?_
  · rintro ⟨st, i, table⟩ h h' s s' hH hc hP ha
    obtain ⟨hsize, h1, hmax, hB⟩ := hH ha
    simp only at hsize h1 hmax hB
    have hc64 : count.toNat ≤ 64 := (hPre ha).1
    have hU : UInt64.size = 18446744073709551616 := rfl
    rw [hStepEq]
    by_cases hlt : i < count
    · have hltN := UInt64.lt_iff_toNat_lt.mp hlt
      have hiN : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
      have hcount : count.toNat - i.toNat = (count.toNat - (i.toNat + 1)) + 1 := by omega
      have hsz := extend_size terrain count i table hlt (by omega)
      have hB' := hP ha (spare + (count.toNat - (i.toNat + 1))) (by
        simpa [extendCost, hlt, hcount, Nat.add_assoc, F] using hB)
      rw [extend_lt terrain count i table hlt] at hsz ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only; rw [hsz, hsize, hiN]; ring
      · simp only; rw [hiN]; omega
      · simp only; rw [hiN]; omega
      · simp only; rw [hiN]; exact hB'
    · have hB' := hP ha (spare + (count.toNat - i.toNat)) (by simpa [extendCost, hlt, F] using hB)
      rw [extend_ge terrain count i table hlt]
      exact ⟨hsize, h1, hmax, hB'⟩
  · intro ha
    refine ⟨by rw [initial_build, build_size]; rfl, by decide, by simp, ?_⟩
    exact (hPost1 ha).mono (by omega)
  · rintro s st ⟨a', b, c⟩ p hHolds -
    have hH : st.get 2 = some (.i64 a') := by
      simp [State.Holds, Scalar.values, OneArray.scalars] at hHolds
      exact hHolds.1
    exact ⟨st, by simp [Expr.eval, hH, hCondEq]⟩
  · rintro heap' s st ⟨a', b, c⟩ p hHolds hL hHoldX hFrame
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
      ⟨_, _, rfl, ⟨pT, rfl, hT⟩, _, _, rfl, rfl, _, _, rfl, rfl, p, rfl, hOld⟩,
      fun ha hlt => ?_, rfl, fun q hq => ?_⟩
    · simp [Expr.evalResults, Expr.eval, hT0, hT1, hH.1, hH.2]
    · obtain ⟨hsize, h1, hmax, hB⟩ := hHoldX ha
      simp only at hsize h1 hmax hB
      have hltN : b.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hc64 : count.toNat ≤ 64 := (hPre ha).1
      refine ⟨by show c.size ≤ 2835; omega, spare + (count.toNat - b.toNat) - 1, ?_⟩
      rw [show spare + (count.toNat - b.toNat) - 1 + 1 = spare + (count.toNat - b.toNat) by
        omega]
      exact hB
    · simp [Represent.reads, Represent.width] at hq
      subst hq
      exact hL.apartB _ (List.mem_singleton_self _) pT terrain hTerrain Apart.nil
  · rintro s st ⟨heap4, p4, hL4, hHolds4, hFrame4, hHold4⟩
    rw [show forwardTuple (terrain, count) = _ from hDef]
    generalize LeanExe.repeatWhile 64 ((0 : UInt64), (1 : UInt64), Demos.Drone.initial)
      cond step = R
      at hL4 hHolds4 hHold4 ⊢
    obtain ⟨a', b, c⟩ := R
    have hH : st.get 2 = some (.i64 a') ∧ st.get 3 = some (.i64 b) ∧
        st.get 4 = some (.i64 p4) := by
      simpa [State.Holds, Scalar.values, OneArray.scalars] using hHolds4
    exact Live.finish_results_oneP (P := fun h s => a = false →
      h.Bounded s drone.module tableBytes spare pages) (y := (a', b, c)) hL4 ⟨st, by
      simp [drone.forward.ir, Expr.evalResults, Expr.eval, hH.1, hH.2.1, hH.2.2,
        OneArray.scalars, Scalar.values]⟩ fun ha => ((hHold4 ha).2.2.2).mono (by omega)

theorem forward_implements : Implements drone.module 14 forwardTuple :=
  (forward_implementsA (a := true) 0 0).implements_of fun _ _ _ h => nomatch h

def outputTuple : Array UInt64 × Array Choice × UInt64 → Array UInt64 :=
  fun (terrain, table, count) => output terrain table count

/-- One step of the loop that follows the parents back. -/
def backStep (table : Array Choice) (count j s : UInt64) : UInt64 :=
  table[((count - 1 - j) * stateCount + s).toNat]!.parent

/-- Word `e` of the output. -/
def outputWord (terrain : Array UInt64) (table : Array Choice) (count e : UInt64) : UInt64 :=
  let state := LeanExe.loop (count - 1 - e / 2) (0 : UInt64) (backStep table count)
  if e % 2 == 0 then altitude (floorAt terrain (e / 2)) state else speed state

theorem output_build (terrain : Array UInt64) (table : Array Choice) (count : UInt64) :
    output terrain table count = LeanExe.build (2 * count) (outputWord terrain table count) :=
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Under `a = false`, `count` is at most 64, and the heap has room for one more block of
`tableBytes` bytes. -/
theorem output_implementsA {a : Bool} (spare pages : Nat) :
    ImplementsA a drone.module 15 outputTuple
      (fun x heap store => a = false → x.2.2.toNat ≤ 64 ∧
        heap.Bounded store drone.module tableBytes (spare + 1) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final drone.module tableBytes spare pages) := by
  refine Func.implements_heapA drone.funcs 13 drone.output.ir "output" rfl outputTuple _ _
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨terrain, table, count⟩ heap initial _ hHeap hPre
    ⟨_, _, rfl, ⟨pT, rfl, hTerrain⟩, _, _, rfl, ⟨pB, rfl, hTable⟩, rfl⟩ hCap
  change heap.Borrowed initial pB (flatWords table) at hTable
  have hSize : (flatWords table).size < 536870912 := by have := hTable.values.1; omega
  set start := drone.output.ir.state ([.i64 pT] ++ ([.i64 pB] ++ Scalar.values count))
    with hStartDef
  have hStart : start.params.length + start.locals.length = 22 := rfl
  have hG0 : start.get 0 = some (.i64 pT) := rfl
  have hG1 : start.get 1 = some (.i64 pB) := rfl
  have hG2 : start.get 2 = some (.i64 count) := rfl
  have hA := altitude_implements (a := a)
  have hS := speed_implements (a := a)
  have hn : a = false → (2 * count).toNat = 2 * count.toNat := fun ha => by
    have := (hPre ha).1
    change count.toNat ≤ 64 at this
    rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  have hNeed : a = false → UInt64.ofNat (8 * ((2 * count).toNat + 1)) ≤ tableBytes := fun ha => by
    have := (hPre ha).1
    change count.toNat ≤ 64 at this
    have hU : UInt64.size = 18446744073709551616 := rfl
    rw [UInt64.le_iff_toNat_le, hn ha, UInt64.toNat_ofNat_of_lt' (by omega)]
    unfold tableBytes; simp; omega
  rw [show outputTuple (terrain, table, count) = _ from output_build terrain table count]
  refine (Stmt.buildWith_specA (writes := (List.range 14).map (· + 6)) (n := 2 * count)
    (scratch := 20) (outputWord terrain table count) rfl rfl rfl (by decide) (by decide)
    (by decide) (by rw [hStart]; omega) hHeap hCap
    (fun ha => by have := (hPre ha).1; change count.toNat ≤ 64 at this; rw [hn ha]; omega)
    (fun ha => (hPre ha).2.room hHeap (by omega) (hNeed ha) tableBytes_eight hCap)
    ⟨start, by simp [Expr.eval, hG2, U64Op.apply]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 22 := by
      rw [hFrame.params, hFrame.locals]; exact hStart
    have hT0 : state.get 0 = some (.i64 pT) :=
      (hFrame.get 0 (by decide) (by decide)).trans hG0
    have hT1 : state.get 1 = some (.i64 pB) :=
      (hFrame.get 1 (by decide) (by decide)).trans hG1
    have hT2 : state.get 2 = some (.i64 count) :=
      (hFrame.get 2 (by decide) (by decide)).trans hG2
    have hXT := hAt pT terrain hTerrain
    have hLenT := hXT.lengthBound
    simp only [UInt64.toNat_toUInt32] at hLenT
    have hX := hAt pB _ hTable
    have hRdT : ∀ (k : UInt64) (st : State), st.get 0 = some (.i64 pT) →
        Expr.readValue store.mem 0 k st = some (terrain[k.toNat]!, st) :=
      fun _ _ h => Expr.readValue_at hXT h
    have hR2 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 1 = some (.i64 pB) →
        Expr.readValue store.mem 1 (k * 3 + 2) st = some (table[k.toNat]!.parent, st) :=
      fun k hk st h => by
        simpa [Scalar.values, Flat.flat, Value.word] using
          Expr.readValue_record (j := 2) choice_length (by decide) (by decide) choice_default hX
            hk h
    have hZ : ∀ (k : UInt64), ¬k < 536870912 → table[k.toNat]!.parent = 0 := fun k hk => by
      have h2 := flatWords_read choice_length (j := 2) (by decide) (by decide) choice_default
        hSize k
      simp only [hk, ite_false] at h2
      simpa [Scalar.values, Flat.flat, Value.word] using h2.symm
    set E := UInt64.ofNat e with hE
    iterate 2 (refine Stmt.seq_run ?_; eval_state [hLength, hIndex])
    refine Stmt.seq_spec (Stmt.loop_spec (vars := [7]) (writes := [7, 10, 11, 12])
      (init := (0 : UInt64)) (n := count - 1 - E / 2) (backStep table count)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [hLength])
      ⟨_, by simp [Expr.eval, U64Op.apply, hT2, hLength]; rfl⟩
      (by simp [State.Holds, Scalar.values, hLength]) ?_)
      (TripleA.of_forall fun s0 st0 h0 => ?_)
    · rintro k s st hk hFr hHolds hIdx hLim
      have hLen : st.params.length + st.locals.length = 22 := by
        rw [hFr.params, hFr.locals]; simp [hLength]
      have hU1 : st.get 1 = some (.i64 pB) :=
        (hFr.get 1 (by decide) (by decide)).trans (by simp [hT1])
      have hU2 : st.get 2 = some (.i64 count) :=
        (hFr.get 2 (by decide) (by decide)).trans (by simp [hT2])
      have hU7 : st.get 7 = some (.i64 s) := by
        simpa [State.Holds, Scalar.values] using hHolds
      by_cases hG : (count - 1 - UInt64.ofNat k) * 45 + s < 536870912
      · refine Stmt.run_triple ?_
        eval_state [hLen, hU1, hU2, hU7, hIdx, hG, hR2]
        refine ⟨?_, ?_⟩
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · simp [State.Holds, hLen, backStep, stateCount]
      · have hZk : table[((count - 1 - UInt64.ofNat k).toNat * 45 + s.toNat) %
            18446744073709551616]!.parent = 0 := by
          simpa using hZ _ hG
        refine Stmt.run_triple ?_
        eval_state [hLen, hU1, hU2, hU7, hIdx, hG]
        refine ⟨?_, ?_⟩
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · simp [State.Holds, hLen, backStep, stateCount, hZk]
    · obtain ⟨rfl, hFr, hHolds⟩ := h0
      have hLen : st0.params.length + st0.locals.length = 22 := by
        rw [hFr.params, hFr.locals]; simp [hLength]
      let state' := LeanExe.loop (count - 1 - E / 2) (0 : UInt64) (backStep table count)
      have hV7 : st0.get 7 = some (.i64 state') := by
        simpa [State.Holds, Scalar.values] using hHolds
      have hV0 : st0.get 0 = some (.i64 pT) :=
        (hFr.get 0 (by decide) (by decide)).trans (by simp [hT0])
      have hV5 : st0.get 5 = some (.i64 E) :=
        (hFr.get 5 (by decide) (by decide)).trans (by simp [hIndex])
      have hV6 : st0.get 6 = some (.i64 (E / 2)) :=
        (hFr.get 6 (by decide) (by decide)).trans (by simp [hLength, U64Op.apply])
      iterate 3 (refine Stmt.seq_run ?_; eval_state [hLen, hV7, hLenT, hXT.lengthRead, hV0])
      refine Stmt.seq_callPure hA rfl rfl rfl (x := (floorAt terrain (E / 2), state')) ?_
      eval_state [hLen, hV6, hV0, hRdT, altitudeTuple]
      refine ⟨by rw [← floor_ir1 terrain (E / 2)]; simp [UInt64.toNat_div], ?_⟩
      refine Stmt.seq_run ?_
      eval_state [hLen]
      refine Stmt.seq_callPure hS rfl rfl rfl (x := state') ?_
      eval_state [hLen]
      refine Stmt.run_triple ?_
      eval_state [hLen]
      refine ⟨?_, ?_⟩
      · refine State.Frame.trans ?_ ((hFr.weaken (by decide)).trans ?_)
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
      · simp [Expr.eval, hLen, hV5, U64Op.apply, outputWord, state', altitudeTuple,
          State.set?_eq_update, remU_eq]
  rintro store state ⟨ptr, -, hPtr, hNew, hPages⟩
  exact ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [drone.output.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, hNew.owned⟩, hNew.keeps,
    fun ha => (hPre ha).2.allocate hHeap (hNeed ha) tableBytes_eight hCap hPages hNew.caps⟩

theorem output_implements : Implements drone.module 15 outputTuple :=
  (output_implementsA (a := true) 0 0).implements_of fun _ _ _ h => nomatch h

/-- The number of stations `compute` plans: the terrain's size for valid terrain, and 0
otherwise. -/
def countOf (terrain : Array UInt64) : UInt64 :=
  if (decide (0 < terrain.size.toUInt64) && decide (terrain.size.toUInt64 ≤ 64) &&
    validHeights terrain) = true then terrain.size.toUInt64 else 0

theorem compute_eq (terrain : Array UInt64) :
    compute terrain = output terrain (forward terrain (countOf terrain)).2.2 (countOf terrain) := by
  unfold compute countOf
  rfl

theorem countOf_le (terrain : Array UInt64) : (countOf terrain).toNat ≤ 64 := by
  unfold countOf
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact UInt64.le_iff_toNat_le.mp h.1.2
  · decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Under `a = false`, the heap has room for 66 more blocks of `tableBytes` bytes: one for the
first row, at most 63 for the tables of the forward pass, one for the output, and one to spare. -/
theorem compute_implementsA {a : Bool} (spare pages : Nat) :
    ImplementsA a drone.module 16 compute
      (fun _ heap store => a = false →
        heap.Bounded store drone.module tableBytes (spare + 66) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final drone.module tableBytes spare pages) := by
  refine Func.implements_heapA drone.funcs 14 drone.compute.ir "compute" rfl compute _ _
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro terrain heap initial _ hHeap hPre ⟨pT, rfl, hT⟩ hCap
  have hc64 := countOf_le terrain
  have hW := hT.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  set start := drone.compute.ir.state [.i64 pT] with hStartDef
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hG0 : start.get 0 = some (.i64 pT) := rfl
  let n := UInt64.ofNat terrain.size
  let s1 := start.update 1 (.i64 n)
  let s2 := s1.update 2 (.i64 n)
  refine Stmt.seq_run ⟨s1, by
    simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hG0, n],
    ?_⟩
  refine Stmt.seq_run ⟨s2, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2],
    ?_⟩
  let s3 := s2.update 3 (.i64 (cond (validHeights terrain) 1 0))
  refine Live.callScalar_seqA validHeights_implementsA rfl rfl rfl (Live.start hHeap) hCap
    (x := terrain) (before := s2) (afterArgs := s2) (after := s3)
    (by simp [Expr.evalResults, Expr.eval, s2, s1, hStart, hG0]) ⟨pT, rfl, hT⟩ trivial
    (by simp [State.setAll, State.set?_eq_update, s3, s2, s1, hStart, Scalar.values, Flat.flat])
    ?_
  rintro heap1 store1 hLive1 ⟨rfl, rfl⟩
  let s4 := s3.update 4 (.i64 (cond (validHeights terrain) 1 0))
  let s5 := s4.update 5 (.i64 (countOf terrain))
  refine Stmt.seq_run ⟨s4, by simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s4, s3,
    s2, s1], ?_⟩
  refine Stmt.seq_run ⟨s5, by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s5, s4, s3, s2, s1, U64Op.apply,
      word_and, word_eq_one, countOf, n, cond_eq_ite]
    by_cases h1 : 0 < UInt64.ofNat terrain.size <;> by_cases h2 : UInt64.ofNat terrain.size ≤ 64 <;>
      by_cases h3 : validHeights terrain = true <;> simp [h1, h2, h3], ?_⟩
  have hS5 : s5.params.length + s5.locals.length = 11 := by simp [s5, s4, s3, s2, s1, hStart]
  have hT1 : heap1.Borrowed store1 pT terrain := hLive1.borrowed pT terrain hT Apart.nil
  let six := fun (q : UInt64) => ((s5.update 8 (.i64 q)).update 7
    (.i64 (forward terrain (countOf terrain)).2.1)).update 6
    (.i64 (forward terrain (countOf terrain)).1)
  refine Live.callOne_seqA (forward_implementsA (spare + 1 + (64 - (countOf terrain).toNat))
    pages) rfl rfl rfl (consumed := []) (rest := []) hLive1 hCap
    (x := (terrain, countOf terrain)) (vals := [.i64 pT, .i64 (countOf terrain)]) (before := s5)
    (afterArgs := s5) (by simp [Expr.evalResults, Expr.eval, s5, s4, s3, s2, s1, hStart, hG0])
    ⟨_, _, rfl, ⟨pT, rfl, hT1⟩, rfl⟩
    (fun ha => ⟨hc64, by
      rw [show spare + 1 + (64 - (countOf terrain).toNat) + (countOf terrain).toNat + 1 =
        spare + 66 by omega]
      exact hPre ha⟩) rfl (fun _ _ _ h => nomatch h)
    (fun q => ⟨six q, by
      simp [State.setAll, State.set?_eq_update, hS5, six, OneArray.scalars, Scalar.values,
        forwardTuple]⟩) ?_
  intro heap2 p8 store2 st6 hLive2 hst6 hPost2
  have hst : st6 = six p8 := by
    simp [State.setAll, State.set?_eq_update, hS5, six, OneArray.scalars, Scalar.values,
      forwardTuple] at hst6
    exact hst6.symm
  subst hst
  have hS6 : (six p8).params.length + (six p8).locals.length = 11 := by simp [six, hS5]
  have hT2 : heap2.Borrowed store2 pT terrain := hLive2.borrowed pT terrain hT Apart.nil
  let table := (forward terrain (countOf terrain)).2.2
  have hTab : heap2.Owned store2 p8 (flatWords table) :=
    hLive2.tempsOwned _ (List.mem_singleton_self _)
  let nine := fun (q : UInt64) => (six p8).update 9 (.i64 q)
  refine Live.callOne_seqA (output_implementsA (spare + (64 - (countOf terrain).toNat)) pages)
    rfl rfl rfl (consumed := [])
    (rest := [(p8, flatWords table)]) hLive2 hCap (x := (terrain, table, countOf terrain))
    (vals := [.i64 pT, .i64 p8, .i64 (countOf terrain)]) (before := six p8) (afterArgs := six p8)
    (by simp [Expr.evalResults, Expr.eval, six, s5, s4, s3, s2, s1, hStart, hG0, hS5])
    ⟨_, _, rfl, ⟨pT, rfl, hT2⟩, _, _, rfl, ⟨p8, rfl, hTab.borrowed⟩, rfl⟩
    (fun ha => ⟨hc64, by
      rw [show spare + (64 - (countOf terrain).toNat) + 1 =
        spare + 1 + (64 - (countOf terrain).toNat) by omega]
      exact hPost2 ha⟩) rfl
    (fun _ _ _ h => nomatch h)
    (fun q => ⟨nine q, by
      simp [State.setAll, State.set?_eq_update, hS6, nine, OneArray.scalars]⟩) ?_
  intro heap3 p9 store3 st9 hLive3 hst9 hPost3
  have hst : st9 = nine p9 := by
    simp [State.setAll, State.set?_eq_update, hS6, nine, OneArray.scalars] at hst9
    exact hst9.symm
  subst hst
  have hS9 : (nine p9).params.length + (nine p9).locals.length = 11 := by simp [nine, hS6]
  refine Stmt.seq_run ⟨(nine p9).update 10 (.i64 p9), by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hS6, nine], ?_⟩
  refine Live.releaseSecond_last_pages hLive3 rfl rfl (by simp [hS9, nine, six, hS5])
    fun s hL hPages => ?_
  rw [compute_eq]
  exact Live.finish_results_oneP (P := fun h s => a = false →
    h.Bounded s drone.module tableBytes spare pages)
    (y := output terrain table (countOf terrain)) hL
    ⟨(nine p9).update 10 (.i64 p9), by
      simp [drone.compute.ir, Expr.evalResults, Expr.eval, hS9, OneArray.scalars, outputTuple]⟩
    fun ha => ((hPost3 ha).release hLive3.at_ (hLive3.tempsOwned (p8, flatWords table) (by simp))
      hPages (hL.caps.trans hLive3.caps.symm)).mono (by omega)

theorem compute_implements : Implements drone.module 16 compute :=
  (compute_implementsA (a := true) 0 0).implements_of fun _ _ _ h => nomatch h

end Demos.Drone
