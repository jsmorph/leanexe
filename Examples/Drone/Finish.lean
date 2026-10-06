import Examples.Drone.Extend
import Examples.Drone.Correct

/-! `output` and `compute` compute their Lean definitions. -/

namespace Examples.Drone

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Drone

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

end Examples.Drone
