import Project.Drone.Kernels
import Project.IR.BuildRecord
import Project.IR.RecordRead
import Project.Drone.Costs
import Project.Pipeline.Budget

/-! The compiled functions of the drone planner's rows compute their Lean definitions.  A
`Choice` is represented as its three words, and an array of choices as `flatWords`, three words
for each choice. -/

namespace Project.Drone

open Wasm Project.Pipeline Project.IR Project.Runtime LeanExe.Examples.Drone

instance : Flat Choice (UInt64 × UInt64 × UInt64) := ⟨fun c => (c.time, c.excess, c.parent)⟩

def chooseTuple : Choice × Choice → Choice := fun (a, b) => choose a b

set_option maxHeartbeats 4000000 in
theorem choose_implements {a : Bool} : ImplementsPureA a drone.module 8 chooseTuple :=
  Func.implementsPureA drone.funcs 6 drone.choose.ir "choose" rfl chooseTuple
    (fun _ => rfl) fun ⟨⟨t0, e0, p0⟩, ⟨t1, e1, p1⟩⟩ initial => by
      refine Stmt.run_triple ?_
      by_cases h : t1 < t0 ∨ t1 = t0 ∧ e1 < e0
      · eval_body [drone.choose.ir, chooseTuple, choose, h]
      · eval_body [drone.choose.ir, chooseTuple, choose, h]

def predecessorTuple : UInt64 × UInt64 × Choice × UInt64 × UInt64 → Choice :=
  fun (r0, r1, old, target, source) => predecessor r0 r1 old target source

set_option maxHeartbeats 4000000 in
theorem predecessor_implements {a : Bool} : ImplementsPureA a drone.module 9 predecessorTuple :=
  Func.implementsPureA drone.funcs 7 drone.predecessor.ir "predecessor" rfl predecessorTuple
    (fun _ => rfl) fun ⟨r0, r1, ⟨t, e, p⟩, target, source⟩ initial => by
      have hA := altitude_implements (a := a)
      have hS := speed_implements (a := a)
      have hE := edgeTicks_implements (a := a)
      refine Stmt.seq_callPure hA rfl rfl rfl (x := (r0, source)) ?_
      eval_body [drone.predecessor.ir]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_callPure hA rfl rfl rfl (x := (r1, target)) ?_
      eval_body [altitudeTuple]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_callPure hS rfl rfl rfl (x := source) ?_
      eval_body [altitudeTuple]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_callPure hS rfl rfl rfl (x := target) ?_
      eval_body [altitudeTuple]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.seq_callPure hE rfl rfl rfl
        (x := (r0, r1, altitude r0 source, altitude r1 target, speed source, speed target)) ?_
      eval_body [altitudeTuple]
      refine Stmt.seq_run ?_
      eval_body []
      refine Stmt.run_triple ?_
      eval_body [edgeTicksTuple, predecessorTuple, predecessor]
      split_ifs <;> simp_all

theorem choice_length (c : Choice) : (Scalar.values c).length = 3 := rfl

theorem choice_default :
    (Scalar.values (default : Choice)).map Value.word = List.replicate 3 0 := rfl

def initialUnit : Unit → Array Choice := fun _ => initial

theorem initialUnit_build : initialUnit () = LeanExe.build 45 initialChoice := rfl

set_option maxHeartbeats 4000000 in
/-- The bytes of the largest block the planner allocates: a table of 64 rows of 45 choices. -/
def tableBytes : UInt64 := 69128

theorem tableBytes_eight : 8 ≤ tableBytes.toNat := by decide

set_option maxHeartbeats 4000000 in
/-- Under `a = false`, the heap has room for one more block of `tableBytes` bytes. -/
theorem initial_implementsA {a : Bool} (spare pages : Nat) :
    ImplementsA a drone.module 11 initialUnit
      (fun _ heap store => a = false →
        heap.Bounded store drone.module tableBytes (spare + 1) pages)
      (fun _ _ _ heap' final => a = false →
        heap'.Bounded final drone.module tableBytes spare pages) := by
  refine Func.implements_heapA drone.funcs 9 drone.initial.ir "initial" rfl initialUnit _ _
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro ⟨⟩ heap initial params hHeap hPre rfl hCap
  rw [show initialUnit () = _ from initialUnit_build]
  refine (Stmt.buildRecords_specA (writes := [3, 4, 5]) (n := 45) (scratch := 6)
    (elements := [.get 3, .get 4, .get 5]) (before := drone.initial.ir.state (Scalar.values ()))
    initialChoice choice_length (by decide) rfl rfl rfl (by decide) (by decide) (by decide)
    (Nat.le_of_eq rfl) hHeap hCap (fun _ => by decide)
    (fun ha => (hPre ha).room hHeap (by omega) (by decide) tableBytes_eight hCap) ⟨_, rfl⟩
    ?_).mono (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 6 := by
      rw [hFrame.params, hFrame.locals]; rfl
    refine Stmt.run_triple ?_
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hLength, hIndex, ScalarType.value,
      initialChoice, Scalar.values, Flat.flat]
    refine ⟨?_, fun j hj => ?_⟩
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      all_goals
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, Value.word]
        exact Expr.yields_get (by simp [hLength])
  rintro store state ⟨ptr, -, hPtr, hNew, hPages⟩
  exact ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [drone.initial.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, hNew.owned⟩, hNew.keeps,
    fun ha => (hPre ha).allocate hHeap (by decide) tableBytes_eight hCap hPages hNew.caps⟩

theorem initial_implements : Implements drone.module 11 initialUnit :=
  (initial_implementsA (a := true) 0 0).implements_of fun _ _ _ h => nomatch h

def advanceTuple : UInt64 × UInt64 × Bool × Array Choice × UInt64 → Array Choice :=
  fun (r0, r1, last, table, base) => advance r0 r1 last table base

set_option maxHeartbeats 8000000 in
theorem advance_implements : Implements drone.module 10 advanceTuple := by
  refine Func.implements_heap drone.funcs 8 drone.advance.ir "advance" rfl advanceTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩
        rfl) ?_
  rintro ⟨r0, r1, last, table, base⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨ptr, rfl, hTable⟩, rfl⟩ hCap
  change heap.Borrowed initial ptr (flatWords table) at hTable
  have hW := hTable.values
  have hSize : (flatWords table).size < 536870912 := by have := hW.1; omega
  have hP := predecessor_implements (a := true)
  have hC := choose_implements (a := true)
  set start := drone.advance.ir.state
    [.i64 r0, .i64 r1, .i64 (cond last 1 0), .i64 ptr, .i64 base] with hStartDef
  have hStart : start.params.length + start.locals.length = 30 := rfl
  have hG0 : start.get 0 = some (.i64 r0) := rfl
  have hG1 : start.get 1 = some (.i64 r1) := rfl
  have hG2 : start.get 2 = some (.i64 (cond last 1 0)) := rfl
  have hG3 : start.get 3 = some (.i64 ptr) := rfl
  have hG4 : start.get 4 = some (.i64 base) := rfl
  rw [show advanceTuple (r0, r1, last, table, base) = _ from advance_build r0 r1 last table base]
  refine (Stmt.buildRecords_spec (writes := (List.range 21).map (· + 8)) (n := 45) (scratch := 29)
    (elements := [.get 26, .get 27, .get 28]) (before := start)
    (fun target => best r0 r1 table base target (sourceCount last target)) choice_length
    (by decide) rfl rfl rfl (by decide) (by decide) (by decide) (by rw [hStart]; omega) hHeap hCap
    ⟨_, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 30 := by
      rw [hFrame.params, hFrame.locals]; exact hStart
    have hS0 : state.get 0 = some (.i64 r0) := (hFrame.get 0 (by decide) (by decide)).trans hG0
    have hS1 : state.get 1 = some (.i64 r1) := (hFrame.get 1 (by decide) (by decide)).trans hG1
    have hS2 : state.get 2 = some (.i64 (cond last 1 0)) :=
      (hFrame.get 2 (by decide) (by decide)).trans hG2
    have hS3 : state.get 3 = some (.i64 ptr) := (hFrame.get 3 (by decide) (by decide)).trans hG3
    have hS4 : state.get 4 = some (.i64 base) := (hFrame.get 4 (by decide) (by decide)).trans hG4
    have hX := hAt ptr _ hTable
    have hRd : ∀ (j : Nat), j < 3 → ∀ (k : UInt64), k < 536870912 → ∀ st : State,
        st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * UInt64.ofNat 3 + UInt64.ofNat j) st =
          some (((Scalar.values table[k.toNat]!).map Value.word)[j]!, st) :=
      fun j hj k hk st h => Expr.readValue_record choice_length hj (by decide) choice_default hX hk h
    have hR0 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 3) st = some (table[k.toNat]!.time, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 0 (by decide) k hk st h
    have hR1 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 3 + 1) st = some (table[k.toNat]!.excess, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 1 (by decide) k hk st h
    have hR2 : ∀ (k : UInt64), k < 536870912 → ∀ st : State, st.get 3 = some (.i64 ptr) →
        Expr.readValue store.mem 3 (k * 3 + 2) st = some (table[k.toNat]!.parent, st) :=
      fun k hk st h => by simpa [Scalar.values, Flat.flat, Value.word] using hRd 2 (by decide) k hk st h
    have hZ : ∀ (k : UInt64), ¬k < 536870912 → table[k.toNat]! = ⟨0, 0, 0⟩ := fun k hk => by
      have h0 := flatWords_read choice_length (j := 0) (by decide) (by decide) choice_default hSize k
      have h1 := flatWords_read choice_length (j := 1) (by decide) (by decide) choice_default hSize k
      have h2 := flatWords_read choice_length (j := 2) (by decide) (by decide) choice_default hSize k
      simp only [hk, ite_false] at h0 h1 h2
      cases hc : table[k.toNat]!
      simp_all [Scalar.values, Flat.flat, Value.word]
    set target := UInt64.ofNat i with hTarget
    iterate 3 (refine Stmt.seq_run ?_; eval_state [hLength])
    refine Stmt.seq_spec (Stmt.loop_spec (vars := [8, 9, 10])
      (writes := [8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25])
      (init := ((infinity : UInt64), (infinity : UInt64), (0 : UInt64)))
      (n := sourceCount last target) (bestStep r0 r1 table base target)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [hLength])
      ⟨_, by
        simp [Expr.eval, U64Op.apply, hS2, hIndex, sourceCount, word_or, target, cond_eq_ite,
          word_not]
        refine ⟨?_, rfl⟩
        cases last <;> simp⟩
      (by simp [State.Holds, Scalar.values, hLength]) ?_)
      (TripleA.of_forall fun s0 st0 h0 => ?_)
    · rintro k ⟨a1, a2, a3⟩ st hk hFr hHolds hIdx hLim
      have hLen : st.params.length + st.locals.length = 30 := by
        rw [hFr.params, hFr.locals]; simp [hLength]
      have hT0 : st.get 0 = some (.i64 r0) :=
        (hFr.get 0 (by decide) (by decide)).trans (by simp [hS0])
      have hT1 : st.get 1 = some (.i64 r1) :=
        (hFr.get 1 (by decide) (by decide)).trans (by simp [hS1])
      have hT3 : st.get 3 = some (.i64 ptr) :=
        (hFr.get 3 (by decide) (by decide)).trans (by simp [hS3])
      have hT4 : st.get 4 = some (.i64 base) :=
        (hFr.get 4 (by decide) (by decide)).trans (by simp [hS4])
      have hT7 : st.get 7 = some (.i64 target) :=
        (hFr.get 7 (by decide) (by decide)).trans (by simp [hIndex, target])
      have hA : st.get 8 = some (.i64 a1) ∧ st.get 9 = some (.i64 a2) ∧
          st.get 10 = some (.i64 a3) := by
        simpa [State.Holds, Scalar.values] using hHolds
      by_cases hG : base + UInt64.ofNat k < 536870912
      · iterate 4 (refine Stmt.seq_run ?_; eval_state [hLen, hT3, hT4, hIdx, hG, hR0, hR1, hR2])
        refine Stmt.seq_callPure hP rfl rfl rfl
          (x := (r0, r1, table[(base + UInt64.ofNat k).toNat]!, target, UInt64.ofNat k)) ?_
        eval_state [hLen, hT0, hT1, hT7, hIdx, predecessorTuple]
        refine Stmt.seq_callPure hC rfl rfl rfl
          (x := (⟨a1, a2, a3⟩, predecessor r0 r1 table[(base + UInt64.ofNat k).toNat]! target
            (UInt64.ofNat k))) ?_
        eval_state [hLen, hA.1, hA.2.1, hA.2.2, chooseTuple]
        refine Stmt.run_triple ?_
        eval_state [hLen]
        refine ⟨?_, ?_⟩
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · simp [State.Holds, hLen, bestStep]
      · have hZk : table[(base.toNat + k) % 18446744073709551616]! = ⟨0, 0, 0⟩ := by
          simpa using hZ _ hG
        iterate 4 (refine Stmt.seq_run ?_; eval_state [hLen, hT3, hT4, hIdx, hG])
        refine Stmt.seq_callPure hP rfl rfl rfl
          (x := (r0, r1, table[(base + UInt64.ofNat k).toNat]!, target, UInt64.ofNat k)) ?_
        eval_state [hLen, hT0, hT1, hT7, hIdx, predecessorTuple, hZk]
        refine Stmt.seq_callPure hC rfl rfl rfl
          (x := (⟨a1, a2, a3⟩, predecessor r0 r1 table[(base + UInt64.ofNat k).toNat]! target
            (UInt64.ofNat k))) ?_
        eval_state [hLen, hA.1, hA.2.1, hA.2.2, chooseTuple, hZk]
        refine Stmt.run_triple ?_
        eval_state [hLen]
        refine ⟨?_, ?_⟩
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · simp [State.Holds, hLen, bestStep, hZk]
    · obtain ⟨rfl, hFr, hHolds⟩ := h0
      have hLen : st0.params.length + st0.locals.length = 30 := by
        rw [hFr.params, hFr.locals]; simp [hLength]
      have hL := best_loop r0 r1 table base target (sourceCount last target)
      have hB : st0.get 8 = some (.i64 (best r0 r1 table base target (sourceCount last target)).time) ∧
          st0.get 9 = some (.i64 (best r0 r1 table base target (sourceCount last target)).excess) ∧
          st0.get 10 = some (.i64 (best r0 r1 table base target (sourceCount last target)).parent) := by
        rw [hL]
        simpa [State.Holds, Scalar.values] using hHolds
      refine Stmt.run_triple ?_
      eval_state [hLen, hB.1, hB.2.1, hB.2.2]
      refine ⟨?_, fun j hj => ?_⟩
      · refine State.Frame.trans (b := ((state.update 8 (.i64 infinity)).update 9
          (.i64 infinity)).update 10 (.i64 0)) ?_ ?_
        · repeat refine State.Frame.update ?_ (by decide)
          exact State.Frame.refl _ _ _
        · repeat refine State.Frame.update ?_ (by decide)
          exact hFr.weaken (by decide)
      · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        all_goals
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some, Value.word]
          exact Expr.yields_get (by simp [hLen, Scalar.values, Flat.flat])
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  exact ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [drone.advance.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, hNew.owned⟩, hNew.keeps⟩

end Project.Drone
