import Library.Arrays.Search.Proof
import Examples.RemoveZero.Module
import Examples.RemoveZero.Proof
import LeanExe.IR.Build
import LeanExe.IR.Correct
import LeanExe.IR.OneArray
import LeanExe.IR.Words
import LeanExe.IR.Combinators
import LeanExe.Encoding.RoundTrip

/-! The bytes of `removeZero.module` compute the specification `expected`. -/

namespace Examples.RemoveZero

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.RemoveZero

export Library.Arrays.Search (firstZeroStep firstZero_cases)

def firstZeroTuple : Array UInt64 × UInt64 → UInt64 := fun (xs, count) => Library.Arrays.Search.firstZero xs count

set_option maxHeartbeats 2000000 in
theorem firstZero_implements : Implements removeZero.module 2 firstZeroTuple := by
  refine Func.implements removeZero.funcs 0 removeZero.firstZero.ir "firstZero" rfl firstZeroTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨xs, count⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hXs⟩, rfl⟩
  have hW := hXs.values
  set start := removeZero.firstZero.ir.state ([.i64 ptr] ++ Scalar.values count) with hStartDef
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  have hGet1 : start.get 1 = some (.i64 count) := rfl
  let s1 := start.update 2 (.i64 count)
  show Triple _ (.seq (.assign 2 (.get 1)) (.loop 3 4 (.get 1)
    (.seq (.assign 5 _) (.assign 2 (.get 5))))) 6 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, hGet1]
  have hS1 : s1.params.length + s1.locals.length = 7 := by simp [s1, hStart]
  refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5]) (init := count) (n := count)
    (firstZeroStep xs count) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) ⟨s1, by simp [Expr.eval, s1, hStart, hGet1]⟩
    (by simp [State.Holds, Scalar.values, s1, hStart]) ?_).mono (fun _ _ h => h) ?_
  · intro i k state hi hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 7 := by
      rw [hFrame.params, hFrame.locals]; exact hS1
    have g0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s1, hGet0])
    have g1 : state.get 1 = some (.i64 count) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s1, hGet1])
    have g2 : state.get 2 = some (.i64 k) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have g0' : (state.update 6 (.i64 (UInt64.ofNat i))).get 0 = some (.i64 ptr) := by
      rw [State.get_update_ne (by decide)]; exact g0
    refine Stmt.run_triple ?_
    eval_state [hLength, hIndex, g0, g1, g2, Expr.readValue_at hW g0']
    refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, firstZeroStep]
  · rintro store state ⟨rfl, -, hHolds⟩
    refine ⟨rfl, _, state, ?_, rfl⟩
    have g2 : state.get 2 = some (.i64 (Library.Arrays.Search.firstZero xs count)) := by
      rw [show Library.Arrays.Search.firstZero xs count = LeanExe.loop count count (firstZeroStep xs count) from rfl]
      simpa [State.Holds, Scalar.values] using hHolds
    simp [removeZero.firstZero.ir, Func.scratch, Expr.evalResults, Expr.eval, g2, Scalar.values,
      firstZeroTuple]

set_option maxHeartbeats 2000000 in
theorem compute_implements : Implements removeZero.module 3 compute := by
  refine Func.implements_heap removeZero.funcs 1 removeZero.compute.ir "compute" rfl compute
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨ptr, rfl, hXs⟩ hCap
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  set start := removeZero.compute.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let n := xs.size.toUInt64
  let count : UInt64 := if n ≤ 8 then n else 0
  let k := Library.Arrays.Search.firstZero xs count
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 2 (.i64 (UInt64.ofNat xs.size))
  let s3 := s2.update 3 (.i64 count)
  let s4 := s3.update 4 (.i64 k)
  let s5 := s4.update 5 (.i64 k)
  show Triple _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.get 1))
    (.seq (.assign 3 (.ite (.leU (.get 2) (.const 8)) (.get 2) (.const 0)))
    (.seq (.call 2 [⟨.u64, .get 0⟩, ⟨.u64, .get 3⟩] [4]) (.seq (.assign 5 (.get 4))
      (Stmt.build 6 7 8 (.ite (.ltU (.get 5) (.get 3)) (.bin .sub (.get 3) (.const 1)) (.get 3))
        (.ite (.ltU (.get 8) (.get 5)) (.read 0 (.get 8))
          (.read 0 (.bin .add (.get 8) (.const 1)))))))))) 9 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, count, n]
  refine Live.callScalar_seq firstZero_implements rfl rfl rfl (Live.start hHeap) hCap
    (x := (xs, count)) (vals := [.i64 ptr, .i64 count]) (before := s3) (afterArgs := s3)
    (after := s4)
    (by simp [Expr.evalResults, Expr.eval, s3, s2, s1, hStart, hGet0])
    ⟨[.i64 ptr], [.i64 count], rfl, ⟨ptr, rfl, hXs⟩, rfl⟩
    (by simp [State.setAll, State.set?_eq_update, s4, s3, s2, s1, hStart, Scalar.values,
      firstZeroTuple, k]) ?_
  intro heap1 sA hLive1
  have hXs1 : heap1.Borrowed sA ptr xs := hLive1.borrowed ptr xs hXs Apart.nil
  refine Stmt.seq_spec (Stmt.run_spec (final := s5) ?_) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s5, s4, s3, s2, s1]
  have hS5 : s5.params.length + s5.locals.length = 10 := by simp [s5, s4, s3, s2, s1, hStart]
  let m : UInt64 := if k < count then count - 1 else count
  refine (Stmt.build_spec (n := m)
    (fun i => if i < k then xs[i.toNat]! else xs[(i + 1).toNat]!) rfl rfl rfl (by decide)
    (by decide) (by omega) hLive1.at_ (hLive1.cap hCap)
    ⟨s5, by simp [Expr.eval, s5, s4, s3, s2, s1, hStart, m, U64Op.apply]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length + state.locals.length = 10 := by
      rw [hFrame.params, hFrame.locals]; exact hS5
    have g0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1, hGet0])
    have g5 : state.get 5 = some (.i64 k) :=
      (hFrame.get 5 (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1, hStart])
    have hX := hAt ptr _ hXs1
    have g0' : ∀ v, (state.update 9 v).get 0 = some (.i64 ptr) := fun v => by
      rw [State.get_update_ne (by decide)]; exact g0
    by_cases hjk : UInt64.ofNat j < k
    · exact ⟨state.update 9 (.i64 (UInt64.ofNat j)), by
        simp [Expr.eval, g5, hIndex, hjk, State.set?_eq_update, hState,
          Expr.readValue_at hX (g0' _), U64Op.apply]⟩
    · exact ⟨state.update 9 (.i64 (UInt64.ofNat j + 1)), by
        simp [Expr.eval, g5, hIndex, hjk, State.set?_eq_update, hState,
          Expr.readValue_at hX (g0' _), U64Op.apply]⟩
  rintro store state ⟨p, -, hPtr, hNew⟩
  exact Live.finish_results_one (y := compute xs) (Live.push hLive1 hNew) ⟨state, by
    simp [removeZero.compute.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr, OneArray.scalars]⟩

/-- `encode` succeeds on `removeZero.module`, and its bytes decode to a module whose entry 3
computes the specification `expected`. -/
theorem removeZero_bytes : ∃ bytes, Wasm.Encoding.encode removeZero.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 3 expected := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip removeZero.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, removeZero.module, decoded, compute_implements.congr
    fun _ _ _ xs ⟨_, _, hXs⟩ => compute_eq xs hXs.values.size_lt⟩

#print axioms removeZero_bytes

end Examples.RemoveZero
