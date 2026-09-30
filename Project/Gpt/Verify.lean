import Project.Gpt.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.Encoding.RoundTrip

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.ProofKit

/-- `dot` with its two arguments as one pair. -/
def dotTuple (x : Array Float × Array Float) : Float :=
  LeanExe.Examples.Gpt.dot x.1 x.2

/-- One step of `dot`'s loop. -/
def dotStep (xs ys : Array Float) (i : UInt64) (acc : Float) : Float :=
  acc + xs[i.toNat]! * ys[i.toNat]!

/-- The compiled loop body of `dot`. -/
def dotBody : Stmt :=
  .seq (.assign 6 (.binF .add (.getF 3) (.binF .mul (.ofBits (.read 0 (.get 5)))
    (.ofBits (.read 1 (.get 5)))))) (.assign 3 (.getF 6))

theorem dotBody_run {initial : Store Unit} {px py : UInt64} {xs ys : Array Float}
    (hX : UInt64Array.At initial px (xs.map Float.toBits))
    (hY : UInt64Array.At initial py (ys.map Float.toBits))
    {state : State} {k : Nat} {acc : Float}
    (hParams : state.params.length = 2) (hLocals : state.locals.length = 6)
    (h0 : state.get 0 = some (.i64 px)) (h1 : state.get 1 = some (.i64 py))
    (h3 : state.get 3 = some (.f64 acc.toBits))
    (h5 : state.get 5 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, dotBody.run initial.mem 7 state = some final ∧
      State.Frame 7 [3, 6] state final ∧
      final.Holds [3] (Scalar.values (dotStep xs ys (UInt64.ofNat k) acc)) := by
  simp [dotBody, Stmt.run, Expr.eval, h0, h1, h3, h5, Expr.readValue_at hX,
    Expr.readValue_at hY, State.set?_eq_update, hParams, hLocals, F64Op.apply,
    getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, dotStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul]

theorem dot_implements : Implements gpt.module 3 dotTuple (fun _ => 0) := by
  refine Func.implements gpt.funcs 0 gpt.dot.ir "dot" rfl dotTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨xs, ys⟩ heap initial _ - ⟨_, _, rfl, ⟨px, rfl, hXs⟩, ⟨py, rfl, hYs⟩⟩
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
  change heap.Borrowed initial py (ys.map Float.toBits) at hYs
  have hX := hXs.values
  have hY := hYs.values
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 py], locals := [.i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  let s1 := start.update 2 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 3 (.f64 0)
  show Triple _ (.seq (.arraySize 2 0) (.seq (.assign 3 (.constF 0))
    (.loop 4 5 (.get 2) dotBody))) 7 (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 2 := rfl
  have hLocals : start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 px) := rfl
  have hLength := hX.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hX.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2]
  refine (Stmt.loop_spec (vars := [3]) (writes := [3, 6]) (init := (0.0 : Float))
    (n := xs.size.toUInt64) (dotStep xs ys)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [s2, s1, hParams, hLocals]) ⟨s2, by simp [Expr.eval, s2, s1, hParams, hLocals]⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hParams, hLocals, hZero]) ?_).mono
      (fun _ _ h => h) ?_
  · intro k acc state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 2 ∧ state.locals.length = 6 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, s1, hParams, hLocals]
    have h0 : state.get 0 = some (.i64 px) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have h1 : state.get 1 = some (.i64 py) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
    have h3 : state.get 3 = some (.f64 acc.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      dotBody_run hX hY hState.1 hState.2 h0 h1 h3 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  rintro store state ⟨rfl, -, hHolds⟩
  have h3 : state.get 3 = some (.f64 (dotTuple (xs, ys)).toBits) :=
    (List.forall₂_cons.mp hHolds).1
  exact ⟨rfl, [.f64 _], state, by
    simp [gpt.dot.ir, Func.scratch, Expr.evalResults, Expr.eval, h3], rfl⟩

/-- `encode` succeeds on `gpt.module`, and its bytes decode to a module whose
exports compute the kernels exactly. -/
theorem gpt_bytes : ∃ bytes, Encoding.encode gpt.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 dotTuple (fun _ => 0) := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip gpt.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, gpt.module, decoded, dot_implements⟩

end Project.Gpt
