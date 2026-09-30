import Project.Gpt.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.Encoding.RoundTrip

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

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

/-- `matVec` with its four arguments as one tuple. -/
def matVecTuple (x : Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.matVec x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `matVec` may allocate: one array of `rows` elements. -/
def matVecNeed (x : Array Float × Array Float × UInt64 × UInt64) : Nat :=
  48 + 8 * (x.2.2.1.toNat + 1)

/-- One step of the loop over row `r`. -/
def rowStep (m v : Array Float) (cols r c : UInt64) (acc : Float) : Float :=
  acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- Element `r` of the product. -/
def row (m v : Array Float) (cols r : UInt64) : Float :=
  LeanExe.loop cols 0.0 (rowStep m v cols r)

theorem matVec_eq (m v : Array Float) (rows cols : UInt64) :
    LeanExe.Examples.Gpt.matVec m v rows cols = LeanExe.build rows (row m v cols) := rfl

/-- The compiled loop body over a row. -/
def rowBody : Stmt :=
  .seq (.assign 10 (.binF .add (.getF 7) (.binF .mul
    (.ofBits (.read 0 (.bin .add (.bin .mul (.get 6) (.get 3)) (.get 9))))
    (.ofBits (.read 1 (.get 9)))))) (.assign 7 (.getF 10))

theorem rowBody_run {initial : Store Unit} {pm pv : UInt64} {m v : Array Float}
    (hM : UInt64Array.At initial pm (m.map Float.toBits))
    (hV : UInt64Array.At initial pv (v.map Float.toBits))
    {state : State} {c : Nat} {r cols : UInt64} {acc : Float}
    (hParams : state.params.length = 4) (hLocals : state.locals.length = 8)
    (h0 : state.get 0 = some (.i64 pm)) (h1 : state.get 1 = some (.i64 pv))
    (h3 : state.get 3 = some (.i64 cols)) (h6 : state.get 6 = some (.i64 r))
    (h7 : state.get 7 = some (.f64 acc.toBits))
    (h9 : state.get 9 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, rowBody.run initial.mem 11 state = some final ∧
      State.Frame 11 [7, 10] state final ∧
      final.Holds [7] (Scalar.values (rowStep m v cols r (UInt64.ofNat c) acc)) := by
  simp [rowBody, Stmt.run, Expr.eval, h0, h1, h3, h6, h7, h9, Expr.readValue_at hM,
    Expr.readValue_at hV, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, rowStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul]

theorem matVec_implements : Implements gpt.module 4 matVecTuple matVecNeed := by
  refine Func.implements_heap gpt.funcs 1 gpt.matVec.ir "matVec" rfl matVecTuple matVecNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨m, v, rows, cols⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨pv, rfl, hVs⟩, rfl⟩ hRoom
  change heap.Borrowed initial pm (m.map Float.toBits) at hMs
  change heap.Borrowed initial pv (v.map Float.toBits) at hVs
  change heap.Room initial gpt.module (48 + 8 * (rows.toNat + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pm, .i64 pv, .i64 rows, .i64 cols]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  show Triple _ (.buildWith 4 5 6 (.get 2)
      (.seq (.assign 7 (.constF 0)) (.loop 8 9 (.get 3) rowBody)) (.toBits (.getF 7))) 11
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [7, 8, 9, 10]) (n := rows)
    (fun r => (row m v cols r).toBits) hMemory32 hImports hAlloc (by decide) (by decide)
    (by decide) (by simp [start]) hHeap hRoom ⟨start, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · -- One element: the accumulator, then the loop over the row.
    intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 8 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 4 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hM := hAt pm _ hMs
    have hV := hAt pv _ hVs
    let s1 := state.update 7 (.f64 0)
    have hS1 : s1.params.length = 4 ∧ s1.locals.length = 8 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 7 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [7]) (writes := [7, 10]) (init := (0.0 : Float)) (n := cols)
      (rowStep m v cols (UInt64.ofNat k)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 3 (by decide), hGet 3 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 4 ∧ st.locals.length = 8 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 4 ∨ j = 6 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g7 : st.get 7 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := rowBody_run hM hV hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 6 (by omega)).trans hIndex) g7 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' t ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' t ⟨rfl, hFrameL, hHolds⟩
      have g7 : t.get 7 = some (.f64 (row m v cols (UInt64.ofNat k)).toBits) :=
        (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), t, by simp [Expr.eval, g7]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨pm, rfl, hNew.borrowed pm _ hMs⟩, _, _, rfl,
      ⟨pv, rfl, hNew.borrowed pv _ hVs⟩, rfl⟩, hNew.top, hNew.pages, hNew.caps, hNew.borrowed,
    fun p ws h => (hNew.ownedKeep p ws h).1, [.i64 ptr], state,
    by simp [gpt.matVec.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ptr, rfl, ?_⟩
  rw [matVecTuple, matVec_eq, build_map]
  exact hNew.owned

/-- `encode` succeeds on `gpt.module`, and its bytes decode to a module whose
exports compute the kernels exactly. -/
theorem gpt_bytes : ∃ bytes, Encoding.encode gpt.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 dotTuple (fun _ => 0) ∧
      Implements m 4 matVecTuple matVecNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip gpt.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, gpt.module, decoded, dot_implements, matVec_implements⟩

end Project.Gpt
