import Project.Gpt.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Run
import Project.IR.Call
import Project.IR.Release
import Project.IR.Live
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
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.matVec.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  rw [matVecTuple, matVec_eq, build_map]
  exact hNew.owned

/-- `layerNorm` with its four arguments as one tuple. -/
def layerTuple (x : Array Float × Array Float × Array Float × Float) : Array Float :=
  LeanExe.Examples.Gpt.layerNorm x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `layerNorm` may allocate: one array as long as `xs`. -/
def layerNeed (x : Array Float × Array Float × Array Float × Float) : Nat :=
  48 + 8 * (x.1.size + 1)

/-- One step of the sum loop. -/
def sumStep (xs : Array Float) (i : UInt64) (acc : Float) : Float := acc + xs[i.toNat]!

/-- One step of the variance loop. -/
def varStep (xs : Array Float) (mean : Float) (i : UInt64) (acc : Float) : Float :=
  acc + (xs[i.toNat]! - mean) * (xs[i.toNat]! - mean)

/-- Element `i` of the result. -/
def layerElement (xs g b : Array Float) (mean inv : Float) (i : UInt64) : Float :=
  (xs[i.toNat]! - mean) * inv * g[i.toNat]! + b[i.toNat]!

theorem layerNorm_eq (xs g b : Array Float) (eps : Float) :
    LeanExe.Examples.Gpt.layerNorm xs g b eps =
      LeanExe.build xs.size.toUInt64 (layerElement xs g b
        (LeanExe.loop xs.size.toUInt64 0.0 (sumStep xs) / xs.size.toUInt64.toFloat)
        (1.0 / (LeanExe.loop xs.size.toUInt64 0.0 (varStep xs
          (LeanExe.loop xs.size.toUInt64 0.0 (sumStep xs) / xs.size.toUInt64.toFloat)) /
            xs.size.toUInt64.toFloat + eps).sqrt)) := rfl

/-- The compiled body of the sum loop. -/
def sumBody : Stmt :=
  .seq (.assign 10 (.binF .add (.getF 7) (.ofBits (.read 0 (.get 9))))) (.assign 7 (.getF 10))

/-- The compiled body of the variance loop. -/
def varBody : Stmt :=
  .seq (.assign 16 (.binF .add (.getF 13) (.binF .mul
    (.binF .sub (.ofBits (.read 0 (.get 15))) (.getF 11))
    (.binF .sub (.ofBits (.read 0 (.get 15))) (.getF 11))))) (.assign 13 (.getF 16))

/-- The compiled element of the result. -/
def layerElementIR : Expr .u64 :=
  .toBits (.binF .add (.binF .mul (.binF .mul (.binF .sub (.ofBits (.read 0 (.get 22)))
    (.getF 11)) (.getF 18)) (.ofBits (.read 1 (.get 22)))) (.ofBits (.read 2 (.get 22))))

theorem sumBody_run {initial : Store Unit} {px : UInt64} {xs : Array Float}
    (hX : UInt64Array.At initial px (xs.map Float.toBits)) {state : State} {k : Nat}
    {acc : Float} (hParams : state.params.length = 4) (hLocals : state.locals.length = 20)
    (h0 : state.get 0 = some (.i64 px)) (h7 : state.get 7 = some (.f64 acc.toBits))
    (h9 : state.get 9 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, sumBody.run initial.mem 23 state = some final ∧
      State.Frame 23 [7, 10] state final ∧
      final.Holds [7] (Scalar.values (sumStep xs (UInt64.ofNat k) acc)) := by
  simp [sumBody, Stmt.run, Expr.eval, h0, h7, h9, Expr.readValue_at hX, State.set?_eq_update,
    hParams, hLocals, F64Op.apply, getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, sumStep, hParams, hLocals, F64Bits.toBits_add]

theorem varBody_run {initial : Store Unit} {px : UInt64} {xs : Array Float}
    (hX : UInt64Array.At initial px (xs.map Float.toBits)) {state : State} {k : Nat}
    {acc mean : Float} (hParams : state.params.length = 4) (hLocals : state.locals.length = 20)
    (h0 : state.get 0 = some (.i64 px)) (h11 : state.get 11 = some (.f64 mean.toBits))
    (h13 : state.get 13 = some (.f64 acc.toBits))
    (h15 : state.get 15 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, varBody.run initial.mem 23 state = some final ∧
      State.Frame 23 [13, 16] state final ∧
      final.Holds [13] (Scalar.values (varStep xs mean (UInt64.ofNat k) acc)) := by
  simp [varBody, Stmt.run, Expr.eval, h0, h11, h13, h15, Expr.readValue_at hX,
    State.set?_eq_update, hParams, hLocals, F64Op.apply, getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, varStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul, F64Bits.toBits_sub]

theorem layerNorm_implements : Implements gpt.module 5 layerTuple layerNeed := by
  refine Func.implements_heap gpt.funcs 2 gpt.layerNorm.ir "layerNorm" rfl layerTuple layerNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨xs, g, b, eps⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pg, rfl, hGs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hRoom
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
  change heap.Borrowed initial pg (g.map Float.toBits) at hGs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  change heap.Room initial gpt.module (48 + 8 * (xs.size + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  have hX := hXs.values
  have hFit := hX.1
  simp only [Array.size_map] at hFit
  have hLength := hX.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hn : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  let start : State :=
    { params := [.i64 px, .i64 pg, .i64 pb, .f64 eps.toBits]
      locals := [.i64 0, .f64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .f64 0, .i64 0, .f64 0,
        .i64 0, .i64 0, .f64 0, .f64 0, .f64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.seq (.arraySize 4 0) (.seq (.assign 5 (.convertU (.get 4)))
    (.seq (.arraySize 6 0) (.seq (.assign 7 (.constF 0)) (.seq (.loop 8 9 (.get 6) sumBody)
    (.seq (.assign 11 (.binF .div (.getF 7) (.getF 5))) (.seq (.arraySize 12 0)
    (.seq (.assign 13 (.constF 0)) (.seq (.loop 14 15 (.get 12) varBody)
    (.seq (.assign 17 (.binF .div (.getF 13) (.getF 5)))
    (.seq (.assign 18 (.binF .div (.constF 4607182418800017408)
      (.unF .sqrt (.binF .add (.getF 17) (.getF 3)))))
    (.seq (.arraySize 19 0) (.build 20 21 22 (.get 19) layerElementIR))))))))))))) 23
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 4 := rfl
  have hLocals : start.locals.length = 20 := rfl
  have hGet0 : start.get 0 = some (.i64 px) := rfl
  -- The count as a float, and the sum loop.
  let n : Float := xs.size.toUInt64.toFloat
  let s1 := start.update 4 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 5 (.f64 n.toBits)
  let s3 := s2.update 6 (.i64 (UInt64.ofNat xs.size))
  let s4 := s3.update 7 (.f64 0)
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hX.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, n,
      F64Convert.toBits_toFloat]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hX.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1, s2, s3]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, s4]
  have hS4 : s4.params.length = 4 ∧ s4.locals.length = 20 := by
    simp [s4, s3, s2, s1, hParams, hLocals]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [7]) (writes := [7, 10]) (init := (0.0 : Float))
    (n := xs.size.toUInt64) (sumStep xs)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hS4.1, hS4.2]) ⟨s4, by simp [Expr.eval, s4, s3, s2, s1, hParams, hLocals]⟩
    (by simp [State.Holds, Scalar.values, s4, s3, s2, s1, hParams, hLocals, hZero]) ?_) ?_
  · intro k acc state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 4 ∧ state.locals.length = 20 :=
      ⟨hFrame.params.trans hS4.1, hFrame.locals.trans hS4.2⟩
    have h0 : state.get 0 = some (.i64 px) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s4, s3, s2, s1, hGet0])
    have h7 : state.get 7 = some (.f64 acc.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      sumBody_run hX hState.1 hState.2 h0 h7 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  apply Triple.of_forall
  rintro store t1 ⟨hStore, hFrame1, hHolds1⟩
  subst store
  generalize hSum : LeanExe.loop xs.size.toUInt64 0.0 (sumStep xs) = total at hHolds1
  have h1Get7 : t1.get 7 = some (.f64 total.toBits) := (List.forall₂_cons.mp hHolds1).1
  have hT1 : t1.params.length = 4 ∧ t1.locals.length = 20 :=
    ⟨hFrame1.params.trans hS4.1, hFrame1.locals.trans hS4.2⟩
  have hT1Get : ∀ j, j < 23 → j ∉ [8, 9, 7, 10] → t1.get j = s4.get j :=
    fun j hj hOut => hFrame1.get j hj hOut
  have h1Get0 : t1.get 0 = some (.i64 px) := (hT1Get 0 (by decide) (by decide)).trans rfl
  have h1Get5 : t1.get 5 = some (.f64 n.toBits) :=
    (hT1Get 5 (by decide) (by decide)).trans (by simp [s4, s3, s2, s1, hParams, hLocals])
  -- The mean and the variance loop.
  let mean := total / n
  let u1 := t1.update 11 (.f64 mean.toBits)
  let u2 := u1.update 12 (.i64 (UInt64.ofNat xs.size))
  let u3 := u2.update 13 (.f64 0)
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u3) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get7, h1Get5, State.set?_eq_update, hT1.1, hT1.2, u1, mean,
      F64Op.apply, F64Bits.toBits_div]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get0, hLength, hX.lengthRead,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hT1.1, hT1.2, u1, u2, u3]
  have hU3 : u3.params.length = 4 ∧ u3.locals.length = 20 := by simp [u3, u2, u1, hT1.1, hT1.2]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [13]) (writes := [13, 16])
    (init := (0.0 : Float)) (n := xs.size.toUInt64) (varStep xs mean)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hU3.1, hU3.2]) ⟨u3, by simp [Expr.eval, u3, u2, u1, hT1.1, hT1.2]⟩
    (by simp [State.Holds, Scalar.values, u3, u2, u1, hT1.1, hT1.2, hZero]) ?_) ?_
  · intro k acc state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 4 ∧ state.locals.length = 20 :=
      ⟨hFrame.params.trans hU3.1, hFrame.locals.trans hU3.2⟩
    have h0 : state.get 0 = some (.i64 px) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get0])
    have h11 : state.get 11 = some (.f64 mean.toBits) :=
      (hFrame.get 11 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
    have h13 : state.get 13 = some (.f64 acc.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      varBody_run hX hState.1 hState.2 h0 h11 h13 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  apply Triple.of_forall
  rintro store t2 ⟨hStore, hFrame2, hHolds2⟩
  subst store
  generalize hVar : LeanExe.loop xs.size.toUInt64 0.0 (varStep xs mean) = spread at hHolds2
  have h2Get13 : t2.get 13 = some (.f64 spread.toBits) := (List.forall₂_cons.mp hHolds2).1
  have hT2 : t2.params.length = 4 ∧ t2.locals.length = 20 :=
    ⟨hFrame2.params.trans hU3.1, hFrame2.locals.trans hU3.2⟩
  have hT2Get : ∀ j, j < 23 → j ∉ [14, 15, 13, 16] → t2.get j = u3.get j :=
    fun j hj hOut => hFrame2.get j hj hOut
  have h2Get0 : t2.get 0 = some (.i64 px) :=
    (hT2Get 0 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get0])
  have h2Get1 : t2.get 1 = some (.i64 pg) :=
    (hT2Get 1 (by decide) (by decide)).trans
      (by simp [u3, u2, u1]; exact (hT1Get 1 (by decide) (by decide)).trans rfl)
  have h2Get2 : t2.get 2 = some (.i64 pb) :=
    (hT2Get 2 (by decide) (by decide)).trans
      (by simp [u3, u2, u1]; exact (hT1Get 2 (by decide) (by decide)).trans rfl)
  have h2Get3 : t2.get 3 = some (.f64 eps.toBits) :=
    (hT2Get 3 (by decide) (by decide)).trans
      (by simp [u3, u2, u1]; exact (hT1Get 3 (by decide) (by decide)).trans rfl)
  have h2Get5 : t2.get 5 = some (.f64 n.toBits) :=
    (hT2Get 5 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get5])
  have h2Get11 : t2.get 11 = some (.f64 mean.toBits) :=
    (hT2Get 11 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
  -- The variance, the inverse deviation, and the result.
  let inv := 1.0 / (spread / n + eps).sqrt
  let v1 := t2.update 17 (.f64 (spread / n).toBits)
  let v2 := v1.update 18 (.f64 inv.toBits)
  let v3 := v2.update 19 (.i64 (UInt64.ofNat xs.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := v1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := v2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := v3) ?_) ?_
  · simp [Stmt.run, Expr.eval, h2Get13, h2Get5, State.set?_eq_update, hT2.1, hT2.2, v1,
      F64Op.apply, F64Bits.toBits_div]
  · simp [Stmt.run, Expr.eval, h2Get3, State.set?_eq_update, hT2.1, hT2.2, v1, v2, inv,
      F64Op.apply, F64UnOp.apply, F64Bits.toBits_div, F64Bits.toBits_sqrt, F64Bits.toBits_add,
      hOne]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h2Get0, hLength, hX.lengthRead,
      State.set?_eq_update, hT2.1, hT2.2, v1, v2, v3]
  have hV3 : v3.params.length = 4 ∧ v3.locals.length = 20 := by simp [v3, v2, v1, hT2.1, hT2.2]
  have hV3Get : ∀ j, j < 17 → v3.get j = t2.get j := fun j hj => by
    simp only [v3, v2, v1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega),
      State.get_update_ne (by omega)]
  have h3Get18 : v3.get 18 = some (.f64 inv.toBits) := by simp [v3, v2, v1, hT2.1, hT2.2]
  refine (Stmt.build_spec (n := xs.size.toUInt64)
    (fun i => (layerElement xs g b mean inv i).toBits) hMemory32 hImports hAlloc (by decide)
    (by decide) (by simp [hV3.1, hV3.2]) hHeap (by rw [show xs.size.toUInt64.toNat = xs.size from hn]; exact hRoom)
    ⟨v3, by simp [Expr.eval, v3, v2, v1, hT2.1, hT2.2]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 20 :=
      ⟨hFrame.params.trans hV3.1, hFrame.locals.trans hV3.2⟩
    have hKeep : ∀ j, j < 20 → state.get j = v3.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 := (hKeep 0 (by decide)).trans ((hV3Get 0 (by decide)).trans h2Get0)
    have g1 := (hKeep 1 (by decide)).trans ((hV3Get 1 (by decide)).trans h2Get1)
    have g2 := (hKeep 2 (by decide)).trans ((hV3Get 2 (by decide)).trans h2Get2)
    have g11 := (hKeep 11 (by decide)).trans ((hV3Get 11 (by decide)).trans h2Get11)
    have g18 := (hKeep 18 (by decide)).trans h3Get18
    exact ⟨state.update 23 (.i64 (UInt64.ofNat k)), by simp [layerElementIR, Expr.eval, g0, g1,
      g2, g11, g18, hIndex,
      Expr.readValue_at (hAt px _ hXs), Expr.readValue_at (hAt pg _ hGs),
      Expr.readValue_at (hAt pb _ hBs), State.set?_eq_update, hState.1, hState.2, F64Op.apply,
      getElem!_map_toBits, layerElement, F64Bits.toBits_add, F64Bits.toBits_mul,
      F64Bits.toBits_sub]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨px, rfl, hNew.borrowed px _ hXs⟩, _, _, rfl,
      ⟨pg, rfl, hNew.borrowed pg _ hGs⟩, _, _, rfl, ⟨pb, rfl, hNew.borrowed pb _ hBs⟩, rfl⟩,
    le_of_le_of_eq hNew.top (by simp [layerNeed, hn]),
    le_of_le_of_eq hNew.pages (by simp [layerNeed, hn]), hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.layerNorm.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  rw [layerTuple, layerNorm_eq, hSum, hVar, build_map]
  exact hNew.owned

/-- `exp` keeps the store, so calls to it may run in loop bodies and array
elements. -/
theorem exp_pure : ImplementsPure gpt.module 6 LeanExe.Examples.Gpt.exp := by
  refine Func.implementsPure gpt.funcs 3 gpt.exp.ir "exp" rfl LeanExe.Examples.Gpt.exp
    (fun _ => rfl) fun x initial => ?_
  have k745 : (745.2 : Float).toBits = 4649766064339130778 := by decide +kernel
  have k709 : (709.8 : Float).toBits = 4649454682646144614 := by decide +kernel
  have kInv : (1.4426950408889634 : Float).toBits = 4609176140021203710 := by decide +kernel
  have kHalf : (1100.5 : Float).toBits = 4652554865631821824 := by decide +kernel
  have kBias : (1100.0 : Float).toBits = 4652552666608566272 := by decide +kernel
  have kHi : (0.6931471803691238 : Float).toBits = 4604418534311723008 := by decide +kernel
  have kLo : (1.9082149292705877e-10 : Float).toBits = 4461442080421002358 := by decide +kernel
  have c0 : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  have c2 : (0.5 : Float).toBits = 4602678819172646912 := by decide +kernel
  have c3 : (0.16666666666666666 : Float).toBits = 4595172819793696085 := by decide +kernel
  have c4 : (0.041666666666666664 : Float).toBits = 4586165620538955093 := by decide +kernel
  have c5 : (0.008333333333333333 : Float).toBits = 4575957461383581969 := by decide +kernel
  have c6 : (0.001388888888888889 : Float).toBits = 4564047942368979991 := by decide +kernel
  have c7 : (1.984126984126984e-4 : Float).toBits = 4551452160554016794 := by decide +kernel
  have c8 : (2.48015873015873e-5 : Float).toBits = 4537941361671905306 := by decide +kernel
  have c9 : (2.7557319223985893e-6 : Float).toBits = 4523617214285662004 := by decide +kernel
  have c10 : (2.755731922398589e-7 : Float).toBits = 4508805057796939612 := by decide +kernel
  have c11 : (2.505210838544172e-8 : Float).toBits = 4493156764026750180 := by decide +kernel
  have c12 : (2.08767569878681e-9 : Float).toBits = 4477122120089393304 := by decide +kernel
  have c13 : (1.6059043836821613e-10 : Float).toBits = 4460272573143870729 := by decide +kernel
  have kBig : (1e308 : Float).toBits = 9214871658872686752 := by decide +kernel
  have kZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let c := max (-745.2) (min x 709.8)
  let m := (c * 1.4426950408889634 + 1100.5).toUInt64
  let kf := m.toFloat - 1100.0
  let r := c - kf * 0.6931471803691238 - kf * 1.9082149292705877e-10
  let p := 1.0 + r * (1.0 + r * (0.5 + r * (0.16666666666666666 + r * (0.041666666666666664 +
    r * (0.008333333333333333 + r * (0.001388888888888889 + r * (1.984126984126984e-4 +
    r * (2.48015873015873e-5 + r * (2.7557319223985893e-6 + r * (2.755731922398589e-7 +
    r * (2.505210838544172e-8 + r * (2.08767569878681e-9 + r * 1.6059043836821613e-10))))))))))))
  let hm := m / 2
  let y := p * Float.ofBits ((hm + 473) <<< 52) * Float.ofBits ((m - hm + 473) <<< 52)
  let start : State :=
    { params := [.f64 x.toBits]
      locals := [.f64 0, .i64 0, .f64 0, .f64 0, .f64 0, .i64 0, .f64 0, .i64 0, .i64 0] }
  let s1 := start.update 1 (.f64 c.toBits)
  let s2 := s1.update 2 (.i64 m)
  let s3 := s2.update 3 (.f64 kf.toBits)
  let s4 := s3.update 4 (.f64 r.toBits)
  let s5 := s4.update 5 (.f64 p.toBits)
  let s6 := ((s5.update 8 (.i64 m)).update 9 (.i64 2)).update 6 (.i64 hm)
  let s7 := s6.update 7 (.f64 y.toBits)
  have hParams : start.params.length = 1 := rfl
  have hLocals : start.locals.length = 9 := rfl
  have hGet0 : start.get 0 = some (.f64 x.toBits) := rfl
  show Triple _ (.seq (.assign 1 (.iteF (.leF (.binF .sub (.constF 9223372036854775808)
      (.constF 4649766064339130778)) (.iteF (.leF (.getF 0) (.constF 4649454682646144614))
      (.getF 0) (.constF 4649454682646144614))) (.iteF (.leF (.getF 0)
      (.constF 4649454682646144614)) (.getF 0) (.constF 4649454682646144614))
      (.binF .sub (.constF 9223372036854775808) (.constF 4649766064339130778))))
    (.seq (.assign 2 (.truncSatU (.binF .add (.binF .mul (.getF 1)
      (.constF 4609176140021203710)) (.constF 4652554865631821824))))
    (.seq (.assign 3 (.binF .sub (.convertU (.get 2)) (.constF 4652552666608566272)))
    (.seq (.assign 4 (.binF .sub (.binF .sub (.getF 1) (.binF .mul (.getF 3)
      (.constF 4604418534311723008))) (.binF .mul (.getF 3) (.constF 4461442080421002358))))
    (.seq (.assign 5 (.binF .add (.constF 4607182418800017408) (.binF .mul (.getF 4)
      (.binF .add (.constF 4607182418800017408) (.binF .mul (.getF 4)
      (.binF .add (.constF 4602678819172646912) (.binF .mul (.getF 4)
      (.binF .add (.constF 4595172819793696085) (.binF .mul (.getF 4)
      (.binF .add (.constF 4586165620538955093) (.binF .mul (.getF 4)
      (.binF .add (.constF 4575957461383581969) (.binF .mul (.getF 4)
      (.binF .add (.constF 4564047942368979991) (.binF .mul (.getF 4)
      (.binF .add (.constF 4551452160554016794) (.binF .mul (.getF 4)
      (.binF .add (.constF 4537941361671905306) (.binF .mul (.getF 4)
      (.binF .add (.constF 4523617214285662004) (.binF .mul (.getF 4)
      (.binF .add (.constF 4508805057796939612) (.binF .mul (.getF 4)
      (.binF .add (.constF 4493156764026750180) (.binF .mul (.getF 4)
      (.binF .add (.constF 4477122120089393304) (.binF .mul (.getF 4)
      (.constF 4460272573143870729))))))))))))))))))))))))))))
    (.seq (.assign 6 (.bin .divU (.get 2) (.const 2)))
    (.assign 7 (.binF .mul (.binF .mul (.getF 5) (.ofBits (.bin .shiftLeft (.bin .add (.get 6)
      (.const 473)) (.const 52)))) (.ofBits (.bin .shiftLeft (.bin .add (.bin .sub (.get 2)
      (.get 6)) (.const 473)) (.const 52))))))))))) 8
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s5) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s6) ?_) <|
    (Stmt.run_spec (final := s7) ?_).mono (fun _ _ h => h) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, hGet0, s1, c, F64Op.apply,
      F64Bits.toBits_max, F64Bits.toBits_min, F64Bits.toBits_neg, k745, k709]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, m, F64Op.apply,
      F64Convert.toUInt64_eq, F64Bits.toBits_add, F64Bits.toBits_mul, kInv, kHalf]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, kf,
      F64Op.apply, F64Bits.toBits_sub, F64Convert.toBits_toFloat, kBias]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, s4, r,
      F64Op.apply, F64Bits.toBits_sub, F64Bits.toBits_mul, kHi, kLo]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, s4, s5, p,
      F64Op.apply, F64Bits.toBits_add, F64Bits.toBits_mul, c0, c2, c3, c4, c5, c6, c7, c8, c9,
      c10, c11, c12, c13]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, s4, s5, s6,
      hm, U64Op.apply]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3, s4, s5, s6,
      s7, y, U64Op.apply, F64Op.apply, F64Bits.toBits_mul, F64Bits.toBits_ofBits,
      F64Bits.shiftLeft_52_not_nan]
  rintro store state ⟨rfl, rfl⟩
  have hExp : LeanExe.Examples.Gpt.exp x =
      if x == x then (if x > 709.8 then x * 1e308 else if x < -745.2 then 0.0 else y) else x :=
    rfl
  refine ⟨rfl, [.f64 (LeanExe.Examples.Gpt.exp x).toBits], s7, ?_, rfl⟩
  have g0 : s7.get 0 = some (.f64 x.toBits) := by simp [s7, s6, s5, s4, s3, s2, s1]; rfl
  have g7 : s7.get 7 = some (.f64 y.toBits) := by simp [s7, s6, s5, s4, s3, s2, s1, hParams, hLocals]
  rw [hExp]
  simp only [gpt.exp.ir, Func.scratch, Expr.evalResults, Expr.eval, g0, g7, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, F64Op.apply]
  by_cases h1 : x == x <;> by_cases h2 : x > 709.8 <;> by_cases h3 : x < -745.2 <;>
    simp_all [F64Bits.beq_eq, F64Bits.lt_iff, F64Bits.toBits_mul, F64Bits.toBits_neg]

theorem exp_implements : Implements gpt.module 6 LeanExe.Examples.Gpt.exp (fun _ => 0) :=
  exp_pure.implements

/-- `softmax` with its argument. -/
def softmaxNeed (xs : Array Float) : Nat := 48 + 8 * (xs.size + 1)

/-- One step of the maximum loop. -/
def maxStep (xs : Array Float) (i : UInt64) (acc : Float) : Float := max acc xs[i.toNat]!

/-- One step of the loop that sums the exponentials. -/
def expSumStep (xs : Array Float) (mx : Float) (i : UInt64) (acc : Float) : Float :=
  acc + LeanExe.Examples.Gpt.exp (xs[i.toNat]! - mx)

theorem softmax_eq (xs : Array Float) :
    LeanExe.Examples.Gpt.softmax xs =
      LeanExe.build xs.size.toUInt64 (fun i =>
        LeanExe.Examples.Gpt.exp (xs[i.toNat]! -
            LeanExe.loop xs.size.toUInt64 (-(1.0 / 0.0)) (maxStep xs)) /
          LeanExe.loop xs.size.toUInt64 0.0
            (expSumStep xs (LeanExe.loop xs.size.toUInt64 (-(1.0 / 0.0)) (maxStep xs)))) := rfl

/-- The compiled body of the maximum loop. -/
def maxBody : Stmt :=
  .seq (.assign 5 (.iteF (.leF (.getF 2) (.ofBits (.read 0 (.get 4))))
    (.ofBits (.read 0 (.get 4))) (.getF 2))) (.assign 2 (.getF 5))

/-- The compiled body of the loop that sums the exponentials. -/
def expSumBody : Stmt :=
  .seq (.call 6 [⟨.f64, .binF .sub (.ofBits (.read 0 (.get 10))) (.getF 6)⟩] [11])
    (.seq (.assign 12 (.binF .add (.getF 8) (.getF 11))) (.assign 8 (.getF 12)))

theorem maxBody_run {initial : Store Unit} {px : UInt64} {xs : Array Float}
    (hX : UInt64Array.At initial px (xs.map Float.toBits)) {state : State} {k : Nat}
    {acc : Float} (hParams : state.params.length = 1) (hLocals : state.locals.length = 19)
    (h0 : state.get 0 = some (.i64 px)) (h2 : state.get 2 = some (.f64 acc.toBits))
    (h4 : state.get 4 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, maxBody.run initial.mem 19 state = some final ∧
      State.Frame 19 [2, 5] state final ∧
      final.Holds [2] (Scalar.values (maxStep xs (UInt64.ofNat k) acc)) := by
  simp [maxBody, Stmt.run, Expr.eval, h0, h2, h4, Expr.readValue_at hX, State.set?_eq_update,
    hParams, hLocals, getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, maxStep, hParams, hLocals, F64Bits.toBits_max]

/-- The call to `exp` in `softmax`, entry 6 of the module. -/
theorem exp_call {scratch : Nat} {args : List ((type : ScalarType) × Expr type)}
    {results : List Nat} (hParams : args.length = 1) {initial : Store Unit}
    {before afterArgs next : State} {d : Float}
    (hArgs : Expr.evalResults initial.mem scratch args before = some ([.f64 d.toBits], afterArgs))
    (hSet : afterArgs.setAll results.reverse [.f64 (LeanExe.Examples.Gpt.exp d).toBits] =
      some next) :
    Triple gpt.module (.call 6 args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) :=
  Stmt.callPure_spec exp_pure (f := gpt.exp.ir.function (2 + 3)) rfl
    (by rw [show gpt.module.imports.length = 0 from rfl]
        exact compile_funcs (funcs := gpt.funcs) (i := 3) rfl) hParams (x := d) hArgs hSet

theorem expSumBody_spec {initial : Store Unit} {px : UInt64} {xs : Array Float} {mx : Float}
    (hX : UInt64Array.At initial px (xs.map Float.toBits)) {state : State} {k : Nat}
    {acc : Float} (hParams : state.params.length = 1) (hLocals : state.locals.length = 19)
    (h0 : state.get 0 = some (.i64 px)) (h6 : state.get 6 = some (.f64 mx.toBits))
    (h8 : state.get 8 = some (.f64 acc.toBits))
    (h10 : state.get 10 = some (.i64 (UInt64.ofNat k))) :
    Triple gpt.module expSumBody 19 (fun store st => store = initial ∧ st = state)
      (fun store st => store = initial ∧ State.Frame 19 [8, 11, 12] state st ∧
        st.Holds [8] (Scalar.values (expSumStep xs mx (UInt64.ofNat k) acc))) := by
  let d := xs[(UInt64.ofNat k).toNat]! - mx
  let e := LeanExe.Examples.Gpt.exp d
  let a := state.update 19 (.i64 (UInt64.ofNat k))
  let b := a.update 11 (.f64 e.toBits)
  let c := b.update 12 (.f64 (acc + e).toBits)
  let f := c.update 8 (.f64 (acc + e).toBits)
  have hA : a.params.length = 1 ∧ a.locals.length = 19 := by simp [a, hParams, hLocals]
  have hB : b.params.length = 1 ∧ b.locals.length = 19 := by simp [b, hA.1, hA.2]
  refine Stmt.seq_spec (exp_call rfl (afterArgs := a) (next := b) (d := d) ?_ ?_) ?_
  · simp [Expr.evalResults, Expr.eval, h0, h6, h10, Expr.readValue_at hX, State.set?_eq_update,
      hParams, hLocals, F64Op.apply, getElem!_map_toBits, d, a, F64Bits.toBits_sub]
  · simp [State.setAll, State.set?_eq_update, b, e, hA.1, hA.2]
  refine (Stmt.run_spec (final := f) ?_).mono (fun _ _ h => h) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hB.1, hB.2, b, a, c, f, h8, hParams,
      hLocals, F64Op.apply, F64Bits.toBits_add]
  rintro s st ⟨rfl, rfl⟩
  refine ⟨rfl, ?_, ?_⟩
  · simp only [f, c, b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, expSumStep, f, c, b, a, hParams, hLocals, d, e]

theorem softmax_implements :
    Implements gpt.module 7 LeanExe.Examples.Gpt.softmax softmaxNeed := by
  refine Func.implements_heap gpt.funcs 4 gpt.softmax.ir "softmax" rfl
    LeanExe.Examples.Gpt.softmax softmaxNeed (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨px, rfl, hXs⟩ hRoom
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
  change heap.Room initial gpt.module (48 + 8 * (xs.size + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  have hX := hXs.values
  have hFit := hX.1
  simp only [Array.size_map] at hFit
  have hLength := hX.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hn : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  let start : State :=
    { params := [.i64 px]
      locals := [.i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .f64 0, .i64 0, .f64 0, .i64 0, .i64 0,
        .f64 0, .f64 0, .f64 0, .i64 0, .i64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  show Triple _ (.seq (.arraySize 1 0) (.seq (.assign 2 (.binF .sub (.constF 9223372036854775808)
    (.binF .div (.constF 4607182418800017408) (.constF 0))))
    (.seq (.loop 3 4 (.get 1) maxBody) (.seq (.assign 6 (.getF 2)) (.seq (.arraySize 7 0)
    (.seq (.assign 8 (.constF 0)) (.seq (.loop 9 10 (.get 7) expSumBody)
    (.seq (.assign 13 (.getF 8)) (.seq (.arraySize 14 0)
    (.buildWith 15 16 17 (.get 14)
      (.call 6 [⟨.f64, .binF .sub (.ofBits (.read 0 (.get 17))) (.getF 6)⟩] [18])
      (.toBits (.binF .div (.getF 18) (.getF 13))))))))))))) 19
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 1 := rfl
  have hLocals : start.locals.length = 19 := rfl
  have hGet0 : start.get 0 = some (.i64 px) := rfl
  -- The maximum.
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 2 (.f64 (-(1.0 / 0.0) : Float).toBits)
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hX.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, F64Op.apply,
      F64Bits.toBits_neg, F64Bits.toBits_div, hZero, hOne]
  have hS2 : s2.params.length = 1 ∧ s2.locals.length = 19 := by
    simp [s2, s1, hParams, hLocals]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [2]) (writes := [2, 5])
    (init := (-(1.0 / 0.0) : Float)) (n := xs.size.toUInt64) (maxStep xs)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hS2.1, hS2.2]) ⟨s2, by simp [Expr.eval, s2, s1, hParams, hLocals]⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hParams, hLocals]) ?_) ?_
  · intro k acc state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 1 ∧ state.locals.length = 19 :=
      ⟨hFrame.params.trans hS2.1, hFrame.locals.trans hS2.2⟩
    have h0 : state.get 0 = some (.i64 px) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have h2 : state.get 2 = some (.f64 acc.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      maxBody_run hX hState.1 hState.2 h0 h2 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  apply Triple.of_forall
  rintro store t1 ⟨hStore, hFrame1, hHolds1⟩
  subst store
  generalize hMax : LeanExe.loop xs.size.toUInt64 (-(1.0 / 0.0)) (maxStep xs) = mx at hHolds1
  have h1Get2 : t1.get 2 = some (.f64 mx.toBits) := (List.forall₂_cons.mp hHolds1).1
  have hT1 : t1.params.length = 1 ∧ t1.locals.length = 19 :=
    ⟨hFrame1.params.trans hS2.1, hFrame1.locals.trans hS2.2⟩
  have h1Get0 : t1.get 0 = some (.i64 px) :=
    (hFrame1.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
  -- The sum of the exponentials.
  let u1 := t1.update 6 (.f64 mx.toBits)
  let u2 := u1.update 7 (.i64 (UInt64.ofNat xs.size))
  let u3 := u2.update 8 (.f64 0)
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u3) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get2, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get0, hLength, hX.lengthRead,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hT1.1, hT1.2, u1, u2, u3]
  have hU3 : u3.params.length = 1 ∧ u3.locals.length = 19 := by simp [u3, u2, u1, hT1.1, hT1.2]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [8]) (writes := [8, 11, 12])
    (init := (0.0 : Float)) (n := xs.size.toUInt64) (expSumStep xs mx)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hU3.1, hU3.2]) ⟨u3, by simp [Expr.eval, u3, u2, u1, hT1.1, hT1.2]⟩
    (by simp [State.Holds, Scalar.values, u3, u2, u1, hT1.1, hT1.2, hZero]) ?_) ?_
  · intro k acc state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 1 ∧ state.locals.length = 19 :=
      ⟨hFrame.params.trans hU3.1, hFrame.locals.trans hU3.2⟩
    have h0 : state.get 0 = some (.i64 px) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get0])
    have h6 : state.get 6 = some (.f64 mx.toBits) :=
      (hFrame.get 6 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
    have h8 : state.get 8 = some (.f64 acc.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    exact expSumBody_spec hX hState.1 hState.2 h0 h6 h8 hIndex
  apply Triple.of_forall
  rintro store t2 ⟨hStore, hFrame2, hHolds2⟩
  subst store
  generalize hSum : LeanExe.loop xs.size.toUInt64 0.0 (expSumStep xs mx) = total at hHolds2
  have h2Get8 : t2.get 8 = some (.f64 total.toBits) := (List.forall₂_cons.mp hHolds2).1
  have hT2 : t2.params.length = 1 ∧ t2.locals.length = 19 :=
    ⟨hFrame2.params.trans hU3.1, hFrame2.locals.trans hU3.2⟩
  have h2Get0 : t2.get 0 = some (.i64 px) :=
    (hFrame2.get 0 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get0])
  have h2Get6 : t2.get 6 = some (.f64 mx.toBits) :=
    (hFrame2.get 6 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
  -- The result.
  let v1 := t2.update 13 (.f64 total.toBits)
  let v2 := v1.update 14 (.i64 (UInt64.ofNat xs.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := v1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := v2) ?_) ?_
  · simp [Stmt.run, Expr.eval, h2Get8, State.set?_eq_update, hT2.1, hT2.2, v1]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h2Get0, hLength, hX.lengthRead,
      State.set?_eq_update, hT2.1, hT2.2, v1, v2]
  have hV2 : v2.params.length = 1 ∧ v2.locals.length = 19 := by simp [v2, v1, hT2.1, hT2.2]
  have hV2Get : ∀ j, j < 13 → v2.get j = t2.get j := fun j hj => by
    simp only [v2, v1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]
  have h3Get13 : v2.get 13 = some (.f64 total.toBits) := by simp [v2, v1, hT2.1, hT2.2]
  refine (Stmt.buildWith_spec (writes := [18]) (n := xs.size.toUInt64)
    (fun i => (LeanExe.Examples.Gpt.exp (xs[i.toNat]! - mx) / total).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by decide) (by simp [hV2.1, hV2.2]) hHeap
    (by rw [show xs.size.toUInt64.toNat = xs.size from hn]; exact hRoom)
    ⟨v2, by simp [Expr.eval, v2, v1, hT2.1, hT2.2]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 1 ∧ state.locals.length = 19 :=
      ⟨hFrame.params.trans hV2.1, hFrame.locals.trans hV2.2⟩
    have hKeep : ∀ j, j < 15 → state.get j = v2.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 := (hKeep 0 (by decide)).trans ((hV2Get 0 (by decide)).trans h2Get0)
    have g6 := (hKeep 6 (by decide)).trans ((hV2Get 6 (by decide)).trans h2Get6)
    have g13 := (hKeep 13 (by decide)).trans h3Get13
    let d := xs[(UInt64.ofNat k).toNat]! - mx
    let a := state.update 19 (.i64 (UInt64.ofNat k))
    let b := a.update 18 (.f64 (LeanExe.Examples.Gpt.exp d).toBits)
    have hA : a.params.length = 1 ∧ a.locals.length = 19 := by
      simp [a, hState.1, hState.2]
    refine (exp_call rfl (afterArgs := a) (next := b) (d := d) ?_ ?_).mono (fun _ _ h => h) ?_
    · simp [Expr.evalResults, Expr.eval, g0, g6, hIndex, Expr.readValue_at (hAt px _ hXs),
        State.set?_eq_update, hState.1, hState.2, F64Op.apply, getElem!_map_toBits, d, a,
        F64Bits.toBits_sub]
    · simp [State.setAll, State.set?_eq_update, b, hA.1, hA.2]
    rintro s st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, b, ?_⟩
    · simp only [b, a]
      repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · simp [Expr.eval, g13, b, a, hState.1, hState.2, F64Op.apply, F64Bits.toBits_div, d]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨px, rfl, hNew.borrowed px _ hXs⟩,
    le_of_le_of_eq hNew.top (by simp [softmaxNeed, hn]),
    le_of_le_of_eq hNew.pages (by simp [softmaxNeed, hn]), hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.softmax.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  rw [softmax_eq, hMax, hSum, build_map]
  exact hNew.owned

/-- `matVec2` with its five arguments as one tuple. -/
def matVec2Tuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.matVec2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The bytes `matVec2` may allocate: the temporary and the result. -/
def matVec2Need (x : Array Float × Array Float × Array Float × UInt64 × UInt64) : Nat :=
  48 + 8 * (x.2.2.2.1.toNat + 1) + (48 + 8 * (x.2.2.2.2.toNat + 1))

theorem matVec2_implements : Implements gpt.module 8 matVec2Tuple matVec2Need := by
  refine Func.implements_heap gpt.funcs 5 gpt.matVec2.ir "matVec2" rfl matVec2Tuple matVec2Need
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨w1, w2, x, hidden, d⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨p1, rfl, hW1⟩, _, _, rfl, ⟨p2, rfl, hW2⟩, _, _, rfl, ⟨px, rfl, hX⟩, rfl⟩ hRoom
  change heap.Borrowed initial p1 (w1.map Float.toBits) at hW1
  change heap.Borrowed initial p2 (w2.map Float.toBits) at hW2
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  change heap.Room initial gpt.module
    (48 + 8 * (hidden.toNat + 1) + (48 + 8 * (d.toNat + 1))) at hRoom
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[2]? = some (releaseFunction 1) := rfl
  have hMatVec : gpt.module.funcs[4 - gpt.module.imports.length]? =
      some (gpt.matVec.ir.function (2 + 1)) := compile_funcs (funcs := gpt.funcs) (i := 1) rfl
  let start : State :=
    { params := [.i64 p1, .i64 p2, .i64 px, .i64 hidden, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 8 := rfl
  have hGet : start.get 0 = some (.i64 p1) ∧ start.get 1 = some (.i64 p2) ∧
      start.get 2 = some (.i64 px) ∧ start.get 3 = some (.i64 hidden) ∧
      start.get 4 = some (.i64 d) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  show Triple _ (.seq (.call 4 [⟨.u64, .get 0⟩, ⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [5])
    (.seq (.call 4 [⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 3⟩] [6])
      (.seq (.assign 7 (.get 6)) (.release 5)))) 8
    (fun store state => store = initial ∧ state = start) _
  -- The temporary: `w1 · x`.
  refine Stmt.seq_spec (Live.call matVec_implements rfl hMatVec rfl (Live.start hHeap) hRoom
    (x := (w1, x, hidden, d)) (by simp only [matVecNeed]; omega) (afterArgs := start)
    (vals := [.i64 p1, .i64 px, .i64 hidden, .i64 d])
    (by simp [Expr.evalResults, Expr.eval, hGet.1, hGet.2.2.1, hGet.2.2.2.1, hGet.2.2.2.2])
    ⟨[.i64 p1], _, rfl, ⟨p1, rfl, hW1⟩, [.i64 px], _, rfl, ⟨px, rfl, hX⟩, rfl⟩
    (by rw [hStart]; decide)) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨heap1, ph, hLive1, rfl⟩
  have hT1 : (start.update 5 (.i64 ph)).params.length +
      (start.update 5 (.i64 ph)).locals.length = 8 := by simp [start]
  have hU : ∀ j, j ≠ 5 → (start.update 5 (.i64 ph)).get j = start.get j :=
    fun j hj => State.get_update_ne hj
  have hU5 : (start.update 5 (.i64 ph)).get 5 = some (.i64 ph) :=
    State.get_update_same (by rw [hStart]; decide)
  -- The result: `w2 · h`.
  refine Stmt.seq_spec (Live.call matVec_implements rfl hMatVec rfl hLive1 hRoom
    (x := (w2, matVecTuple (w1, x, hidden, d), d, hidden)) (by simp only [matVecNeed]; omega)
    (afterArgs := start.update 5 (.i64 ph)) (vals := [.i64 p2, .i64 ph, .i64 d, .i64 hidden])
    (by simp [Expr.evalResults, Expr.eval, hU 1 (by decide), hU 4 (by decide),
      hU 3 (by decide), hU5, hGet.2.1, hGet.2.2.2.1, hGet.2.2.2.2])
    ⟨[.i64 p2], _, rfl, ⟨p2, rfl, hLive1.borrowed p2 _ hW2⟩, [.i64 ph], _, rfl,
      ⟨ph, rfl, (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩, rfl⟩
    (by rw [hT1]; decide)) ?_
  apply Triple.of_forall
  rintro store2 t2 ⟨heap2, pr, hLive2, rfl⟩
  -- The result is stored, and the temporary released.
  let t3 := ((start.update 5 (.i64 ph)).update 6 (.i64 pr)).update 7 (.i64 pr)
  refine Stmt.seq_spec (Stmt.run_spec (final := t3) (by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, start, t3])) ?_
  refine (hLive2.releaseSecond hImports hRelease (by simp [t3, start])).mono
    (fun _ _ h => h) ?_
  rintro store3 state3 ⟨hLive3, rfl⟩
  have hParams : ∀ (heap' : Heap) (store' : Store Unit),
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' [.i64 p1, .i64 p2, .i64 px, .i64 hidden, .i64 d]
        (w1, w2, x, hidden, d) := fun heap' store' hKeep =>
    ⟨[.i64 p1], _, rfl, ⟨p1, rfl, hKeep p1 _ hW1⟩, [.i64 p2], _, rfl, ⟨p2, rfl, hKeep p2 _ hW2⟩,
      [.i64 px], _, rfl, ⟨px, rfl, hKeep px _ hX⟩, rfl⟩
  obtain ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLive3.finish (need := matVec2Need (w1, w2, x, hidden, d))
      (by simp only [matVecNeed, matVec2Need]; omega) hParams
  exact ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, [.i64 pr], t3,
    by simp [gpt.matVec2.ir, Func.scratch, Expr.evalResults, Expr.eval, t3, start], hOwned,
    hOutB, hOutO⟩

/-- `matMul` with its five arguments as one tuple. -/
def matMulTuple (x : Array Float × Array Float × UInt64 × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.matMul x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The bytes `matMul` may allocate: one array of `n × m` elements. -/
def matMulNeed (x : Array Float × Array Float × UInt64 × UInt64 × UInt64) : Nat :=
  48 + 8 * ((x.2.2.1 * x.2.2.2.2).toNat + 1)

/-- One step of the loop for element `e`. -/
def cellStep (a b : Array Float) (k m e c : UInt64) (acc : Float) : Float :=
  acc + a[(e / m * k + c).toNat]! * b[(c * m + e % m).toNat]!

/-- Element `e` of the product. -/
def cell (a b : Array Float) (k m e : UInt64) : Float :=
  LeanExe.loop k 0.0 (cellStep a b k m e)

theorem matMul_eq (a b : Array Float) (n k m : UInt64) :
    LeanExe.Examples.Gpt.matMul a b n k m = LeanExe.build (n * m) (cell a b k m) := rfl

/-- The compiled loop body for an element. -/
def cellBody : Stmt :=
  .seq (.assign 11 (.binF .add (.getF 8) (.binF .mul
    (.ofBits (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 7) (.get 4)) (.get 3)) (.get 10))))
    (.ofBits (.read 1 (.bin .add (.bin .mul (.get 10) (.get 4)) (.bin .remU (.get 7) (.get 4))))))))
    (.assign 8 (.getF 11))

theorem cellBody_run {initial : Store Unit} {pa pb : UInt64} {a b : Array Float}
    (hA : UInt64Array.At initial pa (a.map Float.toBits))
    (hB : UInt64Array.At initial pb (b.map Float.toBits))
    {state : State} {c : Nat} {k m e : UInt64} {acc : Float}
    (hParams : state.params.length = 5) (hLocals : state.locals.length = 10)
    (h0 : state.get 0 = some (.i64 pa)) (h1 : state.get 1 = some (.i64 pb))
    (h3 : state.get 3 = some (.i64 k)) (h4 : state.get 4 = some (.i64 m))
    (h7 : state.get 7 = some (.i64 e)) (h8 : state.get 8 = some (.f64 acc.toBits))
    (h10 : state.get 10 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, cellBody.run initial.mem 12 state = some final ∧
      State.Frame 12 [8, 11] state final ∧
      final.Holds [8] (Scalar.values (cellStep a b k m e (UInt64.ofNat c) acc)) := by
  simp [cellBody, Stmt.run, Expr.eval, h0, h1, h3, h4, h7, h8, h10, Expr.readValue_at hA,
    Expr.readValue_at hB, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · by_cases hm : m = 0 <;> simp [State.Holds, Scalar.values, cellStep, hParams, hLocals,
      F64Bits.toBits_add, F64Bits.toBits_mul, hm]

theorem matMul_implements : Implements gpt.module 9 matMulTuple matMulNeed := by
  refine Func.implements_heap gpt.funcs 6 gpt.matMul.ir "matMul" rfl matMulTuple matMulNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨a, b, n, k, m⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pa, rfl, hAs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hRoom
  change heap.Borrowed initial pa (a.map Float.toBits) at hAs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  change heap.Room initial gpt.module (48 + 8 * ((n * m).toNat + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pa, .i64 pb, .i64 n, .i64 k, .i64 m]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.buildWith 5 6 7 (.bin .mul (.get 2) (.get 4))
      (.seq (.assign 8 (.constF 0)) (.loop 9 10 (.get 3) cellBody)) (.toBits (.getF 8))) 12
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [8, 9, 10, 11]) (n := n * m)
    (fun e => (cell a b k m e).toBits) hMemory32 hImports hAlloc (by decide) (by decide)
    (by decide) (by simp [start]) hHeap hRoom
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · -- One element: the accumulator, then the loop over the shared dimension.
    intro e store state he hAt hFrame hIndex
    have hState : state.params.length = 5 ∧ state.locals.length = 10 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 5 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hA := hAt pa _ hAs
    have hB := hAt pb _ hBs
    let s1 := state.update 8 (.f64 0)
    have hS1 : s1.params.length = 5 ∧ s1.locals.length = 10 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 8 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [8]) (writes := [8, 11]) (init := (0.0 : Float)) (n := k)
      (cellStep a b k m (UInt64.ofNat e)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 3 (by decide), hGet 3 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 5 ∧ st.locals.length = 10 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 5 ∨ j = 7 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g8 : st.get 8 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := cellBody_run hA hB hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 4 (by omega)).trans ((hGet 4 (by decide)).trans rfl))
        ((hKeep 7 (by omega)).trans hIndex) g8 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' t ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' t ⟨rfl, hFrameL, hHolds⟩
      have g8 : t.get 8 = some (.f64 (cell a b k m (UInt64.ofNat e)).toBits) :=
        (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), t, by simp [Expr.eval, g8]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨pa, rfl, hNew.borrowed pa _ hAs⟩, _, _, rfl,
      ⟨pb, rfl, hNew.borrowed pb _ hBs⟩, rfl⟩, hNew.top, hNew.pages, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.matMul.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  rw [matMulTuple, matMul_eq, build_map]
  exact hNew.owned

/-- `add` with its two arguments as one pair. -/
def addTuple (x : Array Float × Array Float) : Array Float :=
  LeanExe.Examples.Gpt.add x.1 x.2

/-- The bytes `add` may allocate: one array as long as the first argument. -/
def addNeed (x : Array Float × Array Float) : Nat := 48 + 8 * (x.1.size + 1)

theorem add_implements : Implements gpt.module 10 addTuple addNeed := by
  refine Func.implements_heap gpt.funcs 7 gpt.add.ir "add" rfl addTuple addNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨a, b⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨pa, rfl, hAs⟩, ⟨pb, rfl, hBs⟩⟩ hRoom
  change heap.Borrowed initial pa (a.map Float.toBits) at hAs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  change heap.Room initial gpt.module (48 + 8 * (a.size + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hA := hAs.values
  have hFit := hA.1
  simp only [Array.size_map] at hFit
  have hLength := hA.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hn : (UInt64.ofNat a.size).toNat = a.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  let start : State :=
    { params := [.i64 pa, .i64 pb], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  have hGet0 : start.get 0 = some (.i64 pa) := rfl
  let s1 := start.update 2 (.i64 (UInt64.ofNat a.size))
  show Triple _ (.seq (.arraySize 2 0) (.build 3 4 5 (.get 2)
      (.toBits (.binF .add (.ofBits (.read 0 (.get 5))) (.ofBits (.read 1 (.get 5))))))) 6
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hA.lengthRead,
      State.set?_eq_update, s1, start])) ?_
  have hS1 : s1.params.length = 2 ∧ s1.locals.length = 5 := by simp [s1, start]
  refine (Stmt.build_spec (n := a.size.toUInt64)
    (fun i => (a[i.toNat]! + b[i.toNat]!).toBits) hMemory32 hImports hAlloc (by decide)
    (by decide) (by simp [hS1.1, hS1.2]) hHeap
    (by rw [show a.size.toUInt64.toNat = a.size from hn]; exact hRoom)
    ⟨s1, by simp [Expr.eval, s1, start]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 2 ∧ state.locals.length = 5 :=
      ⟨hFrame.params.trans hS1.1, hFrame.locals.trans hS1.2⟩
    have g0 : state.get 0 = some (.i64 pa) := (hFrame.get 0 (by decide) (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 pb) := (hFrame.get 1 (by decide) (by decide)).trans rfl
    exact ⟨state.update 6 (.i64 (UInt64.ofNat k)), by simp [Expr.eval, g0, g1, hIndex,
      Expr.readValue_at (hAt pa _ hAs), Expr.readValue_at (hAt pb _ hBs), State.set?_eq_update,
      hState.1, hState.2, F64Op.apply, getElem!_map_toBits, F64Bits.toBits_add]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨pa, rfl, hNew.borrowed pa _ hAs⟩,
      ⟨pb, rfl, hNew.borrowed pb _ hBs⟩⟩,
    le_of_le_of_eq hNew.top (by simp [addNeed, hn]),
    le_of_le_of_eq hNew.pages (by simp [addNeed, hn]), hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.add.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  have hAdd : LeanExe.Examples.Gpt.add a b =
      LeanExe.build a.size.toUInt64 (fun i => a[i.toNat]! + b[i.toNat]!) := rfl
  rw [addTuple, hAdd, build_map]
  exact hNew.owned

theorem tanh_pure : ImplementsPure gpt.module 11 LeanExe.Examples.Gpt.tanh := by
  refine Func.implementsPure gpt.funcs 8 gpt.tanh.ir "tanh" rfl LeanExe.Examples.Gpt.tanh
    (fun _ => rfl) fun z initial => ?_
  have k2 : (2.0 : Float).toBits = 4611686018427387904 := by decide +kernel
  have k1 : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let start : State := { params := [.f64 z.toBits], locals := [.f64 0] }
  let final := start.update 1 (.f64 (LeanExe.Examples.Gpt.exp (2.0 * z)).toBits)
  show Triple _ (.call 6 [⟨.f64, .binF .mul (.constF 4611686018427387904) (.getF 0)⟩] [1]) 2
    (fun store state => store = initial ∧ state = start) _
  have g0 : start.get 0 = some (.f64 z.toBits) := rfl
  refine (exp_call rfl (afterArgs := start) (next := final) (d := 2.0 * z) ?_ ?_).mono
    (fun _ _ h => h) ?_
  · simp [Expr.evalResults, Expr.eval, g0, F64Op.apply, F64Bits.toBits_mul, k2]
  · simp [State.setAll, State.set?_eq_update, final, start]
  rintro s st ⟨rfl, rfl⟩
  have g1 : final.get 1 = some (.f64 (LeanExe.Examples.Gpt.exp (2.0 * z)).toBits) := by
    simp [final, start]
  exact ⟨rfl, [.f64 (LeanExe.Examples.Gpt.tanh z).toBits], final, by
    simp [gpt.tanh.ir, Func.scratch, Expr.evalResults, Expr.eval, g1, F64Op.apply,
      LeanExe.Examples.Gpt.tanh, F64Bits.toBits_sub, F64Bits.toBits_div, F64Bits.toBits_add, k1,
      k2], rfl⟩

/-- The call to `tanh`, entry 11 of the module. -/
theorem tanh_call {scratch : Nat} {args : List ((type : ScalarType) × Expr type)}
    {results : List Nat} (hParams : args.length = 1) {initial : Store Unit}
    {before afterArgs next : State} {d : Float}
    (hArgs : Expr.evalResults initial.mem scratch args before = some ([.f64 d.toBits], afterArgs))
    (hSet : afterArgs.setAll results.reverse [.f64 (LeanExe.Examples.Gpt.tanh d).toBits] =
      some next) :
    Triple gpt.module (.call 11 args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) :=
  Stmt.callPure_spec tanh_pure (f := gpt.tanh.ir.function (2 + 8)) rfl
    (by rw [show gpt.module.imports.length = 0 from rfl]
        exact compile_funcs (funcs := gpt.funcs) (i := 8) rfl) hParams (x := d) hArgs hSet

theorem gelu_pure : ImplementsPure gpt.module 12 LeanExe.Examples.Gpt.gelu := by
  refine Func.implementsPure gpt.funcs 9 gpt.gelu.ir "gelu" rfl LeanExe.Examples.Gpt.gelu
    (fun _ => rfl) fun x initial => ?_
  have kScale : (0.7978845608028654 : Float).toBits = 4605361924766709329 := by decide +kernel
  have kCube : (0.044715 : Float).toBits = 4586604931670606327 := by decide +kernel
  have kHalf : (0.5 : Float).toBits = 4602678819172646912 := by decide +kernel
  have kOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let u := 0.7978845608028654 * (x + 0.044715 * x * x * x)
  let start : State := { params := [.f64 x.toBits], locals := [.f64 0, .f64 0] }
  let s1 := start.update 1 (.f64 u.toBits)
  let final := s1.update 2 (.f64 (LeanExe.Examples.Gpt.tanh u).toBits)
  have g0 : start.get 0 = some (.f64 x.toBits) := rfl
  show Triple _ (.seq (.assign 1 (.binF .mul (.constF 4605361924766709329) (.binF .add (.getF 0)
      (.binF .mul (.binF .mul (.binF .mul (.constF 4586604931670606327) (.getF 0)) (.getF 0))
        (.getF 0))))) (.call 11 [⟨.f64, .getF 1⟩] [2])) 3
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    simp [Stmt.run, Expr.eval, g0, State.set?_eq_update, s1, start, u, F64Op.apply,
      F64Bits.toBits_mul, F64Bits.toBits_add, kScale, kCube])) ?_
  have g1 : s1.get 1 = some (.f64 u.toBits) := by simp [s1, start]
  refine (tanh_call rfl (afterArgs := s1) (next := final) (d := u) ?_ ?_).mono
    (fun _ _ h => h) ?_
  · simp [Expr.evalResults, Expr.eval, g1]
  · simp [State.setAll, State.set?_eq_update, final, s1, start]
  rintro s st ⟨rfl, rfl⟩
  have f0 : final.get 0 = some (.f64 x.toBits) := by simp [final, s1, start]; rfl
  have f2 : final.get 2 = some (.f64 (LeanExe.Examples.Gpt.tanh u).toBits) := by
    simp [final, s1, start]
  exact ⟨rfl, [.f64 (LeanExe.Examples.Gpt.gelu x).toBits], final, by
    simp [gpt.gelu.ir, Func.scratch, Expr.evalResults, Expr.eval, f0, f2, F64Op.apply,
      LeanExe.Examples.Gpt.gelu, F64Bits.toBits_mul, F64Bits.toBits_add, kHalf, kOne, u], rfl⟩

/-- The call to `gelu`, entry 12 of the module. -/
theorem gelu_call {scratch : Nat} {args : List ((type : ScalarType) × Expr type)}
    {results : List Nat} (hParams : args.length = 1) {initial : Store Unit}
    {before afterArgs next : State} {d : Float}
    (hArgs : Expr.evalResults initial.mem scratch args before = some ([.f64 d.toBits], afterArgs))
    (hSet : afterArgs.setAll results.reverse [.f64 (LeanExe.Examples.Gpt.gelu d).toBits] =
      some next) :
    Triple gpt.module (.call 12 args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) :=
  Stmt.callPure_spec gelu_pure (f := gpt.gelu.ir.function (2 + 9)) rfl
    (by rw [show gpt.module.imports.length = 0 from rfl]
        exact compile_funcs (funcs := gpt.funcs) (i := 9) rfl) hParams (x := d) hArgs hSet

/-- The bytes `geluArray` may allocate: one array as long as its argument. -/
def geluNeed (xs : Array Float) : Nat := 48 + 8 * (xs.size + 1)

theorem geluArray_implements :
    Implements gpt.module 13 LeanExe.Examples.Gpt.geluArray geluNeed := by
  refine Func.implements_heap gpt.funcs 10 gpt.geluArray.ir "geluArray" rfl
    LeanExe.Examples.Gpt.geluArray geluNeed (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨px, rfl, hXs⟩ hRoom
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
  change heap.Room initial gpt.module (48 + 8 * (xs.size + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hX := hXs.values
  have hFit := hX.1
  simp only [Array.size_map] at hFit
  have hLength := hX.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hn : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  let start : State :=
    { params := [.i64 px], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  have hGet0 : start.get 0 = some (.i64 px) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  show Triple _ (.seq (.arraySize 1 0) (.buildWith 2 3 4 (.get 1)
      (.call 12 [⟨.f64, .ofBits (.read 0 (.get 4))⟩] [5]) (.toBits (.getF 5)))) 6
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hX.lengthRead,
      State.set?_eq_update, s1, start])) ?_
  have hS1 : s1.params.length = 1 ∧ s1.locals.length = 6 := by simp [s1, start]
  refine (Stmt.buildWith_spec (writes := [5]) (n := xs.size.toUInt64)
    (fun i => (LeanExe.Examples.Gpt.gelu xs[i.toNat]!).toBits) hMemory32 hImports hAlloc
    (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2]) hHeap
    (by rw [show xs.size.toUInt64.toNat = xs.size from hn]; exact hRoom)
    ⟨s1, by simp [Expr.eval, s1, start]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 1 ∧ state.locals.length = 6 :=
      ⟨hFrame.params.trans hS1.1, hFrame.locals.trans hS1.2⟩
    have g0 : state.get 0 = some (.i64 px) := (hFrame.get 0 (by decide) (by decide)).trans rfl
    let a := state.update 6 (.i64 (UInt64.ofNat k))
    let b := a.update 5 (.f64 (LeanExe.Examples.Gpt.gelu xs[(UInt64.ofNat k).toNat]!).toBits)
    have hA : a.params.length = 1 ∧ a.locals.length = 6 := by simp [a, hState.1, hState.2]
    refine (gelu_call rfl (afterArgs := a) (next := b) (d := xs[(UInt64.ofNat k).toNat]!) ?_ ?_).mono
      (fun _ _ h => h) ?_
    · simp [Expr.evalResults, Expr.eval, g0, hIndex, Expr.readValue_at (hAt px _ hXs),
        State.set?_eq_update, hState.1, hState.2, getElem!_map_toBits, a]
    · simp [State.setAll, State.set?_eq_update, b, hA.1, hA.2]
    rintro s st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, b, by simp [Expr.eval, b, a, hState.1, hState.2]⟩
    simp only [b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨px, rfl, hNew.borrowed px _ hXs⟩,
    le_of_le_of_eq hNew.top (by simp [geluNeed, hn]),
    le_of_le_of_eq hNew.pages (by simp [geluNeed, hn]), hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.geluArray.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  have hGelu : LeanExe.Examples.Gpt.geluArray xs =
      LeanExe.build xs.size.toUInt64 (fun i => LeanExe.Examples.Gpt.gelu xs[i.toNat]!) := rfl
  rw [hGelu, build_map]
  exact hNew.owned

theorem matMul_size (a b : Array Float) (n k m : UInt64) :
    (matMulTuple (a, b, n, k, m)).size = (n * m).toNat := by
  simp [matMulTuple, matMul_eq, LeanExe.build]

/-- `mlp` with its six arguments as one tuple. -/
def mlpTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64) :
    Array Float :=
  LeanExe.Examples.Gpt.mlp x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- The bytes `mlp` may allocate: two `t × f` arrays and the `t × d` result. -/
def mlpNeed (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64) : Nat :=
  48 + 8 * ((x.2.2.2.1 * x.2.2.2.2.2).toNat + 1) + (48 + 8 * ((x.2.2.2.1 * x.2.2.2.2.2).toNat + 1)) +
    (48 + 8 * ((x.2.2.2.1 * x.2.2.2.2.1).toNat + 1))

theorem mlp_implements : Implements gpt.module 14 mlpTuple mlpNeed := by
  refine Func.implements_heap gpt.funcs 11 gpt.mlp.ir "mlp" rfl mlpTuple mlpNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨x, w1, w2, t, d, f⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hX⟩, _, _, rfl, ⟨p1, rfl, hW1⟩, _, _, rfl, ⟨p2, rfl, hW2⟩, rfl⟩ hRoom
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  change heap.Borrowed initial p1 (w1.map Float.toBits) at hW1
  change heap.Borrowed initial p2 (w2.map Float.toBits) at hW2
  change heap.Room initial gpt.module (48 + 8 * ((t * f).toNat + 1) +
    (48 + 8 * ((t * f).toNat + 1)) + (48 + 8 * ((t * d).toNat + 1))) at hRoom
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[2]? = some (releaseFunction 1) := rfl
  have hMatMul : gpt.module.funcs[9 - gpt.module.imports.length]? =
      some (gpt.matMul.ir.function (2 + 6)) := compile_funcs (funcs := gpt.funcs) (i := 6) rfl
  have hGelu : gpt.module.funcs[13 - gpt.module.imports.length]? =
      some (gpt.geluArray.ir.function (2 + 10)) := compile_funcs (funcs := gpt.funcs) (i := 10) rfl
  let h := matMulTuple (x, w1, t, d, f)
  let g := LeanExe.Examples.Gpt.geluArray h
  have hSize : h.size = (t * f).toNat := matMul_size x w1 t d f
  let start : State :=
    { params := [.i64 px, .i64 p1, .i64 p2, .i64 t, .i64 d, .i64 f]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have hGet : start.get 0 = some (.i64 px) ∧ start.get 1 = some (.i64 p1) ∧
      start.get 2 = some (.i64 p2) ∧ start.get 3 = some (.i64 t) ∧ start.get 4 = some (.i64 d) ∧
      start.get 5 = some (.i64 f) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  show Triple _ (.seq (.call 9 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩,
      ⟨.u64, .get 5⟩] [6]) (.seq (.call 13 [⟨.u64, .get 6⟩] [7]) (.seq (.call 9 [⟨.u64, .get 7⟩,
      ⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 5⟩, ⟨.u64, .get 4⟩] [8])
      (.seq (.assign 9 (.get 8)) (.seq (.release 7) (.release 6)))))) 10
    (fun store state => store = initial ∧ state = start) _
  -- `h = x · w1`.
  refine Stmt.seq_spec (Live.call matMul_implements rfl hMatMul rfl (Live.start hHeap) hRoom
    (x := (x, w1, t, d, f)) (by simp only [matMulNeed]; omega) (afterArgs := start)
    (vals := [.i64 px, .i64 p1, .i64 t, .i64 d, .i64 f])
    (by simp [Expr.evalResults, Expr.eval, hGet.1, hGet.2.1, hGet.2.2.2.1, hGet.2.2.2.2.1,
      hGet.2.2.2.2.2])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hX⟩, [.i64 p1], _, rfl, ⟨p1, rfl, hW1⟩, rfl⟩
    (by rw [hStart]; decide)) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨heap1, ph, hLive1, rfl⟩
  let s1 := start.update 6 (.i64 ph)
  have hS1 : s1.params.length + s1.locals.length = 10 := by rw [hLen, hStart]
  -- `g = gelu h`.
  refine Stmt.seq_spec (Live.call geluArray_implements rfl hGelu rfl hLive1 hRoom
    (x := h) (by simp only [matMulNeed, geluNeed, hSize]; omega) (afterArgs := s1)
    (vals := [.i64 ph]) (by simp [Expr.evalResults, Expr.eval, s1, State.get_update_same,
      hStart])
    ⟨ph, rfl, (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩
    (by rw [hS1]; decide)) ?_
  apply Triple.of_forall
  rintro store2 t2 ⟨heap2, pg, hLive2, rfl⟩
  let s2 := s1.update 7 (.i64 pg)
  have hS2 : s2.params.length + s2.locals.length = 10 := by rw [hLen, hS1]
  have hGetS2 : ∀ j, j < 6 → s2.get j = start.get j := fun j hj => by
    simp only [s2, s1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]
  -- The result, `g · w2`.
  refine Stmt.seq_spec (Live.call matMul_implements rfl hMatMul rfl hLive2 hRoom
    (x := (g, w2, t, f, d)) (by simp only [matMulNeed, geluNeed, hSize]; omega)
    (afterArgs := s2) (vals := [.i64 pg, .i64 p2, .i64 t, .i64 f, .i64 d])
    (by simp [Expr.evalResults, Expr.eval, s2, State.get_update_same, hS1,
      hGetS2 2 (by decide), hGetS2 3 (by decide), hGetS2 4 (by decide), hGetS2 5 (by decide),
      hGet.2.2.1, hGet.2.2.2.1, hGet.2.2.2.2.1, hGet.2.2.2.2.2])
    ⟨[.i64 pg], _, rfl, ⟨pg, rfl, (hLive2.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩,
      [.i64 p2], _, rfl, ⟨p2, rfl, hLive2.borrowed p2 _ hW2⟩, rfl⟩
    (by rw [hS2]; decide)) ?_
  apply Triple.of_forall
  rintro store3 t3 ⟨heap3, pr, hLive3, rfl⟩
  let s3 := s2.update 8 (.i64 pr)
  let s4 := s3.update 9 (.i64 pr)
  have hS3 : s3.params.length + s3.locals.length = 10 := by rw [hLen, hS2]
  refine Stmt.seq_spec (Stmt.run_spec (final := s4) (by
    simp [Stmt.run, Expr.eval, State.set?_eq_update _ (show 9 < s3.params.length +
      s3.locals.length by rw [hS3]; decide), s4, s3, State.get_update_same,
      show 8 < s2.params.length + s2.locals.length by rw [hS2]; decide])) ?_
  -- The temporaries are released, `g` first.
  have hS4Get7 : s4.get 7 = some (.i64 pg) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hS1]; decide)
  have hS4Get6 : s4.get 6 = some (.i64 ph) := by
    simp only [s4, s3, s2]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide),
      State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hStart]; decide)
  refine Stmt.seq_spec (hLive3.releaseSecond hImports hRelease hS4Get7) ?_
  apply Triple.of_forall
  rintro store4 st4 ⟨hLive4, rfl⟩
  refine (hLive4.releaseSecond hImports hRelease hS4Get6).mono (fun _ _ h => h) ?_
  rintro store5 st5 ⟨hLive5, rfl⟩
  have hParams : ∀ (heap' : Heap) (store' : Store Unit),
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' [.i64 px, .i64 p1, .i64 p2, .i64 t, .i64 d, .i64 f]
        (x, w1, w2, t, d, f) := fun heap' store' hKeep =>
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hKeep px _ hX⟩, [.i64 p1], _, rfl, ⟨p1, rfl, hKeep p1 _ hW1⟩,
      [.i64 p2], _, rfl, ⟨p2, rfl, hKeep p2 _ hW2⟩, rfl⟩
  obtain ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLive5.finish (need := mlpNeed (x, w1, w2, t, d, f))
      (by simp only [matMulNeed, geluNeed, mlpNeed, hSize]; omega) hParams
  exact ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, [.i64 pr], s4,
    by simp [gpt.mlp.ir, Func.scratch, Expr.evalResults, Expr.eval, s4, State.get_update_same,
      hS3], hOwned, hOutB, hOutO⟩

/-- `rowMeans` with its three arguments as one tuple. -/
def rowMeansTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.rowMeans x.1 x.2.1 x.2.2

/-- The bytes `rowMeans` may allocate: one array of `t` elements. -/
def rowMeansNeed (x : Array Float × UInt64 × UInt64) : Nat := 48 + 8 * (x.2.1.toNat + 1)

/-- One step of the sum over row `r`. -/
def meanStep (x : Array Float) (d r c : UInt64) (acc : Float) : Float :=
  acc + x[(r * d + c).toNat]!

/-- The compiled loop body of `rowMeans`. -/
def meanBody : Stmt :=
  .seq (.assign 9 (.binF .add (.getF 6)
    (.ofBits (.read 0 (.bin .add (.bin .mul (.get 5) (.get 2)) (.get 8)))))) (.assign 6 (.getF 9))

theorem meanBody_run {initial : Store Unit} {px : UInt64} {x : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits)) {state : State} {c : Nat}
    {d r : UInt64} {acc : Float} (hParams : state.params.length = 3)
    (hLocals : state.locals.length = 8) (h0 : state.get 0 = some (.i64 px))
    (h2 : state.get 2 = some (.i64 d)) (h5 : state.get 5 = some (.i64 r))
    (h6 : state.get 6 = some (.f64 acc.toBits)) (h8 : state.get 8 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, meanBody.run initial.mem 10 state = some final ∧
      State.Frame 10 [6, 9] state final ∧
      final.Holds [6] (Scalar.values (meanStep x d r (UInt64.ofNat c) acc)) := by
  simp [meanBody, Stmt.run, Expr.eval, h0, h2, h5, h6, h8, Expr.readValue_at hX,
    State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply, getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, meanStep, hParams, hLocals, F64Bits.toBits_add]

theorem rowMeans_implements : Implements gpt.module 15 rowMeansTuple rowMeansNeed := by
  refine Func.implements_heap gpt.funcs 12 gpt.rowMeans.ir "rowMeans" rfl rowMeansTuple
    rowMeansNeed (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, t, d⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨px, rfl, hXs⟩, rfl⟩ hRoom
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Room initial gpt.module (48 + 8 * (t.toNat + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 t, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  show Triple _ (.buildWith 3 4 5 (.get 1)
      (.seq (.assign 6 (.constF 0)) (.loop 7 8 (.get 2) meanBody))
      (.toBits (.binF .div (.getF 6) (.convertU (.get 2))))) 10
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [6, 7, 8, 9]) (n := t)
    (fun r => (LeanExe.loop d 0.0 (meanStep x d r) / d.toFloat).toBits) hMemory32 hImports hAlloc
    (by decide) (by decide) (by decide) (by simp [start]) hHeap hRoom ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro r store state hr hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 8 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 3 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hX := hAt px _ hXs
    let s1 := state.update 6 (.f64 0)
    have hS1 : s1.params.length = 3 ∧ s1.locals.length = 8 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 6 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [6]) (writes := [6, 9]) (init := (0.0 : Float)) (n := d)
      (meanStep x d (UInt64.ofNat r)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 2 (by decide), hGet 2 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 3 ∧ st.locals.length = 8 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 3 ∨ j = 5 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g6 : st.get 6 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := meanBody_run hX hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans ((hGet 2 (by decide)).trans rfl))
        ((hKeep 5 (by omega)).trans hIndex) g6 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g6 : u.get 6 = some (.f64 (LeanExe.loop d 0.0
          (meanStep x d (UInt64.ofNat r))).toBits) := (List.forall₂_cons.mp hHolds).1
      have g2 : u.get 2 = some (.i64 d) :=
        ((hFrameL.get 2 (by decide) (by decide)).trans (hS1Get 2 (by decide))).trans
          ((hGet 2 (by decide)).trans rfl)
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by
        simp [Expr.eval, g6, g2, F64Op.apply, F64Bits.toBits_div, F64Convert.toBits_toFloat]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨px, rfl, hNew.borrowed px _ hXs⟩, rfl⟩, hNew.top, hNew.pages,
    hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.rowMeans.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  have hEq : rowMeansTuple (x, t, d) =
      LeanExe.build t (fun r => LeanExe.loop d 0.0 (meanStep x d r) / d.toFloat) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowInvStd` with its five arguments as one tuple. -/
def rowInvStdTuple (x : Array Float × Array Float × UInt64 × UInt64 × Float) : Array Float :=
  LeanExe.Examples.Gpt.rowInvStd x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The bytes `rowInvStd` may allocate: one array of `t` elements. -/
def rowInvStdNeed (x : Array Float × Array Float × UInt64 × UInt64 × Float) : Nat :=
  48 + 8 * (x.2.2.1.toNat + 1)

/-- One step of the sum of squared deviations over row `r`. -/
def devStep (x means : Array Float) (d r c : UInt64) (acc : Float) : Float :=
  acc + (x[(r * d + c).toNat]! - means[r.toNat]!) * (x[(r * d + c).toNat]! - means[r.toNat]!)

/-- The compiled loop body of `rowInvStd`. -/
def devBody : Stmt :=
  .seq (.assign 11 (.binF .add (.getF 8) (.binF .mul
    (.binF .sub (.ofBits (.read 0 (.bin .add (.bin .mul (.get 7) (.get 3)) (.get 10))))
      (.ofBits (.read 1 (.get 7))))
    (.binF .sub (.ofBits (.read 0 (.bin .add (.bin .mul (.get 7) (.get 3)) (.get 10))))
      (.ofBits (.read 1 (.get 7))))))) (.assign 8 (.getF 11))

theorem devBody_run {initial : Store Unit} {px pm : UInt64} {x means : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits))
    (hM : UInt64Array.At initial pm (means.map Float.toBits)) {state : State} {c : Nat}
    {d r : UInt64} {acc : Float} (hParams : state.params.length = 5)
    (hLocals : state.locals.length = 8) (h0 : state.get 0 = some (.i64 px))
    (h1 : state.get 1 = some (.i64 pm)) (h3 : state.get 3 = some (.i64 d))
    (h7 : state.get 7 = some (.i64 r)) (h8 : state.get 8 = some (.f64 acc.toBits))
    (h10 : state.get 10 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, devBody.run initial.mem 12 state = some final ∧
      State.Frame 12 [8, 11] state final ∧
      final.Holds [8] (Scalar.values (devStep x means d r (UInt64.ofNat c) acc)) := by
  simp [devBody, Stmt.run, Expr.eval, h0, h1, h3, h7, h8, h10, Expr.readValue_at hX,
    Expr.readValue_at hM, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, devStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul, F64Bits.toBits_sub]

theorem rowInvStd_implements : Implements gpt.module 16 rowInvStdTuple rowInvStdNeed := by
  refine Func.implements_heap gpt.funcs 13 gpt.rowInvStd.ir "rowInvStd" rfl rowInvStdTuple
    rowInvStdNeed (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, means, t, d, eps⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, rfl⟩ hRoom
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (means.map Float.toBits) at hMs
  change heap.Room initial gpt.module (48 + 8 * (t.toNat + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 pm, .i64 t, .i64 d, .f64 eps.toBits]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  show Triple _ (.buildWith 5 6 7 (.get 2)
      (.seq (.assign 8 (.constF 0)) (.loop 9 10 (.get 3) devBody))
      (.toBits (.binF .div (.constF 4607182418800017408) (.unF .sqrt
        (.binF .add (.binF .div (.getF 8) (.convertU (.get 3))) (.getF 4)))))) 12
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [8, 9, 10, 11]) (n := t)
    (fun r => (1.0 / (LeanExe.loop d 0.0 (devStep x means d r) / d.toFloat + eps).sqrt).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hRoom
    ⟨start, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro r store state hr hAt hFrame hIndex
    have hState : state.params.length = 5 ∧ state.locals.length = 8 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 5 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hX := hAt px _ hXs
    have hM := hAt pm _ hMs
    let s1 := state.update 8 (.f64 0)
    have hS1 : s1.params.length = 5 ∧ s1.locals.length = 8 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 8 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [8]) (writes := [8, 11]) (init := (0.0 : Float)) (n := d)
      (devStep x means d (UInt64.ofNat r)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 3 (by decide), hGet 3 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 5 ∧ st.locals.length = 8 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 5 ∨ j = 7 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g8 : st.get 8 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := devBody_run hX hM hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 7 (by omega)).trans hIndex) g8 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g8 : u.get 8 = some (.f64 (LeanExe.loop d 0.0
          (devStep x means d (UInt64.ofNat r))).toBits) := (List.forall₂_cons.mp hHolds).1
      have g3 : u.get 3 = some (.i64 d) :=
        ((hFrameL.get 3 (by decide) (by decide)).trans (hS1Get 3 (by decide))).trans
          ((hGet 3 (by decide)).trans rfl)
      have g4 : u.get 4 = some (.f64 eps.toBits) :=
        ((hFrameL.get 4 (by decide) (by decide)).trans (hS1Get 4 (by decide))).trans
          ((hGet 4 (by decide)).trans rfl)
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by
        simp [Expr.eval, g8, g3, g4, F64Op.apply, F64UnOp.apply, F64Bits.toBits_div,
          F64Bits.toBits_sqrt, F64Bits.toBits_add, F64Convert.toBits_toFloat, hOne]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨px, rfl, hNew.borrowed px _ hXs⟩, _, _, rfl,
      ⟨pm, rfl, hNew.borrowed pm _ hMs⟩, rfl⟩, hNew.top, hNew.pages, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.rowInvStd.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  have hEq : rowInvStdTuple (x, means, t, d, eps) = LeanExe.build t (fun r =>
      1.0 / (LeanExe.loop d 0.0 (devStep x means d r) / d.toFloat + eps).sqrt) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `normalizeRows` with its seven arguments as one tuple. -/
def normalizeTuple (x : Array Float × Array Float × Array Float × Array Float × Array Float ×
    UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.normalizeRows x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    x.2.2.2.2.2.2

/-- The bytes `normalizeRows` may allocate: one array of `t × d` elements. -/
def normalizeNeed (x : Array Float × Array Float × Array Float × Array Float × Array Float ×
    UInt64 × UInt64) : Nat :=
  48 + 8 * ((x.2.2.2.2.2.1 * x.2.2.2.2.2.2).toNat + 1)

/-- Element `e` of `normalizeRows`. -/
def normalizeAt (x means inv g b : Array Float) (d e : UInt64) : Float :=
  (x[e.toNat]! - means[(e / d).toNat]!) * inv[(e / d).toNat]! * g[(e % d).toNat]! +
    b[(e % d).toNat]!

theorem normalizeRows_implements : Implements gpt.module 17 normalizeTuple normalizeNeed := by
  refine Func.implements_heap gpt.funcs 14 gpt.normalizeRows.ir "normalizeRows" rfl
    normalizeTuple normalizeNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, means, inv, g, b, t, d⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨pi, rfl, hIs⟩,
      _, _, rfl, ⟨pg, rfl, hGs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hRoom
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (means.map Float.toBits) at hMs
  change heap.Borrowed initial pi (inv.map Float.toBits) at hIs
  change heap.Borrowed initial pg (g.map Float.toBits) at hGs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  change heap.Room initial gpt.module (48 + 8 * ((t * d).toNat + 1)) at hRoom
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 px, .i64 pm, .i64 pi, .i64 pg, .i64 pb, .i64 t, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.build 7 8 9 (.bin .mul (.get 5) (.get 6)) (.toBits (.binF .add (.binF .mul
      (.binF .mul (.binF .sub (.ofBits (.read 0 (.get 9)))
        (.ofBits (.read 1 (.bin .divU (.get 9) (.get 6)))))
        (.ofBits (.read 2 (.bin .divU (.get 9) (.get 6)))))
      (.ofBits (.read 3 (.bin .remU (.get 9) (.get 6)))))
      (.ofBits (.read 4 (.bin .remU (.get 9) (.get 6))))))) 10
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.build_spec (n := t * d) (fun e => (normalizeAt x means inv g b d e).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by simp [start]) hHeap hRoom
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hState : state.params.length = 7 ∧ state.locals.length = 6 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 7 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 px) := (hGet 0 (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 pm) := (hGet 1 (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 pi) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 pg) := (hGet 3 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 pb) := (hGet 4 (by decide)).trans rfl
    have g6 : state.get 6 = some (.i64 d) := (hGet 6 (by decide)).trans rfl
    by_cases hd : d = 0 <;> simp [Expr.eval, g0, g1, g2, g3, g4, g6, hIndex,
      Expr.readValue_at (hAt px _ hXs), Expr.readValue_at (hAt pm _ hMs),
      Expr.readValue_at (hAt pi _ hIs), Expr.readValue_at (hAt pg _ hGs),
      Expr.readValue_at (hAt pb _ hBs), State.set?_eq_update, hState.1, hState.2, F64Op.apply,
      U64Op.apply, getElem!_map_toBits, normalizeAt, F64Bits.toBits_add, F64Bits.toBits_mul,
      F64Bits.toBits_sub, hd]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨px, rfl, hNew.borrowed px _ hXs⟩, _, _, rfl,
      ⟨pm, rfl, hNew.borrowed pm _ hMs⟩, _, _, rfl, ⟨pi, rfl, hNew.borrowed pi _ hIs⟩, _, _, rfl,
      ⟨pg, rfl, hNew.borrowed pg _ hGs⟩, _, _, rfl, ⟨pb, rfl, hNew.borrowed pb _ hBs⟩, rfl⟩,
    hNew.top, hNew.pages, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.normalizeRows.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => ⟨ptr, rfl, hNew.borrowedApart p ws h⟩,
    fun p ws h => ⟨ptr, rfl, hNew.ownedApart p ws h⟩⟩
  have hEq : normalizeTuple (x, means, inv, g, b, t, d) =
      LeanExe.build (t * d) (normalizeAt x means inv g b d) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `layerNormRows` with its six arguments as one tuple. -/
def layerNormRowsTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × Float) :
    Array Float :=
  LeanExe.Examples.Gpt.layerNormRows x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- The bytes `layerNormRows` may allocate: the means, the inverse deviations, and the
`t × d` result. -/
def layerNormRowsNeed (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × Float) :
    Nat :=
  48 + 8 * (x.2.2.2.1.toNat + 1) + (48 + 8 * (x.2.2.2.1.toNat + 1)) +
    (48 + 8 * ((x.2.2.2.1 * x.2.2.2.2.1).toNat + 1))

theorem layerNormRows_implements :
    Implements gpt.module 18 layerNormRowsTuple layerNormRowsNeed := by
  refine Func.implements_heap gpt.funcs 15 gpt.layerNormRows.ir "layerNormRows" rfl
    layerNormRowsTuple layerNormRowsNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨x, g, b, t, d, eps⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hX⟩, _, _, rfl, ⟨pg, rfl, hG⟩, _, _, rfl, ⟨pb, rfl, hB⟩, rfl⟩ hRoom
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  change heap.Borrowed initial pg (g.map Float.toBits) at hG
  change heap.Borrowed initial pb (b.map Float.toBits) at hB
  change heap.Room initial gpt.module (48 + 8 * (t.toNat + 1) + (48 + 8 * (t.toNat + 1)) +
    (48 + 8 * ((t * d).toNat + 1))) at hRoom
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[2]? = some (releaseFunction 1) := rfl
  have hMeans : gpt.module.funcs[15 - gpt.module.imports.length]? =
      some (gpt.rowMeans.ir.function (2 + 12)) := compile_funcs (funcs := gpt.funcs) (i := 12) rfl
  have hInv : gpt.module.funcs[16 - gpt.module.imports.length]? =
      some (gpt.rowInvStd.ir.function (2 + 13)) := compile_funcs (funcs := gpt.funcs) (i := 13) rfl
  have hNormalize : gpt.module.funcs[17 - gpt.module.imports.length]? =
      some (gpt.normalizeRows.ir.function (2 + 14)) :=
    compile_funcs (funcs := gpt.funcs) (i := 14) rfl
  let means := rowMeansTuple (x, t, d)
  let inv := rowInvStdTuple (x, means, t, d, eps)
  let start : State :=
    { params := [.i64 px, .i64 pg, .i64 pb, .i64 t, .i64 d, .f64 eps.toBits]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have hGet : start.get 0 = some (.i64 px) ∧ start.get 1 = some (.i64 pg) ∧
      start.get 2 = some (.i64 pb) ∧ start.get 3 = some (.i64 t) ∧ start.get 4 = some (.i64 d) ∧
      start.get 5 = some (.f64 eps.toBits) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  show Triple _ (.seq (.call 15 [⟨.u64, .get 0⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [6])
      (.seq (.call 16 [⟨.u64, .get 0⟩, ⟨.u64, .get 6⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩,
        ⟨.f64, .getF 5⟩] [7])
      (.seq (.call 17 [⟨.u64, .get 0⟩, ⟨.u64, .get 6⟩, ⟨.u64, .get 7⟩, ⟨.u64, .get 1⟩,
        ⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [8])
      (.seq (.assign 9 (.get 8)) (.seq (.release 7) (.release 6)))))) 10
    (fun store state => store = initial ∧ state = start) _
  -- The means of the rows.
  refine Stmt.seq_spec (Live.call rowMeans_implements rfl hMeans rfl (Live.start hHeap) hRoom
    (x := (x, t, d)) (by simp only [rowMeansNeed]; omega) (afterArgs := start)
    (vals := [.i64 px, .i64 t, .i64 d])
    (by simp [Expr.evalResults, Expr.eval, hGet.1, hGet.2.2.2.1, hGet.2.2.2.2.1])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hX⟩, rfl⟩ (by rw [hStart]; decide)) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨heap1, pm, hLive1, rfl⟩
  let s1 := start.update 6 (.i64 pm)
  have hS1 : s1.params.length + s1.locals.length = 10 := by rw [hLen, hStart]
  have hGetS1 : ∀ j, j < 6 → s1.get j = start.get j := fun j hj => by
    simp only [s1]
    rw [State.get_update_ne (by omega)]
  -- The inverse standard deviations of the rows.
  refine Stmt.seq_spec (Live.call rowInvStd_implements rfl hInv rfl hLive1 hRoom
    (x := (x, means, t, d, eps)) (by simp only [rowMeansNeed, rowInvStdNeed]; omega)
    (afterArgs := s1) (vals := [.i64 px, .i64 pm, .i64 t, .i64 d, .f64 eps.toBits])
    (by simp [Expr.evalResults, Expr.eval, s1, State.get_update_same, hStart,
      hGetS1 0 (by decide), hGetS1 3 (by decide), hGetS1 4 (by decide), hGetS1 5 (by decide),
      hGet.1, hGet.2.2.2.1, hGet.2.2.2.2.1, hGet.2.2.2.2.2])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hLive1.borrowed px _ hX⟩, [.i64 pm], _, rfl,
      ⟨pm, rfl, (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩, rfl⟩
    (by rw [hS1]; decide)) ?_
  apply Triple.of_forall
  rintro store2 t2 ⟨heap2, pi, hLive2, rfl⟩
  let s2 := s1.update 7 (.i64 pi)
  have hS2 : s2.params.length + s2.locals.length = 10 := by rw [hLen, hS1]
  have hGetS2 : ∀ j, j < 6 → s2.get j = start.get j := fun j hj => by
    simp only [s2, s1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]
  have hS2Get6 : s2.get 6 = some (.i64 pm) := by
    simp only [s2, s1]
    rw [State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hStart]; decide)
  -- The normalized rows, scaled and shifted.
  refine Stmt.seq_spec (Live.call normalizeRows_implements rfl hNormalize rfl hLive2 hRoom
    (x := (x, means, inv, g, b, t, d))
    (by simp only [rowMeansNeed, rowInvStdNeed, normalizeNeed]; omega)
    (afterArgs := s2) (vals := [.i64 px, .i64 pm, .i64 pi, .i64 pg, .i64 pb, .i64 t, .i64 d])
    (by simp [Expr.evalResults, Expr.eval, s2, State.get_update_same, hS1, hS2Get6,
      hGetS2 0 (by decide), hGetS2 1 (by decide), hGetS2 2 (by decide), hGetS2 3 (by decide),
      hGetS2 4 (by decide), hGet.1, hGet.2.1, hGet.2.2.1, hGet.2.2.2.1, hGet.2.2.2.2.1])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hLive2.borrowed px _ hX⟩, [.i64 pm], _, rfl,
      ⟨pm, rfl, (hLive2.tempsOwned _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).borrowed⟩,
      [.i64 pi], _, rfl, ⟨pi, rfl, (hLive2.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩,
      [.i64 pg], _, rfl, ⟨pg, rfl, hLive2.borrowed pg _ hG⟩,
      [.i64 pb], _, rfl, ⟨pb, rfl, hLive2.borrowed pb _ hB⟩, rfl⟩
    (by rw [hS2]; decide)) ?_
  apply Triple.of_forall
  rintro store3 t3 ⟨heap3, pr, hLive3, rfl⟩
  let s3 := s2.update 8 (.i64 pr)
  let s4 := s3.update 9 (.i64 pr)
  have hS3 : s3.params.length + s3.locals.length = 10 := by rw [hLen, hS2]
  refine Stmt.seq_spec (Stmt.run_spec (final := s4) (by
    simp [Stmt.run, Expr.eval, State.set?_eq_update _ (show 9 < s3.params.length +
      s3.locals.length by rw [hS3]; decide), s4, s3, State.get_update_same,
      show 8 < s2.params.length + s2.locals.length by rw [hS2]; decide])) ?_
  -- The temporaries are released, the inverse deviations first.
  have hS4Get7 : s4.get 7 = some (.i64 pi) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hS1]; decide)
  have hS4Get6 : s4.get 6 = some (.i64 pm) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact hS2Get6
  refine Stmt.seq_spec (hLive3.releaseSecond hImports hRelease hS4Get7) ?_
  apply Triple.of_forall
  rintro store4 st4 ⟨hLive4, rfl⟩
  refine (hLive4.releaseSecond hImports hRelease hS4Get6).mono (fun _ _ h => h) ?_
  rintro store5 st5 ⟨hLive5, rfl⟩
  have hParams : ∀ (heap' : Heap) (store' : Store Unit),
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' [.i64 px, .i64 pg, .i64 pb, .i64 t, .i64 d, .f64 eps.toBits]
        (x, g, b, t, d, eps) := fun heap' store' hKeep =>
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hKeep px _ hX⟩, [.i64 pg], _, rfl, ⟨pg, rfl, hKeep pg _ hG⟩,
      [.i64 pb], _, rfl, ⟨pb, rfl, hKeep pb _ hB⟩, rfl⟩
  obtain ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLive5.finish (need := layerNormRowsNeed (x, g, b, t, d, eps))
      (by simp only [rowMeansNeed, rowInvStdNeed, normalizeNeed, layerNormRowsNeed]; omega)
      hParams
  exact ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, [.i64 pr], s4,
    by simp [gpt.layerNormRows.ir, Func.scratch, Expr.evalResults, Expr.eval, s4,
      State.get_update_same, hS3], hOwned, hOutB, hOutO⟩

/-- `encode` succeeds on `gpt.module`, and its bytes decode to a module whose
exports compute the kernels exactly. -/
theorem gpt_bytes : ∃ bytes, Encoding.encode gpt.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 dotTuple (fun _ => 0) ∧
      Implements m 4 matVecTuple matVecNeed ∧ Implements m 5 layerTuple layerNeed ∧
      Implements m 6 LeanExe.Examples.Gpt.exp (fun _ => 0) ∧
      Implements m 7 LeanExe.Examples.Gpt.softmax softmaxNeed ∧
      Implements m 8 matVec2Tuple matVec2Need ∧ Implements m 9 matMulTuple matMulNeed ∧
      Implements m 10 addTuple addNeed ∧ Implements m 11 LeanExe.Examples.Gpt.tanh (fun _ => 0) ∧
      Implements m 12 LeanExe.Examples.Gpt.gelu (fun _ => 0) ∧
      Implements m 13 LeanExe.Examples.Gpt.geluArray geluNeed ∧ Implements m 14 mlpTuple mlpNeed ∧
      Implements m 15 rowMeansTuple rowMeansNeed ∧ Implements m 16 rowInvStdTuple rowInvStdNeed ∧
      Implements m 17 normalizeTuple normalizeNeed ∧
      Implements m 18 layerNormRowsTuple layerNormRowsNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip gpt.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, gpt.module, decoded, dot_implements, matVec_implements,
    layerNorm_implements, exp_implements, softmax_implements, matVec2_implements,
    matMul_implements, add_implements, tanh_pure.implements, gelu_pure.implements,
    geluArray_implements, mlp_implements, rowMeans_implements, rowInvStd_implements,
    normalizeRows_implements, layerNormRows_implements⟩

end Project.Gpt
