import Project.Gpt.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Run
import Project.IR.Call
import Project.IR.Release
import Project.IR.Live

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

theorem dot_implements : Implements gpt.module 2 dotTuple := by
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

theorem matVec_implements : Implements gpt.module 3 matVecTuple := by
  refine Func.implements_heap gpt.funcs 1 gpt.matVec.ir "matVec" rfl matVecTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨m, v, rows, cols⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨pv, rfl, hVs⟩, rfl⟩ hCap
  change heap.Borrowed initial pm (m.map Float.toBits) at hMs
  change heap.Borrowed initial pv (v.map Float.toBits) at hVs
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
    (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono (fun _ _ h => h) ?_
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.matVec.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  rw [matVecTuple, matVec_eq, build_map]
  exact hNew.owned

/-- `layerNorm` with its four arguments as one tuple. -/
def layerTuple (x : Array Float × Array Float × Array Float × Float) : Array Float :=
  LeanExe.Examples.Gpt.layerNorm x.1 x.2.1 x.2.2.1 x.2.2.2

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

theorem layerNorm_implements : Implements gpt.module 4 layerTuple := by
  refine Func.implements_heap gpt.funcs 2 gpt.layerNorm.ir "layerNorm" rfl layerTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨xs, g, b, eps⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pg, rfl, hGs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
  change heap.Borrowed initial pg (g.map Float.toBits) at hGs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
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
    (by decide) (by simp [hV3.1, hV3.2]) hHeap hCap
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.layerNorm.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  rw [layerTuple, layerNorm_eq, hSum, hVar, build_map]
  exact hNew.owned

/-- `exp` keeps the store, so calls to it may run in loop bodies and array
elements. -/
theorem exp_pure : ImplementsPure gpt.module 5 LeanExe.Examples.Gpt.exp := by
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

theorem exp_implements : Implements gpt.module 5 LeanExe.Examples.Gpt.exp :=
  exp_pure.implements

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
  .seq (.call 5 [⟨.f64, .binF .sub (.ofBits (.read 0 (.get 10))) (.getF 6)⟩] [11])
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
    Triple gpt.module (.call 5 args results) scratch
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
    Implements gpt.module 6 LeanExe.Examples.Gpt.softmax := by
  refine Func.implements_heap gpt.funcs 4 gpt.softmax.ir "softmax" rfl
    LeanExe.Examples.Gpt.softmax (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨px, rfl, hXs⟩ hCap
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
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
      (.call 5 [⟨.f64, .binF .sub (.ofBits (.read 0 (.get 17))) (.getF 6)⟩] [18])
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
    hCap
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.softmax.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  rw [softmax_eq, hMax, hSum, build_map]
  exact hNew.owned

/-- `matVec2` with its five arguments as one tuple. -/
def matVec2Tuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.matVec2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem matVec2_implements : Implements gpt.module 7 matVec2Tuple := by
  refine Func.implements_heap gpt.funcs 5 gpt.matVec2.ir "matVec2" rfl matVec2Tuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨w1, w2, x, hidden, d⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨p1, rfl, hW1⟩, _, _, rfl, ⟨p2, rfl, hW2⟩, _, _, rfl, ⟨px, rfl, hX⟩, rfl⟩ hCap
  change heap.Borrowed initial p1 (w1.map Float.toBits) at hW1
  change heap.Borrowed initial p2 (w2.map Float.toBits) at hW2
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hMatVec : gpt.module.funcs[3 - gpt.module.imports.length]? =
      some (gpt.matVec.ir.function (2 + 1)) := compile_funcs (funcs := gpt.funcs) (i := 1) rfl
  let start : State :=
    { params := [.i64 p1, .i64 p2, .i64 px, .i64 hidden, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 8 := rfl
  have hGet : start.get 0 = some (.i64 p1) ∧ start.get 1 = some (.i64 p2) ∧
      start.get 2 = some (.i64 px) ∧ start.get 3 = some (.i64 hidden) ∧
      start.get 4 = some (.i64 d) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  show Triple _ (.seq (.call 3 [⟨.u64, .get 0⟩, ⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [5])
    (.seq (.call 3 [⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 3⟩] [6])
      (.seq (.assign 7 (.get 6)) (.release 5)))) 8
    (fun store state => store = initial ∧ state = start) _
  -- The temporary: `w1 · x`.
  refine Stmt.seq_spec (Live.call matVec_implements rfl hMatVec rfl (Live.start hHeap) hCap
    (x := (w1, x, hidden, d)) (afterArgs := start)
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
  refine Stmt.seq_spec (Live.call matVec_implements rfl hMatVec rfl hLive1 hCap
    (x := (w2, matVecTuple (w1, x, hidden, d), d, hidden))
    (afterArgs := start.update 5 (.i64 ph)) (vals := [.i64 p2, .i64 ph, .i64 d, .i64 hidden])
    (by simp [Expr.evalResults, Expr.eval, hU 1 (by decide), hU 4 (by decide),
      hU 3 (by decide), hU5, hGet.2.1, hGet.2.2.2.1, hGet.2.2.2.2])
    ⟨[.i64 p2], _, rfl, ⟨p2, rfl, hLive1.borrowed p2 _ hW2 Apart.nil⟩, [.i64 ph], _, rfl,
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
  obtain ⟨heap', hAt', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLive3.finish
  exact ⟨heap', hAt', hCaps', hKeepB, hKeepO, [.i64 pr], t3,
    by simp [gpt.matVec2.ir, Func.scratch, Expr.evalResults, Expr.eval, t3, start], hOwned,
    hOutB, hOutO⟩

/-- `matMul` with its five arguments as one tuple. -/
def matMulTuple (x : Array Float × Array Float × UInt64 × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.matMul x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

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

theorem matMul_implements : Implements gpt.module 8 matMulTuple := by
  refine Func.implements_heap gpt.funcs 6 gpt.matMul.ir "matMul" rfl matMulTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨a, b, n, k, m⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pa, rfl, hAs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hCap
  change heap.Borrowed initial pa (a.map Float.toBits) at hAs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
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
    (by decide) (by simp [start]) hHeap hCap
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.matMul.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  rw [matMulTuple, matMul_eq, build_map]
  exact hNew.owned

/-- `add` with its two arguments as one pair. -/
def addTuple (x : Array Float × Array Float) : Array Float :=
  LeanExe.Examples.Gpt.add x.1 x.2

theorem add_implements : Implements gpt.module 9 addTuple := by
  refine Func.implements_heap gpt.funcs 7 gpt.add.ir "add" rfl addTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨a, b⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨pa, rfl, hAs⟩, ⟨pb, rfl, hBs⟩⟩ hCap
  change heap.Borrowed initial pa (a.map Float.toBits) at hAs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
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
    hCap
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.add.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hAdd : LeanExe.Examples.Gpt.add a b =
      LeanExe.build a.size.toUInt64 (fun i => a[i.toNat]! + b[i.toNat]!) := rfl
  rw [addTuple, hAdd, build_map]
  exact hNew.owned

theorem tanh_pure : ImplementsPure gpt.module 10 LeanExe.Examples.Gpt.tanh := by
  refine Func.implementsPure gpt.funcs 8 gpt.tanh.ir "tanh" rfl LeanExe.Examples.Gpt.tanh
    (fun _ => rfl) fun z initial => ?_
  have k2 : (2.0 : Float).toBits = 4611686018427387904 := by decide +kernel
  have k1 : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let start : State := { params := [.f64 z.toBits], locals := [.f64 0] }
  let final := start.update 1 (.f64 (LeanExe.Examples.Gpt.exp (2.0 * z)).toBits)
  show Triple _ (.call 5 [⟨.f64, .binF .mul (.constF 4611686018427387904) (.getF 0)⟩] [1]) 2
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
    Triple gpt.module (.call 10 args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) :=
  Stmt.callPure_spec tanh_pure (f := gpt.tanh.ir.function (2 + 8)) rfl
    (by rw [show gpt.module.imports.length = 0 from rfl]
        exact compile_funcs (funcs := gpt.funcs) (i := 8) rfl) hParams (x := d) hArgs hSet

theorem gelu_pure : ImplementsPure gpt.module 11 LeanExe.Examples.Gpt.gelu := by
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
        (.getF 0))))) (.call 10 [⟨.f64, .getF 1⟩] [2])) 3
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
    Triple gpt.module (.call 11 args results) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧ state = next) :=
  Stmt.callPure_spec gelu_pure (f := gpt.gelu.ir.function (2 + 9)) rfl
    (by rw [show gpt.module.imports.length = 0 from rfl]
        exact compile_funcs (funcs := gpt.funcs) (i := 9) rfl) hParams (x := d) hArgs hSet

theorem geluArray_implements :
    Implements gpt.module 12 LeanExe.Examples.Gpt.geluArray := by
  refine Func.implements_heap gpt.funcs 10 gpt.geluArray.ir "geluArray" rfl
    LeanExe.Examples.Gpt.geluArray (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨px, rfl, hXs⟩ hCap
  change heap.Borrowed initial px (xs.map Float.toBits) at hXs
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
      (.call 11 [⟨.f64, .ofBits (.read 0 (.get 4))⟩] [5]) (.toBits (.getF 5)))) 6
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hX.lengthRead,
      State.set?_eq_update, s1, start])) ?_
  have hS1 : s1.params.length = 1 ∧ s1.locals.length = 6 := by simp [s1, start]
  refine (Stmt.buildWith_spec (writes := [5]) (n := xs.size.toUInt64)
    (fun i => (LeanExe.Examples.Gpt.gelu xs[i.toNat]!).toBits) hMemory32 hImports hAlloc
    (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2]) hHeap
    hCap
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.geluArray.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hGelu : LeanExe.Examples.Gpt.geluArray xs =
      LeanExe.build xs.size.toUInt64 (fun i => LeanExe.Examples.Gpt.gelu xs[i.toNat]!) := rfl
  rw [hGelu, build_map]
  exact hNew.owned

theorem matMul_size (a b : Array Float) (n k m : UInt64) :
    (matMulTuple (a, b, n, k, m)).size = (n * m).toNat := by
  simp [matMulTuple, matMul_eq, LeanExe.build]

/-- `linear` with its seven arguments as one tuple. -/
def linearTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64 × UInt64) :
    Array Float :=
  LeanExe.Examples.Gpt.linear x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2

theorem linear_size (x w b : Array Float) (l n k m : UInt64) :
    (linearTuple (x, w, b, l, n, k, m)).size = (n * m).toNat := by
  simp [linearTuple, LeanExe.Examples.Gpt.linear, LeanExe.build]

/-- One step of the sum for element `e` of `linear`, with layer `l` of the weights. -/
def linStep (x w : Array Float) (l k m e c : UInt64) (acc : Float) : Float :=
  acc + x[(e / m * k + c).toNat]! * w[(l * (k * m) + (c * m + e % m)).toNat]!

/-- The compiled loop body of `linear`. -/
def linBody : Stmt :=
  .seq (.assign 13 (.binF .add (.getF 10) (.binF .mul
    (.ofBits (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 9) (.get 6)) (.get 5)) (.get 12))))
    (.ofBits (.read 1 (.bin .add (.bin .mul (.get 3) (.bin .mul (.get 5) (.get 6)))
      (.bin .add (.bin .mul (.get 12) (.get 6)) (.bin .remU (.get 9) (.get 6)))))))))
    (.assign 10 (.getF 13))

theorem linBody_run {initial : Store Unit} {px pw : UInt64} {x w : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits))
    (hW : UInt64Array.At initial pw (w.map Float.toBits)) {state : State} {c : Nat}
    {l k m e : UInt64} {acc : Float} (hm : m ≠ 0) (hParams : state.params.length = 7)
    (hLocals : state.locals.length = 10) (h0 : state.get 0 = some (.i64 px))
    (h1 : state.get 1 = some (.i64 pw)) (h3 : state.get 3 = some (.i64 l))
    (h5 : state.get 5 = some (.i64 k)) (h6 : state.get 6 = some (.i64 m))
    (h9 : state.get 9 = some (.i64 e)) (h10 : state.get 10 = some (.f64 acc.toBits))
    (h12 : state.get 12 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, linBody.run initial.mem 14 state = some final ∧
      State.Frame 14 [10, 13] state final ∧
      final.Holds [10] (Scalar.values (linStep x w l k m e (UInt64.ofNat c) acc)) := by
  simp [linBody, Stmt.run, Expr.eval, h0, h1, h3, h5, h6, h9, h10, h12, Expr.readValue_at hX,
    Expr.readValue_at hW, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits, hm]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, linStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul]

theorem linear_implements : Implements gpt.module 29 linearTuple := by
  refine Func.implements_heap gpt.funcs 27 gpt.linear.ir "linear" rfl linearTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨x, w, b, l, n, k, m⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pw, rfl, hWs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pw (w.map Float.toBits) at hWs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 pw, .i64 pb, .i64 l, .i64 n, .i64 k, .i64 m]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.buildWith 7 8 9 (.bin .mul (.get 4) (.get 6))
      (.seq (.assign 10 (.constF 0)) (.loop 11 12 (.get 5) linBody))
      (.toBits (.binF .add (.getF 10) (.ofBits (.read 2 (.bin .add (.bin .mul (.get 3) (.get 6))
        (.bin .remU (.get 9) (.get 6)))))))) 14
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [10, 11, 12, 13]) (n := n * m)
    (fun e => (LeanExe.loop k 0.0 (linStep x w l k m e) + b[(l * m + e % m).toNat]!).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hm : m ≠ 0 := by rintro rfl; simp at he
    have hState : state.params.length = 7 ∧ state.locals.length = 10 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 7 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g2 : state.get 2 = some (.i64 pb) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 l) := (hGet 3 (by decide)).trans rfl
    have g5 : state.get 5 = some (.i64 k) := (hGet 5 (by decide)).trans rfl
    have g6 : state.get 6 = some (.i64 m) := (hGet 6 (by decide)).trans rfl
    have hX := hAt px _ hXs
    have hW := hAt pw _ hWs
    have hB := hAt pb _ hBs
    let s1 := state.update 10 (.f64 0)
    have hS1 : s1.params.length = 7 ∧ s1.locals.length = 10 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 10 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [10]) (writes := [10, 13]) (init := (0.0 : Float)) (n := k)
      (linStep x w l k m (UInt64.ofNat e)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2]) ⟨s1, by simp [Expr.eval, hS1Get 5 (by decide), g5]⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 7 ∧ st.locals.length = 10 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 7 ∨ j = 9 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g10 : st.get 10 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := linBody_run hX hW hm hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans g3) ((hKeep 5 (by omega)).trans g5)
        ((hKeep 6 (by omega)).trans g6) ((hKeep 9 (by omega)).trans hIndex) g10 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g10 : u.get 10 = some (.f64 (LeanExe.loop k 0.0
          (linStep x w l k m (UInt64.ofNat e))).toBits) := (List.forall₂_cons.mp hHolds).1
      have hU : ∀ j, j < 7 ∨ j = 9 → u.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have hUL : u.params.length = 7 ∧ u.locals.length = 10 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have u2 : u.get 2 = some (.i64 pb) := (hU 2 (by omega)).trans g2
      have u3 : u.get 3 = some (.i64 l) := (hU 3 (by omega)).trans g3
      have u6 : u.get 6 = some (.i64 m) := (hU 6 (by omega)).trans g6
      have u9 : u.get 9 = some (.i64 (UInt64.ofNat e)) := (hU 9 (by omega)).trans hIndex
      refine ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), ?_⟩
      simp [Expr.eval, u2, u3, u6, u9, g10, hUL.1, hUL.2, State.set?_eq_update,
        Expr.readValue_at hB, F64Op.apply, U64Op.apply, getElem!_map_toBits, F64Bits.toBits_add,
        hm]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.linear.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : linearTuple (x, w, b, l, n, k, m) = LeanExe.build (n * m)
      (fun e => LeanExe.loop k 0.0 (linStep x w l k m e) + b[(l * m + e % m).toNat]!) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowMeans` with its three arguments as one tuple. -/
def rowMeansTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.rowMeans x.1 x.2.1 x.2.2

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

theorem rowMeans_implements : Implements gpt.module 14 rowMeansTuple := by
  refine Func.implements_heap gpt.funcs 12 gpt.rowMeans.ir "rowMeans" rfl rowMeansTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, t, d⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨px, rfl, hXs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
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
    (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.rowMeans.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : rowMeansTuple (x, t, d) =
      LeanExe.build t (fun r => LeanExe.loop d 0.0 (meanStep x d r) / d.toFloat) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowInvStd` with its five arguments as one tuple. -/
def rowInvStdTuple (x : Array Float × Array Float × UInt64 × UInt64 × Float) : Array Float :=
  LeanExe.Examples.Gpt.rowInvStd x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

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

theorem rowInvStd_implements : Implements gpt.module 15 rowInvStdTuple := by
  refine Func.implements_heap gpt.funcs 13 gpt.rowInvStd.ir "rowInvStd" rfl rowInvStdTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, means, t, d, eps⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (means.map Float.toBits) at hMs
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
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
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
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.rowInvStd.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : rowInvStdTuple (x, means, t, d, eps) = LeanExe.build t (fun r =>
      1.0 / (LeanExe.loop d 0.0 (devStep x means d r) / d.toFloat + eps).sqrt) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `normalizeRows` with its eight arguments as one tuple. -/
def normalizeTuple (x : Array Float × Array Float × Array Float × Array Float × Array Float ×
    UInt64 × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.normalizeRows x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2

/-- Element `e` of `normalizeRows`, with layer `l` of the gains and biases. -/
def normalizeAt (x means inv g b : Array Float) (l d e : UInt64) : Float :=
  (x[e.toNat]! - means[(e / d).toNat]!) * inv[(e / d).toNat]! * g[(l * d + e % d).toNat]! +
    b[(l * d + e % d).toNat]!

theorem normalizeRows_implements : Implements gpt.module 16 normalizeTuple := by
  refine Func.implements_heap gpt.funcs 14 gpt.normalizeRows.ir "normalizeRows" rfl
    normalizeTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, means, inv, g, b, l, t, d⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨pi, rfl, hIs⟩,
      _, _, rfl, ⟨pg, rfl, hGs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (means.map Float.toBits) at hMs
  change heap.Borrowed initial pi (inv.map Float.toBits) at hIs
  change heap.Borrowed initial pg (g.map Float.toBits) at hGs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 px, .i64 pm, .i64 pi, .i64 pg, .i64 pb, .i64 l, .i64 t, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.build 8 9 10 (.bin .mul (.get 6) (.get 7)) (.toBits (.binF .add (.binF .mul
      (.binF .mul (.binF .sub (.ofBits (.read 0 (.get 10)))
        (.ofBits (.read 1 (.bin .divU (.get 10) (.get 7)))))
        (.ofBits (.read 2 (.bin .divU (.get 10) (.get 7)))))
      (.ofBits (.read 3 (.bin .add (.bin .mul (.get 5) (.get 7)) (.bin .remU (.get 10) (.get 7))))))
      (.ofBits (.read 4 (.bin .add (.bin .mul (.get 5) (.get 7)) (.bin .remU (.get 10) (.get 7)))))))) 11
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.build_spec (n := t * d) (fun e => (normalizeAt x means inv g b l d e).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hState : state.params.length = 8 ∧ state.locals.length = 6 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 8 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 px) := (hGet 0 (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 pm) := (hGet 1 (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 pi) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 pg) := (hGet 3 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 pb) := (hGet 4 (by decide)).trans rfl
    have g5 : state.get 5 = some (.i64 l) := (hGet 5 (by decide)).trans rfl
    have g7 : state.get 7 = some (.i64 d) := (hGet 7 (by decide)).trans rfl
    by_cases hd : d = 0 <;> simp [Expr.eval, g0, g1, g2, g3, g4, g5, g7, hIndex,
      Expr.readValue_at (hAt px _ hXs), Expr.readValue_at (hAt pm _ hMs),
      Expr.readValue_at (hAt pi _ hIs), Expr.readValue_at (hAt pg _ hGs),
      Expr.readValue_at (hAt pb _ hBs), State.set?_eq_update, hState.1, hState.2, F64Op.apply,
      U64Op.apply, getElem!_map_toBits, normalizeAt, F64Bits.toBits_add, F64Bits.toBits_mul,
      F64Bits.toBits_sub, hd]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.normalizeRows.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : normalizeTuple (x, means, inv, g, b, l, t, d) =
      LeanExe.build (t * d) (normalizeAt x means inv g b l d) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `layerNormRows` with its seven arguments as one tuple. -/
def layerNormRowsTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64 ×
    Float) : Array Float :=
  LeanExe.Examples.Gpt.layerNormRows x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    x.2.2.2.2.2.2

theorem layerNormRows_implements :
    Implements gpt.module 17 layerNormRowsTuple := by
  refine Func.implements_heap gpt.funcs 15 gpt.layerNormRows.ir "layerNormRows" rfl
    layerNormRowsTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨x, g, b, l, t, d, eps⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hX⟩, _, _, rfl, ⟨pg, rfl, hG⟩, _, _, rfl, ⟨pb, rfl, hB⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  change heap.Borrowed initial pg (g.map Float.toBits) at hG
  change heap.Borrowed initial pb (b.map Float.toBits) at hB
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hMeans : gpt.module.funcs[14 - gpt.module.imports.length]? =
      some (gpt.rowMeans.ir.function (2 + 12)) := compile_funcs (funcs := gpt.funcs) (i := 12) rfl
  have hInv : gpt.module.funcs[15 - gpt.module.imports.length]? =
      some (gpt.rowInvStd.ir.function (2 + 13)) := compile_funcs (funcs := gpt.funcs) (i := 13) rfl
  have hNormalize : gpt.module.funcs[16 - gpt.module.imports.length]? =
      some (gpt.normalizeRows.ir.function (2 + 14)) :=
    compile_funcs (funcs := gpt.funcs) (i := 14) rfl
  let means := rowMeansTuple (x, t, d)
  let inv := rowInvStdTuple (x, means, t, d, eps)
  let start : State :=
    { params := [.i64 px, .i64 pg, .i64 pb, .i64 l, .i64 t, .i64 d, .f64 eps.toBits]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have sg0 : start.get 0 = some (.i64 px) := rfl
  have sg1 : start.get 1 = some (.i64 pg) := rfl
  have sg2 : start.get 2 = some (.i64 pb) := rfl
  have sg3 : start.get 3 = some (.i64 l) := rfl
  have sg4 : start.get 4 = some (.i64 t) := rfl
  have sg5 : start.get 5 = some (.i64 d) := rfl
  have sg6 : start.get 6 = some (.f64 eps.toBits) := rfl
  show Triple _ (.seq (.call 14 [⟨.u64, .get 0⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 5⟩] [7])
      (.seq (.call 15 [⟨.u64, .get 0⟩, ⟨.u64, .get 7⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 5⟩,
        ⟨.f64, .getF 6⟩] [8])
      (.seq (.call 16 [⟨.u64, .get 0⟩, ⟨.u64, .get 7⟩, ⟨.u64, .get 8⟩, ⟨.u64, .get 1⟩,
        ⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 5⟩] [9])
      (.seq (.assign 10 (.get 9)) (.seq (.release 8) (.release 7)))))) 11
    (fun store state => store = initial ∧ state = start) _
  -- The means of the rows.
  refine Stmt.seq_spec (Live.call rowMeans_implements rfl hMeans rfl (Live.start hHeap) hCap
    (x := (x, t, d)) (afterArgs := start)
    (vals := [.i64 px, .i64 t, .i64 d])
    (by simp [Expr.evalResults, Expr.eval, sg0, sg4, sg5])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hX⟩, rfl⟩ (by rw [hStart]; decide)) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨heap1, pm, hLive1, rfl⟩
  let s1 := start.update 7 (.i64 pm)
  have hS1 : s1.params.length + s1.locals.length = 11 := by rw [hLen, hStart]
  have hGetS1 : ∀ j, j < 7 → s1.get j = start.get j := fun j hj => by
    simp only [s1]
    rw [State.get_update_ne (by omega)]
  -- The inverse standard deviations of the rows.
  refine Stmt.seq_spec (Live.call rowInvStd_implements rfl hInv rfl hLive1 hCap
    (x := (x, means, t, d, eps))
    (afterArgs := s1) (vals := [.i64 px, .i64 pm, .i64 t, .i64 d, .f64 eps.toBits])
    (by simp [Expr.evalResults, Expr.eval, s1, State.get_update_same, hStart,
      hGetS1 0 (by decide), hGetS1 4 (by decide), hGetS1 5 (by decide), hGetS1 6 (by decide),
      sg0, sg4, sg5, sg6])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hLive1.borrowed px _ hX Apart.nil⟩, [.i64 pm], _, rfl,
      ⟨pm, rfl, (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩, rfl⟩
    (by rw [hS1]; decide)) ?_
  apply Triple.of_forall
  rintro store2 t2 ⟨heap2, pi, hLive2, rfl⟩
  let s2 := s1.update 8 (.i64 pi)
  have hS2 : s2.params.length + s2.locals.length = 11 := by rw [hLen, hS1]
  have hGetS2 : ∀ j, j < 7 → s2.get j = start.get j := fun j hj => by
    simp only [s2, s1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]
  have hS2Get7 : s2.get 7 = some (.i64 pm) := by
    simp only [s2, s1]
    rw [State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hStart]; decide)
  -- The normalized rows, scaled and shifted.
  refine Stmt.seq_spec (Live.call normalizeRows_implements rfl hNormalize rfl hLive2 hCap
    (x := (x, means, inv, g, b, l, t, d))
    (afterArgs := s2)
    (vals := [.i64 px, .i64 pm, .i64 pi, .i64 pg, .i64 pb, .i64 l, .i64 t, .i64 d])
    (by simp [Expr.evalResults, Expr.eval, s2, State.get_update_same, hS1, hS2Get7,
      hGetS2 0 (by decide), hGetS2 1 (by decide), hGetS2 2 (by decide), hGetS2 3 (by decide),
      hGetS2 4 (by decide), hGetS2 5 (by decide), sg0, sg1, sg2, sg3, sg4, sg5])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hLive2.borrowed px _ hX Apart.nil⟩, [.i64 pm], _, rfl,
      ⟨pm, rfl, (hLive2.tempsOwned _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).borrowed⟩,
      [.i64 pi], _, rfl, ⟨pi, rfl, (hLive2.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩,
      [.i64 pg], _, rfl, ⟨pg, rfl, hLive2.borrowed pg _ hG Apart.nil⟩,
      [.i64 pb], _, rfl, ⟨pb, rfl, hLive2.borrowed pb _ hB Apart.nil⟩, rfl⟩
    (by rw [hS2]; decide)) ?_
  apply Triple.of_forall
  rintro store3 t3 ⟨heap3, pr, hLive3, rfl⟩
  let s3 := s2.update 9 (.i64 pr)
  let s4 := s3.update 10 (.i64 pr)
  have hS3 : s3.params.length + s3.locals.length = 11 := by rw [hLen, hS2]
  refine Stmt.seq_spec (Stmt.run_spec (final := s4) (by
    simp [Stmt.run, Expr.eval, State.set?_eq_update _ (show 10 < s3.params.length +
      s3.locals.length by rw [hS3]; decide), s4, s3, State.get_update_same,
      show 9 < s2.params.length + s2.locals.length by rw [hS2]; decide])) ?_
  -- The temporaries are released, the inverse deviations first.
  have hS4Get8 : s4.get 8 = some (.i64 pi) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hS1]; decide)
  have hS4Get7 : s4.get 7 = some (.i64 pm) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact hS2Get7
  refine Stmt.seq_spec (hLive3.releaseSecond hImports hRelease hS4Get8) ?_
  apply Triple.of_forall
  rintro store4 st4 ⟨hLive4, rfl⟩
  refine (hLive4.releaseSecond hImports hRelease hS4Get7).mono (fun _ _ h => h) ?_
  rintro store5 st5 ⟨hLive5, rfl⟩
  obtain ⟨heap', hAt', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLive5.finish
  exact ⟨heap', hAt', hCaps', hKeepB, hKeepO, [.i64 pr], s4,
    by simp [gpt.layerNormRows.ir, Func.scratch, Expr.evalResults, Expr.eval, s4,
      State.get_update_same, hS3], hOwned, hOutB, hOutO⟩

/-- `maskedScores` with its six arguments as one tuple. -/
def maskedTuple (x : Array Float × Array Float × UInt64 × UInt64 × UInt64 × Float) : Array Float :=
  LeanExe.Examples.Gpt.maskedScores x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- One step of the dot product of query row `e / (nh · t)` and key row `e % t` over the
columns of head `e / t % nh`. -/
def scoreStep (q k : Array Float) (t nh dh e c : UInt64) (acc : Float) : Float :=
  acc + q[(e / (nh * t) * (nh * dh) + (e / t % nh * dh + c)).toNat]! *
    k[(e % t * (nh * dh) + (e / t % nh * dh + c)).toNat]!

/-- The compiled loop body of `maskedScores`. -/
def scoreBody : Stmt :=
  .seq (.assign 12 (.binF .add (.getF 9) (.binF .mul
    (.ofBits (.read 0 (.bin .add
      (.bin .mul (.bin .divU (.get 8) (.bin .mul (.get 3) (.get 2))) (.bin .mul (.get 3) (.get 4)))
      (.bin .add (.bin .mul (.bin .remU (.bin .divU (.get 8) (.get 2)) (.get 3)) (.get 4))
        (.get 11)))))
    (.ofBits (.read 1 (.bin .add (.bin .mul (.bin .remU (.get 8) (.get 2)) (.bin .mul (.get 3) (.get 4)))
      (.bin .add (.bin .mul (.bin .remU (.bin .divU (.get 8) (.get 2)) (.get 3)) (.get 4))
        (.get 11)))))))) (.assign 9 (.getF 12))

theorem scoreBody_run {initial : Store Unit} {pq pk : UInt64} {q k : Array Float}
    (hQ : UInt64Array.At initial pq (q.map Float.toBits))
    (hK : UInt64Array.At initial pk (k.map Float.toBits)) {state : State} {c : Nat}
    {t nh dh e : UInt64} {acc : Float} (ht : t ≠ 0) (hn : nh ≠ 0) (hnt : nh * t ≠ 0)
    (hParams : state.params.length = 6) (hLocals : state.locals.length = 12)
    (h0 : state.get 0 = some (.i64 pq)) (h1 : state.get 1 = some (.i64 pk))
    (h2 : state.get 2 = some (.i64 t)) (h3 : state.get 3 = some (.i64 nh))
    (h4 : state.get 4 = some (.i64 dh)) (h8 : state.get 8 = some (.i64 e))
    (h9 : state.get 9 = some (.f64 acc.toBits))
    (h11 : state.get 11 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, scoreBody.run initial.mem 13 state = some final ∧
      State.Frame 13 [9, 12] state final ∧
      final.Holds [9] (Scalar.values (scoreStep q k t nh dh e (UInt64.ofNat c) acc)) := by
  simp [scoreBody, Stmt.run, Expr.eval, h0, h1, h2, h3, h4, h8, h9, h11, Expr.readValue_at hQ,
    Expr.readValue_at hK, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits, ht, hn, hnt]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, scoreStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul]

theorem maskedScores_implements : Implements gpt.module 18 maskedTuple := by
  refine Func.implements_heap gpt.funcs 16 gpt.maskedScores.ir "maskedScores" rfl maskedTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨q, k, t, nh, dh, scale⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pq, rfl, hQs⟩, _, _, rfl, ⟨pk, rfl, hKs⟩, rfl⟩ hCap
  change heap.Borrowed initial pq (q.map Float.toBits) at hQs
  change heap.Borrowed initial pk (k.map Float.toBits) at hKs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pq, .i64 pk, .i64 t, .i64 nh, .i64 dh, .f64 scale.toBits]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0] }
  show Triple _ (.buildWith 6 7 8 (.bin .mul (.bin .mul (.get 2) (.get 3)) (.get 2))
      (.seq (.assign 9 (.constF 0)) (.loop 10 11 (.ite (.leU (.bin .remU (.get 8) (.get 2))
        (.bin .divU (.get 8) (.bin .mul (.get 3) (.get 2)))) (.get 4) (.const 0)) scoreBody))
      (.toBits (.binF .mul (.getF 9) (.getF 5)))) 13
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [9, 10, 11, 12]) (n := t * nh * t)
    (fun e => (LeanExe.loop (if e % t ≤ e / (nh * t) then dh else 0) 0.0 (scoreStep q k t nh dh e) *
      scale).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have ht : t ≠ 0 := by rintro rfl; simp at he
    have hn : nh ≠ 0 := by rintro rfl; simp at he
    have hnt : nh * t ≠ 0 := by
      intro h
      rw [UInt64.mul_assoc, h, UInt64.mul_zero] at he
      simp at he
    have hState : state.params.length = 6 ∧ state.locals.length = 12 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 6 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hQ := hAt pq _ hQs
    have hK := hAt pk _ hKs
    let s1 := state.update 9 (.f64 0)
    have hS1 : s1.params.length = 6 ∧ s1.locals.length = 12 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 9 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    have g2 : state.get 2 = some (.i64 t) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 nh) := (hGet 3 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 dh) := (hGet 4 (by decide)).trans rfl
    have g5 : state.get 5 = some (.f64 scale.toBits) := (hGet 5 (by decide)).trans rfl
    refine (Stmt.loop_spec (vars := [9]) (writes := [9, 12]) (init := (0.0 : Float))
      (n := if UInt64.ofNat e % t ≤ UInt64.ofNat e / (nh * t) then dh else 0)
      (scoreStep q k t nh dh (UInt64.ofNat e)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      (by by_cases hc : UInt64.ofNat e % t ≤ UInt64.ofNat e / (nh * t) <;>
        simp [Expr.eval, hS1Get 2 (by decide), hS1Get 3 (by decide), hS1Get 4 (by decide),
          hS1Get 8 (by decide), g2, g3, g4, hIndex, State.set?_eq_update, hS1.1, hS1.2, U64Op.apply,
          ht, hnt, hc])
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 6 ∧ st.locals.length = 12 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 6 ∨ j = 8 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g9 : st.get 9 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := scoreBody_run hQ hK ht hn hnt hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans g2) ((hKeep 3 (by omega)).trans g3)
        ((hKeep 4 (by omega)).trans g4) ((hKeep 8 (by omega)).trans hIndex) g9 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g9 : u.get 9 = some (.f64 (LeanExe.loop
          (if UInt64.ofNat e % t ≤ UInt64.ofNat e / (nh * t) then dh else 0) 0.0
          (scoreStep q k t nh dh (UInt64.ofNat e))).toBits) := (List.forall₂_cons.mp hHolds).1
      have hU : ∀ j, j < 6 ∨ j = 8 → u.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have u5 : u.get 5 = some (.f64 scale.toBits) := (hU 5 (by omega)).trans g5
      refine ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), ?_⟩
      simp [Expr.eval, u5, g9, F64Op.apply, F64Bits.toBits_mul]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.maskedScores.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : maskedTuple (q, k, t, nh, dh, scale) = LeanExe.build (t * nh * t) (fun e =>
      LeanExe.loop (if e % t ≤ e / (nh * t) then dh else 0) 0.0 (scoreStep q k t nh dh e) *
        scale) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowMax` with its three arguments as one tuple. -/
def rowMaxTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.rowMax x.1 x.2.1 x.2.2

/-- One step of the maximum over row `r`. -/
def rowMaxStep (x : Array Float) (w r c : UInt64) (acc : Float) : Float :=
  max acc x[(r * w + c).toNat]!

/-- The compiled loop body of `rowMax`. -/
def rowMaxBody : Stmt :=
  .seq (.assign 9 (.iteF
    (.leF (.getF 6) (.ofBits (.read 0 (.bin .add (.bin .mul (.get 5) (.get 1)) (.get 8)))))
    (.ofBits (.read 0 (.bin .add (.bin .mul (.get 5) (.get 1)) (.get 8)))) (.getF 6)))
    (.assign 6 (.getF 9))

theorem rowMaxBody_run {initial : Store Unit} {px : UInt64} {x : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits)) {state : State} {c : Nat}
    {w r : UInt64} {acc : Float} (hParams : state.params.length = 3)
    (hLocals : state.locals.length = 9) (h0 : state.get 0 = some (.i64 px))
    (h1 : state.get 1 = some (.i64 w)) (h5 : state.get 5 = some (.i64 r))
    (h6 : state.get 6 = some (.f64 acc.toBits)) (h8 : state.get 8 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, rowMaxBody.run initial.mem 10 state = some final ∧
      State.Frame 10 [6, 9] state final ∧
      final.Holds [6] (Scalar.values (rowMaxStep x w r (UInt64.ofNat c) acc)) := by
  simp [rowMaxBody, Stmt.run, Expr.eval, h0, h1, h5, h6, h8, Expr.readValue_at hX,
    State.set?_eq_update, hParams, hLocals, U64Op.apply, getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, rowMaxStep, hParams, hLocals, F64Bits.toBits_max]

theorem rowMax_implements : Implements gpt.module 19 rowMaxTuple := by
  refine Func.implements_heap gpt.funcs 17 gpt.rowMax.ir "rowMax" rfl rowMaxTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, t, nh⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨px, rfl, hXs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 t, .i64 nh]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0] }
  show Triple _ (.buildWith 3 4 5 (.bin .mul (.get 1) (.get 2))
      (.seq (.assign 6 (.binF .sub (.constF 9223372036854775808)
        (.binF .div (.constF 4607182418800017408) (.constF 0))))
        (.loop 7 8 (.bin .add (.bin .divU (.get 5) (.get 2)) (.const 1)) rowMaxBody))
      (.toBits (.getF 6))) 10
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [6, 7, 8, 9]) (n := t * nh)
    (fun r => (LeanExe.loop (r / nh + 1) (-(1.0 / 0.0)) (rowMaxStep x t r)).toBits) hMemory32
    hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro r store state hr hAt hFrame hIndex
    have hn : nh ≠ 0 := by rintro rfl; simp at hr
    have hState : state.params.length = 3 ∧ state.locals.length = 9 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 3 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hX := hAt px _ hXs
    let s1 := state.update 6 (.f64 (-(1.0 / 0.0) : Float).toBits)
    have hS1 : s1.params.length = 3 ∧ s1.locals.length = 9 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 6 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1, F64Op.apply,
        F64Bits.toBits_neg, F64Bits.toBits_div, hZero, hOne])) ?_
    have g2 : state.get 2 = some (.i64 nh) := (hGet 2 (by decide)).trans rfl
    refine (Stmt.loop_spec (vars := [6]) (writes := [6, 9]) (init := (-(1.0 / 0.0) : Float))
      (n := UInt64.ofNat r / nh + 1) (rowMaxStep x t (UInt64.ofNat r)) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2])
      (by simp [Expr.eval, hS1Get 2 (by decide), hS1Get 5 (by decide), g2, hIndex,
        State.set?_eq_update, hS1.1, hS1.2, U64Op.apply, hn])
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 3 ∧ st.locals.length = 9 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 3 ∨ j = 5 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g6 : st.get 6 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := rowMaxBody_run hX hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 5 (by omega)).trans hIndex) g6 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g6 : u.get 6 = some (.f64 (LeanExe.loop (UInt64.ofNat r / nh + 1) (-(1.0 / 0.0))
          (rowMaxStep x t (UInt64.ofNat r))).toBits) := (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g6]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.rowMax.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : rowMaxTuple (x, t, nh) = LeanExe.build (t * nh)
      (fun r => LeanExe.loop (r / nh + 1) (-(1.0 / 0.0)) (rowMaxStep x t r)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowSumExp` with its four arguments as one tuple. -/
def rowSumExpTuple (x : Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.rowSumExp x.1 x.2.1 x.2.2.1 x.2.2.2

/-- One step of the sum of exponentials over row `r`. -/
def sumExpStep (x mx : Array Float) (w r c : UInt64) (acc : Float) : Float :=
  acc + LeanExe.Examples.Gpt.exp (x[(r * w + c).toNat]! - mx[r.toNat]!)

/-- The compiled loop body of `rowSumExp`. -/
def sumExpBody : Stmt :=
  .seq (.call 5 [⟨.f64, .binF .sub
      (.ofBits (.read 0 (.bin .add (.bin .mul (.get 6) (.get 2)) (.get 9))))
      (.ofBits (.read 1 (.get 6)))⟩] [10])
    (.seq (.assign 11 (.binF .add (.getF 7) (.getF 10))) (.assign 7 (.getF 11)))

theorem sumExpBody_spec {initial : Store Unit} {px pm : UInt64} {x mx : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits))
    (hM : UInt64Array.At initial pm (mx.map Float.toBits)) {state : State} {c : Nat}
    {w r : UInt64} {acc : Float} (hParams : state.params.length = 4)
    (hLocals : state.locals.length = 10) (h0 : state.get 0 = some (.i64 px))
    (h1 : state.get 1 = some (.i64 pm)) (h2 : state.get 2 = some (.i64 w))
    (h6 : state.get 6 = some (.i64 r)) (h7 : state.get 7 = some (.f64 acc.toBits))
    (h9 : state.get 9 = some (.i64 (UInt64.ofNat c))) :
    Triple gpt.module sumExpBody 12 (fun store st => store = initial ∧ st = state)
      (fun store st => store = initial ∧ State.Frame 12 [7, 10, 11] state st ∧
        st.Holds [7] (Scalar.values (sumExpStep x mx w r (UInt64.ofNat c) acc))) := by
  let dv := x[(r * w + UInt64.ofNat c).toNat]! - mx[r.toNat]!
  let e := LeanExe.Examples.Gpt.exp dv
  let a := (state.update 12 (.i64 (r * w + UInt64.ofNat c))).update 12 (.i64 r)
  let b := a.update 10 (.f64 e.toBits)
  let s := b.update 11 (.f64 (acc + e).toBits)
  let f := s.update 7 (.f64 (acc + e).toBits)
  have hA : a.params.length = 4 ∧ a.locals.length = 10 := by simp [a, hParams, hLocals]
  refine Stmt.seq_spec (exp_call rfl (afterArgs := a) (next := b) (d := dv) ?_ ?_) ?_
  · simp [Expr.evalResults, Expr.eval, h0, h1, h2, h6, h9, Expr.readValue_at hX,
      Expr.readValue_at hM, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
      getElem!_map_toBits, dv, a, F64Bits.toBits_sub]
  · simp [State.setAll, State.set?_eq_update, b, e, hA.1, hA.2]
  refine (Stmt.run_spec (final := f) ?_).mono (fun _ _ h => h) ?_
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, b, a, s, f, h7, hParams, hLocals,
      F64Op.apply, F64Bits.toBits_add]
  rintro s' st ⟨rfl, rfl⟩
  refine ⟨rfl, ?_, ?_⟩
  · simp only [f, s, b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, sumExpStep, f, s, b, a, hParams, hLocals, dv, e]

theorem rowSumExp_implements : Implements gpt.module 20 rowSumExpTuple := by
  refine Func.implements_heap gpt.funcs 18 gpt.rowSumExp.ir "rowSumExp" rfl rowSumExpTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, mx, t, nh⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (mx.map Float.toBits) at hMs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 pm, .i64 t, .i64 nh]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .f64 0, .i64 0, .i64 0] }
  show Triple _ (.buildWith 4 5 6 (.bin .mul (.get 2) (.get 3))
      (.seq (.assign 7 (.constF 0))
        (.loop 8 9 (.bin .add (.bin .divU (.get 6) (.get 3)) (.const 1)) sumExpBody))
      (.toBits (.getF 7))) 12
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [7, 8, 9, 10, 11]) (n := t * nh)
    (fun r => (LeanExe.loop (r / nh + 1) 0.0 (sumExpStep x mx t r)).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro r store state hr hAt hFrame hIndex
    have hn : nh ≠ 0 := by rintro rfl; simp at hr
    have hState : state.params.length = 4 ∧ state.locals.length = 10 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 4 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hX := hAt px _ hXs
    have hM := hAt pm _ hMs
    let s1 := state.update 7 (.f64 0)
    have hS1 : s1.params.length = 4 ∧ s1.locals.length = 10 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 7 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    have g3 : state.get 3 = some (.i64 nh) := (hGet 3 (by decide)).trans rfl
    refine (Stmt.loop_spec (vars := [7]) (writes := [7, 10, 11]) (init := (0.0 : Float))
      (n := UInt64.ofNat r / nh + 1) (sumExpStep x mx t (UInt64.ofNat r)) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2])
      (by simp [Expr.eval, hS1Get 3 (by decide), hS1Get 6 (by decide), g3, hIndex,
        State.set?_eq_update, hS1.1, hS1.2, U64Op.apply, hn])
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 4 ∧ st.locals.length = 10 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 4 ∨ j = 6 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g7 : st.get 7 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      exact sumExpBody_spec hX hM hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans ((hGet 2 (by decide)).trans rfl))
        ((hKeep 6 (by omega)).trans hIndex) g7 hIdx
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g7 : u.get 7 = some (.f64 (LeanExe.loop (UInt64.ofNat r / nh + 1) 0.0
          (sumExpStep x mx t (UInt64.ofNat r))).toBits) := (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g7]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.rowSumExp.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : rowSumExpTuple (x, mx, t, nh) = LeanExe.build (t * nh)
      (fun r => LeanExe.loop (r / nh + 1) 0.0 (sumExpStep x mx t r)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `softmaxApply` with its five arguments as one tuple. -/
def softmaxApplyTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64) :
    Array Float :=
  LeanExe.Examples.Gpt.softmaxApply x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem softmaxApply_implements :
    Implements gpt.module 21 softmaxApplyTuple := by
  refine Func.implements_heap gpt.funcs 19 gpt.softmaxApply.ir "softmaxApply" rfl
    softmaxApplyTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨x, mx, sums, t, w⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨ps, rfl, hSs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (mx.map Float.toBits) at hMs
  change heap.Borrowed initial ps (sums.map Float.toBits) at hSs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 px, .i64 pm, .i64 ps, .i64 t, .i64 w]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.buildWith 5 6 7 (.bin .mul (.get 3) (.get 4))
      (.call 5 [⟨.f64, .binF .sub (.ofBits (.read 0 (.get 7)))
        (.ofBits (.read 1 (.bin .divU (.get 7) (.get 4))))⟩] [8])
      (.toBits (.binF .div (.getF 8) (.ofBits (.read 2 (.bin .divU (.get 7) (.get 4))))))) 9
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [8]) (n := t * w)
    (fun e => (LeanExe.Examples.Gpt.exp (x[e.toNat]! - mx[(e / w).toNat]!) /
      sums[(e / w).toNat]!).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hw : w ≠ 0 := by rintro rfl; simp at hk
    have hState : state.params.length = 5 ∧ state.locals.length = 7 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 5 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 px) := (hGet 0 (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 pm) := (hGet 1 (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 ps) := (hGet 2 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 w) := (hGet 4 (by decide)).trans rfl
    let dv := x[(UInt64.ofNat k).toNat]! - mx[(UInt64.ofNat k / w).toNat]!
    let a := (((state.update 9 (.i64 (UInt64.ofNat k))).update 10 (.i64 (UInt64.ofNat k))).update
      11 (.i64 w)).update 9 (.i64 (UInt64.ofNat k / w))
    let b := a.update 8 (.f64 (LeanExe.Examples.Gpt.exp dv).toBits)
    have hA : a.params.length = 5 ∧ a.locals.length = 7 := by simp [a, hState.1, hState.2]
    refine (exp_call rfl (afterArgs := a) (next := b) (d := dv) ?_ ?_).mono (fun _ _ h => h) ?_
    · simp [Expr.evalResults, Expr.eval, g0, g1, g4, hIndex, Expr.readValue_at (hAt px _ hXs),
        Expr.readValue_at (hAt pm _ hMs), State.set?_eq_update, hState.1, hState.2, F64Op.apply,
        U64Op.apply, getElem!_map_toBits, dv, a, F64Bits.toBits_sub, hw]
    · simp [State.setAll, State.set?_eq_update, b, hA.1, hA.2]
    rintro s st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, ?_⟩
    · simp only [b, a]
      repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · simp [Expr.eval, b, a, g2, g4, hIndex, hState.1, hState.2,
        Expr.readValue_at (hAt ps _ hSs), State.set?_eq_update, F64Op.apply, U64Op.apply,
        getElem!_map_toBits, F64Bits.toBits_div, dv, hw]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.softmaxApply.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : softmaxApplyTuple (x, mx, sums, t, w) = LeanExe.build (t * w) (fun e =>
      LeanExe.Examples.Gpt.exp (x[e.toNat]! - mx[(e / w).toNat]!) / sums[(e / w).toNat]!) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `causalMatMul` with its five arguments as one tuple. -/
def causalMatMulTuple (x : Array Float × Array Float × UInt64 × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.causalMatMul x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- One step of the loop for element `e`: the weight of row `j` in row `e / (nh · dh)`
for the head of column `e % (nh · dh)`, times that column of row `j` of the values. -/
def mixStep (p v : Array Float) (t nh dh e j : UInt64) (acc : Float) : Float :=
  acc + p[(e / (nh * dh) * (nh * t) + (e % (nh * dh) / dh * t + j)).toNat]! *
    v[(j * (nh * dh) + e % (nh * dh)).toNat]!

/-- The compiled loop body of `causalMatMul`. -/
def mixBody : Stmt :=
  .seq (.assign 11 (.binF .add (.getF 8) (.binF .mul
    (.ofBits (.read 0 (.bin .add
      (.bin .mul (.bin .divU (.get 7) (.bin .mul (.get 3) (.get 4))) (.bin .mul (.get 3) (.get 2)))
      (.bin .add (.bin .mul (.bin .divU (.bin .remU (.get 7) (.bin .mul (.get 3) (.get 4))) (.get 4))
        (.get 2)) (.get 10)))))
    (.ofBits (.read 1 (.bin .add (.bin .mul (.get 10) (.bin .mul (.get 3) (.get 4)))
      (.bin .remU (.get 7) (.bin .mul (.get 3) (.get 4))))))))) (.assign 8 (.getF 11))

theorem mixBody_run {initial : Store Unit} {pp pv : UInt64} {p v : Array Float}
    (hP : UInt64Array.At initial pp (p.map Float.toBits))
    (hV : UInt64Array.At initial pv (v.map Float.toBits)) {state : State} {c : Nat}
    {t nh dh e : UInt64} {acc : Float} (hd : dh ≠ 0) (hnd : nh * dh ≠ 0)
    (hParams : state.params.length = 5) (hLocals : state.locals.length = 12)
    (h0 : state.get 0 = some (.i64 pp)) (h1 : state.get 1 = some (.i64 pv))
    (h2 : state.get 2 = some (.i64 t)) (h3 : state.get 3 = some (.i64 nh))
    (h4 : state.get 4 = some (.i64 dh)) (h7 : state.get 7 = some (.i64 e))
    (h8 : state.get 8 = some (.f64 acc.toBits))
    (h10 : state.get 10 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, mixBody.run initial.mem 12 state = some final ∧
      State.Frame 12 [8, 11] state final ∧
      final.Holds [8] (Scalar.values (mixStep p v t nh dh e (UInt64.ofNat c) acc)) := by
  simp [mixBody, Stmt.run, Expr.eval, h0, h1, h2, h3, h4, h7, h8, h10, Expr.readValue_at hP,
    Expr.readValue_at hV, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits, hd, hnd]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, mixStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul]

theorem causalMatMul_implements :
    Implements gpt.module 25 causalMatMulTuple := by
  refine Func.implements_heap gpt.funcs 23 gpt.causalMatMul.ir "causalMatMul" rfl
    causalMatMulTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨p, v, t, nh, dh⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPs⟩, _, _, rfl, ⟨pv, rfl, hVs⟩, rfl⟩ hCap
  change heap.Borrowed initial pp (p.map Float.toBits) at hPs
  change heap.Borrowed initial pv (v.map Float.toBits) at hVs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pp, .i64 pv, .i64 t, .i64 nh, .i64 dh]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0] }
  show Triple _ (.buildWith 5 6 7 (.bin .mul (.get 2) (.bin .mul (.get 3) (.get 4)))
      (.seq (.assign 8 (.constF 0))
        (.loop 9 10 (.bin .add (.bin .divU (.get 7) (.bin .mul (.get 3) (.get 4))) (.const 1))
          mixBody))
      (.toBits (.getF 8))) 12
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [8, 9, 10, 11]) (n := t * (nh * dh))
    (fun e => (LeanExe.loop (e / (nh * dh) + 1) 0.0 (mixStep p v t nh dh e)).toBits) hMemory32
    hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hnd : nh * dh ≠ 0 := by
      intro h
      rw [h, UInt64.mul_zero] at he
      simp at he
    have hd : dh ≠ 0 := by rintro rfl; simp at he
    have hState : state.params.length = 5 ∧ state.locals.length = 12 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 5 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g2 : state.get 2 = some (.i64 t) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 nh) := (hGet 3 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 dh) := (hGet 4 (by decide)).trans rfl
    have hP := hAt pp _ hPs
    have hV := hAt pv _ hVs
    let s1 := state.update 8 (.f64 0)
    have hS1 : s1.params.length = 5 ∧ s1.locals.length = 12 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 8 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [8]) (writes := [8, 11]) (init := (0.0 : Float))
      (n := UInt64.ofNat e / (nh * dh) + 1) (mixStep p v t nh dh (UInt64.ofNat e)) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2])
      (by simp [Expr.eval, hS1Get 3 (by decide), hS1Get 4 (by decide), hS1Get 7 (by decide), g3,
        g4, hIndex, State.set?_eq_update, hS1.1, hS1.2, U64Op.apply, hnd])
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 5 ∧ st.locals.length = 12 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 5 ∨ j = 7 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g8 : st.get 8 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := mixBody_run hP hV hd hnd hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans g2) ((hKeep 3 (by omega)).trans g3)
        ((hKeep 4 (by omega)).trans g4) ((hKeep 7 (by omega)).trans hIndex) g8 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g8 : u.get 8 = some (.f64 (LeanExe.loop (UInt64.ofNat e / (nh * dh) + 1) 0.0
          (mixStep p v t nh dh (UInt64.ofNat e))).toBits) := (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g8]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.causalMatMul.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : causalMatMulTuple (p, v, t, nh, dh) = LeanExe.build (t * (nh * dh))
      (fun e => LeanExe.loop (e / (nh * dh) + 1) 0.0 (mixStep p v t nh dh e)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `softmaxRows` with its three arguments as one tuple. -/
def softmaxRowsTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.softmaxRows x.1 x.2.1 x.2.2

theorem softmaxRows_implements : Implements gpt.module 22 softmaxRowsTuple := by
  refine Func.implements_heap gpt.funcs 20 gpt.softmaxRows.ir "softmaxRows" rfl softmaxRowsTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, t, nh⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨px, rfl, hX⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hMax : gpt.module.funcs[19 - gpt.module.imports.length]? =
      some (gpt.rowMax.ir.function (2 + 17)) := compile_funcs (funcs := gpt.funcs) (i := 17) rfl
  have hSum : gpt.module.funcs[20 - gpt.module.imports.length]? =
      some (gpt.rowSumExp.ir.function (2 + 18)) := compile_funcs (funcs := gpt.funcs) (i := 18) rfl
  have hApply : gpt.module.funcs[21 - gpt.module.imports.length]? =
      some (gpt.softmaxApply.ir.function (2 + 19)) :=
    compile_funcs (funcs := gpt.funcs) (i := 19) rfl
  let mx := rowMaxTuple (x, t, nh)
  let sums := rowSumExpTuple (x, mx, t, nh)
  let start : State :=
    { params := [.i64 px, .i64 t, .i64 nh]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have hGet : start.get 0 = some (.i64 px) ∧ start.get 1 = some (.i64 t) ∧
      start.get 2 = some (.i64 nh) := ⟨rfl, rfl, rfl⟩
  show Triple _ (.seq (.call 19 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [3])
      (.seq (.call 20 [⟨.u64, .get 0⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [4])
      (.seq (.call 21 [⟨.u64, .get 0⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩,
        ⟨.u64, .bin .mul (.get 1) (.get 2)⟩, ⟨.u64, .get 1⟩] [5])
      (.seq (.assign 6 (.get 5)) (.seq (.release 4) (.release 3)))))) 7
    (fun store state => store = initial ∧ state = start) _
  -- The maxima of the rows.
  refine Stmt.seq_spec (Live.call rowMax_implements rfl hMax rfl (Live.start hHeap) hCap
    (x := (x, t, nh)) (afterArgs := start)
    (vals := [.i64 px, .i64 t, .i64 nh])
    (by simp [Expr.evalResults, Expr.eval, hGet.1, hGet.2.1, hGet.2.2])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hX⟩, rfl⟩ (by rw [hStart]; decide)) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨heap1, pm, hLive1, rfl⟩
  let s1 := start.update 3 (.i64 pm)
  have hS1 : s1.params.length + s1.locals.length = 7 := by rw [hLen, hStart]
  have hGetS1 : ∀ j, j < 3 → s1.get j = start.get j := fun j hj => by
    simp only [s1]
    rw [State.get_update_ne (by omega)]
  -- The sums of the exponentials.
  refine Stmt.seq_spec (Live.call rowSumExp_implements rfl hSum rfl hLive1 hCap
    (x := (x, mx, t, nh))
    (afterArgs := s1) (vals := [.i64 px, .i64 pm, .i64 t, .i64 nh])
    (by simp [Expr.evalResults, Expr.eval, s1, State.get_update_same, hStart,
      hGetS1 0 (by decide), hGetS1 1 (by decide), hGetS1 2 (by decide), hGet.1, hGet.2.1,
      hGet.2.2])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hLive1.borrowed px _ hX Apart.nil⟩, [.i64 pm], _, rfl,
      ⟨pm, rfl, (hLive1.tempsOwned _ (List.mem_singleton_self _)).borrowed⟩, rfl⟩
    (by rw [hS1]; decide)) ?_
  apply Triple.of_forall
  rintro store2 t2 ⟨heap2, ps, hLive2, rfl⟩
  let s2 := s1.update 4 (.i64 ps)
  have hS2 : s2.params.length + s2.locals.length = 7 := by rw [hLen, hS1]
  have hGetS2 : ∀ j, j < 3 → s2.get j = start.get j := fun j hj => by
    simp only [s2, s1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]
  have hS2Get3 : s2.get 3 = some (.i64 pm) := by
    simp only [s2, s1]
    rw [State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hStart]; decide)
  -- The normalized exponentials.
  refine Stmt.seq_spec (Live.call softmaxApply_implements rfl hApply rfl hLive2 hCap
    (x := (x, mx, sums, t * nh, t))
    (afterArgs := s2) (vals := [.i64 px, .i64 pm, .i64 ps, .i64 (t * nh), .i64 t])
    (by simp [Expr.evalResults, Expr.eval, s2, State.get_update_same, hS1, hS2Get3,
      hGetS2 0 (by decide), hGetS2 1 (by decide), hGetS2 2 (by decide), hGet.1, hGet.2.1,
      hGet.2.2, U64Op.apply])
    ⟨[.i64 px], _, rfl, ⟨px, rfl, hLive2.borrowed px _ hX Apart.nil⟩, [.i64 pm], _, rfl,
      ⟨pm, rfl, (hLive2.tempsOwned _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).borrowed⟩,
      [.i64 ps], _, rfl, ⟨ps, rfl, (hLive2.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩, rfl⟩
    (by rw [hS2]; decide)) ?_
  apply Triple.of_forall
  rintro store3 t3 ⟨heap3, pr, hLive3, rfl⟩
  let s3 := s2.update 5 (.i64 pr)
  let s4 := s3.update 6 (.i64 pr)
  have hS3 : s3.params.length + s3.locals.length = 7 := by rw [hLen, hS2]
  refine Stmt.seq_spec (Stmt.run_spec (final := s4) (by
    simp [Stmt.run, Expr.eval, State.set?_eq_update _ (show 6 < s3.params.length +
      s3.locals.length by rw [hS3]; decide), s4, s3, State.get_update_same,
      show 5 < s2.params.length + s2.locals.length by rw [hS2]; decide])) ?_
  -- The temporaries are released, the sums first.
  have hS4Get4 : s4.get 4 = some (.i64 ps) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [hS1]; decide)
  have hS4Get3 : s4.get 3 = some (.i64 pm) := by
    simp only [s4, s3]
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
    exact hS2Get3
  refine Stmt.seq_spec (hLive3.releaseSecond hImports hRelease hS4Get4) ?_
  apply Triple.of_forall
  rintro store4 st4 ⟨hLive4, rfl⟩
  refine (hLive4.releaseSecond hImports hRelease hS4Get3).mono (fun _ _ h => h) ?_
  rintro store5 st5 ⟨hLive5, rfl⟩
  obtain ⟨heap', hAt', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLive5.finish
  exact ⟨heap', hAt', hCaps', hKeepB, hKeepO, [.i64 pr], s4,
    by simp [gpt.softmaxRows.ir, Func.scratch, Expr.evalResults, Expr.eval, s4,
      State.get_update_same, hS3], hOwned, hOutB, hOutO⟩

/-- `embed` with its five arguments as one tuple. -/
def embedTuple (x : Array UInt64 × Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.embed x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem embed_implements : Implements gpt.module 26 embedTuple := by
  refine Func.implements_heap gpt.funcs 24 gpt.embed.ir "embed" rfl embedTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨tokens, wte, wpe, t, d⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pk, rfl, hKs⟩, _, _, rfl, ⟨pe, rfl, hEs⟩, _, _, rfl, ⟨pp, rfl, hPs⟩, rfl⟩ hCap
  change heap.Borrowed initial pk tokens at hKs
  change heap.Borrowed initial pe (wte.map Float.toBits) at hEs
  change heap.Borrowed initial pp (wpe.map Float.toBits) at hPs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 pk, .i64 pe, .i64 pp, .i64 t, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.build 5 6 7 (.bin .mul (.get 3) (.get 4)) (.toBits (.binF .add
      (.ofBits (.read 1 (.bin .add (.bin .mul (.read 0 (.bin .divU (.get 7) (.get 4))) (.get 4))
        (.bin .remU (.get 7) (.get 4)))))
      (.ofBits (.read 2 (.get 7)))))) 8
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.build_spec (n := t * d)
    (fun e => (wte[(tokens[(e / d).toNat]! * d + e % d).toNat]! + wpe[e.toNat]!).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hd : d ≠ 0 := by rintro rfl; simp at he
    have hState : state.params.length = 5 ∧ state.locals.length = 7 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 5 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 pk) := (hGet 0 (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 pe) := (hGet 1 (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 pp) := (hGet 2 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 d) := (hGet 4 (by decide)).trans rfl
    simp [Expr.eval, g0, g1, g2, g4, hIndex, Expr.readValue_at (hAt pk _ hKs),
      Expr.readValue_at (hAt pe _ hEs), Expr.readValue_at (hAt pp _ hPs), State.set?_eq_update,
      hState.1, hState.2, F64Op.apply, U64Op.apply, getElem!_map_toBits, F64Bits.toBits_add, hd]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.embed.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : embedTuple (tokens, wte, wpe, t, d) = LeanExe.build (t * d)
      (fun e => wte[(tokens[(e / d).toNat]! * d + e % d).toNat]! + wpe[e.toNat]!) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `matMulT` with its five arguments as one tuple. -/
def matMulTTuple (x : Array Float × Array Float × UInt64 × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.matMulT x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- One step of the loop for element `e`: row `e / m` of `a` times row `e % m` of `b`. -/
def cellTStep (a b : Array Float) (k m e c : UInt64) (acc : Float) : Float :=
  acc + a[(e / m * k + c).toNat]! * b[(e % m * k + c).toNat]!

/-- The compiled loop body of `matMulT`. -/
def cellTBody : Stmt :=
  .seq (.assign 11 (.binF .add (.getF 8) (.binF .mul
    (.ofBits (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 7) (.get 4)) (.get 3)) (.get 10))))
    (.ofBits (.read 1 (.bin .add (.bin .mul (.bin .remU (.get 7) (.get 4)) (.get 3))
      (.get 10))))))) (.assign 8 (.getF 11))

theorem cellTBody_run {initial : Store Unit} {pa pb : UInt64} {a b : Array Float}
    (hA : UInt64Array.At initial pa (a.map Float.toBits))
    (hB : UInt64Array.At initial pb (b.map Float.toBits)) {state : State} {c : Nat}
    {k m e : UInt64} {acc : Float} (hm : m ≠ 0) (hParams : state.params.length = 5)
    (hLocals : state.locals.length = 10) (h0 : state.get 0 = some (.i64 pa))
    (h1 : state.get 1 = some (.i64 pb)) (h3 : state.get 3 = some (.i64 k))
    (h4 : state.get 4 = some (.i64 m)) (h7 : state.get 7 = some (.i64 e))
    (h8 : state.get 8 = some (.f64 acc.toBits))
    (h10 : state.get 10 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, cellTBody.run initial.mem 12 state = some final ∧
      State.Frame 12 [8, 11] state final ∧
      final.Holds [8] (Scalar.values (cellTStep a b k m e (UInt64.ofNat c) acc)) := by
  simp [cellTBody, Stmt.run, Expr.eval, h0, h1, h3, h4, h7, h8, h10, Expr.readValue_at hA,
    Expr.readValue_at hB, State.set?_eq_update, hParams, hLocals, F64Op.apply, U64Op.apply,
    getElem!_map_toBits, hm]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, cellTStep, hParams, hLocals, F64Bits.toBits_add,
      F64Bits.toBits_mul]

theorem matMulT_implements : Implements gpt.module 27 matMulTTuple := by
  refine Func.implements_heap gpt.funcs 25 gpt.matMulT.ir "matMulT" rfl matMulTTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨a, b, n, k, m⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pa, rfl, hAs⟩, _, _, rfl, ⟨pb, rfl, hBs⟩, rfl⟩ hCap
  change heap.Borrowed initial pa (a.map Float.toBits) at hAs
  change heap.Borrowed initial pb (b.map Float.toBits) at hBs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pa, .i64 pb, .i64 n, .i64 k, .i64 m]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.buildWith 5 6 7 (.bin .mul (.get 2) (.get 4))
      (.seq (.assign 8 (.constF 0)) (.loop 9 10 (.get 3) cellTBody)) (.toBits (.getF 8))) 12
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [8, 9, 10, 11]) (n := n * m)
    (fun e => (LeanExe.loop k 0.0 (cellTStep a b k m e)).toBits) hMemory32 hImports hAlloc
    (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hm : m ≠ 0 := by rintro rfl; simp at he
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
      (cellTStep a b k m (UInt64.ofNat e)) (by decide) (by decide) (by decide) (by decide)
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
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := cellTBody_run hA hB hm hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 4 (by omega)).trans ((hGet 4 (by decide)).trans rfl))
        ((hKeep 7 (by omega)).trans hIndex) g8 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g8 : u.get 8 = some (.f64 (LeanExe.loop k 0.0
          (cellTStep a b k m (UInt64.ofNat e))).toBits) := (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g8]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
    hNew.ownedKeep, [.i64 ptr], state,
    by simp [gpt.matMulT.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : matMulTTuple (a, b, n, k, m) =
      LeanExe.build (n * m) (fun e => LeanExe.loop k 0.0 (cellTStep a b k m e)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

end Project.Gpt
