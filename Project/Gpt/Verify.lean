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
    fun p ws h => (hNew.ownedKeep p ws h).1, [.i64 ptr], state,
    by simp [gpt.layerNorm.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ptr, rfl, ?_⟩
  rw [layerTuple, layerNorm_eq, hSum, hVar, build_map]
  exact hNew.owned

/-- `encode` succeeds on `gpt.module`, and its bytes decode to a module whose
exports compute the kernels exactly. -/
theorem gpt_bytes : ∃ bytes, Encoding.encode gpt.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 dotTuple (fun _ => 0) ∧
      Implements m 4 matVecTuple matVecNeed ∧ Implements m 5 layerTuple layerNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip gpt.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, gpt.module, decoded, dot_implements, matVec_implements,
    layerNorm_implements⟩

end Project.Gpt
