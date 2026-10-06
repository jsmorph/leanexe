import Examples.Gpt.Verify

/-! The `Implements` theorems of the kernels of the cached step and of `stepSoftmax`. -/

namespace Examples.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

/-- `firstRow` with its two arguments as one tuple. -/
def firstRowTuple (x : Array Float × UInt64) : Array Float :=
  Examples.Gpt.firstRow x.1 x.2

theorem firstRow_implements : Implements gpt.module 31 firstRowTuple := by
  refine Func.implements_heap gpt.funcs 29 gpt.firstRow.ir "firstRow" rfl firstRowTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨s, d⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ps, rfl, hSs⟩, rfl⟩ hCap
  change heap.Borrowed initial ps (s.map Float.toBits) at hSs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 ps, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.build 2 3 4 (.get 1) (.toBits (.ofBits (.read 0 (.get 4))))) 5
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.build_spec (n := d) (fun c => (s[c.toNat]!).toBits) hMemory32 hImports hAlloc
    (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hState : state.params.length = 2 ∧ state.locals.length = 4 :=
      ⟨hFrame.params, hFrame.locals⟩
    have g0 : state.get 0 = some (.i64 ps) :=
      (hFrame.get 0 (by decide) (by decide)).trans rfl
    simp [Expr.eval, g0, hIndex, Expr.readValue_at (hAt ps _ hSs), State.set?_eq_update,
      hState.1, hState.2, getElem!_map_toBits]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.firstRow.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : firstRowTuple (s, d) = LeanExe.build d (fun c => s[c.toNat]!) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `lastHidden` with its three arguments as one tuple. -/
def lastHiddenTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  Examples.Gpt.lastHidden x.1 x.2.1 x.2.2

theorem lastHidden_implements : Implements gpt.module 39 lastHiddenTuple := by
  refine Func.implements_heap gpt.funcs 37 gpt.lastHidden.ir "lastHidden" rfl lastHiddenTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨cache, d, bsize⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨pc, rfl, hCs⟩, rfl⟩ hCap
  change heap.Borrowed initial pc (cache.map Float.toBits) at hCs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hA := hCs.values
  have hLength := hA.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  let start : State :=
    { params := [.i64 pc, .i64 d, .i64 bsize]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  have hGet0 : start.get 0 = some (.i64 pc) := rfl
  let s1 := start.update 3 (.i64 (UInt64.ofNat cache.size))
  let s2 := s1.update 4 (.i64 (UInt64.ofNat cache.size))
  show Triple _ (.seq (.arraySize 3 0) (.seq (.assign 4 (.get 3)) (.build 5 6 7 (.get 1)
      (.toBits (.ofBits (.read 0 (.bin .add (.bin .sub (.get 4) (.get 2)) (.get 7)))))))) 8
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hA.lengthRead,
      State.set?_eq_update, s1, start])) ?_
  refine Stmt.seq_spec (Stmt.run_spec (final := s2) (by
    simp [Stmt.run, Expr.eval, State.set?_eq_update, s2, s1, start])) ?_
  have hS2 : s2.params.length = 3 ∧ s2.locals.length = 6 := by simp [s2, s1, start]
  refine (Stmt.build_spec (n := d)
    (fun c => (cache[(UInt64.ofNat cache.size - bsize + c).toNat]!).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by simp [hS2.1, hS2.2]) hHeap hCap
    ⟨s2, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 6 :=
      ⟨hFrame.params.trans hS2.1, hFrame.locals.trans hS2.2⟩
    have g0 : state.get 0 = some (.i64 pc) := (hFrame.get 0 (by decide) (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 bsize) :=
      (hFrame.get 2 (by decide) (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 (UInt64.ofNat cache.size)) :=
      (hFrame.get 4 (by decide) (by decide)).trans rfl
    simp [Expr.eval, g0, g2, g4, hIndex, Expr.readValue_at (hAt pc _ hCs), State.set?_eq_update,
      hState.1, hState.2, U64Op.apply, getElem!_map_toBits]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.lastHidden.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : lastHiddenTuple (cache, d, bsize) =
      LeanExe.build d (fun c => cache[(UInt64.ofNat cache.size - bsize + c).toNat]!) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `embedBlock` with its six arguments as one tuple. -/
def embedBlockTuple (x : Array Float × Array Float × UInt64 × UInt64 × UInt64 × UInt64) :
    Array Float :=
  Examples.Gpt.embedBlock x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

theorem embedBlock_implements : Implements gpt.module 30 embedBlockTuple := by
  refine Func.implements_heap gpt.funcs 28 gpt.embedBlock.ir "embedBlock" rfl embedBlockTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨wte, wpe, token, p, d, bsize⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pt, rfl, hTs⟩, _, _, rfl, ⟨pp, rfl, hPs⟩, rfl⟩ hCap
  change heap.Borrowed initial pt (wte.map Float.toBits) at hTs
  change heap.Borrowed initial pp (wpe.map Float.toBits) at hPs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pt, .i64 pp, .i64 token, .i64 p, .i64 d, .i64 bsize]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  show Triple _ (.build 6 7 8 (.get 5) (.toBits (.iteF (.ltU (.get 8) (.get 4))
      (.binF .add (.ofBits (.read 0 (.bin .add (.bin .mul (.get 2) (.get 4)) (.get 8))))
        (.ofBits (.read 1 (.bin .add (.bin .mul (.get 3) (.get 4)) (.get 8)))))
      (.constF 0)))) 9
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.build_spec (n := bsize) (fun e => (if e < d then
      wte[(token * d + e).toNat]! + wpe[(p * d + e).toNat]! else 0.0).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hState : state.params.length = 6 ∧ state.locals.length = 4 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 6 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 pt) := (hGet 0 (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 pp) := (hGet 1 (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 token) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 p) := (hGet 3 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 d) := (hGet 4 (by decide)).trans rfl
    by_cases hc : UInt64.ofNat i < d <;> simp [Expr.eval, g0, g1, g2, g3, g4, hIndex, hc,
      Expr.readValue_at (hAt pt _ hTs), Expr.readValue_at (hAt pp _ hPs), State.set?_eq_update,
      hState.1, hState.2, F64Op.apply, U64Op.apply, getElem!_map_toBits, F64Bits.toBits_add,
      hZero]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.embedBlock.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : embedBlockTuple (wte, wpe, token, p, d, bsize) = LeanExe.build bsize (fun e =>
      if e < d then wte[(token * d + e).toNat]! + wpe[(p * d + e).toNat]! else 0.0) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowMax` with its three arguments as one tuple. -/
def headMaxTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  Examples.Gpt.headMax x.1 x.2.1 x.2.2

/-- One step of the maximum over row `r`. -/
def headMaxStep (x : Array Float) (w r c : UInt64) (acc : Float) : Float :=
  max acc x[(r * w + c).toNat]!

/-- The compiled loop body of `rowMax`. -/
def headMaxBody : Stmt :=
  .seq (.assign 9 (.iteF
    (.leF (.getF 6) (.ofBits (.read 0 (.bin .add (.bin .mul (.get 5) (.get 2)) (.get 8)))))
    (.ofBits (.read 0 (.bin .add (.bin .mul (.get 5) (.get 2)) (.get 8)))) (.getF 6)))
    (.assign 6 (.getF 9))

theorem headMaxBody_run {initial : Store Unit} {px : UInt64} {x : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits)) {state : State} {c : Nat}
    {w r : UInt64} {acc : Float} (hParams : state.params.length = 3)
    (hLocals : state.locals.length = 8) (h0 : state.get 0 = some (.i64 px))
    (h2 : state.get 2 = some (.i64 w)) (h5 : state.get 5 = some (.i64 r))
    (h6 : state.get 6 = some (.f64 acc.toBits)) (h8 : state.get 8 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, headMaxBody.run initial.mem 10 state = some final ∧
      State.Frame 10 [6, 9] state final ∧
      final.Holds [6] (Scalar.values (headMaxStep x w r (UInt64.ofNat c) acc)) := by
  simp [headMaxBody, Stmt.run, Expr.eval, h0, h2, h5, h6, h8, Expr.readValue_at hX,
    State.set?_eq_update, hParams, hLocals, U64Op.apply, getElem!_map_toBits]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, headMaxStep, hParams, hLocals, F64Bits.toBits_max]

theorem headMax_implements : Implements gpt.module 33 headMaxTuple := by
  refine Func.implements_heap gpt.funcs 31 gpt.headMax.ir "headMax" rfl headMaxTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, t, w⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨px, rfl, hXs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 t, .i64 w]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0] }
  show Triple _ (.buildWith 3 4 5 (.get 1)
      (.seq (.assign 6 (.binF .sub (.constF 9223372036854775808)
        (.binF .div (.constF 4607182418800017408) (.constF 0)))) (.loop 7 8 (.get 2) headMaxBody))
      (.toBits (.getF 6))) 10
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [6, 7, 8, 9]) (n := t)
    (fun r => (LeanExe.loop w (-(1.0 / 0.0)) (headMaxStep x w r)).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro r store state hr hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 8 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 3 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hX := hAt px _ hXs
    let s1 := state.update 6 (.f64 (-(1.0 / 0.0) : Float).toBits)
    have hS1 : s1.params.length = 3 ∧ s1.locals.length = 8 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 6 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1, F64Op.apply,
        F64Bits.toBits_neg, F64Bits.toBits_div, hZero, hOne])) ?_
    refine (Stmt.loop_spec (vars := [6]) (writes := [6, 9]) (init := (-(1.0 / 0.0) : Float))
      (n := w) (headMaxStep x w (UInt64.ofNat r)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 2 (by decide), hGet 2 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 3 ∧ st.locals.length = 8 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 3 ∨ j = 5 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g6 : st.get 6 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := headMaxBody_run hX hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans ((hGet 2 (by decide)).trans rfl))
        ((hKeep 5 (by omega)).trans hIndex) g6 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g6 : u.get 6 = some (.f64 (LeanExe.loop w (-(1.0 / 0.0))
          (headMaxStep x w (UInt64.ofNat r))).toBits) := (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g6]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.headMax.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : headMaxTuple (x, t, w) =
      LeanExe.build t (fun r => LeanExe.loop w (-(1.0 / 0.0)) (headMaxStep x w r)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `rowSumExp` with its four arguments as one tuple. -/
def headSumExpTuple (x : Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  Examples.Gpt.headSumExp x.1 x.2.1 x.2.2.1 x.2.2.2

/-- One step of the sum of exponentials over row `r`. -/
def headSumStep (x mx : Array Float) (w r c : UInt64) (acc : Float) : Float :=
  acc + Examples.Gpt.exp (x[(r * w + c).toNat]! - mx[r.toNat]!)

/-- The compiled loop body of `rowSumExp`. -/
def headSumBody : Stmt :=
  .seq (.call 5 [⟨.f64, .binF .sub
      (.ofBits (.read 0 (.bin .add (.bin .mul (.get 6) (.get 3)) (.get 9))))
      (.ofBits (.read 1 (.get 6)))⟩] [10])
    (.seq (.assign 11 (.binF .add (.getF 7) (.getF 10))) (.assign 7 (.getF 11)))

theorem headSumBody_spec {initial : Store Unit} {px pm : UInt64} {x mx : Array Float}
    (hX : UInt64Array.At initial px (x.map Float.toBits))
    (hM : UInt64Array.At initial pm (mx.map Float.toBits)) {state : State} {c : Nat}
    {w r : UInt64} {acc : Float} (hParams : state.params.length = 4)
    (hLocals : state.locals.length = 9) (h0 : state.get 0 = some (.i64 px))
    (h1 : state.get 1 = some (.i64 pm)) (h3 : state.get 3 = some (.i64 w))
    (h6 : state.get 6 = some (.i64 r)) (h7 : state.get 7 = some (.f64 acc.toBits))
    (h9 : state.get 9 = some (.i64 (UInt64.ofNat c))) :
    Triple gpt.module headSumBody 12 (fun store st => store = initial ∧ st = state)
      (fun store st => store = initial ∧ State.Frame 12 [7, 10, 11] state st ∧
        st.Holds [7] (Scalar.values (headSumStep x mx w r (UInt64.ofNat c) acc))) := by
  let dv := x[(r * w + UInt64.ofNat c).toNat]! - mx[r.toNat]!
  let e := Examples.Gpt.exp dv
  let a := (state.update 12 (.i64 (r * w + UInt64.ofNat c))).update 12 (.i64 r)
  let b := a.update 10 (.f64 e.toBits)
  let s := b.update 11 (.f64 (acc + e).toBits)
  let f := s.update 7 (.f64 (acc + e).toBits)
  have hA : a.params.length = 4 ∧ a.locals.length = 9 := by simp [a, hParams, hLocals]
  refine Stmt.seq_spec (exp_call rfl (afterArgs := a) (next := b) (d := dv) ?_ ?_) ?_
  · simp [Expr.evalResults, Expr.eval, h0, h1, h3, h6, h9, Expr.readValue_at hX,
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
  · simp [State.Holds, Scalar.values, headSumStep, f, s, b, a, hParams, hLocals, dv, e]

theorem headSumExp_implements : Implements gpt.module 34 headSumExpTuple := by
  refine Func.implements_heap gpt.funcs 32 gpt.headSumExp.ir "headSumExp" rfl headSumExpTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, mx, t, w⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pm, rfl, hMs⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pm (mx.map Float.toBits) at hMs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 px, .i64 pm, .i64 t, .i64 w]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .f64 0, .i64 0] }
  show Triple _ (.buildWith 4 5 6 (.get 2)
      (.seq (.assign 7 (.constF 0)) (.loop 8 9 (.get 3) headSumBody)) (.toBits (.getF 7))) 12
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [7, 8, 9, 10, 11]) (n := t)
    (fun r => (LeanExe.loop w 0.0 (headSumStep x mx w r)).toBits) hMemory32 hImports hAlloc
    (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro r store state hr hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 9 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 4 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hX := hAt px _ hXs
    have hM := hAt pm _ hMs
    let s1 := state.update 7 (.f64 0)
    have hS1 : s1.params.length = 4 ∧ s1.locals.length = 9 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 7 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [7]) (writes := [7, 10, 11]) (init := (0.0 : Float)) (n := w)
      (headSumStep x mx w (UInt64.ofNat r)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 3 (by decide), hGet 3 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 4 ∧ st.locals.length = 9 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 4 ∨ j = 6 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g7 : st.get 7 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      exact headSumBody_spec hX hM hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 6 (by omega)).trans hIndex) g7 hIdx
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g7 : u.get 7 = some (.f64 (LeanExe.loop w 0.0
          (headSumStep x mx w (UInt64.ofNat r))).toBits) := (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g7]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.headSumExp.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : headSumExpTuple (x, mx, t, w) =
      LeanExe.build t (fun r => LeanExe.loop w 0.0 (headSumStep x mx w r)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

def stepSoftmaxTuple (x : Array Float × UInt64 × UInt64) : Array Float :=
  Examples.Gpt.stepSoftmax x.1 x.2.1 x.2.2

theorem stepSoftmax_implements : Implements gpt.module 35 stepSoftmaxTuple := by
  refine Func.implements_heap gpt.funcs 33 gpt.stepSoftmax.ir "stepSoftmax" rfl stepSoftmaxTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨x, t, w⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨px, rfl, hX⟩, rfl⟩ hCap
  change heap.Borrowed initial px (x.map Float.toBits) at hX
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hMax : gpt.module.funcs[33 - gpt.module.imports.length]? =
      some (gpt.headMax.ir.function (2 + 31)) := compile_funcs (funcs := gpt.funcs) (i := 31) rfl
  have hSum : gpt.module.funcs[34 - gpt.module.imports.length]? =
      some (gpt.headSumExp.ir.function (2 + 32)) := compile_funcs (funcs := gpt.funcs) (i := 32) rfl
  have hApply : gpt.module.funcs[21 - gpt.module.imports.length]? =
      some (gpt.softmaxApply.ir.function (2 + 19)) :=
    compile_funcs (funcs := gpt.funcs) (i := 19) rfl
  let mx := headMaxTuple (x, t, w)
  let sums := headSumExpTuple (x, mx, t, w)
  let start : State :=
    { params := [.i64 px, .i64 t, .i64 w]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 7 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have hGet : start.get 0 = some (.i64 px) ∧ start.get 1 = some (.i64 t) ∧
      start.get 2 = some (.i64 w) := ⟨rfl, rfl, rfl⟩
  show Triple _ (.seq (.call 33 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [3])
      (.seq (.call 34 [⟨.u64, .get 0⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [4])
      (.seq (.call 21 [⟨.u64, .get 0⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 1⟩,
        ⟨.u64, .get 2⟩] [5])
      (.seq (.assign 6 (.get 5)) (.seq (.release 4) (.release 3)))))) 7
    (fun store state => store = initial ∧ state = start) _
  -- The maxima of the rows.
  refine Stmt.seq_spec (Live.call headMax_implements rfl hMax rfl (Live.start hHeap) hCap
    (x := (x, t, w)) (afterArgs := start)
    (vals := [.i64 px, .i64 t, .i64 w])
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
  refine Stmt.seq_spec (Live.call headSumExp_implements rfl hSum rfl hLive1 hCap
    (x := (x, mx, t, w))
    (afterArgs := s1) (vals := [.i64 px, .i64 pm, .i64 t, .i64 w])
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
    (x := (x, mx, sums, t, w))
    (afterArgs := s2) (vals := [.i64 px, .i64 pm, .i64 ps, .i64 t, .i64 w])
    (by simp [Expr.evalResults, Expr.eval, s2, State.get_update_same, hS1, hS2Get3,
      hGetS2 0 (by decide), hGetS2 1 (by decide), hGetS2 2 (by decide), hGet.1, hGet.2.1,
      hGet.2.2])
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
  obtain ⟨heap', hAt', hCaps', hOwned, hKeeps⟩ :=
    hLive5.finish
  exact ⟨heap', hAt', hCaps', [.i64 pr], s4,
    by simp [gpt.stepSoftmax.ir, Func.scratch, Expr.evalResults, Expr.eval, s4,
      State.get_update_same, hS3], hOwned, hKeeps⟩

/-- `stepScores` with its nine arguments as one tuple. -/
def stepScoresTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × Float) : Array Float :=
  Examples.Gpt.stepScores x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2

/-- One step of the dot product of `q` and key `e % (p + 1)` over the columns of head
`e / (p + 1)`. -/
def stepScoreStep (q k cache : Array Float) (l p nh dh bsize e c : UInt64) (acc : Float) : Float :=
  acc + q[(e / (p + 1) * dh + c).toNat]! *
    (if e % (p + 1) < p then
      cache[(e % (p + 1) * bsize + (2 * l + 1) * (nh * dh) + (e / (p + 1) * dh + c)).toNat]!
    else k[(e / (p + 1) * dh + c).toNat]!)

/-- The compiled loop body of `stepScores`. -/
def stepScoreBody : Stmt :=
  .seq (.assign 15 (.binF .add (.getF 12) (.binF .mul
    (.ofBits (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 11) (.bin .add (.get 4) (.const 1)))
      (.get 6)) (.get 14))))
    (.iteF (.ltU (.bin .remU (.get 11) (.bin .add (.get 4) (.const 1))) (.get 4))
      (.ofBits (.read 2 (.bin .add (.bin .add
        (.bin .mul (.bin .remU (.get 11) (.bin .add (.get 4) (.const 1))) (.get 7))
        (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 3)) (.const 1)) (.bin .mul (.get 5) (.get 6))))
        (.bin .add (.bin .mul (.bin .divU (.get 11) (.bin .add (.get 4) (.const 1))) (.get 6))
          (.get 14)))))
      (.ofBits (.read 1 (.bin .add (.bin .mul (.bin .divU (.get 11) (.bin .add (.get 4) (.const 1)))
        (.get 6)) (.get 14))))))))
    (.assign 12 (.getF 15))

set_option maxHeartbeats 400000 in
theorem stepScoreBody_run {initial : Store Unit} {pq pk pc : UInt64} {q k cache : Array Float}
    (hQ : UInt64Array.At initial pq (q.map Float.toBits))
    (hK : UInt64Array.At initial pk (k.map Float.toBits))
    (hC : UInt64Array.At initial pc (cache.map Float.toBits)) {state : State} {c : Nat}
    {l p nh dh bsize e : UInt64} {acc : Float} (hp : p + 1 ≠ 0)
    (hParams : state.params.length = 9) (hLocals : state.locals.length = 10)
    (h0 : state.get 0 = some (.i64 pq)) (h1 : state.get 1 = some (.i64 pk))
    (h2 : state.get 2 = some (.i64 pc)) (h3 : state.get 3 = some (.i64 l))
    (h4 : state.get 4 = some (.i64 p)) (h5 : state.get 5 = some (.i64 nh))
    (h6 : state.get 6 = some (.i64 dh)) (h7 : state.get 7 = some (.i64 bsize))
    (h11 : state.get 11 = some (.i64 e)) (h12 : state.get 12 = some (.f64 acc.toBits))
    (h14 : state.get 14 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, stepScoreBody.run initial.mem 16 state = some final ∧
      State.Frame 16 [12, 15] state final ∧
      final.Holds [12]
        (Scalar.values (stepScoreStep q k cache l p nh dh bsize e (UInt64.ofNat c) acc)) := by
  by_cases hc : e % (p + 1) < p <;>
  · simp [stepScoreBody, Stmt.run, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h11, h12, h14,
      Expr.readValue_at hQ, Expr.readValue_at hK, Expr.readValue_at hC, State.set?_eq_update,
      hParams, hLocals, F64Op.apply, U64Op.apply, getElem!_map_toBits, hp, hc]
    constructor
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, Scalar.values, stepScoreStep, hParams, hLocals, F64Bits.toBits_add,
        F64Bits.toBits_mul, hc]

theorem stepScores_implements : Implements gpt.module 32 stepScoresTuple := by
  refine Func.implements_heap gpt.funcs 30 gpt.stepScores.ir "stepScores" rfl stepScoresTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl,
      ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨q, k, cache, l, p, nh, dh, bsize, scale⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pq, rfl, hQs⟩, _, _, rfl, ⟨pk, rfl, hKs⟩, _, _, rfl, ⟨pc, rfl, hCs⟩, rfl⟩ hCap
  change heap.Borrowed initial pq (q.map Float.toBits) at hQs
  change heap.Borrowed initial pk (k.map Float.toBits) at hKs
  change heap.Borrowed initial pc (cache.map Float.toBits) at hCs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pq, .i64 pk, .i64 pc, .i64 l, .i64 p, .i64 nh, .i64 dh, .i64 bsize,
        .f64 scale.toBits]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0,
        .i64 0] }
  show Triple _ (.buildWith 9 10 11 (.bin .mul (.get 5) (.bin .add (.get 4) (.const 1)))
      (.seq (.assign 12 (.constF 0)) (.loop 13 14 (.get 6) stepScoreBody))
      (.toBits (.binF .mul (.getF 12) (.getF 8)))) 16
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [12, 13, 14, 15]) (n := nh * (p + 1))
    (fun e => (LeanExe.loop dh 0.0 (stepScoreStep q k cache l p nh dh bsize e) * scale).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro e store state he hAt hFrame hIndex
    have hp : p + 1 ≠ 0 := by
      intro h
      rw [h, UInt64.mul_zero] at he
      simp at he
    have hState : state.params.length = 9 ∧ state.locals.length = 10 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 9 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hQ := hAt pq _ hQs
    have hK := hAt pk _ hKs
    have hC := hAt pc _ hCs
    let s1 := state.update 12 (.f64 0)
    have hS1 : s1.params.length = 9 ∧ s1.locals.length = 10 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 12 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    have g6 : state.get 6 = some (.i64 dh) := (hGet 6 (by decide)).trans rfl
    have g8 : state.get 8 = some (.f64 scale.toBits) := (hGet 8 (by decide)).trans rfl
    refine (Stmt.loop_spec (vars := [12]) (writes := [12, 15]) (init := (0.0 : Float)) (n := dh)
      (stepScoreStep q k cache l p nh dh bsize (UInt64.ofNat e)) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 6 (by decide), g6]⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 9 ∧ st.locals.length = 10 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 9 ∨ j = 11 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g12 : st.get 12 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := stepScoreBody_run hQ hK hC hp hSt.1
        hSt.2 ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans ((hGet 2 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 4 (by omega)).trans ((hGet 4 (by decide)).trans rfl))
        ((hKeep 5 (by omega)).trans ((hGet 5 (by decide)).trans rfl))
        ((hKeep 6 (by omega)).trans g6)
        ((hKeep 7 (by omega)).trans ((hGet 7 (by decide)).trans rfl))
        ((hKeep 11 (by omega)).trans hIndex) g12 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g12 : u.get 12 = some (.f64 (LeanExe.loop dh 0.0
          (stepScoreStep q k cache l p nh dh bsize (UInt64.ofNat e))).toBits) :=
        (List.forall₂_cons.mp hHolds).1
      have hU : ∀ j, j < 9 ∨ j = 11 → u.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have u8 : u.get 8 = some (.f64 scale.toBits) := (hU 8 (by omega)).trans g8
      refine ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), ?_⟩
      simp [Expr.eval, u8, g12, F64Op.apply, F64Bits.toBits_mul]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.stepScores.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : stepScoresTuple (q, k, cache, l, p, nh, dh, bsize, scale) =
      LeanExe.build (nh * (p + 1)) (fun e =>
        LeanExe.loop dh 0.0 (stepScoreStep q k cache l p nh dh bsize e) * scale) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `stepMix` with its eight arguments as one tuple. -/
def stepMixTuple (x : Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64) : Array Float :=
  Examples.Gpt.stepMix x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2

/-- One step of the sum for column `c` of `stepMix`: the weight of position `j` for the head
of column `c`, times column `c` of value `j`. -/
def stepMixStep (pw v cache : Array Float) (l p nh dh bsize c j : UInt64) (acc : Float) : Float :=
  acc + pw[(c / dh * (p + 1) + j).toNat]! *
    (if j < p then cache[(j * bsize + (2 * l + 2) * (nh * dh) + c).toNat]! else v[c.toNat]!)

/-- The compiled loop body of `stepMix`. -/
def stepMixBody : Stmt :=
  .seq (.assign 14 (.binF .add (.getF 11) (.binF .mul
    (.ofBits (.read 0 (.bin .add (.bin .mul (.bin .divU (.get 10) (.get 6))
      (.bin .add (.get 4) (.const 1))) (.get 13))))
    (.iteF (.ltU (.get 13) (.get 4))
      (.ofBits (.read 2 (.bin .add (.bin .add (.bin .mul (.get 13) (.get 7))
        (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 3)) (.const 2))
          (.bin .mul (.get 5) (.get 6)))) (.get 10))))
      (.ofBits (.read 1 (.get 10)))))))
    (.assign 11 (.getF 14))

theorem stepMixBody_run {initial : Store Unit} {pp pv pc : UInt64} {pw v cache : Array Float}
    (hP : UInt64Array.At initial pp (pw.map Float.toBits))
    (hV : UInt64Array.At initial pv (v.map Float.toBits))
    (hC : UInt64Array.At initial pc (cache.map Float.toBits)) {state : State} {j : Nat}
    {l p nh dh bsize c : UInt64} {acc : Float} (hd : dh ≠ 0)
    (hParams : state.params.length = 8) (hLocals : state.locals.length = 10)
    (h0 : state.get 0 = some (.i64 pp)) (h1 : state.get 1 = some (.i64 pv))
    (h2 : state.get 2 = some (.i64 pc)) (h3 : state.get 3 = some (.i64 l))
    (h4 : state.get 4 = some (.i64 p)) (h5 : state.get 5 = some (.i64 nh))
    (h6 : state.get 6 = some (.i64 dh)) (h7 : state.get 7 = some (.i64 bsize))
    (h10 : state.get 10 = some (.i64 c)) (h11 : state.get 11 = some (.f64 acc.toBits))
    (h13 : state.get 13 = some (.i64 (UInt64.ofNat j))) :
    ∃ final, stepMixBody.run initial.mem 15 state = some final ∧
      State.Frame 15 [11, 14] state final ∧
      final.Holds [11]
        (Scalar.values (stepMixStep pw v cache l p nh dh bsize c (UInt64.ofNat j) acc)) := by
  by_cases hc : UInt64.ofNat j < p <;>
  · simp [stepMixBody, Stmt.run, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h10, h11, h13,
      Expr.readValue_at hP, Expr.readValue_at hV, Expr.readValue_at hC, State.set?_eq_update,
      hParams, hLocals, F64Op.apply, U64Op.apply, getElem!_map_toBits, hd, hc]
    constructor
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, Scalar.values, stepMixStep, hParams, hLocals, F64Bits.toBits_add,
        F64Bits.toBits_mul, hc]

theorem stepMix_implements : Implements gpt.module 36 stepMixTuple := by
  refine Func.implements_heap gpt.funcs 34 gpt.stepMix.ir "stepMix" rfl stepMixTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨pw, v, cache, l, p, nh, dh, bsize⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPs⟩, _, _, rfl, ⟨pv, rfl, hVs⟩, _, _, rfl, ⟨pc, rfl, hCs⟩, rfl⟩ hCap
  change heap.Borrowed initial pp (pw.map Float.toBits) at hPs
  change heap.Borrowed initial pv (v.map Float.toBits) at hVs
  change heap.Borrowed initial pc (cache.map Float.toBits) at hCs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pp, .i64 pv, .i64 pc, .i64 l, .i64 p, .i64 nh, .i64 dh, .i64 bsize]
      locals := [.i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0,
        .i64 0] }
  show Triple _ (.buildWith 8 9 10 (.bin .mul (.get 5) (.get 6))
      (.seq (.assign 11 (.constF 0)) (.loop 12 13 (.bin .add (.get 4) (.const 1)) stepMixBody))
      (.toBits (.getF 11))) 15
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [11, 12, 13, 14]) (n := nh * dh)
    (fun c => (LeanExe.loop (p + 1) 0.0 (stepMixStep pw v cache l p nh dh bsize c)).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by decide) (by simp [start]) hHeap hCap
    ⟨start, by simp [Expr.eval, U64Op.apply]; rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro c store state hc hAt hFrame hIndex
    have hd : dh ≠ 0 := by rintro rfl; simp at hc
    have hState : state.params.length = 8 ∧ state.locals.length = 10 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 8 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g4 : state.get 4 = some (.i64 p) := (hGet 4 (by decide)).trans rfl
    have hP := hAt pp _ hPs
    have hV := hAt pv _ hVs
    have hC := hAt pc _ hCs
    let s1 := state.update 11 (.f64 0)
    have hS1 : s1.params.length = 8 ∧ s1.locals.length = 10 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 11 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [11]) (writes := [11, 14]) (init := (0.0 : Float))
      (n := p + 1) (stepMixStep pw v cache l p nh dh bsize (UInt64.ofNat c)) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by simp [hS1.1, hS1.2])
      (by simp [Expr.eval, hS1Get 4 (by decide), g4, U64Op.apply])
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro j acc st hj hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 8 ∧ st.locals.length = 10 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ i, i < 8 ∨ i = 10 → st.get i = state.get i := fun i hi =>
        (hFrameL.get i (by omega) (by simp; omega)).trans (hS1Get i (by omega))
      have g11 : st.get 11 = some (.f64 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := stepMixBody_run hP hV hC hd hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 2 (by omega)).trans ((hGet 2 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 4 (by omega)).trans g4)
        ((hKeep 5 (by omega)).trans ((hGet 5 (by decide)).trans rfl))
        ((hKeep 6 (by omega)).trans ((hGet 6 (by decide)).trans rfl))
        ((hKeep 7 (by omega)).trans ((hGet 7 (by decide)).trans rfl))
        ((hKeep 10 (by omega)).trans hIndex) g11 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' u ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' u ⟨rfl, hFrameL, hHolds⟩
      have g11 : u.get 11 = some (.f64 (LeanExe.loop (p + 1) 0.0
          (stepMixStep pw v cache l p nh dh bsize (UInt64.ofNat c))).toBits) :=
        (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), u, by simp [Expr.eval, g11]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.stepMix.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : stepMixTuple (pw, v, cache, l, p, nh, dh, bsize) = LeanExe.build (nh * dh)
      (fun c => LeanExe.loop (p + 1) 0.0 (stepMixStep pw v cache l p nh dh bsize c)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `writeBlock` with its six arguments as one tuple. -/
def writeBlockTuple (x : Array Float × Array Float × Array Float × Array Float × UInt64 ×
    UInt64) : Array Float :=
  Examples.Gpt.writeBlock x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- Element `e` of `writeBlock`. -/
def writeAt (s x k v : Array Float) (l d e : UInt64) : Float :=
  if e < d then x[e.toNat]!
  else if e < (2 * l + 1) * d then s[e.toNat]!
  else if e < (2 * l + 2) * d then k[(e - (2 * l + 1) * d).toNat]!
  else if e < (2 * l + 3) * d then v[(e - (2 * l + 2) * d).toNat]!
  else s[e.toNat]!

/-- The compiled element of `writeBlock`. -/
def writeElem : Expr .u64 :=
  .toBits (.iteF (.ltU (.get 9) (.get 5)) (.ofBits (.read 1 (.get 9)))
    (.iteF (.ltU (.get 9) (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 4)) (.const 1))
      (.get 5))) (.ofBits (.read 0 (.get 9)))
    (.iteF (.ltU (.get 9) (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 4)) (.const 2))
      (.get 5)))
      (.ofBits (.read 2 (.bin .sub (.get 9) (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 4))
        (.const 1)) (.get 5)))))
    (.iteF (.ltU (.get 9) (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 4)) (.const 3))
      (.get 5)))
      (.ofBits (.read 3 (.bin .sub (.get 9) (.bin .mul (.bin .add (.bin .mul (.const 2) (.get 4))
        (.const 2)) (.get 5)))))
      (.ofBits (.read 0 (.get 9)))))))

theorem writeElem_row {px : UInt64} {s x k v : Array Float} {store : Store Unit} {state : State} {i : Nat} {l d : UInt64}
    (hParams : state.params.length = 6) (hLocals : state.locals.length = 5)
    (g5 : state.get 5 = some (.i64 d))
    (hIndex : state.get 9 = some (.i64 (UInt64.ofNat i)))
    (hX : UInt64Array.At store px (x.map Float.toBits)) (g1 : state.get 1 = some (.i64 px))
    (h1 : UInt64.ofNat i < d) : ∃ next, writeElem.eval store.mem 10 state =
      some ((writeAt s x k v l d (UInt64.ofNat i)).toBits, next) := by
  simp [writeElem, writeAt, Expr.eval, g1, g5, hIndex, h1, Expr.readValue_at hX,
    State.set?_eq_update, hParams, hLocals, getElem!_map_toBits]

theorem writeElem_before {ps : UInt64} {s x k v : Array Float} {store : Store Unit} {state : State} {i : Nat} {l d : UInt64}
    (hParams : state.params.length = 6) (hLocals : state.locals.length = 5)
    (g4 : state.get 4 = some (.i64 l)) (g5 : state.get 5 = some (.i64 d))
    (hIndex : state.get 9 = some (.i64 (UInt64.ofNat i)))
    (hS : UInt64Array.At store ps (s.map Float.toBits)) (g0 : state.get 0 = some (.i64 ps))
    (h1 : ¬ UInt64.ofNat i < d) (h2 : UInt64.ofNat i < (2 * l + 1) * d) :
    ∃ next, writeElem.eval store.mem 10 state =
      some ((writeAt s x k v l d (UInt64.ofNat i)).toBits, next) := by
  simp [writeElem, writeAt, Expr.eval, g0, g4, g5, hIndex, h1, h2, Expr.readValue_at hS,
    State.set?_eq_update, hParams, hLocals, U64Op.apply, getElem!_map_toBits]

theorem writeElem_key {pk : UInt64} {s x k v : Array Float} {store : Store Unit} {state : State} {i : Nat} {l d : UInt64}
    (hParams : state.params.length = 6) (hLocals : state.locals.length = 5)
    (g4 : state.get 4 = some (.i64 l)) (g5 : state.get 5 = some (.i64 d))
    (hIndex : state.get 9 = some (.i64 (UInt64.ofNat i)))
    (hK : UInt64Array.At store pk (k.map Float.toBits)) (g2 : state.get 2 = some (.i64 pk))
    (h1 : ¬ UInt64.ofNat i < d) (h2 : ¬ UInt64.ofNat i < (2 * l + 1) * d)
    (h3 : UInt64.ofNat i < (2 * l + 2) * d) : ∃ next, writeElem.eval store.mem 10 state =
      some ((writeAt s x k v l d (UInt64.ofNat i)).toBits, next) := by
  simp [writeElem, writeAt, Expr.eval, g2, g4, g5, hIndex, h1, h2, h3, Expr.readValue_at hK,
    State.set?_eq_update, hParams, hLocals, U64Op.apply, getElem!_map_toBits]

theorem writeElem_value {pv : UInt64} {s x k v : Array Float} {store : Store Unit} {state : State} {i : Nat} {l d : UInt64}
    (hParams : state.params.length = 6) (hLocals : state.locals.length = 5)
    (g4 : state.get 4 = some (.i64 l)) (g5 : state.get 5 = some (.i64 d))
    (hIndex : state.get 9 = some (.i64 (UInt64.ofNat i)))
    (hV : UInt64Array.At store pv (v.map Float.toBits)) (g3 : state.get 3 = some (.i64 pv))
    (h1 : ¬ UInt64.ofNat i < d) (h2 : ¬ UInt64.ofNat i < (2 * l + 1) * d)
    (h3 : ¬ UInt64.ofNat i < (2 * l + 2) * d) (h4 : UInt64.ofNat i < (2 * l + 3) * d) :
    ∃ next, writeElem.eval store.mem 10 state =
      some ((writeAt s x k v l d (UInt64.ofNat i)).toBits, next) := by
  simp [writeElem, writeAt, Expr.eval, g3, g4, g5, hIndex, h1, h2, h3, h4, Expr.readValue_at hV,
    State.set?_eq_update, hParams, hLocals, U64Op.apply, getElem!_map_toBits]

theorem writeElem_after {ps : UInt64} {s x k v : Array Float} {store : Store Unit} {state : State} {i : Nat} {l d : UInt64}
    (hParams : state.params.length = 6) (hLocals : state.locals.length = 5)
    (g4 : state.get 4 = some (.i64 l)) (g5 : state.get 5 = some (.i64 d))
    (hIndex : state.get 9 = some (.i64 (UInt64.ofNat i)))
    (hS : UInt64Array.At store ps (s.map Float.toBits)) (g0 : state.get 0 = some (.i64 ps))
    (h1 : ¬ UInt64.ofNat i < d) (h2 : ¬ UInt64.ofNat i < (2 * l + 1) * d)
    (h3 : ¬ UInt64.ofNat i < (2 * l + 2) * d) (h4 : ¬ UInt64.ofNat i < (2 * l + 3) * d) :
    ∃ next, writeElem.eval store.mem 10 state =
      some ((writeAt s x k v l d (UInt64.ofNat i)).toBits, next) := by
  simp [writeElem, writeAt, Expr.eval, g0, g4, g5, hIndex, h1, h2, h3, h4, Expr.readValue_at hS,
    State.set?_eq_update, hParams, hLocals, U64Op.apply, getElem!_map_toBits]

theorem writeBlock_implements : Implements gpt.module 37 writeBlockTuple := by
  refine Func.implements_heap gpt.funcs 35 gpt.writeBlock.ir "writeBlock" rfl writeBlockTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl,
      ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨s, x, k, v, l, d⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨ps, rfl, hSs⟩, _, _, rfl, ⟨px, rfl, hXs⟩, _, _, rfl, ⟨pk, rfl, hKs⟩, _, _, rfl,
      ⟨pv, rfl, hVs⟩, rfl⟩ hCap
  change heap.Borrowed initial ps (s.map Float.toBits) at hSs
  change heap.Borrowed initial px (x.map Float.toBits) at hXs
  change heap.Borrowed initial pk (k.map Float.toBits) at hKs
  change heap.Borrowed initial pv (v.map Float.toBits) at hVs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hA := hSs.values
  have hFit := hA.1
  simp only [Array.size_map] at hFit
  have hLength := hA.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hn : (UInt64.ofNat s.size).toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  let start : State :=
    { params := [.i64 ps, .i64 px, .i64 pk, .i64 pv, .i64 l, .i64 d]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  have hGet0 : start.get 0 = some (.i64 ps) := rfl
  let s1 := start.update 6 (.i64 (UInt64.ofNat s.size))
  show Triple _ (.seq (.arraySize 6 0) (.build 7 8 9 (.get 6) writeElem)) 10
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hA.lengthRead,
      State.set?_eq_update, s1, start])) ?_
  have hS1 : s1.params.length = 6 ∧ s1.locals.length = 5 := by simp [s1, start]
  refine (Stmt.build_spec (n := s.size.toUInt64) (fun e => (writeAt s x k v l d e).toBits)
    hMemory32 hImports hAlloc (by decide) (by decide) (by simp [hS1.1, hS1.2]) hHeap
    hCap
    ⟨s1, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hState : state.params.length = 6 ∧ state.locals.length = 5 :=
      ⟨hFrame.params.trans hS1.1, hFrame.locals.trans hS1.2⟩
    have hGet : ∀ j, j < 6 → state.get j = s1.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 ps) := (hGet 0 (by decide)).trans rfl
    have g1 : state.get 1 = some (.i64 px) := (hGet 1 (by decide)).trans rfl
    have g2 : state.get 2 = some (.i64 pk) := (hGet 2 (by decide)).trans rfl
    have g3 : state.get 3 = some (.i64 pv) := (hGet 3 (by decide)).trans rfl
    have g4 : state.get 4 = some (.i64 l) := (hGet 4 (by decide)).trans rfl
    have g5 : state.get 5 = some (.i64 d) := (hGet 5 (by decide)).trans rfl
    by_cases h1 : UInt64.ofNat i < d
    · exact writeElem_row (l := l) hState.1 hState.2 g5 hIndex (hAt px _ hXs) g1 h1
    by_cases h2 : UInt64.ofNat i < (2 * l + 1) * d
    · exact writeElem_before hState.1 hState.2 g4 g5 hIndex (hAt ps _ hSs) g0 h1 h2
    by_cases h3 : UInt64.ofNat i < (2 * l + 2) * d
    · exact writeElem_key hState.1 hState.2 g4 g5 hIndex (hAt pk _ hKs) g2 h1 h2 h3
    by_cases h4 : UInt64.ofNat i < (2 * l + 3) * d
    · exact writeElem_value hState.1 hState.2 g4 g5 hIndex (hAt pv _ hVs) g3 h1 h2 h3 h4
    · exact writeElem_after hState.1 hState.2 g4 g5 hIndex (hAt ps _ hSs) g0 h1 h2 h3 h4
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [gpt.writeBlock.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  have hEq : writeBlockTuple (s, x, k, v, l, d) =
      LeanExe.build s.size.toUInt64 (writeAt s x k v l d) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `appendBlock` with its two arguments as one pair: the call consumes the cache. -/
def appendBlockTuple (x : Moved (Array Float) × Array Float) : Array Float :=
  Examples.Gpt.appendBlock x.1.val x.2

theorem appendBlock_implements : Implements gpt.module 38 appendBlockTuple := by
  refine Func.implements_moves gpt.funcs 36 gpt.appendBlock.ir "appendBlock" rfl appendBlockTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨⟨cache⟩, s⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨pc, rfl, hCs⟩, ⟨ps, rfl, hSs⟩⟩ ⟨-, hSep⟩
    hCap
  change heap.Owned initial pc (cache.map Float.toBits) at hCs
  change heap.Borrowed initial ps (s.map Float.toBits) at hSs
  have hMoves : ∀ r, Apart initial [pc] r → regionsDisjoint r (Project.Pipeline.block initial pc) :=
    fun r h => h pc (List.mem_singleton_self _)
  have hApart := hMoves _ (hSep _ (List.mem_singleton_self _))
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  show Triple _ (Stmt.append 2 3 4 5 6 7 0 1) 8
    (fun store state => store = initial ∧ state = gpt.appendBlock.ir.state [.i64 pc, .i64 ps]) _
  refine (Stmt.append_spec hMemory32 hImports hAlloc hRelease (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by simp only [Func.state, List.length_cons, List.length_nil, List.length_map]; decide)
    hHeap hCap hCs hSs hApart rfl rfl).mono
    (fun _ _ h => h) ?_
  rintro store state ⟨heap', p, -, hDst, hAt, hOwned, hCaps, hKeeps⟩
  refine ⟨heap', hAt, hCaps, [.i64 p], state,
    by simp [gpt.appendBlock.ir, Func.scratch, Expr.evalResults, Expr.eval, hDst],
    ⟨p, rfl, ?_⟩, hKeeps⟩
  show heap'.Owned store p ((cache ++ s).map Float.toBits)
  rw [Array.map_append]
  exact hOwned

end Examples.Gpt
