import Project.Binary32.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Run
import Project.ProofKit.F32Bits
import Project.Encoding.RoundTrip

namespace Project.Binary32

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Binary32

/-- `axpy32` with its three arguments as one tuple. -/
def axpy32Tuple (x : Float32 × Float32 × Float32) : Float32 := axpy32 x.1 x.2.1 x.2.2

/-- `hypot32` with its two arguments as one pair. -/
def hypot32Pair (x : Float32 × Float32) : Float32 := hypot32 x.1 x.2

/-- `ratio32` with its three arguments as one tuple. -/
def ratio32Tuple (x : Float32 × Float32 × Float32) : Float32 := ratio32 x.1 x.2.1 x.2.2

theorem axpy32_implements : Implements binary32.module 2 axpy32Tuple :=
  Func.implements binary32.funcs 0 binary32.axpy32.ir "axpy32" rfl axpy32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.axpy32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        Scalar.values, axpy32Tuple, axpy32, F32Bits.toBits_add, F32Bits.toBits_mul]⟩)
      fun _ _ h => h

theorem hypot32_implements : Implements binary32.module 3 hypot32Pair :=
  Func.implements binary32.funcs 1 binary32.hypot32.ir "hypot32" rfl hypot32Pair
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.hypot32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        F32UnOp.apply, Scalar.values, hypot32Pair, hypot32, F32Bits.toBits_add,
        F32Bits.toBits_mul, F32Bits.toBits_sqrt]⟩)
      fun _ _ h => h

theorem ratio32_implements : Implements binary32.module 4 ratio32Tuple :=
  Func.implements binary32.funcs 2 binary32.ratio32.ir "ratio32" rfl ratio32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, b, c⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.ratio32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        Scalar.values, ratio32Tuple, ratio32, F32Bits.toBits_sub, F32Bits.toBits_div]⟩)
      fun _ _ h => h

/-- `matVec32` with its four arguments as one tuple. -/
def matVec32Tuple (x : Array Float32 × Array Float32 × UInt64 × UInt64) : Array Float32 :=
  matVec32 x.1 x.2.1 x.2.2.1 x.2.2.2

/-- One step of the loop over row `r`. -/
def rowStep32 (m v : Array Float32) (cols r c : UInt64) (acc : Float32) : Float32 :=
  acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- Element `r` of the product. -/
def row32 (m v : Array Float32) (cols r : UInt64) : Float32 :=
  LeanExe.loop cols 0.0 (rowStep32 m v cols r)

theorem matVec32_eq (m v : Array Float32) (rows cols : UInt64) :
    matVec32 m v rows cols = LeanExe.build rows (row32 m v cols) := rfl

/-- The compiled loop body over a row. -/
def rowBody32 : Stmt :=
  .seq (.assign 10 (.binF32 .add (.getF32 7) (.binF32 .mul
    (.ofBits32 (.read 0 (.bin .add (.bin .mul (.get 6) (.get 3)) (.get 9))))
    (.ofBits32 (.read 1 (.get 9)))))) (.assign 7 (.getF32 10))

theorem rowBody32_run {initial : Store Unit} {pm pv : UInt64} {m v : Array Float32}
    (hM : UInt64Array.At initial pm (m.map fun x : Float32 => x.toBits.toUInt64))
    (hV : UInt64Array.At initial pv (v.map fun x : Float32 => x.toBits.toUInt64))
    {state : State} {c : Nat} {r cols : UInt64} {acc : Float32}
    (hParams : state.params.length = 4) (hLocals : state.locals.length = 8)
    (h0 : state.get 0 = some (.i64 pm)) (h1 : state.get 1 = some (.i64 pv))
    (h3 : state.get 3 = some (.i64 cols)) (h6 : state.get 6 = some (.i64 r))
    (h7 : state.get 7 = some (.f32 acc.toBits))
    (h9 : state.get 9 = some (.i64 (UInt64.ofNat c))) :
    ∃ final, rowBody32.run initial.mem 11 state = some final ∧
      State.Frame 11 [7, 10] state final ∧
      final.Holds [7] (Scalar.values (rowStep32 m v cols r (UInt64.ofNat c) acc)) := by
  simp [rowBody32, Stmt.run, Expr.eval, h0, h1, h3, h6, h7, h9, Expr.readValue_at hM,
    Expr.readValue_at hV, State.set?_eq_update, hParams, hLocals, F32Op.apply, U64Op.apply,
    getElem!_map_toBits32]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, rowStep32, hParams, hLocals, F32Bits.toBits_add,
      F32Bits.toBits_mul]

theorem matVec32_implements : Implements binary32.module 5 matVec32Tuple := by
  refine Func.implements_heap binary32.funcs 3 binary32.matVec32.ir "matVec32" rfl matVec32Tuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨m, v, rows, cols⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨pv, rfl, hVs⟩, rfl⟩ hCap
  change heap.Borrowed initial pm (m.map fun x : Float32 => x.toBits.toUInt64) at hMs
  change heap.Borrowed initial pv (v.map fun x : Float32 => x.toBits.toUInt64) at hVs
  have hMemory32 : binary32.module.memIs64 = false := rfl
  have hImports : binary32.module.imports = [] := rfl
  have hAlloc : binary32.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float32).toBits = 0 := by decide +kernel
  let start : State :=
    { params := [.i64 pm, .i64 pv, .i64 rows, .i64 cols]
      locals := [.i64 0, .i64 0, .i64 0, .f32 0, .i64 0, .i64 0, .f32 0, .i64 0] }
  show Triple _ (.buildWith 4 5 6 (.get 2)
      (.seq (.assign 7 (.constF32 0)) (.loop 8 9 (.get 3) rowBody32)) (.toBits32 (.getF32 7))) 11
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := [7, 8, 9, 10]) (n := rows)
    (fun r => (row32 m v cols r).toBits.toUInt64) hMemory32 hImports hAlloc (by decide)
    (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · -- One element: the accumulator, then the loop over the row.
    intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 8 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 4 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp; omega)
    have hM := hAt pm _ hMs
    have hV := hAt pv _ hVs
    let s1 := state.update 7 (.f32 0)
    have hS1 : s1.params.length = 4 ∧ s1.locals.length = 8 := by
      simp [s1, hState.1, hState.2]
    have hS1Get : ∀ j, j ≠ 7 → s1.get j = state.get j := fun j hj => State.get_update_ne hj
    refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hState.1, hState.2, s1])) ?_
    refine (Stmt.loop_spec (vars := [7]) (writes := [7, 10]) (init := (0.0 : Float32))
      (n := cols) (rowStep32 m v cols (UInt64.ofNat k)) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [hS1.1, hS1.2])
      ⟨s1, by simp [Expr.eval, hS1Get 3 (by decide), hGet 3 (by decide)]; rfl⟩
      (by simp [State.Holds, Scalar.values, s1, hState.1, hState.2, hZero]) ?_).mono
        (fun _ _ h => h) ?_
    · intro c acc st hc hFrameL hHolds hIdx hLim
      have hSt : st.params.length = 4 ∧ st.locals.length = 8 :=
        ⟨hFrameL.params.trans hS1.1, hFrameL.locals.trans hS1.2⟩
      have hKeep : ∀ j, j < 4 ∨ j = 6 → st.get j = state.get j := fun j hj =>
        (hFrameL.get j (by omega) (by simp; omega)).trans (hS1Get j (by omega))
      have g7 : st.get 7 = some (.f32 acc.toBits) := by
        simpa [State.Holds, Scalar.values] using hHolds
      obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ := rowBody32_run hM hV hSt.1 hSt.2
        ((hKeep 0 (by omega)).trans ((hGet 0 (by decide)).trans rfl))
        ((hKeep 1 (by omega)).trans ((hGet 1 (by decide)).trans rfl))
        ((hKeep 3 (by omega)).trans ((hGet 3 (by decide)).trans rfl))
        ((hKeep 6 (by omega)).trans hIndex) g7 hIdx
      refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
      rintro s' t ⟨rfl, rfl⟩
      exact ⟨rfl, hFinalFrame, hFinalHolds⟩
    · rintro s' t ⟨rfl, hFrameL, hHolds⟩
      have g7 : t.get 7 = some (.f32 (row32 m v cols (UInt64.ofNat k)).toBits) :=
        (List.forall₂_cons.mp hHolds).1
      exact ⟨rfl, (State.Frame.update (State.Frame.refl _ _ _) (Or.inl (by simp))).trans
          (hFrameL.weaken (by simp)), t, by simp [Expr.eval, g7]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [binary32.matVec32.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  rw [matVec32Tuple, matVec32_eq, build_map]
  exact hNew.owned

/-- `piecewise32` with its three arguments as one tuple. -/
def piecewise32Tuple (x : Float32 × Float32 × Float32) : Float32 := piecewise32 x.1 x.2.1 x.2.2

theorem piecewise32_implements : Implements binary32.module 6 piecewise32Tuple :=
  Func.implements binary32.funcs 4 binary32.piecewise32.ir "piecewise32" rfl piecewise32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, lo, hi⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨[.f32 (piecewise32 x lo hi).toBits],
        binary32.piecewise32.ir.state (Scalar.values (x, lo, hi)), ?_, rfl⟩
      have h0 : (0.0 : Float32).toBits = 0 := by decide
      have h05 : (0.5 : Float32).toBits = 0x3f000000 := by decide
      have h15 : (1.5 : Float32).toBits = 0x3fc00000 := by decide
      have hx : binary32.piecewise32.ir.state (Scalar.values (x, lo, hi)) =
          { params := [.f32 x.toBits, .f32 lo.toBits, .f32 hi.toBits], locals := [] } := rfl
      rw [hx]
      dsimp only [binary32.piecewise32.ir, Func.scratch]
      simp [Expr.evalResults, Expr.eval, State.get, F32Op.apply, F32UnOp.apply, piecewise32,
        F32Bits.beq_eq, F32Bits.lt_iff, F32Bits.le_iff]
      cases h1 : Wasm.IEEE32.eq x.toBits lo.toBits <;>
        cases h2 : Wasm.IEEE32.lt x.toBits lo.toBits <;>
        cases h3 : Wasm.IEEE32.le hi.toBits x.toBits <;>
        cases h4 : Wasm.IEEE32.le x.toBits hi.toBits <;>
        cases h5 : Wasm.IEEE32.le lo.toBits x.toBits <;>
        cases h6 : Wasm.IEEE32.le lo.toBits hi.toBits <;>
        simp [h1, h2, h3, h4, h5, h6, F32Bits.toBits_add, F32Bits.toBits_sub, F32Bits.toBits_mul,
          F32Bits.toBits_neg, F32Bits.toBits_abs, F32Bits.toBits_min, F32Bits.toBits_max, h0, h05,
          h15]⟩) fun _ _ h => h

/-- `encode` succeeds on `binary32.module`, and its bytes decode to a module that computes
`axpy32`, `hypot32`, `ratio32`, `matVec32`, and `piecewise32` bit for bit. -/
theorem binary32_bytes : ∃ bytes, Wasm.Encoding.encode binary32.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 axpy32Tuple ∧
      Implements m 3 hypot32Pair ∧ Implements m 4 ratio32Tuple ∧
      Implements m 5 matVec32Tuple ∧ Implements m 6 piecewise32Tuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip binary32.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, binary32.module, decoded, axpy32_implements, hypot32_implements,
    ratio32_implements, matVec32_implements, piecewise32_implements⟩

#print axioms binary32_bytes

end Project.Binary32
