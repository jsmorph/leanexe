import Examples.Calc.Module
import Examples.Calc.Flat
import Project.IR.Correct
import Project.IR.Run
import Project.IR.Call
import Project.IR.Live
import Project.IR.Loop
import Project.IR.Read
import Project.Encoding.RoundTrip

/-! The calculator's compiled functions compute their Lean definitions exactly.  The five
functions of words keep the store; `calcRun` reads its array of instructions. -/

namespace Examples.Calc

open Wasm Project.Pipeline Project.IR Examples.Calc

/-- `Op.apply` with its three arguments as one tuple. -/
def applyTuple (x : Op × UInt64 × UInt64) : UInt64 := x.1.apply x.2.1 x.2.2

theorem apply_pure : ImplementsPure calculator.module 2 applyTuple := by
  refine Func.implementsPure calculator.funcs 0 calculator.apply.ir "apply" rfl applyTuple
    (fun _ => rfl) fun ⟨op, a, b⟩ initial => ?_
  show Triple _ .skip _ _ _
  refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
  subst hState
  cases op <;> simp [calculator.apply.ir, Func.scratch, Func.state, Func.locals, Func.width,
    Expr.evalResults, Expr.eval, Expr.scratchWidth, Stmt.scratchWidth, State.get, State.set?,
    U64Op.apply, Scalar.values, Flat.flat, applyTuple, Op.apply, Op.ctorIdx]
  by_cases hb : b = 0 <;> simp [hb]

theorem ofWord_pure : ImplementsPure calculator.module 3 Op.ofWord := by
  refine Func.implementsPure calculator.funcs 1 calculator.ofWord.ir "ofWord" rfl Op.ofWord
    (fun _ => rfl) fun w initial => ?_
  show Triple _ .skip _ _ _
  refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
  subst hState
  simp only [calculator.ofWord.ir, Func.scratch, Func.state, Func.locals, Func.width,
    Expr.evalResults, Expr.eval, Stmt.scratchWidth, State.get, Scalar.values, Flat.flat,
    Op.ofWord]
  simp
  split_ifs <;> rfl

theorem inverse_pure : ImplementsPure calculator.module 4 Op.inverse := by
  refine Func.implementsPure calculator.funcs 2 calculator.inverse.ir "inverse" rfl Op.inverse
    (fun _ => rfl) fun op initial => ?_
  show Triple _ .skip _ _ _
  refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
  subst hState
  cases op <;> simp [calculator.inverse.ir, Func.scratch, Func.state, Func.locals, Func.width,
    Expr.evalResults, Expr.eval, Expr.scratchWidth, Stmt.scratchWidth, State.get, Scalar.values,
    Flat.flat, Op.inverse, Op.ctorIdx]

/-- `Calc.step` with its three arguments as one tuple. -/
def stepTuple (x : Calc × Op × UInt64) : Calc := x.1.step x.2.1 x.2.2

theorem step_pure : ImplementsPure calculator.module 5 stepTuple := by
  refine Func.implementsPure calculator.funcs 3 calculator.step.ir "step" rfl stepTuple
    (fun _ => rfl) fun ⟨⟨value, steps, last⟩, op, x⟩ initial => ?_
  let start : State :=
    { params := [.i64 value, .i64 steps, .i64 last.ctorIdx.toUInt64, .i64 op.ctorIdx.toUInt64,
        .i64 x], locals := List.replicate 1 (.i64 0) }
  show Triple _ (.call 2 [⟨.u64, .get 3⟩, ⟨.u64, .get 0⟩, ⟨.u64, .get 4⟩] [5]) 6
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.callPure_spec apply_pure rfl rfl rfl (x := (op, value, x))
    (next := start.update 5 (.i64 (op.apply value x))) rfl ?_).mono (fun _ _ h => h) ?_
  · simp [State.setAll, State.set?_eq_update, start, Scalar.values, applyTuple]
  rintro s st ⟨rfl, rfl⟩
  refine ⟨rfl, _, _, rfl, ?_⟩
  simp [Scalar.values, Flat.flat, stepTuple, Calc.step, U64Op.apply]

/-- `Calc.undo` with its two arguments as one tuple. -/
def undoTuple (x : Calc × UInt64) : Calc := x.1.undo x.2

theorem undo_pure : ImplementsPure calculator.module 6 undoTuple := by
  refine Func.implementsPure calculator.funcs 4 calculator.undo.ir "undo" rfl undoTuple
    (fun _ => rfl) fun ⟨⟨value, steps, last⟩, x⟩ initial => ?_
  let start : State :=
    { params := [.i64 value, .i64 steps, .i64 last.ctorIdx.toUInt64, .i64 x],
      locals := List.replicate 3 (.i64 0) }
  let r := Calc.undo ⟨value, steps, last⟩ x
  show Triple _ calculator.undo.ir.body 7 (fun store state => store = initial ∧ state = start) _
  refine (Stmt.run_spec (final := ((start.update 4 (.i64 r.value)).update 5 (.i64 r.steps)).update
    6 (.i64 r.last.ctorIdx.toUInt64)) ?_).mono (fun _ _ h => h) ?_
  have hParams : start.params.length = 4 := rfl
  have hLocals : start.locals.length = 3 := rfl
  have h0 : start.get 0 = some (.i64 value) := rfl
  have h1 : start.get 1 = some (.i64 steps) := rfl
  have h2 : start.get 2 = some (.i64 last.ctorIdx.toUInt64) := rfl
  have h3 : start.get 3 = some (.i64 x) := rfl
  · cases last <;> simp [calculator.undo.ir, Stmt.run, Expr.eval, State.set?_eq_update, hParams,
      hLocals, h0, h1, h2, h3, r, Calc.undo, Op.ctorIdx, U64Op.apply]
  rintro s st ⟨rfl, rfl⟩
  refine ⟨rfl, _, _, rfl, ?_⟩
  simp [Scalar.values, Flat.flat, undoTuple, r]

/-- The step of `calcRun`'s loop: instruction `i` of `words` applied to the state. -/
def calcStep (words : Array UInt64) (i : UInt64) (c : Calc) : Calc :=
  c.step (Op.ofWord words[(2 * i).toNat]!) words[(2 * i + 1).toNat]!

theorem calcRun_implements : Implements calculator.module 7 calcRun := by
  refine Func.implements calculator.funcs 5 calculator.calcRun.ir "calcRun" rfl calcRun
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro words heap initial _ - ⟨pw, rfl, hWords⟩
  change heap.Borrowed initial pw words at hWords
  have hW := hWords.values
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  let start : State := { params := [.i64 pw], locals := List.replicate 9 (.i64 0) }
  have hParams : start.params.length = 1 := rfl
  have hLocals : start.locals.length = 9 := rfl
  have hGet0 : start.get 0 = some (.i64 pw) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat words.size))
  let s4 := ((s1.update 2 (.i64 0)).update 3 (.i64 0)).update 4 (.i64 0)
  show Triple _ (.seq (.arraySize 1 0) (.seq (.assign 2 (.const 0)) (.seq (.assign 3 (.const 0))
    (.seq (.assign 4 (.const 0)) (.loop 5 6 (.bin .divU (.get 1) (.const 2))
      (.seq (.call 3 [⟨.u64, .read 0 (.bin .mul (.const 2) (.get 6))⟩] [7])
        (.call 5 [⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩, ⟨.u64, .get 7⟩,
          ⟨.u64, .read 0 (.bin .add (.bin .mul (.const 2) (.get 6)) (.const 1))⟩] [2, 3, 4]))))))) 8
    (fun store state => store = initial ∧ state = start) _
  have hLength := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s1.update 2 (.i64 0)) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := (s1.update 2 (.i64 0)).update 3 (.i64 0)) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hW.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s4]
  have hS4Len : s4.params.length + s4.locals.length = 10 := by
    simp [s4, s1, hParams, hLocals]
  have hCount : ∃ next, (Expr.bin .divU (.get 1) (.const 2)).eval initial.mem 8 s4 =
      some (UInt64.ofNat words.size / 2, next) := by
    have g1 : s4.get 1 = some (.i64 (UInt64.ofNat words.size)) := by
      simp [s4, s1, State.get_update_ne, hParams, hLocals]
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := s4) (index := 8)
      (.i64 (UInt64.ofNat words.size)) (by omega)
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := m1) (index := 9) (.i64 2) (by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1; subst hm1
      rw [hLenU]; omega)
    exact ⟨m2, by simp [Expr.eval, g1, hm1, hm2, U64Op.apply]⟩
  refine (Stmt.loop_spec (vars := [2, 3, 4]) (writes := [2, 3, 4, 7])
    (init := ({ value := 0, steps := 0, last := .add } : Calc))
    (n := UInt64.ofNat words.size / 2) (calcStep words)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hS4Len]; decide) hCount
    (by simp [State.Holds, Scalar.values, Flat.flat, Op.ctorIdx, s4, s1, State.get_update_ne,
      hParams, hLocals]) ?_).mono (fun _ _ h => h) ?_
  · intro k c state hk hFrame hHolds hIndex hLimit
    have hLen : state.params.length + state.locals.length = 10 := by
      rw [hFrame.params, hFrame.locals]; exact hS4Len
    have h0 : state.get 0 = some (.i64 pw) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s4, s1, hGet0])
    obtain ⟨g2, g3, g4⟩ : state.get 2 = some (.i64 c.value) ∧ state.get 3 = some (.i64 c.steps) ∧
        state.get 4 = some (.i64 c.last.ctorIdx.toUInt64) := by
      simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := state) (index := 8)
      (.i64 (2 * UInt64.ofNat k)) (by omega)
    have hm1' := hm1
    rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1'
    subst hm1'
    let w := words[(2 * UInt64.ofNat k).toNat]!
    let x := words[(2 * UInt64.ofNat k + 1).toNat]!
    let next1 := (state.update 8 (.i64 (2 * UInt64.ofNat k))).update 7
      (.i64 (Op.ofWord w).ctorIdx.toUInt64)
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := next1) (index := 8)
      (.i64 (2 * UInt64.ofNat k + 1)) (by simp only [next1, hLenU]; omega)
    have hm2' := hm2
    rw [State.set?_eq_update _ (by simp only [next1, hLenU]; omega), Option.some.injEq] at hm2'
    subst hm2'
    let r := stepTuple (c, Op.ofWord w, x)
    let final := (((next1.update 8 (.i64 (2 * UInt64.ofNat k + 1))).update 4
      (.i64 r.last.ctorIdx.toUInt64)).update 3 (.i64 r.steps)).update 2 (.i64 r.value)
    refine Stmt.seq_spec (Stmt.callPure_spec ofWord_pure rfl rfl rfl (x := w) (next := next1)
      (Expr.evalResults_cons (Expr.read_spec hW (by simp [Expr.eval, hIndex, U64Op.apply]) hm1
        (by rw [State.get_update_ne (by decide), h0])) Expr.evalResults_nil)
      (by simp [State.setAll, State.set?_eq_update, hLen, next1, Scalar.values,
        Flat.flat])) ?_
    refine (Stmt.callPure_spec step_pure rfl rfl rfl (x := (c, Op.ofWord w, x)) (next := final)
      (Expr.evalResults_get (by simp [next1, State.get_update_ne, g2, Flat.flat]) <|
        Expr.evalResults_get (by simp [next1, State.get_update_ne, g3, Flat.flat]) <|
        Expr.evalResults_get (by simp [next1, State.get_update_ne, g4, Flat.flat]) <|
        Expr.evalResults_get (by simp [next1, State.get_update_same, hLen, Flat.flat]) <|
        Expr.evalResults_cons (Expr.read_spec hW
          (by simp [Expr.eval, next1, State.get_update_ne, hIndex, U64Op.apply]) hm2
          (by simp [next1, State.get_update_ne, h0])) Expr.evalResults_nil)
      (by simp [State.setAll, State.set?_eq_update, hLen, final, next1, Scalar.values,
        Flat.flat, r])).mono (fun _ _ h => h) ?_
    rintro s st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · show final.Holds [2, 3, 4] (Scalar.values r)
      simp [State.Holds, Scalar.values, Flat.flat, final, next1, State.get_update_ne,
        State.get_update_same, hLen]
  rintro s st ⟨rfl, -, hHolds⟩
  change st.Holds [2, 3, 4] (Scalar.values (calcRun words)) at hHolds
  obtain ⟨g2, g3, g4⟩ : st.get 2 = some (.i64 (calcRun words).value) ∧
      st.get 3 = some (.i64 (calcRun words).steps) ∧
      st.get 4 = some (.i64 (calcRun words).last.ctorIdx.toUInt64) := by
    simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
  exact ⟨rfl, Scalar.values (calcRun words), st, by simp [calculator.calcRun.ir, Func.scratch,
    Expr.evalResults, Expr.eval, g2, g3, g4, Scalar.values, Flat.flat], rfl⟩

/-- `encode` succeeds on `calculator.module`, and its bytes decode to a module whose exports
compute the calculator's functions exactly. -/
theorem calculator_bytes : ∃ bytes, Wasm.Encoding.encode calculator.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 applyTuple ∧ Implements m 3 Op.ofWord ∧ Implements m 4 Op.inverse ∧
      Implements m 5 stepTuple ∧ Implements m 6 undoTuple ∧ Implements m 7 calcRun := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip calculator.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, calculator.module, decoded, apply_pure.implements,
    ofWord_pure.implements, inverse_pure.implements, step_pure.implements, undo_pure.implements,
    calcRun_implements⟩

end Examples.Calc
