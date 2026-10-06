import Examples.Shape.Module
import Examples.Shape.Flat
import Project.IR.Correct
import Project.IR.Run
import Project.IR.Call
import Project.IR.Live
import Project.IR.Loop
import Project.IR.Read
import Project.ProofKit.F64Bits
import Project.ProofKit.F64Convert
import Project.Encoding.RoundTrip

/-! The shape module's compiled functions compute their Lean definitions exactly.  The six
functions of words and floats keep the store; `totalArea` reads its array of shapes. -/

namespace Examples.Shape

open Wasm Project.Pipeline Project.IR Project.ProofKit Examples.Shape

theorem zero_toBits : (0 : Float).toBits = 0 := by decide +kernel
theorem zero_toBits' : (0.0 : Float).toBits = 0 := by decide +kernel
theorem three_toBits : (3.0 : Float).toBits = 4613937818241073152 := by decide +kernel

theorem area_pure : ImplementsPure shapes.module 2 Shape.area := by
  refine Func.implementsPure shapes.funcs 0 shapes.area.ir "area" rfl Shape.area (fun _ => rfl)
    fun s initial => ?_
  show Triple _ .skip _ _ _
  refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
  subst hState
  cases s with
  | circle r =>
    refine ⟨_, _, rfl, ?_⟩
    show [Value.f64 (IEEE64.mul (IEEE64.mul 4613937818241073152 r.toBits) r.toBits)] =
      [.f64 (3.0 * r * r : Float).toBits]
    rw [F64Bits.toBits_mul, F64Bits.toBits_mul, three_toBits]
  | rect w h =>
    refine ⟨_, _, rfl, ?_⟩
    show [Value.f64 (IEEE64.convertI64U (w * h))] = [.f64 (w * h).toFloat.toBits]
    rw [F64Convert.toBits_toFloat]
  | point =>
    refine ⟨_, _, rfl, ?_⟩
    show [Value.f64 0] = [.f64 (0.0 : Float).toBits]
    rw [zero_toBits']

theorem width_pure : ImplementsPure shapes.module 5 Shape.width := by
  refine Func.implementsPure shapes.funcs 3 shapes.width.ir "width" rfl Shape.width (fun _ => rfl)
    fun s initial => ?_
  show Triple _ .skip _ _ _
  refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
  subst hState
  cases s <;> simp [shapes.width.ir, Func.scratch, Func.state, Func.locals, Func.width,
    Expr.evalResults, Expr.eval, Expr.scratchWidth, Stmt.scratchWidth, State.get, Scalar.values,
    Flat.flat, Shape.width]

theorem grow_pure : ImplementsPure shapes.module 6 Shape.grow := by
  refine Func.implementsPure shapes.funcs 4 shapes.grow.ir "grow" rfl Shape.grow (fun _ => rfl)
    fun s initial => ?_
  cases s <;>
  · refine (Stmt.run_spec (final := _) rfl).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, _, _, rfl, rfl⟩

/-- `Shape.scale` with its two arguments as one tuple. -/
def scaleTuple (x : Shape × UInt64) : Shape := x.1.scale x.2

theorem scale_pure : ImplementsPure shapes.module 4 scaleTuple := by
  refine Func.implementsPure shapes.funcs 2 shapes.scale.ir "scale" rfl scaleTuple (fun _ => rfl)
    fun ⟨s, f⟩ initial => ?_
  cases s with
  | circle r =>
    refine (Stmt.run_spec (final := _) rfl).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine ⟨rfl, _, _, rfl, ?_⟩
    show [Value.i64 0, .f64 (IEEE64.mul r.toBits (IEEE64.convertI64U f)), .i64 0, .i64 0] =
      [.i64 0, .f64 (r * f.toFloat).toBits, .i64 0, .i64 0]
    rw [F64Bits.toBits_mul, F64Convert.toBits_toFloat]
  | rect w h =>
    refine (Stmt.run_spec (final := _) rfl).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, _, _, rfl, rfl⟩
  | point =>
    refine (Stmt.run_spec (final := _) rfl).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, _, _, rfl, rfl⟩

/-- `Shape.ofWords` with its three arguments as one tuple. -/
def ofWordsTuple (x : UInt64 × UInt64 × UInt64) : Shape := Shape.ofWords x.1 x.2.1 x.2.2

theorem ofWords_pure : ImplementsPure shapes.module 3 ofWordsTuple := by
  refine Func.implementsPure shapes.funcs 1 shapes.ofWords.ir "ofWords" rfl ofWordsTuple
    (fun _ => rfl) fun ⟨k, a, b⟩ initial => ?_
  by_cases h0 : k = 0
  · subst h0
    refine (Stmt.run_spec (final := _) rfl).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine ⟨rfl, _, _, rfl, ?_⟩
    show [Value.i64 0, .f64 (IEEE64.convertI64U a), .i64 0, .i64 0] =
      [.i64 0, .f64 a.toFloat.toBits, .i64 0, .i64 0]
    rw [F64Convert.toBits_toFloat]
  by_cases h1 : k = 1
  · subst h1
    refine (Stmt.run_spec (final := _) rfl).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, _, _, rfl, rfl⟩
  have hOther : ofWordsTuple (k, a, b) = .point := by simp [ofWordsTuple, Shape.ofWords, h0, h1]
  let start : State :=
    { params := [.i64 k, .i64 a, .i64 b], locals := [.i64 0, .f64 0, .i64 0, .i64 0] }
  have hParams : start.params.length = 3 := rfl
  have hLocals : start.locals.length = 4 := rfl
  show Triple _ shapes.ofWords.ir.body 7 (fun store state => store = initial ∧ state = start) _
  refine (Stmt.run_spec (final := (((start.update 3 (.i64 2)).update 4 (.f64 0)).update 5
    (.i64 0)).update 6 (.i64 0)) ?_).mono (fun _ _ h => h) ?_
  · have g0 : start.get 0 = some (.i64 k) := rfl
    simp [shapes.ofWords.ir, Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, g0, h0,
      h1, ScalarType.value]
  rintro _ _ ⟨rfl, rfl⟩
  rw [hOther]
  exact ⟨rfl, _, _, rfl, rfl⟩

/-- `Shape.normalize` with its three arguments as one tuple. -/
def normalizeTuple (x : UInt64 × UInt64 × UInt64) : Shape := Shape.normalize x.1 x.2.1 x.2.2

theorem normalize_pure : ImplementsPure shapes.module 7 normalizeTuple := by
  refine Func.implementsPure shapes.funcs 5 shapes.normalize.ir "normalize" rfl normalizeTuple
    (fun _ => rfl) fun ⟨k, a, b⟩ initial => ?_
  let start : State :=
    { params := [.i64 k, .i64 a, .i64 b],
      locals := [.i64 0, .f64 0, .i64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0] }
  show Triple _ (.seq (.call 3 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [7, 8, 9, 10])
      (.ite (.eq (.get 7) (.const 0))
        (.seq (.assign 3 (.get 7)) (.seq (.assign 4 (.getF 8))
          (.seq (.assign 5 (.get 9)) (.assign 6 (.get 10)))))
        (.ite (.eq (.get 7) (.const 1))
          (.seq (.assign 3 (.get 7)) (.seq (.assign 4 (.getF 8))
            (.seq (.assign 5 (.get 9)) (.assign 6 (.get 10)))))
          (.seq (.assign 3 (.const 1)) (.seq (.assign 4 (.constF 0))
            (.seq (.assign 5 (.const 0)) (.assign 6 (.const 0)))))))) 11
    (fun store state => store = initial ∧ state = start) _
  have hN : normalizeTuple (k, a, b) =
      (match ofWordsTuple (k, a, b) with
        | .point => .rect 0 0
        | other => other) := rfl
  rw [hN]
  generalize hS : ofWordsTuple (k, a, b) = sh
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have hStart : start.params.length + start.locals.length = 11 := rfl
  -- After the call, locals 7 to 10 hold `sh`'s slots; the chain copies them or writes the
  -- empty rectangle into locals 3 to 6.
  have key : ∀ (v0 v2 v3 : UInt64) (v1 : UInt64) (w0 w2 w3 w1 : UInt64),
      let next := (((start.update 10 (.i64 v3)).update 9 (.i64 v2)).update 8 (.f64 v1)).update 7
        (.i64 v0)
      (if v0 = 0 ∨ v0 = 1 then (w0, w1, w2, w3) = (v0, v1, v2, v3)
        else (w0, w1, w2, w3) = (1, 0, 0, 0)) →
      Stmt.run initial.mem 11 (.ite (.eq (.get 7) (.const 0))
        (.seq (.assign 3 (.get 7)) (.seq (.assign 4 (.getF 8))
          (.seq (.assign 5 (.get 9)) (.assign 6 (.get 10)))))
        (.ite (.eq (.get 7) (.const 1))
          (.seq (.assign 3 (.get 7)) (.seq (.assign 4 (.getF 8))
            (.seq (.assign 5 (.get 9)) (.assign 6 (.get 10)))))
          (.seq (.assign 3 (.const 1)) (.seq (.assign 4 (.constF 0))
            (.seq (.assign 5 (.const 0)) (.assign 6 (.const 0))))))) next =
        some ((((next.update 3 (.i64 w0)).update 4 (.f64 w1)).update 5 (.i64 w2)).update 6
          (.i64 w3)) := by
    intro v0 v2 v3 v1 w0 w2 w3 w1 next hW
    have g7 : next.get 7 = some (.i64 v0) :=
      State.get_update_same (by simp only [hLenU, hStart]; decide)
    have g8 : next.get 8 = some (.f64 v1) := by
      simp only [next, State.get_update_ne (show 8 ≠ 7 by decide)]
      exact State.get_update_same (by simp only [hLenU, hStart]; decide)
    have g9 : next.get 9 = some (.i64 v2) := by
      simp only [next, State.get_update_ne (show 9 ≠ 7 by decide),
        State.get_update_ne (show 9 ≠ 8 by decide)]
      exact State.get_update_same (by simp only [hLenU, hStart]; decide)
    have g10 : next.get 10 = some (.i64 v3) := by
      simp only [next, State.get_update_ne (show 10 ≠ 7 by decide),
        State.get_update_ne (show 10 ≠ 8 by decide), State.get_update_ne (show 10 ≠ 9 by decide)]
      exact State.get_update_same (by simp only [hStart]; decide)
    have hNext : next.params.length + next.locals.length = 11 := by simp only [next, hLenU, hStart]
    by_cases h0 : v0 = 0
    · simp only [h0, true_or, ite_true, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
      simp [Stmt.run, Expr.eval, g7, g8, g9, g10, h0, State.set?_eq_update, hNext,
        ScalarType.value]
    by_cases h1 : v0 = 1
    · simp only [h1, or_true, ite_true, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
      simp [Stmt.run, Expr.eval, g7, g8, g9, g10, h1, State.set?_eq_update, hNext,
        ScalarType.value]
    · simp only [h0, h1, or_self, ite_false, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
      simp [Stmt.run, Expr.eval, g7, h0, h1, State.set?_eq_update, hNext, ScalarType.value]
  have post : ∀ (mem : Mem) (next : State) (w0 w1 w2 w3 : UInt64),
      next.params.length + next.locals.length = 11 →
      Expr.evalResults mem 11 shapes.normalize.ir.results
          ((((next.update 3 (.i64 w0)).update 4 (.f64 w1)).update 5 (.i64 w2)).update 6 (.i64 w3)) =
        some ([.i64 w0, .f64 w1, .i64 w2, .i64 w3],
          (((next.update 3 (.i64 w0)).update 4 (.f64 w1)).update 5 (.i64 w2)).update 6 (.i64 w3)) := by
    intro mem next w0 w1 w2 w3 hNext
    simp [shapes.normalize.ir, Expr.evalResults, Expr.eval, State.get_update_ne,
      State.get_update_same, hNext]
  have setAll4 : ∀ (v0 v1 v2 v3 : UInt64),
      start.setAll [10, 9, 8, 7] [.i64 v3, .i64 v2, .f64 v1, .i64 v0] =
        some ((((start.update 10 (.i64 v3)).update 9 (.i64 v2)).update 8 (.f64 v1)).update 7
          (.i64 v0)) := by
    intro v0 v1 v2 v3
    simp [State.setAll, State.set?_eq_update, hStart]
  cases sh with
  | circle r =>
    refine Stmt.seq_spec (Stmt.callPure_spec ofWords_pure rfl rfl rfl (x := (k, a, b)) rfl
      (by rw [hS]; exact setAll4 0 r.toBits 0 0)) ?_
    refine (Stmt.run_spec (key 0 0 0 r.toBits 0 0 0 r.toBits (by simp))).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, _, _, post _ _ _ _ _ _ (by simp [hStart]), rfl⟩
  | rect w h =>
    refine Stmt.seq_spec (Stmt.callPure_spec ofWords_pure rfl rfl rfl (x := (k, a, b)) rfl
      (by rw [hS]; exact setAll4 1 (Float.toBits 0) w h)) ?_
    refine (Stmt.run_spec (key 1 w h (Float.toBits 0) 1 w h (Float.toBits 0) (by simp))).mono
      (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, _, _, post _ _ _ _ _ _ (by simp [hStart]), rfl⟩
  | point =>
    refine Stmt.seq_spec (Stmt.callPure_spec ofWords_pure rfl rfl rfl (x := (k, a, b)) rfl
      (by rw [hS]; exact setAll4 2 (Float.toBits 0) 0 0)) ?_
    refine (Stmt.run_spec (key 2 0 0 (Float.toBits 0) 1 0 0 0 (by simp))).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine ⟨rfl, _, _, post _ _ _ _ _ _ (by simp [hStart]), ?_⟩
    show [Value.i64 1, .f64 0, .i64 0, .i64 0] = [.i64 1, .f64 (Float.toBits 0), .i64 0, .i64 0]
    rw [zero_toBits]

/-- The step of `totalArea`'s loop: the area of shape `i` of `words` added to the total. -/
def areaStep (words : Array UInt64) (i : UInt64) (total : Float) : Float :=
  total + (ofWordsTuple (words[(3 * i).toNat]!, words[(3 * i + 1).toNat]!,
    words[(3 * i + 2).toNat]!)).area

theorem totalArea_implements : Implements shapes.module 8 totalArea := by
  refine Func.implements shapes.funcs 6 shapes.totalArea.ir "totalArea" rfl totalArea
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro words heap initial _ - ⟨pw, rfl, hWords⟩
  change heap.Borrowed initial pw words at hWords
  have hW := hWords.values
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  let start : State :=
    { params := [.i64 pw], locals := [.i64 0, .f64 0, .i64 0, .i64 0, .i64 0, .f64 0, .i64 0,
        .i64 0, .f64 0, .f64 0, .i64 0, .i64 0] }
  have hParams : start.params.length = 1 := rfl
  have hLocals : start.locals.length = 12 := rfl
  have hGet0 : start.get 0 = some (.i64 pw) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat words.size))
  let s2 := s1.update 2 (.f64 (0.0 : Float).toBits)
  show Triple _ (.seq (.arraySize 1 0) (.seq (.assign 2 (.constF 0))
    (.loop 3 4 (.bin .divU (.get 1) (.const 3))
      (.seq (.call 3 [⟨.u64, .read 0 (.bin .mul (.const 3) (.get 4))⟩,
          ⟨.u64, .read 0 (.bin .add (.bin .mul (.const 3) (.get 4)) (.const 1))⟩,
          ⟨.u64, .read 0 (.bin .add (.bin .mul (.const 3) (.get 4)) (.const 2))⟩] [5, 6, 7, 8])
        (.seq (.call 2 [⟨.u64, .get 5⟩, ⟨.f64, .getF 6⟩, ⟨.u64, .get 7⟩, ⟨.u64, .get 8⟩] [9])
          (.seq (.assign 10 (.binF .add (.getF 2) (.getF 9))) (.assign 2 (.getF 10)))))))) 11
    (fun store state => store = initial ∧ state = start) _
  have hLength := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hW.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp only [Stmt.run, Expr.eval, s2, s1, zero_toBits', Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, ScalarType.value]
    exact State.set?_eq_update _ (by simp [hParams, hLocals])
  have hS2Len : s2.params.length + s2.locals.length = 13 := by simp [s2, s1, hParams, hLocals]
  have hCount : ∃ next, (Expr.bin .divU (.get 1) (.const 3)).eval initial.mem 11 s2 =
      some (UInt64.ofNat words.size / 3, next) := by
    have g1 : s2.get 1 = some (.i64 (UInt64.ofNat words.size)) := by
      simp [s2, s1, State.get_update_ne, hParams, hLocals]
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := s2) (index := 11)
      (.i64 (UInt64.ofNat words.size)) (by omega)
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := m1) (index := 12) (.i64 3) (by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1; subst hm1
      rw [hLenU]; omega)
    exact ⟨m2, by simp [Expr.eval, g1, hm1, hm2, U64Op.apply]⟩
  refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5, 6, 7, 8, 9, 10]) (init := (0.0 : Float))
    (n := UInt64.ofNat words.size / 3) (areaStep words)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hS2Len]; decide) hCount
    (.cons (State.get_update_same (by simp [s1, hParams, hLocals])) .nil) ?_).mono
      (fun _ _ h => h) ?_
  · intro k total state hk hFrame hHolds hIndex hLimit
    have hLen : state.params.length + state.locals.length = 13 := by
      rw [hFrame.params, hFrame.locals]; exact hS2Len
    have h0 : state.get 0 = some (.i64 pw) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have g2 : state.get 2 = some (.f64 total.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have setAll4 : ∀ (st : State) (v0 v1 v2 v3 : Value),
        st.params.length + st.locals.length = 13 →
        st.setAll [8, 7, 6, 5] [v3, v2, v1, v0] =
          some ((((st.update 8 v3).update 7 v2).update 6 v1).update 5 v0) := by
      intro st v0 v1 v2 v3 h
      simp [State.setAll, State.set?_eq_update, h]
    let p := 3 * UInt64.ofNat k
    have hm1 : state.set? 11 (.i64 p) = some (state.update 11 (.i64 p)) :=
      State.set?_eq_update _ (by omega)
    have hm2 : (state.update 11 (.i64 p)).set? 11 (.i64 (p + 1)) =
        some ((state.update 11 (.i64 p)).update 11 (.i64 (p + 1))) :=
      State.set?_eq_update _ (by rw [hLenU]; omega)
    have hm3 : ((state.update 11 (.i64 p)).update 11 (.i64 (p + 1))).set? 11 (.i64 (p + 2)) =
        some (((state.update 11 (.i64 p)).update 11 (.i64 (p + 1))).update 11 (.i64 (p + 2))) :=
      State.set?_eq_update _ (by rw [hLenU, hLenU]; omega)
    let m := ((state.update 11 (.i64 p)).update 11 (.i64 (p + 1))).update 11 (.i64 (p + 2))
    have hmLen : m.params.length + m.locals.length = 13 := by simp only [m, hLenU, hLen]
    let a := words[(3 * UInt64.ofNat k).toNat]!
    let b := words[(3 * UInt64.ofNat k + 1).toNat]!
    let c := words[(3 * UInt64.ofNat k + 2).toNat]!
    let sh := ofWordsTuple (a, b, c)
    let v0 : Value := .i64 (Flat.flat sh).1
    let v1 : Value := .f64 (Flat.flat sh).2.1.toBits
    let v2 : Value := .i64 (Flat.flat sh).2.2.1
    let v3 : Value := .i64 (Flat.flat sh).2.2.2
    let n8 := m.update 8 v3
    let n7 := n8.update 7 v2
    let n6 := n7.update 6 v1
    let next1 := n6.update 5 v0
    have l8 : n8.params.length + n8.locals.length = 13 := by simp only [n8, hLenU, hmLen]
    have l7 : n7.params.length + n7.locals.length = 13 := by simp only [n7, hLenU, l8]
    have l6 : n6.params.length + n6.locals.length = 13 := by simp only [n6, hLenU, l7]
    have hN1Len : next1.params.length + next1.locals.length = 13 := by
      simp only [next1, hLenU, l6]
    refine Stmt.seq_spec (Stmt.callPure_spec ofWords_pure rfl rfl rfl (x := (a, b, c))
      (next := next1)
      (Expr.evalResults_cons (Expr.read_spec hW (by simp [Expr.eval, hIndex, U64Op.apply]) hm1
        (by rw [State.get_update_ne (by decide), h0])) <|
        Expr.evalResults_cons (Expr.read_spec hW
          (by simp [Expr.eval, State.get_update_ne, hIndex, U64Op.apply]) hm2
          (by simp [State.get_update_ne, h0])) <|
        Expr.evalResults_cons (Expr.read_spec hW
          (by simp [Expr.eval, State.get_update_ne, hIndex, U64Op.apply]) hm3
          (by simp [State.get_update_ne, h0])) Expr.evalResults_nil)
      (setAll4 m v0 v1 v2 v3 hmLen)) ?_
    have g5 : next1.get 5 = some v0 := State.get_update_same (by rw [l6]; decide)
    have g6 : next1.get 6 = some v1 := by
      rw [State.get_update_ne (by decide)]; exact State.get_update_same (by rw [l7]; decide)
    have g7 : next1.get 7 = some v2 := by
      rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]
      exact State.get_update_same (by rw [l8]; decide)
    have g8 : next1.get 8 = some v3 := by
      rw [State.get_update_ne (by decide), State.get_update_ne (by decide),
        State.get_update_ne (by decide)]
      exact State.get_update_same (by rw [hmLen]; decide)
    let next2 := next1.update 9 (.f64 sh.area.toBits)
    refine Stmt.seq_spec (Stmt.callPure_spec area_pure rfl rfl rfl (x := sh) (next := next2)
      (Expr.evalResults_get g5 <| Expr.evalResults_getF g6 <| Expr.evalResults_get g7 <|
        Expr.evalResults_get g8 Expr.evalResults_nil)
      (by
        show next1.setAll [9] [.f64 sh.area.toBits] = some next2
        simp only [State.setAll, State.set?_eq_update _
          (show 9 < next1.params.length + next1.locals.length by rw [hN1Len]; decide),
          Option.bind_eq_bind, Option.bind_some]
        rfl)) ?_
    have hN2Len : next2.params.length + next2.locals.length = 13 := by
      simp only [next2, hLenU, hN1Len]
    have g2' : next2.get 2 = some (.f64 total.toBits) := by
      simp only [next2, next1, n6, n7, n8, m, State.get_update_ne (show 2 ≠ 9 by decide),
        State.get_update_ne (show 2 ≠ 5 by decide), State.get_update_ne (show 2 ≠ 6 by decide),
        State.get_update_ne (show 2 ≠ 7 by decide), State.get_update_ne (show 2 ≠ 8 by decide),
        State.get_update_ne (show 2 ≠ 11 by decide), g2]
    have g9 : next2.get 9 = some (.f64 sh.area.toBits) :=
      State.get_update_same (by rw [hN1Len]; decide)
    let final := (next2.update 10 (.f64 (areaStep words (UInt64.ofNat k) total).toBits)).update 2
      (.f64 (areaStep words (UInt64.ofNat k) total).toBits)
    refine (Stmt.run_spec (final := final) ?_).mono (fun _ _ h => h) ?_
    · have hAdd : IEEE64.add total.toBits sh.area.toBits =
          (areaStep words (UInt64.ofNat k) total).toBits := by
        rw [areaStep, F64Bits.toBits_add]
      simp only [Stmt.run, Expr.eval, g2', g9, F64Op.apply, hAdd, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def, ScalarType.value]
      rw [State.set?_eq_update _ (by rw [hN2Len]; decide), Option.bind_some]
      have g10 : (next2.update 10 (.f64 (areaStep words (UInt64.ofNat k) total).toBits)).get 10 =
          some (.f64 (areaStep words (UInt64.ofNat k) total).toBits) :=
        State.get_update_same (by rw [hN2Len]; decide)
      simp only [g10, Option.bind_some]
      exact State.set?_eq_update _ (by rw [hLenU, hN2Len]; decide)
    rintro s st ⟨hs, hst⟩
    refine ⟨hs, ?_, ?_⟩
    · rw [hst]
      show State.Frame 11 [2, 5, 6, 7, 8, 9, 10] state final
      repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · rw [hst]
      exact .cons (State.get_update_same (by rw [hLenU, hN2Len]; decide)) .nil
  rintro s st ⟨rfl, -, hHolds⟩
  change st.Holds [2] (Scalar.values (totalArea words)) at hHolds
  have g2 : st.get 2 = some (.f64 (totalArea words).toBits) := by
    simpa [State.Holds, Scalar.values] using hHolds
  exact ⟨rfl, Scalar.values (totalArea words), st, by simp [shapes.totalArea.ir, Func.scratch,
    Expr.evalResults, Expr.eval, g2, Scalar.values], rfl⟩

/-- `encode` succeeds on `shapes.module`, and its bytes decode to a module whose exports
compute the shape functions exactly. -/
theorem shapes_bytes : ∃ bytes, Wasm.Encoding.encode shapes.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      Implements m 2 Shape.area ∧ Implements m 3 ofWordsTuple ∧
      Implements m 4 scaleTuple ∧ Implements m 5 Shape.width ∧
      Implements m 6 Shape.grow ∧ Implements m 7 normalizeTuple ∧ Implements m 8 totalArea := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip shapes.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, shapes.module, decoded, area_pure.implements, ofWords_pure.implements,
    scale_pure.implements, width_pure.implements, grow_pure.implements, normalize_pure.implements,
    totalArea_implements⟩

end Examples.Shape
