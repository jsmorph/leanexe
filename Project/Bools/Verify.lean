import Project.Bools.Module
import Project.IR.Correct
import Project.IR.Run
import Project.IR.Loop
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

/-! The compiled `Bool` functions compute their Lean definitions.  A `Bool` is the word of its
constructor index (`Flat Bool UInt64`), so each theorem states that the result word is 1 exactly
when the Lean function returns `true`. -/

namespace Project.Bools

open Project.Pipeline Project.IR Project.ProofKit LeanExe.Examples.Bools

def bothTuple : Bool × Bool → Bool := fun (a, b) => both a b
def eitherTuple : Bool × Bool → Bool := fun (a, b) => either a b
def sameTuple : UInt64 × UInt64 → Bool := fun (x, y) => same x y
def differTuple : UInt64 × UInt64 → Bool := fun (x, y) => differ x y
def agreeTuple : Bool × Bool → Bool := fun (a, b) => agree a b
def floatSameTuple : Float × Float → Bool := fun (x, y) => floatSame x y
def inRangeTuple : Float × Float × Float → Bool := fun (lo, hi, x) => inRange lo hi x
def pickTuple : Bool × UInt64 × UInt64 → UInt64 := fun (a, x, y) => pick a x y
def anyEqualTuple : UInt64 × UInt64 → Bool := fun (n, k) => anyEqual n k

instance : Flat Flagged (Bool × UInt64) := ⟨fun f => (f.flag, f.value)⟩

/-- The goal of a compiled function whose body is `skip`, reduced to its results. -/
macro "skip_body" : tactic =>
  `(tactic| (show Triple _ .skip _ _ _
             refine Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, ?_⟩) fun _ _ h => h
             subst hState))

/-- The lemmas that evaluate a compiled function's results. -/
macro "results" : tactic =>
  `(tactic| simp [Func.scratch, Func.state, Func.locals, Func.width, Expr.evalResults, Expr.eval,
      Expr.scratchWidth, Stmt.scratchWidth, State.get, U64Op.apply, Scalar.values, Flat.flat,
      ScalarType.value])

theorem isPositive_implements : Implements bools.module 2 isPositive :=
  (Func.implementsPure bools.funcs 0 bools.isPositive.ir "isPositive" rfl isPositive
    (fun _ => rfl) fun x initial => by
      skip_body
      simp [bools.isPositive.ir, isPositive]
      results).implements

theorem both_implements : Implements bools.module 3 bothTuple :=
  (Func.implementsPure bools.funcs 1 bools.both.ir "both" rfl bothTuple (fun _ => rfl)
    fun ⟨a, b⟩ initial => by
      skip_body
      cases a <;> cases b <;> simp [bools.both.ir, bothTuple, both] <;> results).implements

theorem either_implements : Implements bools.module 4 eitherTuple :=
  (Func.implementsPure bools.funcs 2 bools.either.ir "either" rfl eitherTuple (fun _ => rfl)
    fun ⟨a, b⟩ initial => by
      skip_body
      cases a <;> cases b <;> simp [bools.either.ir, eitherTuple, either] <;> results).implements

theorem negate_implements : Implements bools.module 5 negate :=
  (Func.implementsPure bools.funcs 3 bools.negate.ir "negate" rfl negate (fun _ => rfl)
    fun a initial => by
      skip_body
      cases a <;> simp [bools.negate.ir, negate] <;> results).implements

theorem same_implements : Implements bools.module 6 sameTuple :=
  (Func.implementsPure bools.funcs 4 bools.same.ir "same" rfl sameTuple (fun _ => rfl)
    fun ⟨x, y⟩ initial => by
      skip_body
      simp [bools.same.ir, sameTuple, same]
      results).implements

theorem differ_implements : Implements bools.module 7 differTuple :=
  (Func.implementsPure bools.funcs 5 bools.differ.ir "differ" rfl differTuple (fun _ => rfl)
    fun ⟨x, y⟩ initial => by
      skip_body
      simp [bools.differ.ir, differTuple, differ]
      results).implements

theorem agree_implements : Implements bools.module 8 agreeTuple :=
  (Func.implementsPure bools.funcs 6 bools.agree.ir "agree" rfl agreeTuple (fun _ => rfl)
    fun ⟨a, b⟩ initial => by
      skip_body
      cases a <;> cases b <;> simp [bools.agree.ir, agreeTuple, agree] <;> results).implements

theorem floatSame_implements : Implements bools.module 9 floatSameTuple :=
  (Func.implementsPure bools.funcs 7 bools.floatSame.ir "floatSame" rfl floatSameTuple
    (fun _ => rfl) fun ⟨x, y⟩ initial => by
      skip_body
      simp [bools.floatSame.ir, floatSameTuple, floatSame, F64Bits.beq_eq]
      results).implements

theorem inRange_implements : Implements bools.module 10 inRangeTuple :=
  (Func.implementsPure bools.funcs 8 bools.inRange.ir "inRange" rfl inRangeTuple
    (fun _ => rfl) fun ⟨lo, hi, x⟩ initial => by
      skip_body
      simp only [bools.inRange.ir, inRangeTuple, inRange, F64Bits.decide_le]
      results
      cases Wasm.IEEE64.le lo.toBits x.toBits <;> cases Wasm.IEEE64.le x.toBits hi.toBits <;>
        simp).implements

theorem pick_implements : Implements bools.module 11 pickTuple :=
  (Func.implementsPure bools.funcs 9 bools.pick.ir "pick" rfl pickTuple (fun _ => rfl)
    fun ⟨a, x, y⟩ initial => by
      skip_body
      cases a <;> simp [bools.pick.ir, pickTuple, pick] <;> results).implements

theorem mark_implements : Implements bools.module 13 mark :=
  (Func.implementsPure bools.funcs 11 bools.mark.ir "mark" rfl mark (fun _ => rfl)
    fun x initial => by
      skip_body
      simp [bools.mark.ir, mark]
      results).implements

theorem flagOf_implements : Implements bools.module 14 flagOf :=
  (Func.implementsPure bools.funcs 12 bools.flagOf.ir "flagOf" rfl flagOf (fun _ => rfl)
    fun ⟨a, v⟩ initial => by
      skip_body
      cases a <;> simp [bools.flagOf.ir, flagOf] <;> results).implements

theorem anyEqual_implements : Implements bools.module 12 anyEqualTuple :=
  (Func.implementsPure bools.funcs 10 bools.anyEqual.ir "anyEqual" rfl anyEqualTuple
    (fun _ => rfl) fun ⟨n, k⟩ initial => by
      let start : State :=
        { params := [.i64 n, .i64 k], locals := [.i64 0, .i64 0, .i64 0, .i64 0] }
      have hParams : start.params.length = 2 := rfl
      have hLocals : start.locals.length = 4 := rfl
      let s1 := start.update 2 (.i64 0)
      show Triple _ (.seq (.assign 2 (.const 0)) (.loop 3 4 (.get 0)
        (.seq (.assign 5 (.bin .bitOr (.get 2) (.ite (.eq (.get 4) (.get 1)) (.const 1)
          (.const 0)))) (.assign 2 (.get 5))))) 6
        (fun store state => store = initial ∧ state = start) _
      refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
      · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1]
      have hS1Len : s1.params.length + s1.locals.length = 6 := by simp [s1, hParams, hLocals]
      have hCount : ∃ next, (Expr.get 0).eval initial.mem 6 s1 = some (n, next) :=
        ⟨s1, by simp [Expr.eval, s1, State.update, State.get, start]⟩
      refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5]) (init := false) (n := n)
        (fun i acc => acc || i == k)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hS1Len]) hCount
        (.cons (by simp [s1, State.get_update_same, hParams, hLocals, Flat.flat])
          .nil) ?_).mono (fun _ _ h => h) ?_
      · intro i acc state hi hFrame hHolds hIndex hLimit
        have hLen : state.params.length + state.locals.length = 6 := by
          rw [hFrame.params, hFrame.locals]; exact hS1Len
        have g1 : state.get 1 = some (.i64 k) :=
          (hFrame.get 1 (by decide) (by decide)).trans (by simp [s1, State.update, State.get, start])
        have g2 : state.get 2 = some (.i64 (if acc then 1 else 0)) := by
          simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
        let v : UInt64 := (if acc then 1 else 0) |||
          (if UInt64.ofNat i = k then 1 else 0)
        let t1 := state.update 5 (.i64 v)
        let t2 := t1.update 2 (.i64 v)
        refine (Stmt.run_spec (final := t2) ?_).mono (fun _ _ h => h) ?_
        · have h5 : 5 < state.params.length + state.locals.length := by omega
          have h2 : 2 < t1.params.length + t1.locals.length := by
            simp [t1, State.update_params_length, State.update_locals_length]; omega
          simp [Stmt.run, Expr.eval, g1, g2, hIndex, State.set?_eq_update _ h5, U64Op.apply, v, t1,
            t2, State.get_update_same h5, State.set?_eq_update _ h2]
        rintro store st ⟨rfl, rfl⟩
        refine ⟨rfl, ?_, ?_⟩
        · exact ((State.Frame.refl _ _ _).update (.inl (by decide))).update (.inl (by decide))
        · refine .cons ?_ .nil
          have h2 : 2 < t1.params.length + t1.locals.length := by
            simp [t1, State.update_params_length, State.update_locals_length]; omega
          simp only [t2, State.get_update_same h2, Flat.flat, v, cond_eq_ite]
          cases acc <;> by_cases h : UInt64.ofNat i = k <;> simp [h]
      · rintro store state ⟨rfl, -, hHolds⟩
        refine ⟨rfl, _, state, ?_, rfl⟩
        have g2 : state.get 2 = some (.i64 (if LeanExe.loop n false (fun i acc => acc || i == k)
            then 1 else 0)) := by
          simpa [State.Holds, Scalar.values, Flat.flat] using hHolds
        simp only [bools.anyEqual.ir, Func.scratch, Expr.evalResults, Expr.eval, g2, Scalar.values,
          Flat.flat, anyEqualTuple, anyEqual, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          ScalarType.value, cond_eq_ite]).implements

/-- `encode` succeeds on `bools.module`, and its bytes decode to a module that computes each
function exactly. -/
theorem bools_bytes : ∃ bytes, Wasm.Encoding.encode bools.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 isPositive ∧
      Implements m 3 bothTuple ∧ Implements m 4 eitherTuple ∧ Implements m 5 negate ∧
      Implements m 6 sameTuple ∧ Implements m 7 differTuple ∧ Implements m 8 agreeTuple ∧
      Implements m 9 floatSameTuple ∧ Implements m 10 inRangeTuple ∧ Implements m 11 pickTuple ∧
      Implements m 12 anyEqualTuple ∧ Implements m 13 mark ∧ Implements m 14 flagOf := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip bools.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, bools.module, decoded, isPositive_implements, both_implements,
    either_implements, negate_implements, same_implements, differ_implements, agree_implements,
    floatSame_implements, inRange_implements, pick_implements, anyEqual_implements,
    mark_implements, flagOf_implements⟩

end Project.Bools
