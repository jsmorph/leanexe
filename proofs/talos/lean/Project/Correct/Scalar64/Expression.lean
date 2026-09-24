import Project.ProofKit.ScalarTransition
import Project.TalosCompat

/-! Typed lowering reuses ScalarTransition semantics and scratch invariants.
The proof is structural in the expression and covers every constructor. Explicit
control result types are retained for exact equality with decoded WASM. -/

namespace Project.ProofKit.ScalarTransition
open Wasm

def Expr.lower : {type : ScalarType} → Expr type → Nat → Program
    | .u64, .get index, _ => [.localGet index]
    | .u64, .const value, _ => [.constI64 value]
    | .bool, .bconst value, _ => [.const (if value then 1 else 0)]
    | .u64, .bin op left right, scratch =>
        if op = .divU ∨ op = .remU then
          let childScratch := scratch + 2
          let zeroValue := if op = .divU then [.constI64 0] else [.localGet scratch]
          left.lower childScratch ++ [.localSet scratch] ++
            right.lower childScratch ++ [.localSet (scratch + 1)] ++
            [.localGet (scratch + 1), .constI64 0, .eqI64,
              .iff 0 1 zeroValue
                [.localGet scratch, .localGet (scratch + 1), op.instruction] [] [.i64]]
        else
          left.lower scratch ++ right.lower scratch ++ [op.instruction]
    | .bool, .eq left right, scratch =>
        left.lower scratch ++ right.lower scratch ++ [.eqI64]
    | .bool, .ne left right, scratch =>
        left.lower scratch ++ right.lower scratch ++ [.neI64]
    | .bool, .ltU left right, scratch =>
        left.lower scratch ++ right.lower scratch ++ [.ltUI64]
    | .bool, .leU left right, scratch =>
        left.lower scratch ++ right.lower scratch ++ [.leUI64]
    | .bool, .not condition, scratch => condition.lower scratch ++ [.eqz]
    | .bool, .and left right, scratch =>
        left.lower scratch ++ [.iff 0 1 (right.lower scratch) [.const 0] [] [.i32]]
    | .bool, .or left right, scratch =>
        left.lower scratch ++ [.iff 0 1 [.const 1] (right.lower scratch) [] [.i32]]
    | .u64, .ite condition thenValue elseValue, scratch =>
        condition.lower scratch ++
          [.iff 0 1 (thenValue.lower scratch) (elseValue.lower scratch) [] [.i64]]


set_option maxHeartbeats 1000000 in
theorem Expr.lower_spec
    {type : ScalarType} (expression : Expr type) (scratch : Nat)
    (state next : State) (result : type.denote) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α)
    (rest : Program) (Q : Assertion α)
    (hEval : expression.eval scratch state = some (result, next))
    (hNext : wp module_ rest Q store
      (next.toLocals (type.value result :: values)) env) :
    wp module_ (expression.lower scratch ++ rest) Q store
      (state.toLocals values) env := by
  induction expression generalizing scratch state next values rest Q with
  | get index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          case i64 value =>
            obtain ⟨rfl, rfl⟩ := hEval
            simp only [Expr.lower, List.cons_append, List.nil_append,
              Wasm.wp_localGet_cons, State.toLocals_get, hGet]
            exact hNext
  | const value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      simp only [Expr.lower, List.cons_append, List.nil_append,
        Wasm.wp_constI64_cons]
      exact hNext
  | bconst value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      cases value <;>
        simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
  | bin op left right leftSpec rightSpec =>
      cases op with
      | add =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.lower, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
      | sub =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.lower, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
      | mul =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.lower, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
      | divU =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.lower, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hSetLeft, hRight] at hEval
          rcases hSetRight : afterRight.set? (scratch + 1) (.i64 rightValue) with _ | savedRight
          · simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch + 2) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          simp only [ScalarType.value]
          apply localSet_spec hSetLeft
          apply rightSpec (scratch := scratch + 2) (state := savedLeft)
            (next := afterRight) (result := rightValue) (values := values)
            (rest := _) (Q := _) hRight
          simp only [ScalarType.value]
          apply localSet_spec hSetRight
          have hRightSlot : savedRight.get (scratch + 1) = some (.i64 rightValue) :=
            State.get_set?_same hSetRight
          have hLeftSlot : savedRight.get scratch = some (.i64 leftValue) := by
            calc
              savedRight.get scratch = afterRight.get scratch :=
                State.get_set?_ne (by omega) hSetRight
              _ = savedLeft.get scratch :=
                Expr.eval_preserves_below right (scratch + 2) savedLeft
                  afterRight rightValue scratch hRight (by omega)
              _ = some (.i64 leftValue) := State.get_set?_same hSetLeft
          simp only [Wasm.wp_localGet_cons, State.toLocals_get, hRightSlot,
            Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
          simp only [Wasm.wp_iff_control_types]
          refine Wasm.wp_iff_cons rfl ?_
          by_cases hZero : rightValue = 0
          · rw [ite_eq_left (by simp [hZero])]
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
          · rw [ite_eq_right (by simp [hZero])]
            apply localGet_spec hLeftSlot
            apply localGet_spec hRightSlot
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
      | remU =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.lower, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval (scratch + 2) state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hSetLeft : afterLeft.set? scratch (.i64 leftValue) with _ | savedLeft
          · simp [hLeft, hSetLeft] at hEval
          rcases hRight : right.eval (scratch + 2) savedLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hSetLeft, hRight] at hEval
          rcases hSetRight : afterRight.set? (scratch + 1) (.i64 rightValue) with _ | savedRight
          · simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          simp [hLeft, hSetLeft, hRight, hSetRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch + 2) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          simp only [ScalarType.value]
          apply localSet_spec hSetLeft
          apply rightSpec (scratch := scratch + 2) (state := savedLeft)
            (next := afterRight) (result := rightValue) (values := values)
            (rest := _) (Q := _) hRight
          simp only [ScalarType.value]
          apply localSet_spec hSetRight
          have hRightSlot : savedRight.get (scratch + 1) = some (.i64 rightValue) :=
            State.get_set?_same hSetRight
          have hLeftSlot : savedRight.get scratch = some (.i64 leftValue) := by
            calc
              savedRight.get scratch = afterRight.get scratch :=
                State.get_set?_ne (by omega) hSetRight
              _ = savedLeft.get scratch :=
                Expr.eval_preserves_below right (scratch + 2) savedLeft
                  afterRight rightValue scratch hRight (by omega)
              _ = some (.i64 leftValue) := State.get_set?_same hSetLeft
          simp only [Wasm.wp_localGet_cons, State.toLocals_get, hRightSlot,
            Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
          simp only [Wasm.wp_iff_control_types]
          refine Wasm.wp_iff_cons rfl ?_
          by_cases hZero : rightValue = 0
          · rw [ite_eq_left (by simp [hZero])]
            apply localGet_spec hLeftSlot
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
          · rw [ite_eq_right (by simp [hZero])]
            apply localGet_spec hLeftSlot
            apply localGet_spec hRightSlot
            simpa [wp_simp, State.toLocals, ScalarType.value, hZero] using hNext
      | bitAnd | bitOr | bitXor | shiftLeft | shiftRight =>
          simp only [Expr.eval, U64Op.apply] at hEval
          simp [Expr.lower, U64Op.instruction, List.append_assoc]
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply leftSpec (scratch := scratch) (state := state)
            (next := afterLeft) (result := leftValue) (values := values)
            (rest := _) (Q := _) hLeft
          apply rightSpec (scratch := scratch) (state := afterLeft)
            (next := afterRight) (result := rightValue)
            (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
          simpa [wp_simp] using hNext
  | eq left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
  | ne left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
  | ltU left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
  | leU left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      apply leftSpec (scratch := scratch) (state := state)
        (next := afterLeft) (result := leftValue) (values := values)
        (rest := _) (Q := _) hLeft
      apply rightSpec (scratch := scratch) (state := afterLeft)
        (next := afterRight) (result := rightValue)
        (values := .i64 leftValue :: values) (rest := _) (Q := _) hRight
      simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
  | not condition conditionSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hCondition : condition.eval scratch state with _ | ⟨value, afterCondition⟩
      · simp [hCondition] at hEval
      cases value with
      | false =>
          simp [hCondition] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply conditionSpec (scratch := scratch) (state := state)
            (next := afterCondition) (result := false) (values := values)
            (rest := _) (Q := _) hCondition
          simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
      | true =>
          simp [hCondition] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          apply conditionSpec (scratch := scratch) (state := state)
            (next := afterCondition) (result := true) (values := values)
            (rest := _) (Q := _) hCondition
          simpa [Expr.lower, ScalarType.value, wp_simp] using hNext
  | and left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := false) (values := values)
          (rest := _) (Q := _) hLeft
        simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [ite_eq_right (by simp)]
        simpa [wp_simp, ScalarType.value] using hNext
      · rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := true) (values := values)
          (rest := _) (Q := _) hLeft
        simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [ite_eq_left (by simp)]
        rw [← List.append_nil (right.lower scratch)]
        apply rightSpec (scratch := scratch) (state := afterLeft)
          (next := afterRight) (result := rightValue) (values := values)
          (rest := []) (Q := _) hRight
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
  | or left right leftSpec rightSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      · rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
        · simp [hLeft, hRight] at hEval
        simp [hLeft, hRight] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := false) (values := values)
          (rest := _) (Q := _) hLeft
        simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [ite_eq_right (by simp)]
        rw [← List.append_nil (right.lower scratch)]
        apply rightSpec (scratch := scratch) (state := afterLeft)
          (next := afterRight) (result := rightValue) (values := values)
          (rest := []) (Q := _) hRight
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · simp [hLeft] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply leftSpec (scratch := scratch) (state := state)
          (next := afterLeft) (result := true) (values := values)
          (rest := _) (Q := _) hLeft
        simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [ite_eq_left (by simp)]
        simpa [wp_simp, ScalarType.value] using hNext
  | ite condition thenValue elseValue conditionSpec thenSpec elseSpec =>
      simp only [Expr.eval] at hEval
      simp only [Expr.lower, List.append_assoc]
      rcases hCondition : condition.eval scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := false) (values := values)
          (rest := _) (Q := _) hCondition
        simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [ite_eq_right (by simp)]
        rw [← List.append_nil (elseValue.lower scratch)]
        apply elseSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hElse
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext
      · rcases hThen : thenValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        apply conditionSpec (scratch := scratch) (state := state)
          (next := afterCondition) (result := true) (values := values)
          (rest := _) (Q := _) hCondition
        simp only [List.cons_append, List.nil_append, Wasm.wp_iff_control_types]
        refine Wasm.wp_iff_cons rfl ?_
        rw [ite_eq_left (by simp)]
        rw [← List.append_nil (thenValue.lower scratch)]
        apply thenSpec (scratch := scratch) (state := afterCondition)
          (next := afterValue) (result := value) (values := values)
          (rest := []) (Q := _) hThen
        simpa [wp_simp, State.toLocals, ScalarType.value] using hNext


end Project.ProofKit.ScalarTransition
