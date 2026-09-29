import Project.ProofKit.ScalarTransition

namespace Project.IR

open Wasm
open Project.ProofKit.ScalarTransition (Expr State ScalarType localSet_spec)

/-- IR statements.  `while` is the only loop; its body runs while the condition
holds. -/
inductive Stmt where
  | skip
  | assign (index : Nat) (value : Expr .u64)
  | seq (first second : Stmt)
  | ite (condition : Expr .bool) (thenStmt elseStmt : Stmt)
  | while (condition : Expr .bool) (body : Stmt)
  deriving Repr

def Stmt.program : Stmt → Nat → Program
  | .skip, _ => []
  | .assign index value, scratch => value.program scratch ++ [.localSet index]
  | .seq first second, scratch => first.program scratch ++ second.program scratch
  | .ite condition thenStmt elseStmt, scratch =>
      condition.program scratch ++
        [.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch)]
  | .while condition body, scratch =>
      [.block 0 0 [.loop 0 0
        (condition.program scratch ++ [.eqz, .br_if 1] ++ body.program scratch ++ [.br 0])]]

def Stmt.scratchWidth : Stmt → Nat
  | .skip => 0
  | .assign _ value => value.scratchWidth
  | .seq first second => max first.scratchWidth second.scratchWidth
  | .ite condition thenStmt elseStmt =>
      max condition.scratchWidth (max thenStmt.scratchWidth elseStmt.scratchWidth)
  | .while condition body => max condition.scratchWidth body.scratchWidth

/-- From any store and IR state satisfying `P`, the compiled code of `s` ends
normally in a store and state satisfying `R`.  This is a statement about the
compiled code under Talos's semantics; the IR has no semantics of its own. -/
def Triple (s : Stmt) (scratch : Nat) (P R : Store Unit → State → Prop) : Prop :=
  ∀ (m : Module) (env : HostEnv Unit) (store : Store Unit) (state : State)
    (values : List Value) (rest : Program) (Q : Assertion Unit),
    P store state →
    (∀ store' state', R store' state' → wp m rest Q store' (state'.toLocals values) env) →
    wp m (s.program scratch ++ rest) Q store (state.toLocals values) env

theorem Triple.mono {s : Stmt} {scratch : Nat} {P P' R R' : Store Unit → State → Prop}
    (h : Triple s scratch P R) (hP : ∀ store state, P' store state → P store state)
    (hR : ∀ store state, R store state → R' store state) : Triple s scratch P' R' :=
  fun m env store state values rest Q hPre hPost =>
    h m env store state values rest Q (hP _ _ hPre) fun store' state' hR' =>
      hPost store' state' (hR _ _ hR')

theorem Stmt.skip_spec {scratch : Nat} {R : Store Unit → State → Prop} :
    Triple .skip scratch R R :=
  fun _ _ store state _ _ _ hPre hPost => by
    simpa [Stmt.program] using hPost store state hPre

theorem Stmt.assign_spec {index scratch : Nat} {value : Expr .u64}
    {R : Store Unit → State → Prop} :
    Triple (.assign index value) scratch
      (fun store state => ∃ result afterValue next,
        value.eval scratch state = some (result, afterValue) ∧
        afterValue.set? index (.i64 result) = some next ∧ R store next) R := by
  intro m env store state values rest Q hPre hPost
  obtain ⟨result, afterValue, next, hValue, hSet, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.singleton_append]
  apply Expr.program_spec value scratch state afterValue result values m env store
    (.localSet index :: rest) Q hValue
  exact localSet_spec hSet (hPost store next hNext)

theorem Stmt.seq_spec {first second : Stmt} {scratch : Nat}
    {P M R : Store Unit → State → Prop}
    (hFirst : Triple first scratch P M) (hSecond : Triple second scratch M R) :
    Triple (.seq first second) scratch P R := by
  intro m env store state values rest Q hPre hPost
  simp only [Stmt.program, List.append_assoc]
  exact hFirst m env store state values (second.program scratch ++ rest) Q hPre
    fun store' state' hMid => hSecond m env store' state' values rest Q hMid hPost

theorem Stmt.ite_spec {condition : Expr .bool} {thenStmt elseStmt : Stmt} {scratch : Nat}
    {PThen PElse R : Store Unit → State → Prop}
    (hThen : Triple thenStmt scratch PThen R) (hElse : Triple elseStmt scratch PElse R) :
    Triple (.ite condition thenStmt elseStmt) scratch
      (fun store state => ∃ result afterCondition,
        condition.eval scratch state = some (result, afterCondition) ∧
        if result then PThen store afterCondition else PElse store afterCondition) R := by
  intro m env store state values rest Q hPre hPost
  obtain ⟨result, afterCondition, hCondition, hBranch⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.singleton_append]
  apply Expr.program_spec condition scratch state afterCondition result values m env store
    (.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch) :: rest) Q hCondition
  try simp only [Wasm.wp_iff_control_types]
  refine Wasm.wp_iff_cons rfl ?_
  cases result
  · rw [ite_eq_right (by simp)]
    rw [← List.append_nil (elseStmt.program scratch)]
    apply hElse m env store afterCondition values [] _ (by simpa using hBranch)
    intro store' state' hR
    simpa [wp_simp, State.toLocals] using hPost store' state' hR
  · rw [ite_eq_left (by simp)]
    rw [← List.append_nil (thenStmt.program scratch)]
    apply hThen m env store afterCondition values [] _ (by simpa using hBranch)
    intro store' state' hR
    simpa [wp_simp, State.toLocals] using hPost store' state' hR

set_option maxHeartbeats 1000000 in
/-- A loop ends in a state where the invariant held and the condition evaluated
to false, provided the condition always evaluates under the invariant and every
iteration restores the invariant with a smaller measure. -/
theorem Stmt.while_spec {condition : Expr .bool} {body : Stmt} {scratch : Nat}
    (Inv : Store Unit → State → Prop) (measure : Store Unit → State → Nat)
    (hCondition : ∀ store state, Inv store state →
      ∃ result afterCondition, condition.eval scratch state = some (result, afterCondition))
    (hBody : ∀ n, Triple body scratch
      (fun store state => ∃ before, Inv store before ∧ measure store before = n ∧
        condition.eval scratch before = some (true, state))
      (fun store state => Inv store state ∧ measure store state < n)) :
    Triple (.while condition body) scratch Inv
      (fun store state => ∃ before, Inv store before ∧
        condition.eval scratch before = some (false, state)) := by
  intro m env store state values rest Q hPre hPost
  let loopInv : AssertionF Unit := fun currentStore locals =>
    ∃ current, locals = current.toLocals values ∧ Inv currentStore current
  let loopMeasure : Store Unit → Locals → Nat := fun currentStore locals =>
    measure currentStore (State.ofLocals locals)
  simp only [Stmt.program, List.singleton_append]
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons (Inv := loopInv) (μ := loopMeasure)
  · exact ⟨state, rfl, hPre⟩
  · intro currentStore locals hInv
    rcases hInv with ⟨current, hLocals, hCurrent⟩
    subst locals
    rcases hCondition currentStore current hCurrent with ⟨result, afterCondition, hEval⟩
    simp only [List.append_assoc]
    refine Expr.program_spec (expression := condition) (scratch := scratch)
      (state := current) (next := afterCondition) (result := result)
      (values := values) (module_ := m) (env := env) (store := currentStore)
      (rest := [Instruction.eqz, Instruction.br_if 1] ++
        (body.program scratch ++ [Instruction.br 0]))
      (Q := _) hEval ?_
    cases result
    · simpa [wp_simp, State.toLocals, ScalarType.value] using
        hPost currentStore afterCondition ⟨current, hCurrent, hEval⟩
    · simp only [List.cons_append, List.nil_append, Wasm.wp_eqz_cons,
        Wasm.wp_br_if_cons, ScalarType.value]
      apply hBody (measure currentStore current) m env currentStore afterCondition values
        [.br 0] _ ⟨current, hCurrent, rfl, hEval⟩
      intro store' state' ⟨hInv', hDecrease⟩
      simp only [Wasm.wp_br_cons]
      constructor
      · exact ⟨state', rfl, hInv'⟩
      · simpa [loopMeasure, State.ofLocals, State.toLocals] using hDecrease

end Project.IR
