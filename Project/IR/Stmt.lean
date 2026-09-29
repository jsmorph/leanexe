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
  /-- Local `index` receives the 64-bit word at `address`, wrapped to 32 bits. -/
  | load (index : Nat) (address : Expr .u64)
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
  | .load index address, scratch =>
      address.program scratch ++ [.wrapI64, .load64 0, .localSet index]

def Stmt.scratchWidth : Stmt → Nat
  | .skip => 0
  | .assign _ value => value.scratchWidth
  | .seq first second => max first.scratchWidth second.scratchWidth
  | .ite condition thenStmt elseStmt =>
      max condition.scratchWidth (max thenStmt.scratchWidth elseStmt.scratchWidth)
  | .while condition body => max condition.scratchWidth body.scratchWidth
  | .load _ address => address.scratchWidth

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

/-- A specification for every start in `P` separately gives one for `P`. -/
theorem Triple.of_forall {s : Stmt} {scratch : Nat} {P R : Store Unit → State → Prop}
    (h : ∀ store₀ state₀, P store₀ state₀ →
      Triple s scratch (fun store state => store = store₀ ∧ state = state₀) R) :
    Triple s scratch P R :=
  fun m env store state values rest Q hPre hPost =>
    h store state hPre m env store state values rest Q ⟨rfl, rfl⟩ hPost

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

/-- `after` has as many parameters and locals as `before` and agrees with it at
every local below `scratch` outside `writes`. -/
structure State.Frame (scratch : Nat) (writes : List Nat) (before after : State) : Prop where
  params : after.params.length = before.params.length
  locals : after.locals.length = before.locals.length
  get : ∀ index, index < scratch → index ∉ writes → after.get index = before.get index

theorem State.Frame.refl (scratch : Nat) (writes : List Nat) (state : State) :
    State.Frame scratch writes state state :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem State.Frame.trans {scratch : Nat} {writes : List Nat} {a b c : State}
    (hFirst : State.Frame scratch writes a b) (hSecond : State.Frame scratch writes b c) :
    State.Frame scratch writes a c :=
  ⟨hSecond.params.trans hFirst.params, hSecond.locals.trans hFirst.locals,
    fun index hIndex hWrite => (hSecond.get index hIndex hWrite).trans (hFirst.get index hIndex hWrite)⟩

theorem State.Frame.mono {scratch scratch' : Nat} {writes : List Nat} {before after : State}
    (h : State.Frame scratch writes before after) (hScratch : scratch' ≤ scratch) :
    State.Frame scratch' writes before after :=
  ⟨h.params, h.locals, fun index hIndex hWrite => h.get index (by omega) hWrite⟩

theorem State.exists_set? {state : State} {index : Nat} (value : Value)
    (hIndex : index < state.params.length + state.locals.length) :
    ∃ next, state.set? index value = some next := by
  unfold State.set?
  split <;> simp

theorem State.Frame.set? {scratch index : Nat} {writes : List Nat} {before state next : State}
    {value : Value} (hFrame : State.Frame scratch writes before state)
    (hSet : state.set? index value = some next) (hIndex : index ∈ writes ∨ scratch ≤ index) :
    State.Frame scratch writes before next := by
  have hLengths : next.params.length = state.params.length ∧
      next.locals.length = state.locals.length := by
    unfold State.set? at hSet
    split at hSet
    · cases hSet; simp
    · split at hSet
      · cases hSet; simp
      · contradiction
  refine ⟨hLengths.1.trans hFrame.params, hLengths.2.trans hFrame.locals,
    fun j hj hWrite => ?_⟩
  have hNe : j ≠ index := by
    rintro rfl
    rcases hIndex with hIndex | hIndex
    · exact hWrite hIndex
    · omega
  rw [State.get_set?_ne hNe hSet]
  exact hFrame.get j hj hWrite

/-- Evaluating an expression changes only scratch locals. -/
theorem Expr.eval_frame (writes : List Nat) {type : ScalarType} (expression : Expr type)
    (scratch : Nat) (state next : State) (result : type.denote)
    (hEval : expression.eval scratch state = some (result, next)) :
    State.Frame scratch writes state next := by
  induction expression generalizing scratch state next with
  | get index =>
      unfold Expr.eval at hEval
      cases hGet : state.get index with
      | none => simp [hGet] at hEval
      | some value =>
          cases value <;> simp [hGet] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact .refl _ _ _
  | const value | bconst value =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hEval
      exact .refl _ _ _
  | bin op left right hLeftFrame hRightFrame =>
      cases op with
      | add | sub | mul | bitAnd | bitOr | bitXor | shiftLeft | shiftRight =>
          simp only [Expr.eval] at hEval
          rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
          · simp [hLeft] at hEval
          rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
          · simp [hLeft, hRight] at hEval
          simp [hLeft, hRight] at hEval
          obtain ⟨rfl, rfl⟩ := hEval
          exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight)
      | divU | remU =>
          simp only [Expr.eval] at hEval
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
          exact ((((hLeftFrame _ _ _ _ hLeft).mono (by omega)).set? hSetLeft
            (Or.inr (by omega))).trans ((hRightFrame _ _ _ _ hRight).mono (by omega))).set?
              hSetRight (Or.inr (by omega))
  | eq left right hLeftFrame hRightFrame
  | ne left right hLeftFrame hRightFrame
  | ltU left right hLeftFrame hRightFrame
  | leU left right hLeftFrame hRightFrame =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
      · simp [hLeft, hRight] at hEval
      simp [hLeft, hRight] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight)
  | not condition hConditionFrame =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval scratch state with _ | ⟨value, afterCondition⟩
      · simp [hCondition] at hEval
      simp [hCondition] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hConditionFrame _ _ _ _ hCondition
  | and left right hLeftFrame hRightFrame | or left right hLeftFrame hRightFrame =>
      simp only [Expr.eval] at hEval
      rcases hLeft : left.eval scratch state with _ | ⟨leftValue, afterLeft⟩
      · simp [hLeft] at hEval
      cases leftValue
      all_goals
        first
        | (simp [hLeft] at hEval
           obtain ⟨rfl, rfl⟩ := hEval
           exact hLeftFrame _ _ _ _ hLeft)
        | (rcases hRight : right.eval scratch afterLeft with _ | ⟨rightValue, afterRight⟩
           · simp [hLeft, hRight] at hEval
           simp [hLeft, hRight] at hEval
           obtain ⟨rfl, rfl⟩ := hEval
           exact (hLeftFrame _ _ _ _ hLeft).trans (hRightFrame _ _ _ _ hRight))
  | ite condition thenValue elseValue hConditionFrame hThenFrame hElseFrame =>
      simp only [Expr.eval] at hEval
      rcases hCondition : condition.eval scratch state with _ | ⟨conditionValue, afterCondition⟩
      · simp [hCondition] at hEval
      cases conditionValue
      · rcases hElse : elseValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hElse] at hEval
        simp [hCondition, hElse] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (hConditionFrame _ _ _ _ hCondition).trans (hElseFrame _ _ _ _ hElse)
      · rcases hThen : thenValue.eval scratch afterCondition with _ | ⟨value, afterValue⟩
        · simp [hCondition, hThen] at hEval
        simp [hCondition, hThen] at hEval
        obtain ⟨rfl, rfl⟩ := hEval
        exact (hConditionFrame _ _ _ _ hCondition).trans (hThenFrame _ _ _ _ hThen)

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

/-- A load reads the word at the address's low 32 bits, which must lie inside
memory. -/
theorem Stmt.load_spec {index scratch : Nat} {address : Expr .u64}
    {R : Store Unit → State → Prop} :
    Triple (.load index address) scratch
      (fun store state => ∃ word afterAddress next,
        address.eval scratch state = some (word, afterAddress) ∧
        word.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 ∧
        afterAddress.set? index (.i64 (store.mem.read64 word.toUInt32)) = some next ∧
        R store next) R := by
  intro m env store state values rest Q hPre hPost
  obtain ⟨word, afterAddress, next, hAddress, hBounds, hSet, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.cons_append, List.nil_append]
  apply Expr.program_spec address scratch state afterAddress word values m env store
    (.wrapI64 :: .load64 0 :: .localSet index :: rest) Q hAddress
  simp only [Wasm.wp_wrapI64_cons, Wasm.wp_load64_cons, State.toLocals, ScalarType.value,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (by omega)]
  simpa using localSet_spec (values := values) (rest := rest) (Q := Q) (module_ := m) (env := env)
    (store := store) hSet (hPost store next hNext)

end Project.IR
