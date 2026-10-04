import Project.IR.Expr
import Project.ProofKit.CallRemainder
import Project.Pipeline.Aborts

namespace Project.IR

open Wasm

variable {m : Module}

/-- IR statements.  `while` is the only loop; its body runs while the condition
holds. -/
inductive Stmt where
  | skip
  | assign {type : ScalarType} (index : Nat) (value : Expr type)
  | seq (first second : Stmt)
  | ite (condition : Expr .bool) (thenStmt elseStmt : Stmt)
  | while (condition : Expr .bool) (body : Stmt)
  /-- Local `index` receives `type.ofBits` of the 64-bit word at `address`,
  wrapped to 32 bits. -/
  | load (type : ScalarType) (index : Nat) (address : Expr .u64)
  /-- The 64-bit word at `address`, wrapped to 32 bits, receives `value`. -/
  | store (address value : Expr .u64)
  /-- Calls function `func` with the values of `args`, and puts its result in
  local `index` when `result` is `some index`. -/
  | call (func : Nat) (args : List ((type : ScalarType) × Expr type)) (results : List Nat)
  /-- Traps at `unreachable`. -/
  | abort
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
  | .load type index address, scratch =>
      address.program scratch ++ [.wrapI64, .load64 0] ++ type.fromBits ++ [.localSet index]
  | .store address value, scratch =>
      address.program scratch ++ [.wrapI64] ++ value.program scratch ++ [.store64 0]
  | .call func args results, scratch =>
      args.flatMap (·.2.program scratch) ++ [.call func] ++ results.reverse.map .localSet
  | .abort, _ => [.unreachable]

def Stmt.scratchWidth : Stmt → Nat
  | .skip => 0
  | .assign _ value => value.scratchWidth
  | .seq first second => max first.scratchWidth second.scratchWidth
  | .ite condition thenStmt elseStmt =>
      max condition.scratchWidth (max thenStmt.scratchWidth elseStmt.scratchWidth)
  | .while condition body => max condition.scratchWidth body.scratchWidth
  | .load _ _ address => address.scratchWidth
  | .store address value => max address.scratchWidth value.scratchWidth
  | .call _ args _ => (args.map (·.2.scratchWidth)).foldr max 0
  | .abort => 0

/-- From any store and IR state satisfying `P`, the compiled code of `s` ends
normally in a store and state satisfying `R`.  This is a statement about the
compiled code under Talos's semantics; the IR has no semantics of its own. -/
def Triple (m : Module) (s : Stmt) (scratch : Nat) (P R : Store Unit → State → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (state : State)
    (values : List Value) (rest : Program) (Q : Assertion Unit),
    (∀ st, Q (.Trap st "unreachable")) → P store state →
    (∀ store' state', R store' state' → wp m rest Q store' (state'.toLocals values) env) →
    wp m (s.program scratch ++ rest) Q store (state.toLocals values) env

theorem Triple.mono {s : Stmt} {scratch : Nat} {P P' R R' : Store Unit → State → Prop}
    (h : Triple m s scratch P R) (hP : ∀ store state, P' store state → P store state)
    (hR : ∀ store state, R store state → R' store state) : Triple m s scratch P' R' :=
  fun env store state values rest Q hTrap hPre hPost =>
    h env store state values rest Q hTrap (hP _ _ hPre) fun store' state' hR' =>
      hPost store' state' (hR _ _ hR')

/-- A specification for every start in `P` separately gives one for `P`. -/
theorem Triple.of_forall {s : Stmt} {scratch : Nat} {P R : Store Unit → State → Prop}
    (h : ∀ store₀ state₀, P store₀ state₀ →
      Triple m s scratch (fun store state => store = store₀ ∧ state = state₀) R) :
    Triple m s scratch P R :=
  fun env store state values rest Q hTrap hPre hPost =>
    h store state hPre env store state values rest Q hTrap ⟨rfl, rfl⟩ hPost

/-- A specification from an unsatisfiable start. -/
theorem Triple.of_false {s : Stmt} {scratch : Nat} {R : Store Unit → State → Prop} :
    Triple m s scratch (fun _ _ => False) R :=
  fun _ _ _ _ _ _ _ hPre _ => hPre.elim

/-- `abort` traps at `unreachable`, which every assertion of a `Triple` accepts. -/
theorem Stmt.abort_spec {scratch : Nat} {P R : Store Unit → State → Prop} :
    Triple m .abort scratch P R := by
  intro env store state values rest Q hTrap hPre hPost
  simp only [Stmt.program, List.singleton_append, wp_unreachable_cons]
  exact hTrap store

theorem Stmt.skip_spec {scratch : Nat} {R : Store Unit → State → Prop} :
    Triple m .skip scratch R R :=
  fun _ store state _ _ _ _ hPre hPost => by
    simpa [Stmt.program] using hPost store state hPre

theorem Stmt.assign_spec {type : ScalarType} {index scratch : Nat} {value : Expr type}
    {R : Store Unit → State → Prop} :
    Triple m (.assign index value) scratch
      (fun store state => ∃ result afterValue next,
        value.eval store.mem scratch state = some (result, afterValue) ∧
        afterValue.set? index (type.value result) = some next ∧ R store next) R := by
  intro env store state values rest Q hTrap hPre hPost
  obtain ⟨result, afterValue, next, hValue, hSet, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.singleton_append]
  apply Expr.program_spec value scratch state afterValue result values m env store
    (.localSet index :: rest) Q hValue
  exact localSet_spec hSet (hPost store next hNext)

theorem Stmt.seq_spec {first second : Stmt} {scratch : Nat}
    {P M R : Store Unit → State → Prop}
    (hFirst : Triple m first scratch P M) (hSecond : Triple m second scratch M R) :
    Triple m (.seq first second) scratch P R := by
  intro env store state values rest Q hTrap hPre hPost
  simp only [Stmt.program, List.append_assoc]
  exact hFirst env store state values (second.program scratch ++ rest) Q hTrap hPre
    fun store' state' hMid => hSecond env store' state' values rest Q hTrap hMid hPost

theorem Stmt.ite_spec {condition : Expr .bool} {thenStmt elseStmt : Stmt} {scratch : Nat}
    {PThen PElse R : Store Unit → State → Prop}
    (hThen : Triple m thenStmt scratch PThen R) (hElse : Triple m elseStmt scratch PElse R) :
    Triple m (.ite condition thenStmt elseStmt) scratch
      (fun store state => ∃ result afterCondition,
        condition.eval store.mem scratch state = some (result, afterCondition) ∧
        if result then PThen store afterCondition else PElse store afterCondition) R := by
  intro env store state values rest Q hTrap hPre hPost
  obtain ⟨result, afterCondition, hCondition, hBranch⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.singleton_append]
  apply Expr.program_spec condition scratch state afterCondition result values m env store
    (.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch) :: rest) Q hCondition
  try simp only [Wasm.wp_iff_control_types]
  refine Wasm.wp_iff_cons rfl ?_
  cases result
  · rw [ite_eq_right (by simp)]
    rw [← List.append_nil (elseStmt.program scratch)]
    apply hElse env store afterCondition values [] _ ?trap (by simpa using hBranch)
    case trap => exact fun st => hTrap st
    intro store' state' hR
    simpa [wp_simp, State.toLocals] using hPost store' state' hR
  · rw [ite_eq_left (by simp)]
    rw [← List.append_nil (thenStmt.program scratch)]
    apply hThen env store afterCondition values [] _ ?trap (by simpa using hBranch)
    case trap => exact fun st => hTrap st
    intro store' state' hR
    simpa [wp_simp, State.toLocals] using hPost store' state' hR

set_option maxHeartbeats 1000000 in
/-- A loop ends in a state where the invariant held and the condition evaluated
to false, provided the condition always evaluates under the invariant and every
iteration restores the invariant with a smaller measure. -/
theorem Stmt.while_spec {condition : Expr .bool} {body : Stmt} {scratch : Nat}
    (Inv : Store Unit → State → Prop) (measure : Store Unit → State → Nat)
    (hCondition : ∀ store state, Inv store state →
      ∃ result afterCondition, condition.eval store.mem scratch state = some (result, afterCondition))
    (hBody : ∀ n, Triple m body scratch
      (fun store state => ∃ before, Inv store before ∧ measure store before = n ∧
        condition.eval store.mem scratch before = some (true, state))
      (fun store state => Inv store state ∧ measure store state < n)) :
    Triple m (.while condition body) scratch Inv
      (fun store state => ∃ before, Inv store before ∧
        condition.eval store.mem scratch before = some (false, state)) := by
  intro env store state values rest Q hTrap hPre hPost
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
      apply hBody (measure currentStore current) env currentStore afterCondition values
        [.br 0] _ ?trap ⟨current, hCurrent, rfl, hEval⟩
      case trap => exact fun st => hTrap st
      intro store' state' ⟨hInv', hDecrease⟩
      simp only [Wasm.wp_br_cons]
      constructor
      · exact ⟨state', rfl, hInv'⟩
      · simpa [loopMeasure, State.ofLocals, State.toLocals] using hDecrease

/-- A load reads the word at the address's low 32 bits, which must lie inside
memory. -/
theorem Stmt.load_spec {type : ScalarType} {index scratch : Nat} {address : Expr .u64}
    {R : Store Unit → State → Prop} :
    Triple m (.load type index address) scratch
      (fun store state => ∃ word afterAddress next,
        address.eval store.mem scratch state = some (word, afterAddress) ∧
        word.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 ∧
        afterAddress.set? index (type.ofBits (store.mem.read64 word.toUInt32)) = some next ∧
        R store next) R := by
  intro env store state values rest Q hTrap hPre hPost
  obtain ⟨word, afterAddress, next, hAddress, hBounds, hSet, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.cons_append, List.nil_append]
  apply Expr.program_spec address scratch state afterAddress word values m env store
    (.wrapI64 :: .load64 0 :: (type.fromBits ++ .localSet index :: rest)) Q hAddress
  simp only [Wasm.wp_wrapI64_cons, Wasm.wp_load64_cons, State.toLocals, ScalarType.value,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (by omega)]
  cases type <;>
    simpa [ScalarType.fromBits, ofNat_mod_toUInt32] using localSet_spec (values := values)
      (rest := rest) (Q := Q)
      (module_ := m) (env := env) (store := store) hSet (hPost store next hNext)

/-- A store writes the value's word at the address's low 32 bits, which must lie
inside memory. -/
theorem Stmt.store_spec {scratch : Nat} {address value : Expr .u64}
    {R : Store Unit → State → Prop} :
    Triple m (.store address value) scratch
      (fun store state => ∃ word afterAddress result afterValue,
        address.eval store.mem scratch state = some (word, afterAddress) ∧
        value.eval store.mem scratch afterAddress = some (result, afterValue) ∧
        word.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 ∧
        R { store with mem := store.mem.write64 word.toUInt32 result } afterValue) R := by
  intro env store state values rest Q hTrap hPre hPost
  obtain ⟨word, afterAddress, result, afterValue, hAddress, hValue, hBounds, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.cons_append, List.nil_append]
  apply Expr.program_spec address scratch state afterAddress word values m env store _ Q hAddress
  simp only [Wasm.wp_wrapI64_cons, State.toLocals, ScalarType.value, wrap_toUInt32]
  apply Expr.program_spec value scratch afterAddress afterValue result (.i32 word.toUInt32 :: values)
    m env store _ Q hValue
  simp only [Wasm.wp_store64_cons, State.toLocals, ScalarType.value, UInt32.toNat_zero,
    Nat.add_zero, add_zero]
  rw [ite_eq_right (by omega)]
  simpa using hPost _ afterValue hNext

/-- Evaluates typed expressions from left to right. -/
def Expr.evalResults (mem : Mem) (scratch : Nat) :
    List ((type : ScalarType) × Expr type) → State → Option (List Value × State)
  | [], state => some ([], state)
  | ⟨type, e⟩ :: rest, state => do
      let (value, next) ← e.eval mem scratch state
      let (values, final) ← Expr.evalResults mem scratch rest next
      pure (type.value value :: values, final)

theorem Expr.evalResults_length {mem : Mem} {scratch : Nat}
    {results : List ((type : ScalarType) × Expr type)} {state next : State} {values : List Value}
    (h : Expr.evalResults mem scratch results state = some (values, next)) :
    values.length = results.length := by
  induction results generalizing state values with
  | nil => simp [Expr.evalResults] at h; simp [← h.1]
  | cons result rest ih =>
      obtain ⟨type, e⟩ := result
      simp only [Expr.evalResults, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨value, afterValue⟩, -, ⟨values', final⟩, hRest, hPure⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hPure
      obtain ⟨rfl, rfl⟩ := hPure
      simp [ih hRest]

/-- The code of `results` pushes their values, the last on top. -/
theorem Expr.evalResults_program_spec {scratch : Nat}
    {results : List ((type : ScalarType) × Expr type)} {state next : State}
    {values out : List Value} {env : HostEnv Unit} {store : Store Unit} {rest : Program}
    {Q : Assertion Unit}
    (hEval : Expr.evalResults store.mem scratch results state = some (values, next))
    (hNext : wp m rest Q store (next.toLocals (values.reverse ++ out)) env) :
    wp m (results.flatMap (·.2.program scratch) ++ rest) Q store (state.toLocals out) env := by
  induction results generalizing state values out with
  | nil =>
      simp only [Expr.evalResults, Option.some.injEq, Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      simpa using hNext
  | cons result others ih =>
      obtain ⟨type, e⟩ := result
      simp only [Expr.evalResults, Option.bind_eq_bind, Option.bind_eq_some_iff] at hEval
      obtain ⟨⟨value, afterValue⟩, hValue, ⟨values', final⟩, hRest, hPure⟩ := hEval
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hPure
      obtain ⟨rfl, rfl⟩ := hPure
      simp only [List.flatMap_cons, List.append_assoc]
      apply Expr.program_spec e scratch state afterValue value out m env store _ Q hValue
      exact ih (out := type.value value :: out) hRest (by simpa using hNext)

/-- Sets the locals `indices` to `values`, the first index first. -/
def State.setAll : State → List Nat → List Value → Option State
  | state, [], [] => some state
  | state, index :: indices, value :: values => do
      State.setAll (← state.set? index value) indices values
  | _, _, _ => none

/-- `local.set` of the locals `indices`, in order, takes `vs` from the stack. -/
theorem State.setAll_spec {state next : State} {indices : List Nat} {vs values : List Value}
    {env : HostEnv Unit} {store : Store Unit} {rest : Program} {Q : Assertion Unit}
    (hSet : state.setAll indices vs = some next)
    (hNext : wp m rest Q store (next.toLocals values) env) :
    wp m (indices.map .localSet ++ rest) Q store (state.toLocals (vs ++ values)) env := by
  induction indices generalizing state vs with
  | nil =>
      cases vs with
      | nil => simp only [State.setAll, Option.some.injEq] at hSet; subst hSet; simpa using hNext
      | cons _ _ => simp [State.setAll] at hSet
  | cons index indices ih =>
      cases vs with
      | nil => simp [State.setAll] at hSet
      | cons v vs =>
          simp only [State.setAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at hSet
          obtain ⟨middle, hMiddle, hRest⟩ := hSet
          simp only [List.map_cons, List.cons_append]
          exact localSet_spec hMiddle (ih hRest)

/-- A call evaluates its arguments, runs the callee, whose specification
`Post` describes the store and results it ends with, and sets the locals
`results` to the callee's results.  Talos lists the results with the last on
top, and the code sets the locals from the last. -/
theorem Stmt.call_spec {scratch func : Nat} {args : List ((type : ScalarType) × Expr type)}
    {results : List Nat} {f : Wasm.Function} {R : Store Unit → State → Prop}
    (hImport : m.imports[func]? = none)
    (hFunc : m.funcs[func - m.imports.length]? = some f)
    (hParams : args.length = f.numParams) :
    Triple m (.call func args results) scratch
      (fun store state => ∃ vals afterArgs, ∃ Post : Store Unit → List Value → Prop,
        Expr.evalResults store.mem scratch args state = some (vals, afterArgs) ∧
        (∀ env, ReturnsOrAborts env m func store vals.reverse Post) ∧
        ∀ store' out, Post store' out →
          ∃ next, afterArgs.setAll results.reverse out = some next ∧ R store' next)
      R := by
  intro env store state values rest Q hTrap hPre hPost
  obtain ⟨vals, afterArgs, Post, hArgs, hRun, hResult⟩ := hPre
  simp only [Stmt.program, List.append_assoc]
  apply Expr.evalResults_program_spec hArgs
  have hLength : vals.reverse.length = f.numParams := by
    simp [Expr.evalResults_length hArgs, hParams]
  refine wp_call_returnsOrAborts ((hRun env).append_args hImport hFunc hLength values) hTrap ?_
  rintro store' _ ⟨out, rfl, hOut⟩
  obtain ⟨next, hSet, hR⟩ := hResult store' out hOut
  exact State.setAll_spec hSet (hPost store' next hR)

/-- `stmts` in sequence, with the code of each placed after the previous. -/
def seqAll : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqAll rest)

end Project.IR
