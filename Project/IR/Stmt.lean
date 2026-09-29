import Project.IR.Expr
import Project.ProofKit.CallRemainder

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
  | call (func : Nat) (args : List (Expr .u64)) (result : Option Nat)
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
  | .call func args result, scratch =>
      args.flatMap (·.program scratch) ++ [.call func] ++ result.toList.map .localSet

def Stmt.scratchWidth : Stmt → Nat
  | .skip => 0
  | .assign _ value => value.scratchWidth
  | .seq first second => max first.scratchWidth second.scratchWidth
  | .ite condition thenStmt elseStmt =>
      max condition.scratchWidth (max thenStmt.scratchWidth elseStmt.scratchWidth)
  | .while condition body => max condition.scratchWidth body.scratchWidth
  | .load _ _ address => address.scratchWidth
  | .store address value => max address.scratchWidth value.scratchWidth
  | .call _ args _ => (args.map (·.scratchWidth)).foldr max 0

/-- From any store and IR state satisfying `P`, the compiled code of `s` ends
normally in a store and state satisfying `R`.  This is a statement about the
compiled code under Talos's semantics; the IR has no semantics of its own. -/
def Triple (m : Module) (s : Stmt) (scratch : Nat) (P R : Store Unit → State → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (state : State)
    (values : List Value) (rest : Program) (Q : Assertion Unit),
    P store state →
    (∀ store' state', R store' state' → wp m rest Q store' (state'.toLocals values) env) →
    wp m (s.program scratch ++ rest) Q store (state.toLocals values) env

theorem Triple.mono {s : Stmt} {scratch : Nat} {P P' R R' : Store Unit → State → Prop}
    (h : Triple m s scratch P R) (hP : ∀ store state, P' store state → P store state)
    (hR : ∀ store state, R store state → R' store state) : Triple m s scratch P' R' :=
  fun env store state values rest Q hPre hPost =>
    h env store state values rest Q (hP _ _ hPre) fun store' state' hR' =>
      hPost store' state' (hR _ _ hR')

/-- A specification for every start in `P` separately gives one for `P`. -/
theorem Triple.of_forall {s : Stmt} {scratch : Nat} {P R : Store Unit → State → Prop}
    (h : ∀ store₀ state₀, P store₀ state₀ →
      Triple m s scratch (fun store state => store = store₀ ∧ state = state₀) R) :
    Triple m s scratch P R :=
  fun env store state values rest Q hPre hPost =>
    h store state hPre env store state values rest Q ⟨rfl, rfl⟩ hPost

theorem Stmt.skip_spec {scratch : Nat} {R : Store Unit → State → Prop} :
    Triple m .skip scratch R R :=
  fun _ store state _ _ _ hPre hPost => by
    simpa [Stmt.program] using hPost store state hPre

theorem Stmt.assign_spec {type : ScalarType} {index scratch : Nat} {value : Expr type}
    {R : Store Unit → State → Prop} :
    Triple m (.assign index value) scratch
      (fun store state => ∃ result afterValue next,
        value.eval scratch state = some (result, afterValue) ∧
        afterValue.set? index (type.value result) = some next ∧ R store next) R := by
  intro env store state values rest Q hPre hPost
  obtain ⟨result, afterValue, next, hValue, hSet, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.singleton_append]
  apply Expr.program_spec value scratch state afterValue result values m env store
    (.localSet index :: rest) Q hValue
  exact localSet_spec hSet (hPost store next hNext)

theorem Stmt.seq_spec {first second : Stmt} {scratch : Nat}
    {P M R : Store Unit → State → Prop}
    (hFirst : Triple m first scratch P M) (hSecond : Triple m second scratch M R) :
    Triple m (.seq first second) scratch P R := by
  intro env store state values rest Q hPre hPost
  simp only [Stmt.program, List.append_assoc]
  exact hFirst env store state values (second.program scratch ++ rest) Q hPre
    fun store' state' hMid => hSecond env store' state' values rest Q hMid hPost

theorem Stmt.ite_spec {condition : Expr .bool} {thenStmt elseStmt : Stmt} {scratch : Nat}
    {PThen PElse R : Store Unit → State → Prop}
    (hThen : Triple m thenStmt scratch PThen R) (hElse : Triple m elseStmt scratch PElse R) :
    Triple m (.ite condition thenStmt elseStmt) scratch
      (fun store state => ∃ result afterCondition,
        condition.eval scratch state = some (result, afterCondition) ∧
        if result then PThen store afterCondition else PElse store afterCondition) R := by
  intro env store state values rest Q hPre hPost
  obtain ⟨result, afterCondition, hCondition, hBranch⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.singleton_append]
  apply Expr.program_spec condition scratch state afterCondition result values m env store
    (.iff 0 0 (thenStmt.program scratch) (elseStmt.program scratch) :: rest) Q hCondition
  try simp only [Wasm.wp_iff_control_types]
  refine Wasm.wp_iff_cons rfl ?_
  cases result
  · rw [ite_eq_right (by simp)]
    rw [← List.append_nil (elseStmt.program scratch)]
    apply hElse env store afterCondition values [] _ (by simpa using hBranch)
    intro store' state' hR
    simpa [wp_simp, State.toLocals] using hPost store' state' hR
  · rw [ite_eq_left (by simp)]
    rw [← List.append_nil (thenStmt.program scratch)]
    apply hThen env store afterCondition values [] _ (by simpa using hBranch)
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
    (hBody : ∀ n, Triple m body scratch
      (fun store state => ∃ before, Inv store before ∧ measure store before = n ∧
        condition.eval scratch before = some (true, state))
      (fun store state => Inv store state ∧ measure store state < n)) :
    Triple m (.while condition body) scratch Inv
      (fun store state => ∃ before, Inv store before ∧
        condition.eval scratch before = some (false, state)) := by
  intro env store state values rest Q hPre hPost
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
        [.br 0] _ ⟨current, hCurrent, rfl, hEval⟩
      intro store' state' ⟨hInv', hDecrease⟩
      simp only [Wasm.wp_br_cons]
      constructor
      · exact ⟨state', rfl, hInv'⟩
      · simpa [loopMeasure, State.ofLocals, State.toLocals] using hDecrease

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

/-- A load reads the word at the address's low 32 bits, which must lie inside
memory. -/
theorem Stmt.load_spec {type : ScalarType} {index scratch : Nat} {address : Expr .u64}
    {R : Store Unit → State → Prop} :
    Triple m (.load type index address) scratch
      (fun store state => ∃ word afterAddress next,
        address.eval scratch state = some (word, afterAddress) ∧
        word.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 ∧
        afterAddress.set? index (type.ofBits (store.mem.read64 word.toUInt32)) = some next ∧
        R store next) R := by
  intro env store state values rest Q hPre hPost
  obtain ⟨word, afterAddress, next, hAddress, hBounds, hSet, hNext⟩ := hPre
  simp only [Stmt.program, List.append_assoc, List.cons_append, List.nil_append]
  apply Expr.program_spec address scratch state afterAddress word values m env store
    (.wrapI64 :: .load64 0 :: (type.fromBits ++ .localSet index :: rest)) Q hAddress
  simp only [Wasm.wp_wrapI64_cons, Wasm.wp_load64_cons, State.toLocals, ScalarType.value,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (by omega)]
  cases type <;>
    simpa [ScalarType.fromBits] using localSet_spec (values := values) (rest := rest) (Q := Q)
      (module_ := m) (env := env) (store := store) hSet (hPost store next hNext)

/-- A store writes the value's word at the address's low 32 bits, which must lie
inside memory. -/
theorem Stmt.store_spec {scratch : Nat} {address value : Expr .u64}
    {R : Store Unit → State → Prop} :
    Triple m (.store address value) scratch
      (fun store state => ∃ word afterAddress result afterValue,
        address.eval scratch state = some (word, afterAddress) ∧
        value.eval scratch afterAddress = some (result, afterValue) ∧
        word.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 ∧
        R { store with mem := store.mem.write64 word.toUInt32 result } afterValue) R := by
  intro env store state values rest Q hPre hPost
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

/-- Evaluates `args` from left to right. -/
def Expr.evalAll (scratch : Nat) : List (Expr .u64) → State → Option (List UInt64 × State)
  | [], state => some ([], state)
  | arg :: rest, state => do
      let (word, next) ← arg.eval scratch state
      let (words, final) ← Expr.evalAll scratch rest next
      pure (word :: words, final)

theorem Expr.evalAll_length {scratch : Nat} {args : List (Expr .u64)} {state next : State}
    {words : List UInt64} (h : Expr.evalAll scratch args state = some (words, next)) :
    words.length = args.length := by
  induction args generalizing state words with
  | nil => simp [Expr.evalAll] at h; simp [← h.1]
  | cons arg rest ih =>
      simp only [Expr.evalAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨word, afterArg⟩, -, ⟨words', final⟩, hRest, hPure⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hPure
      obtain ⟨rfl, rfl⟩ := hPure
      simp [ih hRest]

/-- The code of `args` pushes their values, the last on top. -/
theorem Expr.evalAll_program_spec {scratch : Nat} {args : List (Expr .u64)}
    {state next : State} {words : List UInt64} {values : List Value} {env : HostEnv Unit}
    {store : Store Unit} {rest : Program} {Q : Assertion Unit}
    (hEval : Expr.evalAll scratch args state = some (words, next))
    (hNext : wp m rest Q store (next.toLocals (words.reverse.map .i64 ++ values)) env) :
    wp m (args.flatMap (·.program scratch) ++ rest) Q store (state.toLocals values) env := by
  induction args generalizing state words values with
  | nil =>
      simp only [Expr.evalAll, Option.some.injEq, Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      simpa using hNext
  | cons arg others ih =>
      simp only [Expr.evalAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at hEval
      obtain ⟨⟨word, afterArg⟩, hArg, ⟨words', final⟩, hRest, hPure⟩ := hEval
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hPure
      obtain ⟨rfl, rfl⟩ := hPure
      simp only [List.flatMap_cons, List.append_assoc]
      apply Expr.program_spec arg scratch state afterArg word values m env store _ Q hArg
      exact ih (values := .i64 word :: values) hRest (by simpa [ScalarType.value] using hNext)

/-- A call evaluates its arguments, runs the callee, whose specification
`Post` describes the store and results it ends with, and stores the single result
when `result` names a local.  A call without a result local requires the callee
to return nothing. -/
theorem Stmt.call_spec {scratch func : Nat} {args : List (Expr .u64)} {result : Option Nat}
    {f : Wasm.Function} {R : Store Unit → State → Prop}
    (hImport : m.imports[func]? = none)
    (hFunc : m.funcs[func - m.imports.length]? = some f)
    (hParams : args.length = f.numParams) :
    Triple m (.call func args result) scratch
      (fun store state => ∃ words afterArgs, ∃ Post : Store Unit → List Value → Prop,
        Expr.evalAll scratch args state = some (words, afterArgs) ∧
        (∀ env, TerminatesWith env m func store (words.reverse.map .i64) Post) ∧
        ∀ store' out, Post store' out →
          match result with
          | none => out = [] ∧ R store' afterArgs
          | some index => ∃ word next, out = [.i64 word] ∧
              afterArgs.set? index (.i64 word) = some next ∧ R store' next)
      R := by
  intro env store state values rest Q hPre hPost
  obtain ⟨words, afterArgs, Post, hArgs, hRun, hResult⟩ := hPre
  simp only [Stmt.program, List.append_assoc]
  apply Expr.evalAll_program_spec hArgs
  have hLength : (words.reverse.map Value.i64).length = f.numParams := by
    simp [Expr.evalAll_length hArgs, hParams]
  refine wp_call_tw ((hRun env).append_args hImport hFunc hLength values) ?_
  rintro store' _ ⟨out, rfl, hOut⟩
  cases result with
  | none =>
      obtain ⟨rfl, hR⟩ := hResult store' out hOut
      simpa using hPost store' afterArgs hR
  | some index =>
      obtain ⟨word, next, rfl, hSet, hR⟩ := hResult store' out hOut
      exact localSet_spec hSet (hPost store' next hR)

end Project.IR
